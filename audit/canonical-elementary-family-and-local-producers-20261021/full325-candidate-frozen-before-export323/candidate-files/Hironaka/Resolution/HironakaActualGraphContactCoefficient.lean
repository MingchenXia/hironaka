/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.LocalGiraudRegularZeroSetOriginalExact
import Hironaka.Resolution.HironakaActualGraphFunctionalIdeal
import Hironaka.MarkedIdeal.MaximalContact
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.MarkedIdeal.LocalGiraudTransform

/-!
# Genuine graph-normal contact and whole marking-one coefficient slice

The literal graph normal has true derivative one. Actual section/projection
relations remove the entire original added graph equation on a smooth contact
hypersurface, without making the arbitrary singular lower graph the ambient N.
-/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaActualGraphContactCoefficient
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm RelativePrincipalizationSpan
  HironakaRelativeNormalIdeal HironakaActualCentreJointJets HironakaActualHolomorphicGraphIdeal
  HironakaActualGraphFunctionalIdeal HironakaActualCylinderPullbackOrigin
  DerivativeIdeal MaximalContact CoefficientIdeal MarkedIdeals IdealWeightPowers HomogenizedGlueing
variable {d t : ℕ}

/-- The actual preferred-chart graph-normal derivative is literally one. -/
theorem graphFunction_chartDeriv_eq_one (f : ComplexModel d → ComplexModel t)
    (z : ComplexModel (d+t)) (hf : DifferentiableAt ℂ f (tangentProjection d t z)) (i : Fin t) :
    chartDeriv (complexChartAt z) (actualJointNormalInclusion d t (EuclideanSpace.single i 1))
      (graphFunction f i) z = 1 := by
  have hcomp := (EuclideanSpace.proj i : ComplexModel t →L[ℂ] ℂ).hasFDerivAt.comp z
    (hf.hasFDerivAt.comp z (tangentProjection d t).hasFDerivAt)
  have hder := (EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).hasFDerivAt.sub hcomp
  change HasFDerivAt (graphFunction f i) _ z at hder
  change fderiv ℂ (graphFunction f i ∘ (complexChartAt z).val.symm) ((complexChartAt z).val z) _ = 1
  simp only [complexChartAt,chartAt_self_eq,OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply,Function.comp_id]
  change (fderiv ℂ (graphFunction f i) z) _ = 1
  rw [hder.fderiv]
  simp [ContinuousLinearMap.comp_apply]

private theorem graphFunction_holomorphicAt (f : ComplexModel d → ComplexModel t)
    {z : ComplexModel (d+t)} (hf : ∀ᶠ x in nhds (tangentProjection d t z),DifferentiableAt ℂ f x)
    (i : Fin t) : HolomorphicAt (d+t) (graphFunction f i) z := by
  have hp := (tangentProjection d t).continuous.tendsto z
  exact (hp.eventually hf).mono fun y hy =>
    ((EuclideanSpace.proj (i.natAdd d) : ComplexModel (d+t) →L[ℂ] ℂ).differentiableAt.sub
      ((EuclideanSpace.proj i : ComplexModel t →L[ℂ] ℂ).differentiableAt.comp y
        (hy.comp y (tangentProjection d t).differentiableAt))).mdifferentiableAt

/-- A genuine normal graph equation is a marking-one tangent direction on its TRUE ambient open. -/
theorem graphFunction_isTangentDirection (f : ComplexModel d → ComplexModel t)
    (W : Set (ComplexModel d)) (U : Opens (ComplexModel d)) (hf : ContDiffOn ℂ ∞ f U) (i : Fin t) :
    IsTangentDirection (vanishingIdeal (n := d+t) (graphCarrier f W)) 1
      ((tangentProjection d t) ⁻¹' U) (graphFunction f i) := by
  have hhol (z : ComplexModel (d+t)) (hz : tangentProjection d t z ∈ U) :
      ∀ᶠ x in nhds (tangentProjection d t z),DifferentiableAt ℂ f x := by
    filter_upwards [U.isOpen.mem_nhds hz] with x hx
    exact (hf.contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt (by simp)
  refine ⟨U.isOpen.preimage (tangentProjection d t).continuous,?_,?_⟩
  · intro z hz
    change (vanishingIdeal (n := d+t) (graphCarrier f W)).mem z (graphFunction f i)
    refine ⟨graphFunction_holomorphicAt f (hhol z hz) i,Eventually.of_forall fun y hy => ?_⟩
    have he := congrArg (fun v : ComplexModel t => v i) hy.2
    exact sub_eq_zero.mpr he
  · intro z hz _hu
    refine ⟨complexChartAt z,actualJointNormalInclusion d t (EuclideanSpace.single i 1),
      mem_complexChartAt_source z,?_⟩
    rw [graphFunction_chartDeriv_eq_one f z (hhol z hz).self_of_nhds i]
    exact one_ne_zero

/-- True graph-normal contact gives an ACTUAL regular hypersurface on the same true ambient open. -/
theorem graphNormalContact_regularAtDim (f : ComplexModel d → ComplexModel t)
    (U : Opens (ComplexModel d)) (hf : ContDiffOn ℂ ∞ f U) (i : Fin t)
    {z : ComplexModel (d+t)} (hz : tangentProjection d t z ∈ U) (hu : graphFunction f i z=0) :
    RegularAtDim (n := d+t)
      ({y | graphFunction f i y=0} ∩ (tangentProjection d t) ⁻¹' U) z (d+t-1) := by
  have ht := graphFunction_isTangentDirection f univ U hf i
  exact LocalGiraudTransform.regularAtDim_zeroSet ht.isOpen (fun y hy => (ht.mem y hy).1)
    ht.multiplicity_one hz hu

private theorem mem_vanishing_of_span {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (W : Set M) {x : M} {F : M → ℂ}
    (hF : IsInSpanAt (n := n) ((vanishingIdeal (n := n) W).mem x) x F) :
    (vanishingIdeal (n := n) W).mem x F := by
  obtain ⟨hhol,N,s,a,hs,_ha,he⟩ := hF
  refine ⟨hhol,?_⟩
  have hall : ∀ᶠ y in nhds x,∀ i : Fin N,y ∈ W → s i y=0 := eventually_all.mpr fun i => (hs i).2
  filter_upwards [he,hall] with y hy hys hyW
  rw [hy]
  exact Finset.sum_eq_zero fun i _ => by rw [hys i hyW,mul_zero]

/-- Actual whole original graph-section pullback recovers the independent original base ideal. -/
theorem graphSection_pullback_mem_iff (f : ComplexModel d → ComplexModel t)
    (x : ComplexModel d) (hf : ∀ᶠ u in nhds x,DifferentiableAt ℂ f u)
    (W : Set (ComplexModel d)) (F : ComplexModel d → ℂ) :
    (GermIdeal.pullback (m := d) (graphSection f)
      (vanishingIdeal (n := d+t) (graphCarrier f W))).mem x F ↔
      (vanishingIdeal (n := d) W).mem x F := by
  have hsec : ∀ᶠ u in nhds x,DifferentiableAt ℂ (graphSection f) u :=
    hf.mono fun u hu => (tangentInclusion d t).differentiableAt.add
      ((actualJointNormalInclusion d t).differentiableAt.comp u hu)
  have hscont : Tendsto (graphSection f) (nhds x) (nhds (graphSection f x)) :=
    hsec.self_of_nhds.continuousAt.tendsto
  constructor
  · intro hF
    change IsInSpanAt (n := d) (fun s => ∃ a,
      (vanishingIdeal (n := d+t) (graphCarrier f W)).mem (graphSection f x) a ∧ s=a∘graphSection f) x F at hF
    apply mem_vanishing_of_span W
    apply IsInSpanAt.mono ?_ hF
    rintro _ ⟨a,ha,rfl⟩
    refine ⟨?_,?_⟩
    · filter_upwards [hsec,hscont.eventually ha.1] with u hu hau
      exact hau.comp u hu.mdifferentiableAt
    · filter_upwards [hscont.eventually ha.2] with u hu huW
      exact hu ⟨by simpa using huW,by simp⟩
  · intro hF
    let a : ComplexModel (d+t) → ℂ := F ∘ tangentProjection d t
    have hp : Tendsto (tangentProjection d t) (nhds (graphSection f x)) (nhds x) := by
      simpa only [projection_graphSection] using (tangentProjection d t).continuous.tendsto (graphSection f x)
    have ha : (vanishingIdeal (n := d+t) (graphCarrier f W)).mem (graphSection f x) a := by
      refine ⟨?_,?_⟩
      · filter_upwards [hp.eventually hF.1] with z hz
        exact hz.comp z (tangentProjection d t).differentiableAt.mdifferentiableAt
      · filter_upwards [hp.eventually hF.2] with z hz hzW
        exact hz hzW.1
    have he : a ∘ graphSection f=F := by
      funext u
      simp [a,Function.comp_def]
    change IsInSpanAt (n := d) (fun s => ∃ a,
      (vanishingIdeal (n := d+t) (graphCarrier f W)).mem (graphSection f x) a ∧ s=a∘graphSection f) x F
    exact InvertibleIdealQuotient.isInSpanAt_self ⟨a,ha,he.symm⟩ hF.1

private theorem idealPow_one_vanishing_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] (W : Set M) :
    idealPow (vanishingIdeal (n := n) W) 1=vanishingIdeal (n := n) W := by
  apply GermIdeal.ext
  funext x F
  apply propext
  constructor
  · intro hF
    change IsInSpanAt (n := n) (fun s => ∃ a b,HolomorphicAt n a x ∧
      (vanishingIdeal (n := n) W).mem x b ∧ s=a*b) x F at hF
    apply mem_vanishing_of_span W
    apply IsInSpanAt.mono ?_ hF
    rintro _ ⟨a,b,ha,hb,rfl⟩
    refine ⟨ha.mul hb.1,hb.2.mono fun y hy hyW => ?_⟩
    change a y*b y=0
    rw [hy hyW,mul_zero]
  · intro hF
    change IsInSpanAt (n := n) (fun s => ∃ a b,HolomorphicAt n a x ∧
      (vanishingIdeal (n := n) W).mem x b ∧ s=a*b) x F
    exact InvertibleIdealQuotient.isInSpanAt_self
      ⟨fun _ => 1,F,holomorphicAt_const 1,hF,by funext y;simp⟩ hF.1

/-- The marking-one original graph ideal retains its FULL smooth ambient stratum and empty boundary. -/
def graphMarked (f : ComplexModel d → ComplexModel t) (W : Set (ComplexModel d)) :
    MarkedIdeal (d+t) (ComplexModel (d+t)) where
  N := univ
  E := []
  ideal := vanishingIdeal (n := d+t) (graphCarrier f W)
  d := 1

private theorem coeffMarked_graphMarked_ideal (f : ComplexModel d → ComplexModel t)
    (W : Set (ComplexModel d)) :
    (coeffMarked (graphMarked f W)).ideal=vanishingIdeal (n := d+t) (graphCarrier f W) := by
  have h0 : sumExp (fun j : ℕ => 1-j) 1 0=1 := by simp [sumExp]
  apply GermIdeal.ext
  funext z F
  apply propext
  change IsInSpanAt (n := d+t) (fun s => ∃ i,i<1 ∧
    (idealPow (iterDerivIdeal (vanishingIdeal (n := d+t) (graphCarrier f W)) i)
      (sumExp (fun j => 1-j) 1 i)).mem z s) z F ↔ _
  constructor
  · intro hF
    apply mem_vanishing_of_span (graphCarrier f W)
    apply IsInSpanAt.mono ?_ hF
    rintro s ⟨i,hi,hs⟩
    obtain rfl : i=0 := by omega
    simpa only [iterDerivIdeal_zero,h0,idealPow_one_vanishing_eq] using hs
  · intro hF
    apply InvertibleIdealQuotient.isInSpanAt_self (g := F) ?_ hF.1
    refine ⟨0,by omega,?_⟩
    simpa only [iterDerivIdeal_zero,h0,idealPow_one_vanishing_eq] using hF

/-- The actual marking-one coefficient ideal has the SAME genuine whole original graph-section slice. -/
theorem coefficientGraphSection_mem_iff (f : ComplexModel d → ComplexModel t)
    (x : ComplexModel d) (hf : ∀ᶠ u in nhds x,DifferentiableAt ℂ f u)
    (W : Set (ComplexModel d)) (F : ComplexModel d → ℂ) :
    (GermIdeal.pullback (m := d) (graphSection f) (coeffMarked (graphMarked f W)).ideal).mem x F ↔
      (vanishingIdeal (n := d) W).mem x F := by
  rw [coeffMarked_graphMarked_ideal]
  exact graphSection_pullback_mem_iff f x hf W F

/-- A TRUE scalar normal-contact slice removes ONE added graph equation above an arbitrary singular lower graph. -/
theorem coefficientGraphSection_lowerGraph_mem_iff (f : ComplexModel d → ComplexModel t)
    (u : ComplexModel (d+t) → ComplexModel 1) (x : ComplexModel (d+t))
    (hu : ∀ᶠ z in nhds x,DifferentiableAt ℂ u z) (W : Set (ComplexModel d))
    (F : ComplexModel (d+t) → ℂ) :
    (GermIdeal.pullback (m := d+t) (graphSection u)
      (coeffMarked (graphMarked u (graphCarrier f W))).ideal).mem x F ↔
      (vanishingIdeal (n := d+t) (graphCarrier f W)).mem x F :=
  coefficientGraphSection_mem_iff u x hu (graphCarrier f W) F

/-- Original near-point data internally choose a GENUINE smooth scalar graph contact and remove its ONE normal equation. -/
theorem exists_scalarGraphContactCoefficientSlice (f : ComplexModel d → ComplexModel t)
    (u : ComplexModel (d+t) → ComplexModel 1) (x : ComplexModel (d+t))
    (hu : ∀ᶠ z in nhds x,DifferentiableAt ℂ u z) (W : Set (ComplexModel d)) :
    ∃ U : Opens (ComplexModel (d+t)),x ∈ U ∧
      IsTangentDirection (vanishingIdeal (n := (d+t)+1) (graphCarrier u (graphCarrier f W))) 1
        ((tangentProjection (d+t) 1) ⁻¹' U) (graphFunction u 0) ∧
      RegularAtDim (n := (d+t)+1)
        ({z | graphFunction u 0 z=0} ∩ (tangentProjection (d+t) 1) ⁻¹' U)
        (graphSection u x) (d+t) ∧
      ∀ F : ComplexModel (d+t) → ℂ,
        (GermIdeal.pullback (m := d+t) (graphSection u)
          (coeffMarked (graphMarked u (graphCarrier f W))).ideal).mem x F ↔
          (vanishingIdeal (n := d+t) (graphCarrier f W)).mem x F := by
  obtain ⟨A,hA,hAo,hxA⟩ := eventually_nhds_iff.mp hu
  let U : Opens (ComplexModel (d+t)) := ⟨A,hAo⟩
  have huc : ContDiffOn ℂ ∞ u U := contDiffOn_of_differentiableOn_complex
    (fun z hz => (hA z hz).differentiableWithinAt) hAo
  refine ⟨U,hxA,graphFunction_isTangentDirection u (graphCarrier f W) U huc 0,?_,?_⟩
  · have hzero : graphFunction u 0 (graphSection u x)=0 := by simp [graphFunction,graphSection,tangentProjection_tangentInclusion]
    have hxU : x ∈ U := hxA
    have hr := graphNormalContact_regularAtDim u U huc 0
      (by simpa only [projection_graphSection] using hxU) hzero
    simpa only [Nat.add_sub_cancel] using hr
  · exact fun F => coefficientGraphSection_lowerGraph_mem_iff f u x hu W F

end
end Hironaka.HironakaActualGraphContactCoefficient
