/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.HadamardControlledCoherenceOriginalExact
import Hironaka.Resolution.HironakaActualPointWeightedCoefficientTracking
import Hironaka.Resolution.HironakaActualFixedFlatteningBlowupCoordinates
import Hironaka.Resolution.HironakaActualCoherentWeightedCoefficientMarked
import Hironaka.Resolution.HironakaSmoothSubmersionGermIdealColon
import Hironaka.Resolution.HironakaSharpActualControlledRelativeSaturation
import Hironaka.Resolution.HironakaActualSingularChartTransport

/-! Whole weighted controlled stalks in genuine arbitrary-centre blowup charts.
The actual global blowup, fixed identity target flattening and universal local
inverse internally construct the whole square. Original positive marks and
entire coefficient families are retained; no full relative HS/history claim.
Blueprint: hironaka-actual-centre-weighted-controlled-stalk-extension.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualCentreWeightedControlledStalk
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  InvertibleIdealQuotient RelativePrincipalizationSpan BlowupFlatCoordinates
  HironakaSmoothSubmersionGermIdealColon HironakaActualSingularChartTransport
  HironakaActualAnalyticBlowupTaylor HironakaActualCoherentWeightedCoefficientMarked
  HironakaActualWeightedCoefficientCompression FiniteGermIdealPullbackGenerators
  ManifoldFiniteSpanChartTransport EuclideanHolomorphicGermSpan
  BlowupExceptionalDivisor BlowupControlledTransform IdealWeightPowers BlowupTowers
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaSharpOriginalMemberProduct
  HironakaSharpActualControlledRelativeSaturation MemberPullback

private theorem adaptedIdeal_eq_span_of_generation {n r : ℕ} {Y : Type}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    (J : GermIdeal n Y) (hJ : J.IsCoherent) (y : Y)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
    (h0 : Θ.toFun (chartAt (ComplexModel n) y y)=0)
    (G : Fin r → Y → ℂ) (hG : ∀ i,HolomorphicAt n (G i) y)
    (hgen : ∀ F,J.mem y F ↔ IsInSpanAt (n := n) (·∈range G) y F) :
    adaptedIdeal J y Θ h0=Ideal.span (range fun i => adaptedGerm y Θ h0 (G i) (hG i)) := by
  ext g
  obtain ⟨F,hF,rfl⟩ := exists_original_adapted_representative y Θ h0 g
  rw [mem_adaptedIdeal_iff J hJ y Θ h0 F hF,hgen F]
  exact (isInSpanAt_comp_adapted_iff y Θ h0 G F).trans
    (isInSpanAt_iff_holGerm_mem_span _
      (fun i => (holomorphic_adapted_iff y Θ h0 (G i)).mpr (hG i))
      ((holomorphic_adapted_iff y Θ h0 F).mpr hF))

private theorem idealPow_principal_mem_iff {n : ℕ} {Y : Type}
    [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
    {A : GermIdeal n Y} {y : Y} {a : Y → ℂ} (ha : HolomorphicAt n a y)
    (hA : ∀ g,A.mem y g ↔ IsInSpanAt (n := n) (·=a) y g) :
    ∀ q g,(idealPow A q).mem y g ↔ IsInSpanAt (n := n) (·=a^q) y g := by
  intro q
  induction q with
  | zero => exact unit_mem_iff_principal
  | succ q ih =>
    exact mul_mem_iff_principal (BlowupDerivativeIdeal.holomorphicAt_pow ha q) ha ih hA

section RealChart
variable {n : ℕ} (U : TopologicalSpace.Opens (ComplexModel n))
  (h0U : (0 : ComplexModel n)∈U) {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y] {π : Y → U}
  (y : Y) (S : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
  (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
  (hΘsrc : Θ.source⊆(chartAt (ComplexModel n) y).target)
  (hΘ0 : Θ.toFun (chartAt (ComplexModel n) y y)=0)
  (hSquare : ∀ z : Y,z∈(chartAt (ComplexModel n) y).source →
    chartAt (ComplexModel n) y z∈Θ.source →
      (π z : ComplexModel n)=actualAnalyticBlowupMap S e b (Θ.toFun (chartAt (ComplexModel n) y z)))

include hΘsrc hΘ0 hSquare in
private theorem inverse_square : ∀ᶠ u in 𝓝 (0 : ComplexModel n),
    (π (inverseCoordinates Θ u) : ComplexModel n)=actualAnalyticBlowupMap S e b u := by
  have htar : (0 : ComplexModel n)∈Θ.target := by
    simpa only [hΘ0] using Θ.mapsTo_toFun Θ.center_mem_source
  filter_upwards [Θ.isOpen_target.mem_nhds htar] with u hu
  have hm := flatInverse_mem Θ hu hΘsrc
  have h := hSquare (inverseCoordinates Θ u) hm.1.1 hm.1.2
  change (π (inverseCoordinates Θ u) : ComplexModel n)=actualAnalyticBlowupMap S e b u
  simpa only [inverseCoordinates,hm.2] using h

include hΘsrc hΘ0 hSquare in
private theorem adapted_restricted_composition (c : ComplexModel n → ℂ)
    (hc : ∀ᶠ z in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ c z)
    (hcomp : HolomorphicAt n (fun z : Y => c (π z)) y) :
    adaptedGerm y Θ hΘ0 (fun z : Y => c (π z)) hcomp=
      actualAnalyticBlowupPullback S e b (HolGerm.mk c hc) := by
  unfold actualAnalyticBlowupPullback
  rw [compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact (inverse_square U y S e b Θ hΘsrc hΘ0 hSquare).mono fun u hu => congrArg c hu

include hΘsrc hSquare in
/-- The actual sheaf total pullback has exactly the WHOLE literal powered
coefficient germ image in the SAME genuine affine chart. -/
theorem actual_weighted_total_stalk {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (c : ι → ComplexModel n → ℂ)
    (hc : ∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i) U)
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π) :
    adaptedIdeal (GermIdeal.pullback (m := n) π (weightedFunctionIdeal (n := n) w (fun i (z : U) => c i z))) y Θ hΘ0=
      Ideal.map (actualAnalyticBlowupPullback S e b).toRingHom
        (weightedCompression w (fun i => HolGerm.mk (c i)
          ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) h0U).mono fun _ hz => hz.differentiableAt))) := by
  let E := Fintype.equivFin ι
  let G : Fin (Fintype.card ι) → U → ℂ := fun j z => c (E.symm j) z^
    (weightedCommonMark w/w (E.symm j))
  have hcU (i : ι) : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (fun z : U => c i z) := by
    intro z
    exact ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) z.property).comp_contMDiff
      (Eventually.of_forall fun _ => (contMDiff_subtype_val (U := U)).contMDiffAt)).mdifferentiableAt
  have hJ := isCoherent_weightedFunctionIdeal (n := n) w (fun i (z : U) => c i z) hcU
  have hG (j : Fin (Fintype.card ι)) : HolomorphicAt n (G j) (π y) :=
    holomorphicAt_of_mdifferentiableOn isOpen_univ ((hcU (E.symm j)).pow _).mdifferentiableOn (mem_univ _)
  have hr : range G=range (fun i (z : U) => c i z^(weightedCommonMark w/w i)) := by
    ext f
    constructor
    · rintro ⟨j,rfl⟩;exact ⟨E.symm j,rfl⟩
    · rintro ⟨i,rfl⟩;exact ⟨E i,by simp [G]⟩
  have hgen (f : U → ℂ) : (weightedFunctionIdeal (n := n) w (fun i (z : U) => c i z)).mem (π y) f ↔
      IsInSpanAt (n := n) (·∈range G) (π y) f := by
    change IsInSpanAt (n := n) (·∈range (fun i (z : U) => c i z^(weightedCommonMark w/w i))) (π y) f ↔ _
    rw [hr]
  have hGP (j : Fin (Fintype.card ι)) : HolomorphicAt n (G j∘π) y :=
    (hG j).comp_contMDiff (Eventually.of_forall fun _ => hπ.contMDiffAt)
  rw [adaptedIdeal_eq_span_of_generation _ (GermIdealPullbackCalculus.isCoherent_pullback hπ hJ)
    y Θ hΘ0 (fun j => G j∘π) hGP
      (mem_pullback_iff_of_finite_generation (Eventually.of_forall fun _ => hπ.contMDiffAt) _ G hG hgen)]
  unfold weightedCompression
  rw [Ideal.map_span,←Set.range_comp]
  apply congrArg Ideal.span
  ext g
  constructor
  · rintro ⟨j,rfl⟩
    refine ⟨E.symm j,?_⟩
    have h := adapted_restricted_composition U y S e b Θ hΘsrc hΘ0 hSquare
      (fun u => c (E.symm j) u^(weightedCommonMark w/w (E.symm j)))
      (eventually_differentiableAt_pow
        ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc (E.symm j)) h0U).mono fun _ hz => hz.differentiableAt) _) (hGP j)
    rw [HolGerm.mk_pow (c (E.symm j))
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc (E.symm j)) h0U).mono fun _ hz => hz.differentiableAt) _,map_pow] at h
    change (actualAnalyticBlowupPullback S e b)
      ((HolGerm.mk (c (E.symm j)) ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc (E.symm j)) h0U).mono fun _ hz => hz.differentiableAt))^
        (weightedCommonMark w/w (E.symm j)))=adaptedGerm y Θ hΘ0 (G j∘π) (hGP j)
    rw [map_pow]
    exact h.symm
  · rintro ⟨i,rfl⟩
    refine ⟨E i,?_⟩
    have h := adapted_restricted_composition U y S e b Θ hΘsrc hΘ0 hSquare
      (fun u => c (E.symm (E i)) u^(weightedCommonMark w/w (E.symm (E i))))
      (eventually_differentiableAt_pow
        ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc (E.symm (E i))) h0U).mono fun _ hz => hz.differentiableAt) _) (hGP (E i))
    rw [HolGerm.mk_pow (c (E.symm (E i)))
      ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc (E.symm (E i))) h0U).mono fun _ hz => hz.differentiableAt) _,map_pow] at h
    simp only [Equiv.symm_apply_apply] at h
    change adaptedGerm y Θ hΘ0 (G (E i)∘π) (hGP (E i))=
      (actualAnalyticBlowupPullback S e b)
        ((HolGerm.mk (c i) ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) h0U).mono fun _ hz => hz.differentiableAt))^
          (weightedCommonMark w/w i))
    rw [map_pow]
    simpa only [G,Equiv.symm_apply_apply,Function.comp_def] using h

include hΘsrc hSquare in
/-- The actual exceptional denominator is internally the literal pivot power
in the SAME chart; no exceptional-stalk equality is an input. -/
theorem actual_exceptional_power_stalk
    (he : e∈S)
    (hπ : IsBlowupAlong n ((Subtype.val : U → ComplexModel n) ⁻¹' {x | ∀ i∈S,x i=0}) π) (q : ℕ) :
    adaptedIdeal (idealPow (exceptionalDivisor hπ).ideal q) y Θ hΘ0=
      Ideal.span {(coordinateGerm e)^q} := by
  have hflat : ∀ {z : Y},z∈(chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z∈Θ.source →
        (z∈π ⁻¹' ((Subtype.val : U → ComplexModel n) ⁻¹' {x | ∀ i∈S,x i=0}) ↔
          Θ.toFun (chartAt (ComplexModel n) y z) e=0) := by
    intro z hz hzΘ
    have hs := hSquare z hz hzΘ
    constructor
    · intro hzC
      have hp : (π z : ComplexModel n) e=0 := hzC e he
      have hev := congrArg (fun v : ComplexModel n => v e) hs
      simpa [hp,actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,he] using hev.symm
    · intro hz0 i hi
      rw [hs,actualAnalyticBlowupMap_apply]
      simp [actualAnalyticBlowupCoordinate,hi,hz0]
  have hE : (exceptionalDivisor hπ).ideal=vanishingIdeal (n := n)
      (π ⁻¹' ((Subtype.val : U → ComplexModel n) ⁻¹' {x | ∀ i∈S,x i=0})) := by
    rw [exceptionalDivisor_ideal]
    exact actual_pullback_centre_ideal_eq_exceptional_vanishing
      (X := CMfd.of (n := n) U) (Y := CMfd.of (n := n) Y) hπ
  let a := flatCoord Θ e
  have ha : HolomorphicAt n a y := holomorphicAt_flatCoord Θ e (mem_flatDomain_self Θ)
  have hgen : ∀ g,(exceptionalDivisor hπ).ideal.mem y g ↔ IsInSpanAt (n := n) (·=a) y g := by
    rw [hE]
    exact vanishingIdeal_mem_iff_flatCoord Θ hflat (mem_flatDomain_self Θ)
  have hpow := idealPow_principal_mem_iff ha hgen q
  have hag : adaptedGerm y Θ hΘ0 (a^q) (BlowupDerivativeIdeal.holomorphicAt_pow ha q)=(coordinateGerm e)^q := by
    change HolGerm.mk _ _=(coordinateGerm e)^q
    change HolGerm.mk _ _=(HolGerm.mk (fun u : ComplexModel n => u e)
      (HolomorphicGermReducednessBridge.eventually_differentiableAt_coordinate e))^q
    rw [←HolGerm.mk_pow]
    apply HolGerm.mk_eq_mk_iff.mpr
    have htar : (0 : ComplexModel n)∈Θ.target := by
      simpa only [hΘ0] using Θ.mapsTo_toFun Θ.center_mem_source
    filter_upwards [Θ.isOpen_target.mem_nhds htar] with u hu
    have hm := (flatInverse_mem Θ hu hΘsrc).2
    exact congrArg (fun v : ComplexModel n => v e^q) hm
  have heq := adaptedIdeal_eq_span_of_generation _
    (GermIdealPullbackCalculus.isCoherent_idealPow (DivisorMetric.isCoherent_of_isInvertible (exceptionalDivisor hπ).isInvertible) q)
    y Θ hΘ0 (fun _ : Fin 1 => a^q) (fun _ => BlowupDerivativeIdeal.holomorphicAt_pow ha q)
    (fun g => (hpow g).trans (isInSpanAt_range_one_iff (a^q) g).symm)
  rw [heq]
  simp only [hag,range_const]

include hΘsrc hSquare in
/-- The actual global blowup's WHOLE controlled sheaf stalk is internally
identified with the true literal powered-coefficient ring colon. -/
theorem actual_weighted_controlled_stalk {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (c : ι → ComplexModel n → ℂ)
    (hc : ∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i) U)
    (he : e∈S)
    (hπ : IsBlowupAlong n ((Subtype.val : U → ComplexModel n) ⁻¹' {x | ∀ i∈S,x i=0}) π) :
    adaptedIdeal (controlledTransform hπ
      (weightedFunctionIdeal (n := n) w (fun i (z : U) => c i z)) (weightedCommonMark w)) y Θ hΘ0=
      (Ideal.map (actualAnalyticBlowupPullback S e b).toRingHom
        (weightedCompression w (fun i => HolGerm.mk (c i)
          ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) h0U).mono fun _ hz => hz.differentiableAt)))).colon
          {(coordinateGerm e)^weightedCommonMark w} := by
  have hcU (i : ι) : MDifferentiable 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (fun z : U => c i z) := by
    intro z
    exact ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) z.property).comp_contMDiff
      (Eventually.of_forall fun _ => (contMDiff_subtype_val (U := U)).contMDiffAt)).mdifferentiableAt
  have hJ := isCoherent_weightedFunctionIdeal (n := n) w (fun i (z : U) => c i z) hcU
  unfold controlledTransform
  rw [adaptedIdeal_colon_eq _ _ (GermIdealPullbackCalculus.isCoherent_pullback hπ.contMDiff hJ)
    (GermIdealPullbackCalculus.isCoherent_idealPow
      (DivisorMetric.isCoherent_of_isInvertible (exceptionalDivisor hπ).isInvertible) _),
    actual_weighted_total_stalk U h0U y S e b Θ hΘsrc hΘ0 hSquare w c hc hπ.contMDiff,
    actual_exceptional_power_stalk U y S e b Θ hΘsrc hΘ0 hSquare he hπ,
    Ideal.colon_span]

end RealChart

private theorem subtype_chart_apply {n : ℕ} (U : TopologicalSpace.Opens (ComplexModel n)) (x z : U) :
    chartAt (ComplexModel n) x z=(z : ComplexModel n) := by
  rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
  rfl

private def coordinateFlatten {n : ℕ} (U : TopologicalSpace.Opens (ComplexModel n)) (x : U) :
    LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x) where
  source := U
  target := U
  isOpen_source := U.isOpen
  isOpen_target := U.isOpen
  center_mem_source := by rw [subtype_chart_apply];exact x.property
  toFun := id
  invFun := id
  toFun_holomorphic := differentiable_id.differentiableOn
  invFun_holomorphic := differentiable_id.differentiableOn
  mapsTo_toFun := fun _ h => h
  mapsTo_invFun := fun _ h => h
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl

private theorem coordinateFlatten_source {n : ℕ}
    (U : TopologicalSpace.Opens (ComplexModel n)) (x : U) :
    (coordinateFlatten U x).source⊆(chartAt (ComplexModel n) x).target := by
  intro v hv
  rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
  exact (OpenPartialHomeomorph.refl (ComplexModel n)).map_subtype_source ⟨x⟩ (x := ⟨v,hv⟩) (mem_univ v)

open HironakaActualFixedFlatteningBlowupCoordinates

/-- The actual global coordinate-centre blowup internally constructs the SAME
chart in which its entire original weighted controlled sheaf stalk is computed. -/
theorem exists_actual_coordinate_centre_weighted_stalk {n : ℕ}
    (U : TopologicalSpace.Opens (ComplexModel n)) (h0U : (0 : ComplexModel n)∈U)
    (k : ℕ) {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] (π : Y → U)
    (hπ : IsBlowupAlong n ((Subtype.val : U → ComplexModel n) ⁻¹' complexCoordinatePlane n k) π)
    (y : Y) (hy : (π y : ComplexModel n)=0) {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (c : ι → ComplexModel n → ℂ)
    (hc : ∀ i,MDifferentiableOn 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ℂ) (c i) U) :
    ∃ (e : Fin n) (b : Fin n → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) y y))
      (hΘ0 : Θ.toFun (chartAt (ComplexModel n) y y)=0),
      k≤e.val ∧ (∀ i : Fin n,i.val<k → b i=0) ∧ b e=0 ∧
      Θ.source⊆(chartAt (ComplexModel n) y).target ∧
      (∀ z : Y,z∈(chartAt (ComplexModel n) y).source →
        chartAt (ComplexModel n) y z∈Θ.source →
        (π z : ComplexModel n)=actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} e b
          (Θ.toFun (chartAt (ComplexModel n) y z))) ∧
      adaptedIdeal (controlledTransform hπ
        (weightedFunctionIdeal (n := n) w (fun i (z : U) => c i z)) (weightedCommonMark w)) y Θ
          hΘ0=
        (Ideal.map (actualAnalyticBlowupPullback {i : Fin n | k ≤ i.val} e b).toRingHom
          (weightedCompression w (fun i => HolGerm.mk (c i)
            ((holomorphicAt_of_mdifferentiableOn U.isOpen (hc i) h0U).mono fun _ hz => hz.differentiableAt)))).colon
          {(coordinateGerm e)^weightedCommonMark w} := by
  let Φ := coordinateFlatten U (π y)
  have hΦsrc : Φ.source⊆(chartAt (ComplexModel n) (π y)).target := coordinateFlatten_source U (π y)
  have hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π y) (π y))=0 := by
    change chartAt (ComplexModel n) (π y) (π y)=0
    rw [subtype_chart_apply]
    exact hy
  have hflat : ∀ {z : U},z∈(chartAt (ComplexModel n) (π y)).source →
      chartAt (ComplexModel n) (π y) z∈Φ.source →
      (z∈(Subtype.val : U → ComplexModel n) ⁻¹' complexCoordinatePlane n k ↔
        Φ.toFun (chartAt (ComplexModel n) (π y) z)∈complexCoordinatePlane n k) := by
    intro z _ _
    change z.val∈complexCoordinatePlane n k ↔ chartAt (ComplexModel n) (π y) z∈complexCoordinatePlane n k
    rw [subtype_chart_apply]
  obtain ⟨e,b,Θ,hΘsrc,hΘ0,he,hbt,hbe,hSquare⟩ :=
    exists_actual_fixed_flattening_blowup_coordinates hπ y k Φ hΦsrc hΦ0 hflat
  have hsq : ∀ z : Y,z∈(chartAt (ComplexModel n) y).source →
      chartAt (ComplexModel n) y z∈Θ.source →
      (π z : ComplexModel n)=actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} e b
        (Θ.toFun (chartAt (ComplexModel n) y z)) := by
    intro z hz hzΘ
    have h := (hSquare z hz hzΘ).2
    change chartAt (ComplexModel n) (π y) (π z)=_ at h
    rwa [subtype_chart_apply] at h
  refine ⟨e,b,Θ,hΘ0,he,hbt,hbe,hΘsrc,hsq,?_⟩
  exact actual_weighted_controlled_stalk U h0U y {i : Fin n | k ≤ i.val} e b Θ
    hΘsrc hΘ0 hsq w c hc he hπ

open HironakaActualAnalyticVertexCoefficientData HironakaActualCoefficientReducedStrictGenerators
  HironakaActualCoefficientControlledTransform HironakaActualFormalInitialDiagram
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalCoordinatePowerDivision
  HironakaRelativeNormalMonomialBasis HironakaActualRelativeCoefficientGerms
  HironakaRelativeNormalActualBaseJetDimension HironakaHolomorphicPointJets GermIdealOrder
  MarkedIdeals NormalCrossings HironakaActualReducedFormalStandardBasis
  HironakaActualAnalyticStrictGenerators HironakaActualFiniteCoefficientIdeals

local instance (t q : ℕ) : Fintype (normalExponentIndex t q) := normalExponentFintype t q

private theorem coefficient_holomorphic_on_domain {k s t : ℕ}
    {I : Ideal (HolGerm (ComplexModel ((k+s)+t)))}
    (P : ActualAnalyticVertexCoefficientData k s t I) (i : weightedCoefficientIndex k s t I) :
    MDifferentiable 𝓘(ℂ,ComplexModel (k+s)) 𝓘(ℂ,ℂ) (coefficientFunction P i) := by
  intro z
  have hf := holomorphicAt_of_mdifferentiableOn P.isOpen_domain
    (P.regular i.1 i.2.val i.2.property) z.property
  exact (hf.comp_contMDiff (Eventually.of_forall fun _ =>
    (contMDiff_subtype_val (U := coefficientDomain P)).contMDiffAt)).mdifferentiableAt

private theorem source_centre_cosupport {k s t : ℕ}
    {I : Ideal (HolGerm (ComplexModel ((k+s)+t)))}
    (P : ActualAnalyticVertexCoefficientData k s t I)
    (hCos : ∀ i : weightedCoefficientIndex k s t I,
      P.domain∩complexCoordinatePlane (k+s) k⊆cosupport (k+s) univ
        (actualPrincipalCoefficientIdeal (k+s) (P.coefficient i.1 i.2.val)) (coefficientWeight i)) :
    ((Subtype.val : coefficientDomain P → ComplexModel (k+s)) ⁻¹' complexCoordinatePlane (k+s) k)⊆
      (coefficientMarked P).cosupp := by
  intro z hz
  change z∈cosupport (k+s) univ
    (weightedFunctionIdeal coefficientWeight (coefficientFunction P)) (weightedCommonMark coefficientWeight)
  rw [cosupport_weightedFunctionIdeal _ coefficientWeight_pos _ (coefficient_holomorphic_on_domain P)]
  apply mem_iInter.mpr
  intro i
  apply (mem_cosupport_finiteFunctionIdeal_iff _ _ _
    (fun _ => holomorphicAt_of_mdifferentiableOn isOpen_univ
      (coefficient_holomorphic_on_domain P i).mdifferentiableOn (mem_univ _))).mpr
  intro _
  have hmem := mem_actualPrincipalCoefficientIdeal (k+s) (P.coefficient i.1 i.2.val)
    P.domain P.isOpen_domain (P.regular i.1 i.2.val i.2.property) z z.property
  have hc := (hCos i ⟨z.property,hz⟩).2 _ hmem
  have hval : ContMDiff 𝓘(ℂ,ComplexModel (k+s)) 𝓘(ℂ,ComplexModel (k+s)) ∞
      (Subtype.val : coefficientDomain P → ComplexModel (k+s)) := contMDiff_subtype_val
  have h := MonomialPartEtale.vanishesToOrderOn_comp
    (θ := (Subtype.val : coefficientDomain P → ComplexModel (k+s)))
    (p := z) (Eventually.of_forall fun u => (hval.contMDiffAt (x := u)).mdifferentiableAt (by simp)) hc
  change VanishesToOrderOn (k+s) univ z (coefficientWeight i)
    (fun x : coefficientDomain P => P.coefficient i.1 i.2.val x)
  simpa only [preimage_univ,Function.comp_def] using h

/-- The SAME original coefficient datum has its entire controlled sheaf stalk
internally represented by its true low coefficient compression over an arbitrary
centre dimension. Neither an affine chart nor a stalk equality is supplied. -/
theorem exists_actual_prescribed_coefficient_controlled_stalk (k s t : ℕ)
    (I : Ideal (HolGerm (ComplexModel ((k+s)+t))))
    (P : ActualAnalyticVertexCoefficientData k s t I)
    (hCos : ∀ i : weightedCoefficientIndex k s t I,
      P.domain∩complexCoordinatePlane (k+s) k⊆cosupport (k+s) univ
        (actualPrincipalCoefficientIdeal (k+s) (P.coefficient i.1 i.2.val)) (coefficientWeight i))
    {Y : Type} [TopologicalSpace Y] [ChartedSpace (ComplexModel (k+s)) Y]
    [IsComplexManifold (k+s) Y] (π : Y → coefficientDomain P)
    (hπ : IsBlowupAlong (k+s)
      ((Subtype.val : coefficientDomain P → ComplexModel (k+s)) ⁻¹' complexCoordinatePlane (k+s) k) π)
    (y : Y) (hy : (π y : ComplexModel (k+s))=0) :
    0<(coefficientMarked P).d ∧
    (coefficientMarked P).IsAdmissibleCentre
      ((Subtype.val : coefficientDomain P → ComplexModel (k+s)) ⁻¹' complexCoordinatePlane (k+s) k) ∧
    (controlledTransform hπ (coefficientMarked P).ideal (coefficientMarked P).d).IsCoherent ∧
    ∃ (e : Fin (k+s)) (b : Fin (k+s) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (k+s)) y y))
      (hΘ0 : Θ.toFun (chartAt (ComplexModel (k+s)) y y)=0),
      k≤e.val ∧ (∀ i : Fin (k+s),i.val<k → b i=0) ∧ b e=0 ∧
      Θ.source⊆(chartAt (ComplexModel (k+s)) y).target ∧
      (∀ z : Y,z∈(chartAt (ComplexModel (k+s)) y).source →
        chartAt (ComplexModel (k+s)) y z∈Θ.source →
        (π z : ComplexModel (k+s))=actualAnalyticBlowupMap (actualTangentCentreVariables k s) e b
          (Θ.toFun (chartAt (ComplexModel (k+s)) y z))) ∧
      ∃ H : actualInitialVertices MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom ((k+s)+t)).toRingHom I) → HolGerm (ComplexModel ((k+s)+t)),
        (∀ a,(coordinateGerm (e.castAdd t))^(actualCoefficientCentreVertexWeight k s t a.val)*H a=
          actualAnalyticBlowupPullback (actualPresentationCentreVariables (t := t) (actualTangentCentreVariables k s))
            (e.castAdd t) (coefficientChartParameters (k+s) t b) (P.generator a)) ∧
        adaptedIdeal (controlledTransform hπ (coefficientMarked P).ideal (coefficientMarked P).d) y Θ hΘ0=
          weightedCompression coefficientWeight
            (fun i : weightedCoefficientIndex k s t I => actualNormalAnalyticCoefficientGerm (k+s) t (H i.1) i.2.val) := by
  have hSub := source_centre_cosupport P hCos
  have hAdm : (coefficientMarked P).IsAdmissibleCentre
      ((Subtype.val : coefficientDomain P → ComplexModel (k+s)) ⁻¹' complexCoordinatePlane (k+s) k) :=
    ⟨hπ.1,hSub,hasNormalCrossings_nil_of_isClosedSubmanifold hπ.1⟩
  have hc := isCoherent_weightedFunctionIdeal coefficientWeight (coefficientFunction P) (coefficient_holomorphic_on_domain P)
  have hCtrl := HadamardBridge.isCoherent_controlledTransform_of_subset_cosupport hπ hc hSub
  obtain ⟨e,b,Θ,hΘ0,he,hbt,hbe,hΘsrc,hSquare,hStalk⟩ :=
    exists_actual_coordinate_centre_weighted_stalk (coefficientDomain P) P.zero_mem_domain k π hπ y hy
      coefficientWeight (fun i : weightedCoefficientIndex k s t I => P.coefficient i.1 i.2.val)
      (fun i => P.regular i.1 i.2.val i.2.property)
  have hVar : actualTangentCentreVariables k s={i : Fin (k+s) | k ≤ i.val} := by
    ext i
    constructor
    · rintro ⟨j,rfl⟩
      simp only [mem_ofPred_eq,Fin.val_natAdd]
      omega
    · intro hi
      change k ≤ i.val at hi
      refine ⟨⟨i.val-k,by omega⟩,?_⟩
      apply Fin.ext
      simp only [Fin.val_natAdd]
      omega
  have he' : e∈actualTangentCentreVariables k s := by rw [hVar];exact he
  obtain ⟨H,hH,_hLow,_hMap,hColon⟩ := exists_actual_vertex_controlled_coefficient_ideals k s t I P hCos e he' b
  rw [←hVar] at hStalk hSquare
  change adaptedIdeal (controlledTransform hπ (coefficientMarked P).ideal (coefficientMarked P).d) y Θ hΘ0=_ at hStalk
  have hEqual : adaptedIdeal (controlledTransform hπ (coefficientMarked P).ideal (coefficientMarked P).d) y Θ hΘ0=
      weightedCompression coefficientWeight
        (fun i : weightedCoefficientIndex k s t I => actualNormalAnalyticCoefficientGerm (k+s) t (H i.1) i.2.val) :=
    hStalk.trans hColon
  exact ⟨weightedCommonMark_pos _ coefficientWeight_pos,hAdm,hCtrl,e,b,Θ,hΘ0,he,hbt,hbe,hΘsrc,hSquare,H,hH,hEqual⟩

end
end Hironaka.HironakaActualCentreWeightedControlledStalk
