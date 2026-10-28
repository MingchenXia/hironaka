/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.CanonicalInvariantStepDefinitionsOriginalExact
import Hironaka.Resolution.HironakaActualMaskSectionRepresentative
import Hironaka.Resolution.HironakaActualNestedSectionCoordinates
import Hironaka.Resolution.HironakaActualAnalyticSubspaceRegularityConverse
import Hironaka.Resolution.HironakaActualAnalyticSubspacePresentationIndependence
import Hironaka.Resolution.HironakaReducedComplexAnalyticSpaces
import Hironaka.Resolution.HironakaSharpOriginalProductTraceOrder
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Resolution.HironakaActualNonregularCoefficientNaturality
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualSectionInitialValues
noncomputable section
open HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
 HironakaActualAnalyticSubspaceManifoldCharts HironakaActualAnalyticSubspaceRegularityConverse
 HironakaActualAnalyticSubspaceMaps HironakaActualAnalyticSubspacePresentationIndependence
variable {n m k : ℕ} {U : Opens (ComplexModel n)} {V : Opens (ComplexModel m)}
 {A : Set U} {B : Set V}

theorem regularAtDim_of_actual_subspace_iso
    (e : actualSubspaceLocallyRingedSpace (n := n) A ≅ actualSubspaceLocallyRingedSpace (n := m) B)
    (he : e.hom ≫ subspacePointMap (n := m) B=subspacePointMap (n := n) A)
    (x : A) (hreg : RegularAtDim (n := n) A x.val k) :
    RegularAtDim (n := m) B (e.hom.base x).val k := by
  obtain ⟨t,hn⟩ := Nat.exists_eq_add_of_le hreg.1
  subst n
  obtain ⟨W,i,hi,hip,hxi⟩ := exists_actual_regular_subspace_manifold_chart A x.val hreg
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let j := i ≫ e.hom
  have hj : LocallyRingedSpace.IsOpenImmersion j := by dsimp [j]; infer_instance
  let := hj
  have hjp : j ≫ subspacePointMap (n := m) B=ambientPointMap k W := by
    dsimp [j]
    rw [Category.assoc,he,hip]
  obtain ⟨z,hz⟩ := hxi
  have hr := regularAtDim_of_native_manifold_chart j hjp z
  have hp : (j.base z).val=(e.hom.base x).val := by
    change (e.hom.base (i.base z)).val=_
    have hx : i.base z=x := by simpa only [Subtype.ext_iff] using hz
    rw [hx]
  simpa only [hp] using hr
open HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
 HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso

private theorem projection_section (U : Opens (ComplexModel n)) (x : U) :
    projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x

private theorem section_mem (A : Set U) (x : U) : zeroSection U x∈liftedCarrier A ↔ x∈A := by
  change (projection U (zeroSection U x)∈A ∧ actualJointNormalProjection n 1 (tangentInclusion n 1 x.val)=0) ↔x∈A
  rw [projection_section]
  simp

private theorem section_projection (z : productOpen U) (hz : z∈liftedCarrier A) :
    zeroSection U (projection U z)=z := by
  apply Subtype.ext
  change tangentInclusion n 1 (tangentProjection n 1 z.val)=z.val
  have hq : actualJointNormalProjection n 1 z.val=0 := hz.2
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hq,map_zero,add_zero]
    using (join_projections (n := n) (m := 1) z.val)

def actualSectionSubspaceIso (A : Set U) :
    actualSubspaceLocallyRingedSpace (n := n) A ≅
      actualSubspaceLocallyRingedSpace (n := n+1) (liftedCarrier A) :=
  actualSubspaceMutualRestrictionIso (zeroSection_contMDiff U) (projection_contMDiff U)
    (fun x hx => (section_mem A x).mpr hx) (fun _ hz => hz.1)
    (fun x _ => projection_section U x) (fun z hz => section_projection z hz)

theorem regularAtDim_actual_section_iff (A : Set U) (x : U) (hx : x∈A) (k : ℕ) :
    RegularAtDim (n := n+1) (liftedCarrier A) (zeroSection U x) k ↔
      RegularAtDim (n := n) A x k := by
  let e:=actualSectionSubspaceIso A
  have he : e.hom ≫ subspacePointMap (n := n+1) (liftedCarrier A)=subspacePointMap (n := n) A :=
    actualSubspaceMap_point (zeroSection_contMDiff U) (fun x hx => (section_mem A x).mpr hx)
  have hei : e.inv ≫ subspacePointMap (n := n) A=subspacePointMap (n := n+1) (liftedCarrier A) :=
    actualSubspaceMap_point (projection_contMDiff U) (fun _ hz => hz.1)
  constructor
  · intro hr
    have h:=regularAtDim_of_actual_subspace_iso e.symm hei
      (⟨zeroSection U x,(section_mem A x).mpr hx⟩ : liftedCarrier A) hr
    change RegularAtDim (n := n) A (projection U (zeroSection U x)) k at h
    simpa only [projection_section] using h
  · intro hr
    exact regularAtDim_of_actual_subspace_iso e he (⟨x,hx⟩ : A) hr

open Hironaka.HolomorphicIdealSheaves IdealOrderArithmetic GermIdealOrder IdealWeightPowers
 RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient HadamardBridge
 HironakaSharpOriginalProductTraceOrder NonmonomialOrderLocal

private theorem scalar_section_order_iff (A : Set U) (x : U) (q : ℕ) (g : productOpen U → ℂ) :
    VanishesToOrderOn (n+1) (liftedCarrier A) (zeroSection U x) q g ↔
      VanishesToOrderOn n A x q (g ∘ zeroSection U) := by
  constructor
  · rintro ⟨h,hh,he⟩
    refine ⟨h ∘ zeroSection U,comp_mem_idealPow_pointIdeal
      (Eventually.of_forall fun _ => (zeroSection_contMDiff U).mdifferentiableAt (by simp)) q hh,?_⟩
    filter_upwards [(zeroSection_contMDiff U).continuous.continuousAt.eventually he] with y hy hyA
    exact hy ((section_mem A y).mpr hyA)
  · rintro ⟨h,hh,he⟩
    have hh' : (idealPow (pointIdeal n (projection U (zeroSection U x))) q).mem
        (projection U (zeroSection U x)) h := by simpa only [projection_section] using hh
    refine ⟨h ∘ projection U,comp_mem_idealPow_pointIdeal
      (Eventually.of_forall fun _ => (projection_contMDiff U).mdifferentiableAt (by simp)) q hh',?_⟩
    have hlim : Tendsto (projection U) (𝓝 (zeroSection U x)) (𝓝 x) := by
      simpa only [projection_section] using ((projection_contMDiff U).continuous.continuousAt (x := zeroSection U x)).tendsto
    filter_upwards [hlim.eventually he] with z hz hzA
    have heq:=hz hzA.1
    simpa only [Function.comp_apply,section_projection z hzA] using heq

private theorem whole_section_orderGE_iff (A : Set U) (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀x g,J.mem x g → HolomorphicAt (n+1) g x) (x : U) (q : ℕ) :
    OrderGE n A (GermIdeal.pullback (m := n) (zeroSection U) J) x q ↔
      OrderGE (n+1) (liftedCarrier A) J (zeroSection U x) q := by
  constructor
  · intro h g hg
    have hp : (GermIdeal.pullback (m := n) (zeroSection U) J).mem x (g ∘ zeroSection U) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg,rfl⟩
        ((hJ _ _ hg).comp_contMDiff (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt)))
    exact (scalar_section_order_iff A x q g).mpr (h _ hp)
  · intro h g hg
    apply IsInSpanAt.vanishesToOrderOn (GermIdeal.mem_pullback_iff.mp hg)
    rintro _ ⟨a,ha,rfl⟩
    exact (scalar_section_order_iff A x q a).mp (h a ha)

private theorem section_cosupport_iff (A : Set U) (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀x g,J.mem x g → HolomorphicAt (n+1) g x) (x : U) (q : ℕ) :
    x∈cosupport n A (GermIdeal.pullback (m := n) (zeroSection U) J) q ↔
      zeroSection U x∈cosupport (n+1) (liftedCarrier A) J q := by
  exact and_congr (section_mem A x).symm (whole_section_orderGE_iff A J hJ x q)

theorem source_cosupport_eq_lifted (A : Set U) (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀x g,J.mem x g → HolomorphicAt (n+1) g x) (q : ℕ) :
    cosupport (n+1) (liftedCarrier A) J q=
      liftedCarrier (cosupport n A (GermIdeal.pullback (m := n) (zeroSection U) J) q) := by
  ext z
  constructor
  · intro hz
    have hsec:=section_projection z hz.1
    have hb : projection U z∈cosupport n A (GermIdeal.pullback (m := n) (zeroSection U) J) q :=
      (section_cosupport_iff A J hJ (projection U z) q).mpr (by simpa only [hsec] using hz)
    exact ⟨hb,hz.1.2⟩
  · rintro ⟨hb,hq⟩
    have hsec:=section_projection z (show z∈liftedCarrier A from ⟨hb.1,hq⟩)
    have hs:=(section_cosupport_iff A J hJ (projection U z) q).mp hb
    simpa only [hsec] using hs

open CodimOneSupportAlong

theorem section_codimOnePart_iff (A : Set U) (J : GermIdeal (n+1) (productOpen U))
    (hJ : ∀x g,J.mem x g → HolomorphicAt (n+1) g x) (x : U) (d : ℕ) :
    zeroSection U x∈codimOnePartAlong (liftedCarrier A) J d ↔
      x∈codimOnePartAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) d := by
  constructor
  · rintro ⟨k,hN,hS⟩
    have hxA : x∈A := (section_mem A x).mp hN.2.1
    have hxS := (section_cosupport_iff A J hJ x d).mpr hS.2.1
    rw [source_cosupport_eq_lifted A J hJ d] at hS
    exact ⟨k,(regularAtDim_actual_section_iff A x hxA (k+1)).mp hN,
      (regularAtDim_actual_section_iff _ x hxS k).mp hS⟩
  · rintro ⟨k,hN,hS⟩
    refine ⟨k,(regularAtDim_actual_section_iff A x hN.2.1 (k+1)).mpr hN,?_⟩
    rw [source_cosupport_eq_lifted A J hJ d]
    exact (regularAtDim_actual_section_iff _ x hS.2.1 k).mpr hS

private theorem section_nmOrd_eq (A : Set U) (J : GermIdeal (n+1) (productOpen U))
    (hJ : J.IsCoherent) (x : U) (d : ℕ) :
    nmOrd (M := BlowupTowers.CMfd.of (n := n+1) (productOpen U)) (⟨liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (n+1) (productOpen U)) (zeroSection U x)=
      nmOrd (M := BlowupTowers.CMfd.of (n := n) U) (⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeals.MarkedIdeal n U) x := by
  unfold nmOrd
  apply congrArg sInf
  ext q
  change (zeroSection U x∉ordGe (ordinaryTraceMarked (X := BlowupTowers.CMfd.of (n := n+1) (productOpen U)) (liftedCarrier A) J) (q+1)) ↔
    (x∉ordGe (ordinaryTraceMarked (X := BlowupTowers.CMfd.of (n := n) U) A (GermIdeal.pullback (m := n) (zeroSection U) J)) (q+1))
  rw [ordGe_ordinaryTraceMarked_eq_cosupport _ _ hJ,
    ordGe_ordinaryTraceMarked_eq_cosupport _ _ (isCoherent_pullback (zeroSection_contMDiff U) hJ)]
  exact not_congr (section_cosupport_iff A J (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ hg) x (q+1)).symm

open HomogenizedIdealAlong DerivativeIdealAlong DerivativeIdealAlongCoherent
 CoefficientIdeal HomogenizedGlueing Hironaka.BlowupSequences GiraudAlong HomogenizedEquivalence

private theorem section_homogenizedIdeal (A : Set U) (hA : IsClosedSubmanifold n A)
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) :
    GermIdeal.pullback (m := n) (zeroSection U) (homogenizedIdealAlong (liftedCarrier A) J d)=
      homogenizedIdealAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) d := by
  unfold homogenizedIdealAlong
  rw [HironakaActualNonregularCoefficientNaturality.pullback_homSum (zeroSection_contMDiff U)
    (fun i => iterDerivIdealAlong (liftedCarrier A) J i) (tangentIdealAlong (liftedCarrier A) J d) d
    (fun i _ {_ _} hg => holomorphicAt_of_mem_iterDerivIdealAlong
      (fun _ _ hj => GermIdeal.IsCoherent.holomorphicAt_mem hJ hj) i _ _ hg)
    (fun {_ _} hg => holomorphicAt_of_mem_iterDerivIdealAlong
      (N := liftedCarrier A) (fun _ _ hj => GermIdeal.IsCoherent.holomorphicAt_mem hJ hj) (d-1) _ _ hg)]
  exact homSum_congr (fun i _ => zero_section_iterDerivIdealAlong U hA J hJ i)
    (zero_section_iterDerivIdealAlong U hA J hJ (d-1))

private theorem section_coefficientIdeal (A : Set U) (hA : IsClosedSubmanifold n A)
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) :
    GermIdeal.pullback (m := n) (zeroSection U)
      (finSumIdeal (fun i => idealPow (iterDerivIdealAlong (liftedCarrier A) J i)
        (sumExp (fun j => d-j) d i)) d)=
      finSumIdeal (fun i => idealPow (iterDerivIdealAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) i)
        (sumExp (fun j => d-j) d i)) d := by
  rw [HironakaActualNonregularCoefficientNaturality.pullback_finSumIdeal (zeroSection_contMDiff U) _ _
    (fun _ _ {_ _} hg => holomorphicAt_of_mem_idealPow hg)]
  apply finSumIdeal_congr
  intro i _
  rw [HironakaActualNonregularCoefficientNaturality.pullback_idealPow (zeroSection_contMDiff U)
    (fun {_ _} hg => holomorphicAt_of_mem_iterDerivIdealAlong
      (N := liftedCarrier A) (fun _ _ hj => GermIdeal.IsCoherent.holomorphicAt_mem hJ hj) i _ _ hg),
    zero_section_iterDerivIdealAlong U hA J hJ i]


private theorem section_bar_ideal (A : Set U) (hA : IsClosedSubmanifold n A)
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) :
    GermIdeal.pullback (m := n) (zeroSection U)
      (StepOneValue.barMarked (X := BlowupTowers.CMfd.of (n := n+1) (productOpen U)) (⟨liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (n+1) (productOpen U))).ideal=
      (StepOneValue.barMarked (X := BlowupTowers.CMfd.of (n := n) U) (⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeals.MarkedIdeal n U)).ideal := by
  change GermIdeal.pullback (m := n) (zeroSection U)
      (finSumIdeal (fun i => idealPow (iterDerivIdealAlong (liftedCarrier A) (homogenizedIdealAlong (liftedCarrier A) J d) i)
        (sumExp (fun j => d-j) d i)) d)=
      finSumIdeal (fun i => idealPow (iterDerivIdealAlong A (homogenizedIdealAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) d) i)
        (sumExp (fun j => d-j) d i)) d
  rw [section_coefficientIdeal A hA _ (isCoherent_homogenizedIdealAlong hJ (liftedCarrier_closed_submanifold hA) d) d,
    section_homogenizedIdeal A hA J hJ d]



private theorem section_second_coefficient_ideal (A : Set U) (hA : IsClosedSubmanifold n A)
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) :
    GermIdeal.pullback (m := n) (zeroSection U)
      (coeffMarkedAlong (StepOneValue.barMarked (X := BlowupTowers.CMfd.of (n := n+1) (productOpen U))
        (⟨liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (n+1) (productOpen U)))).ideal=
      (coeffMarkedAlong (StepOneValue.barMarked (X := BlowupTowers.CMfd.of (n := n) U)
        (⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeals.MarkedIdeal n U))).ideal := by
  let M : MarkedIdeals.MarkedIdeal (n+1) (BlowupTowers.CMfd.of (n := n+1) (productOpen U)):=⟨liftedCarrier A,[],J,d⟩
  let B : MarkedIdeals.MarkedIdeal n (BlowupTowers.CMfd.of (n := n) U):=⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
  have hc : (StepOneValue.barMarked M).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong (𝔪 := M) hJ (liftedCarrier_closed_submanifold hA))
      (liftedCarrier_closed_submanifold hA)
  change GermIdeal.pullback (m := n) (zeroSection U)
    (finSumIdeal (fun i => idealPow (iterDerivIdealAlong (liftedCarrier A) (StepOneValue.barMarked M).ideal i)
      (sumExp (fun j => (StepOneValue.barMarked M).d-j) (StepOneValue.barMarked M).d i)) (StepOneValue.barMarked M).d)=
    finSumIdeal (fun i => idealPow (iterDerivIdealAlong A (StepOneValue.barMarked B).ideal i)
      (sumExp (fun j => (StepOneValue.barMarked B).d-j) (StepOneValue.barMarked B).d i)) (StepOneValue.barMarked B).d
  rw [section_coefficientIdeal A hA _ hc (StepOneValue.barMarked M).d,section_bar_ideal A hA J hJ d]
  rfl

private theorem section_isSpecial_refl_iff (A : Set U) (hA : IsClosedSubmanifold n A)
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) (x : U) :
    StepOneValue.IsSpecial (X := BlowupTowers.CMfd.of (n := n+1) (productOpen U))
      (⟨liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (n+1) (productOpen U)) .refl (zeroSection U x) ↔
    StepOneValue.IsSpecial (X := BlowupTowers.CMfd.of (n := n) U)
      (⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeals.MarkedIdeal n U) .refl x := by
  let M : MarkedIdeals.MarkedIdeal (n+1) (BlowupTowers.CMfd.of (n := n+1) (productOpen U)):=⟨liftedCarrier A,[],J,d⟩
  let B : MarkedIdeals.MarkedIdeal n (BlowupTowers.CMfd.of (n := n) U):=⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
  have hc : (StepOneValue.barMarked M).ideal.IsCoherent :=
    isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong (𝔪 := M) hJ (liftedCarrier_closed_submanifold hA))
      (liftedCarrier_closed_submanifold hA)
  have hC:=section_codimOnePart_iff A (StepOneValue.barMarked M).ideal
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc hg) x (StepOneValue.barMarked M).d
  have hIdeal : GermIdeal.pullback (m := n) (zeroSection U) (StepOneValue.barMarked M).ideal=
      (StepOneValue.barMarked B).ideal:=section_bar_ideal A hA J hJ d
  rw [hIdeal] at hC
  have hLM : StepOneValue.level M .refl (zeroSection U x)=0:=rfl
  have hLB : StepOneValue.level B .refl x=0:=rfl
  have h01 : ¬(1≤0) := by omega
  have hNM : (StepOneValue.barMarked M).N=liftedCarrier A:=rfl
  have hNB : (StepOneValue.barMarked B).N=A:=rfl
  have hmark : (StepOneValue.barMarked M).d=(StepOneValue.barMarked B).d:=rfl
  rw [hmark] at hC
  change StepOneValue.IsSpecial M .refl (zeroSection U x) ↔StepOneValue.IsSpecial B .refl x
  simpa only [StepOneValue.IsSpecial,hLM,hLB,MarkedIdeals.MarkedIdeal.geoTransformAlong,
    h01,hNM,hNB,hmark,eq_self,true_and,false_and,or_false] using hC

open BlowupFlatCoordinates GiraudAlong TangentDirectionAlong

private theorem model_chart_apply {r : ℕ} (V : Opens (ComplexModel r)) (x y : V) :
    chartAt (ComplexModel r) x y=y.val := by
  rw [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq]
  rfl

private theorem model_chart_source {r : ℕ} (V : Opens (ComplexModel r)) (x y : V) :
    y∈(chartAt (ComplexModel r) x).source :=
  AnalyticSubsetOpens.mem_chartAt_opens_source.mpr (by simp)

private theorem model_chart_target {r : ℕ} (V : Opens (ComplexModel r)) (x : V) (v : ComplexModel r) :
    v∈(chartAt (ComplexModel r) x).target ↔ v∈V := by
  constructor
  · intro hv
    have h := (chartAt (ComplexModel r) x).right_inv hv
    rw [model_chart_apply] at h
    exact h ▸ ((chartAt (ComplexModel r) x).symm v).property
  · intro hv
    have h := AnalyticSubsetOpens.chart_mem_opens_target (n := r) (x := x) (y := ⟨v,hv⟩) (by simp)
    simpa using h

private theorem product_plane_iff (a : ComplexModel n) (b : ComplexModel 1) {k : ℕ} (hk : k≤n) :
    HironakaActualIntrinsicStableAmbientIso.join a b∈complexCoordinatePlane (n+1) k ↔
      a∈complexCoordinatePlane n k ∧ b=0 := by
  constructor
  · intro h
    refine ⟨?_,?_⟩
    · intro i hi
      simpa [HironakaActualIntrinsicStableAmbientIso.join] using h (i.castAdd 1) hi
    · ext i
      simpa [HironakaActualIntrinsicStableAmbientIso.join] using h (i.natAdd n) (by simp;omega)
  · rintro ⟨ha,hb⟩ i hi
    refine Fin.addCases (fun j hj => ?_) (fun j _hj => ?_) i hi
    · simpa [HironakaActualIntrinsicStableAmbientIso.join] using ha j hj
    · simp [HironakaActualIntrinsicStableAmbientIso.join,hb]


theorem open_section_tangent_descent (A : Set U) (hA : IsClosedSubmanifold n A)
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent)
    {d : ℕ} {O : Set (productOpen U)} {u : productOpen U → ℂ}
    (hu : IsTangentDirectionAlong (liftedCarrier A) J d O u)
    (x : U) (hx : x∈A) (hxO : zeroSection U x∈O) (hu0 : u (zeroSection U x)=0) :
    ∃ W : Opens U,x∈W ∧ (W : Set U)⊆zeroSection U ⁻¹' O ∧
      IsTangentDirectionAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) d W (u ∘ zeroSection U) := by
  obtain ⟨k,hkn,_hx,Φ,hsrc,h0,hflat⟩ := hA.2 x hx
  have hΓsrc : (productFlat U x Φ).source⊆(chartAt (ComplexModel (n+1)) (zeroSection U x)).target := by
    intro z hz
    apply (model_chart_target (productOpen U) (zeroSection U x) z).mpr
    change tangentProjection n 1 z∈U
    exact (model_chart_target U x _).mp (hsrc hz)
  have hΓflat : ∀{z : productOpen U},z∈(chartAt (ComplexModel (n+1)) (zeroSection U x)).source →
      chartAt (ComplexModel (n+1)) (zeroSection U x) z∈(productFlat U x Φ).source →
      (z∈liftedCarrier A ↔ (productFlat U x Φ).toFun (chartAt (ComplexModel (n+1)) (zeroSection U x) z)∈complexCoordinatePlane (n+1) k) := by
    intro z _ hz
    have hΦ : chartAt (ComplexModel n) x (projection U z)∈Φ.source := by
      change tangentProjection n 1 z.val∈Φ.source
      change tangentProjection n 1 z.val∈Φ.source at hz
      exact hz
    have h := hflat (model_chart_source U x _) hΦ
    simp only [model_chart_apply] at h ⊢
    change (projection U z∈A ∧ actualJointNormalProjection n 1 z.val=0) ↔
      HironakaActualIntrinsicStableAmbientIso.join (Φ.toFun (tangentProjection n 1 z.val))
        (actualJointNormalProjection n 1 z.val)∈complexCoordinatePlane (n+1) k
    rw [product_plane_iff _ _ hkn]
    exact and_congr_left fun _ => h
  have hholJ : ∀z g,J.mem z g → HolomorphicAt (n+1) g z :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ hg
  have huhol : ∀z∈O,HolomorphicAt (n+1) u z :=
    fun z hz => holomorphicAt_of_mem_iterDerivIdealAlong hholJ (d-1) z u (hu.mem z hz)
  obtain ⟨e,ξ,hξ,hne⟩ := hu.multiplicity_one _ hxO hu0
  obtain ⟨j,hjk,hj⟩ := exists_flatPartial_ne_zero hΓsrc hΓflat (mem_flatDomain_self _)
    ((section_mem A x).mpr hx) (huhol _ hxO) hξ hne
  let i : Fin n:=⟨j.val,by omega⟩
  have hij : i.castAdd 1=j := Fin.ext rfl
  have hi : i.val<k:=hjk
  have hbase : flatPartial Φ i (u ∘ zeroSection U) x≠0 := by
    rw [←hij,product_partial_zero_section U x Φ hsrc (mem_flatDomain_self Φ) u (huhol _ hxO)] at hj
    exact hj
  have hcomp : HolomorphicAt n (u ∘ zeroSection U) x :=
    (huhol _ hxO).comp_contMDiff (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt)
  have hcont := (holomorphicAt_flatPartial i (mem_flatDomain_self Φ) hcomp).self_of_nhds.continuousAt
  obtain ⟨V,hVsub,hVo,hxV⟩ := mem_nhds_iff.mp (hcont.eventually (isOpen_ne.mem_nhds hbase))
  let W : Opens U:=⟨(V∩zeroSection U ⁻¹' O)∩flatDomain Φ,
    (hVo.inter (hu.isOpen.preimage (zeroSection_contMDiff U).continuous)).inter (isOpen_flatDomain Φ)⟩
  refine ⟨W,⟨⟨hxV,hxO⟩,mem_flatDomain_self Φ⟩,fun _ hy => hy.1.2,⟨W.isOpen,?_,?_⟩⟩
  · intro y hy
    rw [←zero_section_iterDerivIdealAlong U hA J hJ (d-1)]
    apply GermIdeal.mem_pullback_iff.mpr
    exact isInSpanAt_self ⟨u,hu.mem _ hy.1.2,rfl⟩
      ((huhol _ hy.1.2).comp_contMDiff (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt))
  · intro y hy _
    exact ⟨complexChartAt x,flatField Φ (EuclideanSpace.single i 1),
      isTangentField_flatField hsrc hflat (single_mem_complexCoordinatePlane hi) hy.2,hVsub hy.1.1⟩


private theorem open_lifted_contact_eq (A : Set U) (u : productOpen U → ℂ) :
    liftedCarrier A∩{z | u z=0}=liftedCarrier (A∩{x | u (zeroSection U x)=0}) := by
  ext z
  constructor
  · rintro ⟨hzA,hzu⟩
    refine ⟨⟨hzA.1,?_⟩,hzA.2⟩
    change u (zeroSection U (projection U z))=0
    rw [section_projection z hzA]
    exact hzu
  · rintro ⟨⟨hzA,hzu⟩,hzq⟩
    have hz : z∈liftedCarrier A:=⟨hzA,hzq⟩
    refine ⟨hz,?_⟩
    change u (zeroSection U (projection U z))=0 at hzu
    rwa [section_projection z hz] at hzu

theorem open_section_regular_contact (A : Set U) (hA : IsClosedSubmanifold n A)
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent)
    {d : ℕ} {O : Set (productOpen U)} {u : productOpen U → ℂ}
    (hu : IsTangentDirectionAlong (liftedCarrier A) J d O u)
    (x : U) (hx : x∈A) (hxO : zeroSection U x∈O) (hu0 : u (zeroSection U x)=0) :
    ∃ W : Opens U,x∈W ∧ (W : Set U)⊆zeroSection U ⁻¹' O ∧
      IsTangentDirectionAlong A (GermIdeal.pullback (m := n) (zeroSection U) J) d W (u ∘ zeroSection U) ∧
      IsClosedSubmanifold n ((Subtype.val : W→U) ⁻¹' (A∩{x | u (zeroSection U x)=0}∩(W:Set U))) ∧
      liftedCarrier A∩{z | u z=0}=liftedCarrier (A∩{x | u (zeroSection U x)=0}) := by
  obtain ⟨W,hxW,hWsub,hw⟩ := open_section_tangent_descent A hA J hJ hu x hx hxO hu0
  have hJP := isCoherent_pullback (zeroSection_contMDiff U) hJ
  have hholJ : ∀y g,(GermIdeal.pullback (m := n) (zeroSection U) J).mem y g → HolomorphicAt n g y :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJP hg
  have hholu : ∀y∈(W:Set U),HolomorphicAt n (u ∘ zeroSection U) y :=
    fun y hy => holomorphicAt_of_mem_iterDerivIdealAlong hholJ (d-1) y _ (hw.mem y hy)
  refine ⟨W,hxW,hWsub,hw,⟨isClosed_preimage_val_inter_zeroSet hA.1 hholu,?_⟩,open_lifted_contact_eq A u⟩
  intro y hy
  obtain ⟨k,_hk,hcontact⟩ := hw.regularAtDim_contact hholJ hA hy
  exact ⟨k-1,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hcontact⟩

open CanonicalCentres ResolutionInvariantSpec GeneralValue BlowupTowers BlowupTowerTransforms MarkedIdeals.MarkedIdeal
 MonomialCaseAlong NonmonomialOrderTail GeneralCanonicalTail

theorem section_projected_domain (q : ℕ) (A : Set U) (I : GermIdeal n U) (d : ℕ)
    (h : IsInvDomain q (⟨A,[],I,d⟩ : MarkedIdeals.MarkedIdeal n U)) :
    IsInvDomain q (⟨liftedCarrier A,[],GermIdeal.pullback (m := n+1) (projection U) I,d⟩ :
      MarkedIdeals.MarkedIdeal (n+1) (productOpen U)) := by
  have hN:=liftedCarrier_closed_submanifold h.isWellFormed.isClosedSubmanifold_N
  have hc:=isCoherent_pullback (projection_contMDiff U) h.isWellFormed.isCoherent
  refine ⟨⟨hN,hc,NormalCrossings.isSNCDivisor_nil,
    NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hN⟩,?_,h.one_le_d,?_⟩
  · intro z hz
    let x:=projection U z
    have hx : x∈A:=hz.1
    obtain ⟨k,hk,hreg⟩:=h.dimLE x hx
    refine ⟨k,hk,?_⟩
    have hr:=(regularAtDim_actual_section_iff A x hx k).mpr hreg
    change RegularAtDim (n := n+1) (liftedCarrier A) (zeroSection U (projection U z)) k at hr
    rwa [section_projection z hz] at hr
  · intro z hz
    let x:=projection U z
    have hx : x∈A:=hz.1
    have hsec : zeroSection U x=z:=section_projection z hz
    rw [←hsec]
    obtain ⟨g,hg,hfreq⟩:=h.isNonzeroAlongAt x hx
    have hg' : I.mem (projection U (zeroSection U x)) g := by
      simpa only [projection_section] using hg
    have hp : (GermIdeal.pullback (m := n+1) (projection U) I).mem (zeroSection U x) (g ∘ projection U) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg',rfl⟩
        ((GermIdeal.IsCoherent.holomorphicAt_mem h.isWellFormed.isCoherent hg').comp_contMDiff
          (Eventually.of_forall fun _ => (projection_contMDiff U).contMDiffAt)))
    refine ⟨g ∘ projection U,hp,?_⟩
    by_contra hn
    have hn' := not_frequently.mp hn
    apply hfreq
    filter_upwards [(zeroSection_contMDiff U).continuous.continuousAt.eventually hn'] with y hy
    rintro ⟨hyA,hyg⟩
    apply hy
    exact ⟨(section_mem A y).mpr hyA,by simpa only [Function.comp_apply,projection_section] using hyg⟩

private theorem section_orderMask_iff (q : ℕ) (hn : 0<n) (A : Set U)
    (J : GermIdeal (n+1) (productOpen U)) (d o : ℕ)
    (hM : IsInvDomain q (⟨liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (n+1) (productOpen U)))
    (hB : IsInvDomain q (⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeals.MarkedIdeal n U))
    (x : U) :
    zeroSection U x∈ordMask (M := CMfd.of (n := n+1) (productOpen U)) ⟨liftedCarrier A,[],J,d⟩ o ↔
      x∈ordMask (M := CMfd.of (n := n) U) ⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ o := by
  rw [mem_ordMask_iff (Nat.succ_pos n) hM.isWellFormed hM.isNonzeroAlongAt,
    mem_ordMask_iff hn hB.isWellFormed hB.isNonzeroAlongAt]
  apply not_congr
  change zeroSection U x∈ordGe (ordinaryTraceMarked (X := CMfd.of (n := n+1) (productOpen U)) (liftedCarrier A) J) (o+1) ↔
    x∈ordGe (ordinaryTraceMarked (X := CMfd.of (n := n) U) A (GermIdeal.pullback (m := n) (zeroSection U) J)) (o+1)
  rw [ordGe_ordinaryTraceMarked_eq_cosupport _ _ hM.isWellFormed.isCoherent,
    ordGe_ordinaryTraceMarked_eq_cosupport _ _ hB.isWellFormed.isCoherent]
  exact (section_cosupport_iff A J (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) x (o+1)).symm

open MaxLocusLocal MarkedIdealBiholomorphism InvDomainTowerAlong BlowupTowerIsomorphism
 HironakaSmoothSubmersionOrderedChoiceImageTrace MarkedIdealRestrictOpen MarkedIdealTowerTransport

private theorem initial_values_open_inclusion {r : ℕ} (hr : 0<r) (q : ℕ)
    {X : CMfd.{0} r} (W V : Opens X) (hVW : V≤W)
    (M : MarkedIdeals.MarkedIdeal r (CMfd.of (n := r) W)) (hM : IsInvDomain q M) :
    let inc : V→W:=fun z => ⟨z.val,hVW z.property⟩
    let P:=MarkedIdealBiholomorphism.MarkedIdeal.pullback inc M
    IsInvDomain q P ∧ P.cosupp=inc ⁻¹' M.cosupp ∧
      ∀(p : V),inc p∈M.cosupp →
        (invFamily hr q).inv (X := CMfd.of (n := r) V) P .refl p=
          (invFamily hr q).inv M .refl (inc p) := by
  dsimp only
  let D:=nestedOpens W V
  let e:=nestedOpensDiffeo (n := r) hVW
  let S:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : D→W) M
  have hS : IsInvDomain q S:=isInvDomain_pullback_val D hM
  have hRecord : MarkedIdealBiholomorphism.MarkedIdeal.pullback e.symm S=
      MarkedIdealBiholomorphism.MarkedIdeal.pullback (fun z : V => (⟨z.val,hVW z.property⟩ : W)) M := by
    have h:=whole_markedPullback_comp (f := (Subtype.val : D→W))
      contMDiff_subtype_val e.symm.contMDiff M hM.isWellFormed.isCoherent
    exact h.symm
  refine ⟨?_,?_,?_⟩
  · rw [←hRecord]
    exact isInvDomain_pullback e.symm hS
  · rw [←hRecord,cosupp_pullback_eq hS.isWellFormed.isCoherent,
      cosupp_pullback_val M (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) D]
    rfl
  · intro p hp
    have hpS : e.symm p∈S.cosupp := by
      rw [cosupp_pullback_val M (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) D]
      exact hp
    have hIso:=(invFamily hr q).isInvValue.towerIso e.symm S hS .refl .refl e.symm (.refl) trivial p hpS
    have hRest:=(invFamily hr q).isInvValue.restrictOpen M hM D .refl trivial (e.symm p) hp
    rw [hRecord] at hIso
    exact hIso.trans hRest

private theorem maximal_values_open_inclusion {r : ℕ} (hr : 0<r) (q : ℕ)
    {X : CMfd.{0} r} (W V : Opens X) (hVW : V≤W)
    (M : MarkedIdeals.MarkedIdeal r (CMfd.of (n := r) W)) (hM : IsInvDomain (q+1) M)
    (hMax : IsMaximalOrderAlong M.N M.ideal M.d) :
    let inc : V→W:=fun z => ⟨z.val,hVW z.property⟩
    let P:=MarkedIdealBiholomorphism.MarkedIdeal.pullback inc M
    IsInvDomain (q+1) P ∧ IsMaximalOrderAlong P.N P.ideal P.d ∧ P.cosupp=inc ⁻¹' M.cosupp ∧
      ∀(p : V),inc p∈M.cosupp →
        Seq.StepOneValueMasked.stepOneInvM (invFamily hr q) (X := CMfd.of (n := r) V) P .refl p=
          Seq.StepOneValueMasked.stepOneInvM (invFamily hr q) M .refl (inc p) := by
  dsimp only
  let D:=nestedOpens W V
  let e:=nestedOpensDiffeo (n := r) hVW
  let S:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : D→W) M
  have hS : IsInvDomain (q+1) S:=isInvDomain_pullback_val D hM
  obtain ⟨_,_,hSMax,_⟩:=StepOneRestrictOpen.hypotheses_restrict M D
    hM.isWellFormed hM.one_le_d hMax hM.dimLE
  have hRecord : MarkedIdealBiholomorphism.MarkedIdeal.pullback e.symm S=
      MarkedIdealBiholomorphism.MarkedIdeal.pullback (fun z : V => (⟨z.val,hVW z.property⟩ : W)) M := by
    exact (whole_markedPullback_comp (f := (Subtype.val : D→W))
      contMDiff_subtype_val e.symm.contMDiff M hM.isWellFormed.isCoherent).symm
  obtain ⟨hP,hCos,_hValues⟩:=initial_values_open_inclusion hr (q+1) W V hVW M hM
  obtain ⟨_,_,hPMax,_⟩:=StepOneTowerIso.hypotheses_pullback e.symm S
    hS.isWellFormed hS.one_le_d hSMax hS.dimLE
  rw [hRecord] at hPMax
  refine ⟨hP,hPMax,hCos,?_⟩
  intro p hp
  have hpS : e.symm p∈S.cosupp := by
    rw [cosupp_pullback_val M (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) D]
    exact hp
  have hF:=StepOneSeq.isMaxOrderValue_stepOneInvM (k := q+1) (invFamily hr q) hr
  have hIso:=hF.towerIso e.symm S hS hSMax .refl .refl e.symm (.refl) trivial p hpS
  have hRest:=hF.restrictOpen M hM hMax D .refl trivial (e.symm p) hp
  rw [hRecord] at hIso
  exact hIso.trans hRest

open HironakaActualMaskSectionRepresentative HironakaActualNestedSectionCoordinates

private def InitialSectionValueProperty (q : ℕ) : Prop :=
  ∀{r : ℕ}{V : Opens (ComplexModel r)} (hr : 0<r) (A : Set V)
    (J : GermIdeal (r+1) (productOpen V)) (d : ℕ),
    IsInvDomain q (⟨liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (r+1) (productOpen V)) →
    IsInvDomain q (⟨A,[],GermIdeal.pullback (m := r) (zeroSection V) J,d⟩ : MarkedIdeals.MarkedIdeal r V) →
    ∀x∈cosupport r A (GermIdeal.pullback (m := r) (zeroSection V) J) d,
      (invFamily (Nat.succ_pos r) q).inv (X := CMfd.of (n := r+1) (productOpen V))
        (⟨liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (r+1) (productOpen V)) .refl (zeroSection V x)=
      (invFamily hr q).inv (X := CMfd.of (n := r) V)
        (⟨A,[],GermIdeal.pullback (m := r) (zeroSection V) J,d⟩ : MarkedIdeals.MarkedIdeal r V) .refl x

private theorem masked_values_of_induction (q : ℕ) (ih : InitialSectionValueProperty q)
    (hn : 0<n) (O : Opens (productOpen U)) (A : Set U) (J : GermIdeal (n+1) O) (d : ℕ)
    (hS : IsInvDomain q (⟨(Subtype.val : O→productOpen U) ⁻¹' liftedCarrier A,[],J,d⟩ :
      MarkedIdeals.MarkedIdeal (n+1) O))
    (hB : IsInvDomain q (⟨(Subtype.val : baseMask U O→U) ⁻¹' A,[],
      GermIdeal.pullback (m := n) (sectionToMask U O) J,d⟩ : MarkedIdeals.MarkedIdeal n (baseMask U O)))
    (x : baseMask U O)
    (hx : x∈(⟨(Subtype.val : baseMask U O→U) ⁻¹' A,[],
      GermIdeal.pullback (m := n) (sectionToMask U O) J,d⟩ : MarkedIdeals.MarkedIdeal n (baseMask U O)).cosupp) :
    (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) O)
      (⟨(Subtype.val : O→productOpen U) ⁻¹' liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (n+1) O)
      .refl (sectionToMask U O x)=
    (invFamily hn q).inv (X := CMfd.of (n := n) (baseMask U O))
      (⟨(Subtype.val : baseMask U O→U) ⁻¹' A,[],GermIdeal.pullback (m := n) (sectionToMask U O) J,d⟩ :
        MarkedIdeals.MarkedIdeal n (baseMask U O)) .refl x := by
  let W:=baseMask U O
  let W0:=globalImage U W
  let e:=baseEquiv U W
  let C:=productWindow U W
  let b:=productEquiv U W
  let B : MarkedIdeals.MarkedIdeal n (CMfd.of (n := n) W):=
    ⟨(Subtype.val : W→U) ⁻¹' A,[],GermIdeal.pullback (m := n) (sectionToMask U O) J,d⟩
  let B0:=MarkedIdealBiholomorphism.MarkedIdeal.pullback e.symm B
  let A0:=B0.N
  let I0:=B0.ideal
  let P0 : MarkedIdeals.MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen W0)):=
    ⟨liftedCarrier A0,[],GermIdeal.pullback (m := n+1) (projection W0) I0,d⟩
  have hB0 : IsInvDomain q B0:=isInvDomain_pullback e.symm hB
  have hP0 : IsInvDomain q P0:=section_projected_domain q A0 I0 d hB0
  have hTrace : GermIdeal.pullback (m := n) (zeroSection W0) P0.ideal=I0 := by
    change GermIdeal.pullback (m := n) (zeroSection W0)
      (GermIdeal.pullback (m := n+1) (projection W0) I0)=I0
    rw [←coherent_pullback_comp (projection_contMDiff W0) (zeroSection_contMDiff W0) I0 hB0.isWellFormed.isCoherent]
    have heq : projection W0 ∘ zeroSection W0=id:=funext (projection_section W0)
    rw [heq,BlowupControlledTransform.pullback_id hB0.isWellFormed.isCoherent]
  let x0:=e x
  have hx0 : x0∈B0.cosupp := by
    rw [cosupp_pullback_eq hB.isWellFormed.isCoherent]
    change e.symm x0∈B.cosupp
    simpa only [x0,e.symm_apply_apply] using hx
  have hBaseForIH : IsInvDomain q
      (⟨A0,[],GermIdeal.pullback (m := n) (zeroSection W0) P0.ideal,d⟩ : MarkedIdeals.MarkedIdeal n W0) := by
    rw [hTrace]
    exact hB0
  have hPointForIH : x0∈cosupport n A0 (GermIdeal.pullback (m := n) (zeroSection W0) P0.ideal) d := by
    rw [hTrace]
    exact hx0
  have hIH:=ih hn A0 P0.ideal d hP0 hBaseForIH x0 hPointForIH
  rw [hTrace] at hIH
  have hxP0 : zeroSection W0 x0∈P0.cosupp :=
    (section_cosupport_iff A0 P0.ideal
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP0.isWellFormed.isCoherent hg) x0 d).mp hPointForIH
  have hBaseValue:=(invFamily hn q).isInvValue.towerIso (X := CMfd.of (n := n) W) (X' := CMfd.of (n := n) W0) e.symm B hB .refl .refl e.symm (.refl) trivial x0
    (show e.symm x0∈B.cosupp from by simpa only [x0,e.symm_apply_apply] using hx)
  simp only [x0] at hBaseValue
  let PC:=MarkedIdealBiholomorphism.MarkedIdeal.pullback b P0
  have hPC : IsInvDomain q PC:=isInvDomain_pullback b hP0
  let c:=windowSection U W x
  have hbc : b c=zeroSection W0 x0:=section_square U W x
  have hpc : c∈PC.cosupp := by
    rw [cosupp_pullback_eq hP0.isWellFormed.isCoherent]
    change b c∈P0.cosupp
    rw [hbc]
    exact hxP0
  have hPCValue:=(invFamily (Nat.succ_pos n) q).isInvValue.towerIso (X := CMfd.of (n := n+1) (productOpen W0)) (X' := CMfd.of (n := n+1) C) b P0 hP0 .refl .refl b (.refl) trivial c
    (show b c∈P0.cosupp from by rw [hbc];exact hxP0)
  rw [hbc] at hPCValue

  have hA0 : A0=e '' B.N := by
    ext y
    change e.symm y∈B.N ↔ y∈e '' B.N
    constructor
    · intro hy
      exact ⟨e.symm y,hy,e.apply_symm_apply y⟩
    · rintro ⟨z,hz,rfl⟩
      simpa only [e.symm_apply_apply] using hz
  have hPCN (z : C) : z∈PC.N ↔
      windowProjection U W z∈B.N ∧ actualJointNormalProjection n 1 z.val.val=0 := by
    change b z∈liftedCarrier A0 ↔ _
    rw [hA0]
    exact (carrier_iff U W B.N z).symm
  have hPCI : PC.ideal=GermIdeal.pullback (m := n+1) (windowProjection U W) B.ideal := by
    change GermIdeal.pullback (m := n+1) b
      (GermIdeal.pullback (m := n+1) (projection W0) (GermIdeal.pullback (m := n) e.symm B.ideal))=
      GermIdeal.pullback (m := n+1) (windowProjection U W) B.ideal
    rw [←coherent_pullback_comp (projection_contMDiff W0) b.contMDiff _
      (isCoherent_pullback e.symm.contMDiff hB.isWellFormed.isCoherent),
      ←coherent_pullback_comp e.symm.contMDiff ((projection_contMDiff W0).comp b.contMDiff) B.ideal hB.isWellFormed.isCoherent]
    have heq : e.symm ∘ (projection W0 ∘ b)=windowProjection U W := by
      funext z
      have hsq : e (windowProjection U W z)=projection W0 (b z):=projection_square U W z
      change e.symm (projection W0 (b z))=windowProjection U W z
      rw [←hsq,e.symm_apply_apply]
    rw [heq]
  let V:=overlap U O
  have hVO : V≤O:=inf_le_left
  have hVC : V≤C:=inf_le_right
  let incS : V→O:=fun z => ⟨z.val,hVO z.property⟩
  let incC : V→C:=fun z => ⟨z.val,hVC z.property⟩
  let S : MarkedIdeals.MarkedIdeal (n+1) (CMfd.of (n := n+1) O):=
    ⟨(Subtype.val : O→productOpen U) ⁻¹' liftedCarrier A,[],J,d⟩
  let VS:=MarkedIdealBiholomorphism.MarkedIdeal.pullback incS S
  let VP:=MarkedIdealBiholomorphism.MarkedIdeal.pullback incC PC
  have hpC : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ (windowProjection U W) := by
    apply (ContMDiff.subtypeVal_comp_iff W _).mp
    exact (projection_contMDiff U).comp contMDiff_subtype_val
  have hVPRecord : VP=(⟨(Subtype.val : V→productOpen U) ⁻¹' liftedCarrier A,[],
      GermIdeal.pullback (m := n+1) (overlapProjection U O) B.ideal,d⟩ : MarkedIdeals.MarkedIdeal (n+1) V) := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · ext z
      change (incC z∈PC.N) ↔ z.val∈liftedCarrier A
      rw [hPCN]
      rfl
    · rfl
    · change GermIdeal.pullback (m := n+1) incC PC.ideal=
        GermIdeal.pullback (m := n+1) (overlapProjection U O) B.ideal
      rw [hPCI,←coherent_pullback_comp hpC (contMDiff_inclusion hVC) B.ideal hB.isWellFormed.isCoherent]
      rfl
    · rfl
  have hEq : MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv VS VP := by
    rw [hVPRecord]
    exact restrictEquiv_actual_mask_section U O A [] d J
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hS.isWellFormed.isCoherent hg)

  let v : V:=⟨zeroSection U x.val,x.property,by
    change projection U (zeroSection U x.val)∈W
    rw [projection_section]
    exact x.property⟩
  have hvc : incC v=c:=rfl
  have hvs : incS v=sectionToMask U O x:=rfl
  obtain ⟨hVS,hVSCos,hVSVal⟩:=initial_values_open_inclusion (Nat.succ_pos n) q
    (X := CMfd.of (n := n+1) (productOpen U)) O V hVO S hS
  obtain ⟨hVP,hVPCos,hVPVal⟩:=initial_values_open_inclusion (Nat.succ_pos n) q
    (X := CMfd.of (n := n+1) (productOpen U)) C V hVC PC hPC
  have hvP : v∈VP.cosupp := by
    rw [hVPCos]
    change incC v∈PC.cosupp
    rw [hvc]
    exact hpc
  have hvS : v∈VS.cosupp := by
    rw [hEq.cosupp_eq]
    exact hvP
  have hspt : incS v∈S.cosupp := by
    rw [hVSCos] at hvS
    exact hvS
  have hRep:=(invFamily (Nat.succ_pos n) q).isInvValue.representative (X := CMfd.of (n := n+1) V) VS VP hVS hVP hEq .refl trivial v hvS
  have hSValue : (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) V) VS .refl v=
      (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) O) S .refl (sectionToMask U O x) := by
    have h:=hVSVal v hspt
    change (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) V) VS .refl v=
      (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) O) S .refl (incS v) at h
    rwa [hvs] at h
  have hPValue : (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) V) VP .refl v=
      (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) C) PC .refl c := by
    have h:=hVPVal v (show incC v∈PC.cosupp from by rw [hvc];exact hpc)
    change (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) V) VP .refl v=
      (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) C) PC .refl (incC v) at h
    rwa [hvc] at h
  change (invFamily hn q).inv (X := CMfd.of (n := n) W0) B0 .refl x0=
    (invFamily hn q).inv (X := CMfd.of (n := n) W) B .refl x at hBaseValue
  change (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) O) S .refl (sectionToMask U O x)=
    (invFamily hn q).inv (X := CMfd.of (n := n) W) B .refl x
  calc
    _=(invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) V) VS .refl v := hSValue.symm
    _=(invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) V) VP .refl v := hRep
    _=(invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) C) PC .refl c := hPValue
    _=(invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) (productOpen W0)) P0 .refl (zeroSection W0 x0) := hPCValue
    _=(invFamily hn q).inv (X := CMfd.of (n := n) W0) B0 .refl x0 := hIH
    _=(invFamily hn q).inv (X := CMfd.of (n := n) W) B .refl x := hBaseValue

private theorem maximal_product_stepOne_of_induction (q : ℕ) (ih : InitialSectionValueProperty q)
    (hn : 0<n) (A : Set U) (J : GermIdeal (n+1) (productOpen U)) (d : ℕ)
    (hM : IsInvDomain (q+1) (⟨liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (n+1) (productOpen U)))
    (hB : IsInvDomain (q+1) (⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeals.MarkedIdeal n U))
    (hMax : IsMaximalOrderAlong (liftedCarrier A) J d)
    (x : U) (hx : x∈cosupport n A (GermIdeal.pullback (m := n) (zeroSection U) J) d) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q)
      (X := CMfd.of (n := n+1) (productOpen U))
      (⟨liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (n+1) (productOpen U)) .refl (zeroSection U x)=
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) (X := CMfd.of (n := n) U)
      (⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeals.MarkedIdeal n U) .refl x := by
  let M : MarkedIdeals.MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=⟨liftedCarrier A,[],J,d⟩
  let B : MarkedIdeals.MarkedIdeal n (CMfd.of (n := n) U):=⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
  change Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q)
      (X := CMfd.of (n := n+1) (productOpen U)) M .refl (zeroSection U x)=
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) (X := CMfd.of (n := n) U) B .refl x
  have hA:=hB.isWellFormed.isClosedSubmanifold_N
  have hJ:=hM.isWellFormed.isCoherent
  have hMaxB : IsMaximalOrderAlong B.N B.ideal B.d := by
    intro y hy
    exact hMax (zeroSection U y) ((section_cosupport_iff A J
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ hg) y (d+1)).mp hy)
  have hSM : zeroSection U x∈M.cosupp :=
    (section_cosupport_iff A J (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ hg) x d).mp hx
  have hSB : x∈B.cosupp:=hx
  have hBarM : zeroSection U x∈(StepOneValue.barMarked M).cosupp := by
    rw [StepOneLowerDomain.cosupp_barMarked M hM.isWellFormed hM.one_le_d]
    exact hSM
  have hBarB : x∈(StepOneValue.barMarked B).cosupp := by
    rw [StepOneLowerDomain.cosupp_barMarked B hB.isWellFormed hB.one_le_d]
    exact hSB
  have hLM : StepOneValue.level M .refl (zeroSection U x)=0:=rfl
  have hLB : StepOneValue.level B .refl x=0:=rfl
  have hSpecial : StepOneValue.IsSpecial M .refl (zeroSection U x) ↔StepOneValue.IsSpecial B .refl x :=
    section_isSpecial_refl_iff A hA J hJ d x
  by_cases hspB : StepOneValue.IsSpecial B .refl x
  · have hspM:=hSpecial.mpr hspB
    simp only [Seq.StepOneValueMasked.stepOneInvM,Seq.StepOneValueMasked.stepOneInvL,hspM,hspB,ite_true,hLM,hLB]
  · have hnsM : ¬StepOneValue.IsSpecial M .refl (zeroSection U x):=fun h => hspB (hSpecial.mp h)
    have hDM:=Seq.StepOneCanonicalTail.lowerDataL_refl (X := CMfd.of (n := n+1) (productOpen U)) M
      (k := q+1) (invFamily (Nat.succ_pos n) q) hM.isWellFormed hM.one_le_d (Nat.succ_pos n)
      hMax hM.dimLE .refl trivial hBarM (show StepOneValue.stepRegime M 0 .refl (zeroSection U x) from ⟨hLM,hnsM⟩)
    have hDB:=Seq.StepOneCanonicalTail.lowerDataL_refl (X := CMfd.of (n := n) U) B
      (k := q+1) (invFamily hn q) hB.isWellFormed hB.one_le_d hn hMaxB hB.dimLE .refl trivial hBarB
      (show StepOneValue.stepRegime B 0 .refl x from ⟨hLB,hspB⟩)
    obtain ⟨hMaskM,hLowM,hCanM,hCosLowM⟩:=hDM
    have hDBsave:=hDB
    obtain ⟨hMaskB,hLowB,hCanB,hCosLowB⟩:=hDB
    change zeroSection U x∈StepOneValue.maskB M .refl (zeroSection U x) at hMaskM
    have hxChosen : zeroSection U x∈(StepOneValue.tangentChoice M (zeroSection U x)).1 := (interior_subset hMaskM).1
    have hu:=StepOneCompare.tangentChoice_spec_of_mem M hxChosen
    let u:productOpen U→ℂ:=(StepOneValue.tangentChoice M (zeroSection U x)).2
    have hu0 : u (zeroSection U x)=0 :=
      TangentDirectionAlong.apply_eq_zero_of_mem_cosupport
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ hg) hM.one_le_d hSM (hu.mem _ hxChosen)
    obtain ⟨Wsmall,hxSmall,hSmallSub,hBaseU,hContactBase,hContactEq⟩ :=
      open_section_regular_contact A hA J hJ hu x hx.1 hxChosen hu0
    let O0:=StepOneValue.maskB M .refl (zeroSection U x)
    let O : Opens (productOpen U):=O0 ⊓ ⟨projection U ⁻¹' Wsmall,Wsmall.isOpen.preimage (projection_contMDiff U).continuous⟩
    have hxO : zeroSection U x∈O := by
      refine ⟨hMaskM,?_⟩
      change projection U (zeroSection U x)∈Wsmall
      rwa [projection_section]
    let W:=baseMask U O
    let xW : W:=⟨x,hxO⟩
    have hWsmall : (W:Set U)⊆Wsmall := by
      intro y hy
      have hp : projection U (zeroSection U y)∈Wsmall:=hy.2
      rwa [projection_section] at hp

    let BaseL:=ContactStageKept.contactMarkedKept B (u ∘ zeroSection U) .refl W
    have hBaseL : IsInvDomain q BaseL := by
      have hd:=ContactStageInvDomain.isInvDomain_stage_coeffHom_of_le (M := U) (k := q+1)
        hB.isWellFormed.isCoherent hA hB.one_le_d hB.dimLE Wsmall hBaseU
        (Y := CMfd.of (n := n) U) .refl trivial W (fun y hy => hWsmall hy) (by
          intro y hy _hycontact hyZ
          have hyO : zeroSection U y∈O0:=hy.1
          have hySZ := (interior_subset hyO).2.2
          have hyB : StepOneValue.IsSpecial B .refl y:=Or.inl ⟨rfl,hyZ⟩
          have hyM:=(section_isSpecial_refl_iff A hA J hJ d y).mpr hyB
          rcases hyM with ⟨_hl,hZ⟩ | ⟨hl,_hmem⟩
          · exact hySZ hZ
          · change 1≤0 at hl
            omega)
      exact hd

    let QS:=coeffMarkedAlong (StepOneValue.barMarked M)
    let QB:=coeffMarkedAlong (StepOneValue.barMarked B)
    have hBarMWF:=StepOneLowerDomain.isWellFormed_barMarked M hM.isWellFormed
    have hBarBWF:=StepOneLowerDomain.isWellFormed_barMarked B hB.isWellFormed
    have hcQS : QS.ideal.IsCoherent:=isCoherent_coeffMarkedAlong hBarMWF.isCoherent hBarMWF.isClosedSubmanifold_N
    have hcQB : QB.ideal.IsCoherent:=isCoherent_coeffMarkedAlong hBarBWF.isCoherent hBarBWF.isClosedSubmanifold_N
    let D:=A∩{y | u (zeroSection U y)=0}
    let μ:=QS.d
    let Jlow:=GermIdeal.pullback (m := n+1) (Subtype.val : O→productOpen U) QS.ideal
    let SL : MarkedIdeals.MarkedIdeal (n+1) (CMfd.of (n := n+1) O):=
      ⟨(Subtype.val : O→productOpen U) ⁻¹' liftedCarrier D,[],Jlow,μ⟩
    let L0:=StepOneValueMasked.lowerMarkedM M 0 .refl (zeroSection U x)
    change IsInvDomain q L0 at hLowM
    change (⟨zeroSection U x,hMaskM⟩ : O0)∈L0.cosupp at hCosLowM
    have hOO0 : O≤O0:=inf_le_left
    let inc : O→O0:=fun z => ⟨z.val,hOO0 z.property⟩
    let LO:=MarkedIdealBiholomorphism.MarkedIdeal.pullback inc L0
    obtain ⟨hLO,hLOCos,hLOVal⟩:=initial_values_open_inclusion (Nat.succ_pos n) q
      (X := CMfd.of (n := n+1) (productOpen U)) O0 O hOO0 L0 hLowM
    have hLORecord : LO=SL := by
      apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      · ext z
        change z.val∈liftedCarrier A∩{z | u z=0} ↔ z.val∈liftedCarrier D
        exact Set.ext_iff.mp (open_lifted_contact_eq A u) z.val
      · rfl
      · change GermIdeal.pullback (m := n+1) inc
          (GermIdeal.pullback (m := n+1) (Subtype.val : O0→productOpen U) QS.ideal)=
          GermIdeal.pullback (m := n+1) (Subtype.val : O→productOpen U) QS.ideal
        rw [←coherent_pullback_comp contMDiff_subtype_val (contMDiff_inclusion hOO0) QS.ideal hcQS]
        rfl
      · rfl
    have hSL : IsInvDomain q SL := by rw [←hLORecord];exact hLO
    have hsO : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+1)) ∞ (sectionToMask U O) := by
      apply (ContMDiff.subtypeVal_comp_iff O _).mp
      exact (zeroSection_contMDiff U).comp contMDiff_subtype_val
    have hSecSecond : GermIdeal.pullback (m := n) (zeroSection U) QS.ideal=QB.ideal :=
      section_second_coefficient_ideal A hA J hJ d
    have hTrace : GermIdeal.pullback (m := n) (sectionToMask U O) Jlow=
        GermIdeal.pullback (m := n) (Subtype.val : W→U) QB.ideal := by
      change GermIdeal.pullback (m := n) (sectionToMask U O)
        (GermIdeal.pullback (m := n+1) (Subtype.val : O→productOpen U) QS.ideal)=_
      rw [←coherent_pullback_comp contMDiff_subtype_val hsO QS.ideal hcQS]
      have heq : (Subtype.val : O→productOpen U) ∘ sectionToMask U O=
          zeroSection U ∘ (Subtype.val : W→U) := rfl
      rw [heq,coherent_pullback_comp (zeroSection_contMDiff U) contMDiff_subtype_val QS.ideal hcQS,hSecSecond]
    let BL : MarkedIdeals.MarkedIdeal n (CMfd.of (n := n) W):=
      ⟨(Subtype.val : W→U) ⁻¹' D,[],GermIdeal.pullback (m := n) (sectionToMask U O) Jlow,μ⟩
    have hBLRecord : BL=BaseL := by
      apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
      · rfl
      · rfl
      · exact hTrace
      · rfl
    have hBL : IsInvDomain q BL := by rw [hBLRecord];exact hBaseL
    have hxQB : x∈QB.cosupp := by
      change x∈(coeffMarkedAlong (StepOneValue.barMarked B)).cosupp
      rw [cosupp_coeffMarkedAlong (𝔪 := StepOneValue.barMarked B) hBarBWF.isClosedSubmanifold_N.2
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hBarBWF.isCoherent hg)
        (ContactIndependenceAlong.one_le_coeffMarkedAlong_d (homMarkedAlong B))]
      exact hBarB
    have hxPullQB : xW∈(MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : W→U) QB).cosupp := by
      rw [cosupp_pullback_val QB (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcQB hg) W]
      exact hxQB
    have hxBaseL : xW∈BaseL.cosupp := by
      refine ⟨⟨hx.1,hu0⟩,?_⟩
      intro g hg
      exact (hxPullQB.2 g hg).mono_set (fun y hy => hy.1)
    have hxBL : xW∈BL.cosupp := by rw [hBLRecord];exact hxBaseL
    have hMasked:=masked_values_of_induction q ih hn O D Jlow μ hSL hBL xW hxBL

    let p0 : O0:=⟨zeroSection U x,hMaskM⟩
    let pO:=sectionToMask U O xW
    have hpO0 : inc pO=p0:=rfl
    have hSourceLowVal:=hLOVal pO (show inc pO∈L0.cosupp from by rw [hpO0];exact hCosLowM)
    change (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) O) LO .refl pO=
      (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) O0) L0 .refl (inc pO) at hSourceLowVal
    rw [hLORecord,hpO0] at hSourceLowVal
    change (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) O) SL .refl pO=
      (invFamily hn q).inv (X := CMfd.of (n := n) W) BL .refl xW at hMasked
    rw [hBLRecord] at hMasked
    have hLowEq:=hSourceLowVal.symm.trans hMasked
    have hAnchor:=Seq.ContactLowerValue.lowerValueL_zero_eq (X := CMfd.of (n := n) U)
      (invFamily hn q) B hB.isWellFormed hB.one_le_d .refl .refl trivial hBaseU W
      (fun y hy => hWsmall hy) (by intro H hH;cases hH) hBaseL trivial xW.property hBarB hDBsave
    have hLowerM : Seq.StepOneValueMasked.lowerValueL (invFamily (Nat.succ_pos n) q) M
        (StepOneValueMasked.lowerMarkedM M) 0 .refl .refl (zeroSection U x)=
        ((invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) O0) L0 .refl p0 : WithTop (ValTy q)) :=
      Seq.StepOneValueMasked.lowerValueL_eq_of_mem (invFamily (Nat.succ_pos n) q) M
        (StepOneValueMasked.lowerMarkedM M) (s := 0) (T₀ := .refl) (T₁ := .refl) (y := zeroSection U x) hMaskM
    change Seq.StepOneValueMasked.lowerValueL (invFamily hn q) B (StepOneValueMasked.lowerMarkedM B)
        0 .refl .refl x=((invFamily hn q).inv (X := CMfd.of (n := n) W) BaseL .refl xW : WithTop (ValTy q)) at hAnchor
    simp only [Seq.StepOneValueMasked.stepOneInvM,Seq.StepOneValueMasked.stepOneInvL,hnsM,hspB,ite_false,hLM,hLB,
      StepOneRegime.regimeRun,BlowupTowerSplit.head,BlowupTowerSplit.tail,BlowupTowerSplit.split]
    rw [hLowerM,hAnchor]
    exact congrArg (fun v : ValTy q => toLex (0,(v : WithTop (ValTy q)))) hLowEq

private theorem masked_maximal_stepOne_of_induction (q : ℕ) (ih : InitialSectionValueProperty q)
    (hn : 0<n) (O : Opens (productOpen U)) (A : Set U) (J : GermIdeal (n+1) O) (d : ℕ)
    (hS : IsInvDomain (q+1) (⟨(Subtype.val : O→productOpen U) ⁻¹' liftedCarrier A,[],J,d⟩ :
      MarkedIdeals.MarkedIdeal (n+1) O))
    (hB : IsInvDomain (q+1) (⟨(Subtype.val : baseMask U O→U) ⁻¹' A,[],
      GermIdeal.pullback (m := n) (sectionToMask U O) J,d⟩ : MarkedIdeals.MarkedIdeal n (baseMask U O)))
    (hMaxS : IsMaximalOrderAlong ((Subtype.val : O→productOpen U) ⁻¹' liftedCarrier A) J d)
    (hMaxB : IsMaximalOrderAlong ((Subtype.val : baseMask U O→U) ⁻¹' A)
      (GermIdeal.pullback (m := n) (sectionToMask U O) J) d)
    (x : baseMask U O)
    (hx : x∈(⟨(Subtype.val : baseMask U O→U) ⁻¹' A,[],
      GermIdeal.pullback (m := n) (sectionToMask U O) J,d⟩ : MarkedIdeals.MarkedIdeal n (baseMask U O)).cosupp) :
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) O)
      (⟨(Subtype.val : O→productOpen U) ⁻¹' liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (n+1) O)
      .refl (sectionToMask U O x)=
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) (X := CMfd.of (n := n) (baseMask U O))
      (⟨(Subtype.val : baseMask U O→U) ⁻¹' A,[],GermIdeal.pullback (m := n) (sectionToMask U O) J,d⟩ :
        MarkedIdeals.MarkedIdeal n (baseMask U O)) .refl x := by
  let W:=baseMask U O
  let W0:=globalImage U W
  let e:=baseEquiv U W
  let C:=productWindow U W
  let b:=productEquiv U W
  let B : MarkedIdeals.MarkedIdeal n (CMfd.of (n := n) W):=
    ⟨(Subtype.val : W→U) ⁻¹' A,[],GermIdeal.pullback (m := n) (sectionToMask U O) J,d⟩
  let B0:=MarkedIdealBiholomorphism.MarkedIdeal.pullback e.symm B
  let A0:=B0.N
  let I0:=B0.ideal
  let P0 : MarkedIdeals.MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen W0)):=
    ⟨liftedCarrier A0,[],GermIdeal.pullback (m := n+1) (projection W0) I0,d⟩
  have hB0 : IsInvDomain (q+1) B0:=isInvDomain_pullback e.symm hB
  obtain ⟨_,_,hB0Max,_⟩:=StepOneTowerIso.hypotheses_pullback (X := CMfd.of (n := n) W) (X' := CMfd.of (n := n) W0) e.symm B hB.isWellFormed hB.one_le_d hMaxB hB.dimLE
  have hFS:=StepOneSeq.isMaxOrderValue_stepOneInvM (k := q+1) (invFamily (Nat.succ_pos n) q) (Nat.succ_pos n)
  have hFB:=StepOneSeq.isMaxOrderValue_stepOneInvM (k := q+1) (invFamily hn q) hn
  have hP0 : IsInvDomain (q+1) P0:=section_projected_domain (q+1) A0 I0 d hB0
  have hTrace : GermIdeal.pullback (m := n) (zeroSection W0) P0.ideal=I0 := by
    change GermIdeal.pullback (m := n) (zeroSection W0)
      (GermIdeal.pullback (m := n+1) (projection W0) I0)=I0
    rw [←coherent_pullback_comp (projection_contMDiff W0) (zeroSection_contMDiff W0) I0 hB0.isWellFormed.isCoherent]
    have heq : projection W0 ∘ zeroSection W0=id:=funext (projection_section W0)
    rw [heq,BlowupControlledTransform.pullback_id hB0.isWellFormed.isCoherent]
  let x0:=e x
  have hx0 : x0∈B0.cosupp := by
    rw [cosupp_pullback_eq hB.isWellFormed.isCoherent]
    change e.symm x0∈B.cosupp
    simpa only [x0,e.symm_apply_apply] using hx
  have hBaseForIH : IsInvDomain (q+1)
      (⟨A0,[],GermIdeal.pullback (m := n) (zeroSection W0) P0.ideal,d⟩ : MarkedIdeals.MarkedIdeal n W0) := by
    rw [hTrace]
    exact hB0
  have hPointForIH : x0∈cosupport n A0 (GermIdeal.pullback (m := n) (zeroSection W0) P0.ideal) d := by
    rw [hTrace]
    exact hx0
  have hP0Max : IsMaximalOrderAlong P0.N P0.ideal P0.d := by
    intro z hz
    have hz' : z∈liftedCarrier (cosupport n A0 (GermIdeal.pullback (m := n) (zeroSection W0) P0.ideal) (d+1)) := by
      rw [←source_cosupport_eq_lifted A0 P0.ideal
        (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP0.isWellFormed.isCoherent hg) (d+1)]
      exact hz
    have hb:=hz'.1
    rw [hTrace] at hb
    exact hB0Max _ hb
  have hIH:=maximal_product_stepOne_of_induction q ih hn A0 P0.ideal d hP0 hBaseForIH hP0Max x0 hPointForIH
  rw [hTrace] at hIH
  have hxP0 : zeroSection W0 x0∈P0.cosupp :=
    (section_cosupport_iff A0 P0.ideal
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hP0.isWellFormed.isCoherent hg) x0 d).mp hPointForIH
  have hBaseValue:=hFB.towerIso (X := CMfd.of (n := n) W) (X' := CMfd.of (n := n) W0) e.symm B hB hMaxB .refl .refl e.symm (.refl) trivial x0
    (show e.symm x0∈B.cosupp from by simpa only [x0,e.symm_apply_apply] using hx)
  simp only [x0] at hBaseValue
  let PC:=MarkedIdealBiholomorphism.MarkedIdeal.pullback b P0
  have hPC : IsInvDomain (q+1) PC:=isInvDomain_pullback b hP0
  obtain ⟨_,_,hPCMax,_⟩:=StepOneTowerIso.hypotheses_pullback (X := CMfd.of (n := n+1) (productOpen W0)) (X' := CMfd.of (n := n+1) C) b P0 hP0.isWellFormed hP0.one_le_d hP0Max hP0.dimLE
  let c:=windowSection U W x
  have hbc : b c=zeroSection W0 x0:=section_square U W x
  have hpc : c∈PC.cosupp := by
    rw [cosupp_pullback_eq hP0.isWellFormed.isCoherent]
    change b c∈P0.cosupp
    rw [hbc]
    exact hxP0
  have hPCValue:=hFS.towerIso (X := CMfd.of (n := n+1) (productOpen W0)) (X' := CMfd.of (n := n+1) C) b P0 hP0 hP0Max .refl .refl b (.refl) trivial c
    (show b c∈P0.cosupp from by rw [hbc];exact hxP0)
  rw [hbc] at hPCValue

  have hA0 : A0=e '' B.N := by
    ext y
    change e.symm y∈B.N ↔ y∈e '' B.N
    constructor
    · intro hy
      exact ⟨e.symm y,hy,e.apply_symm_apply y⟩
    · rintro ⟨z,hz,rfl⟩
      simpa only [e.symm_apply_apply] using hz
  have hPCN (z : C) : z∈PC.N ↔
      windowProjection U W z∈B.N ∧ actualJointNormalProjection n 1 z.val.val=0 := by
    change b z∈liftedCarrier A0 ↔ _
    rw [hA0]
    exact (carrier_iff U W B.N z).symm
  have hPCI : PC.ideal=GermIdeal.pullback (m := n+1) (windowProjection U W) B.ideal := by
    change GermIdeal.pullback (m := n+1) b
      (GermIdeal.pullback (m := n+1) (projection W0) (GermIdeal.pullback (m := n) e.symm B.ideal))=
      GermIdeal.pullback (m := n+1) (windowProjection U W) B.ideal
    rw [←coherent_pullback_comp (projection_contMDiff W0) b.contMDiff _
      (isCoherent_pullback e.symm.contMDiff hB.isWellFormed.isCoherent),
      ←coherent_pullback_comp e.symm.contMDiff ((projection_contMDiff W0).comp b.contMDiff) B.ideal hB.isWellFormed.isCoherent]
    have heq : e.symm ∘ (projection W0 ∘ b)=windowProjection U W := by
      funext z
      have hsq : e (windowProjection U W z)=projection W0 (b z):=projection_square U W z
      change e.symm (projection W0 (b z))=windowProjection U W z
      rw [←hsq,e.symm_apply_apply]
    rw [heq]
  let V:=overlap U O
  have hVO : V≤O:=inf_le_left
  have hVC : V≤C:=inf_le_right
  let incS : V→O:=fun z => ⟨z.val,hVO z.property⟩
  let incC : V→C:=fun z => ⟨z.val,hVC z.property⟩
  let S : MarkedIdeals.MarkedIdeal (n+1) (CMfd.of (n := n+1) O):=
    ⟨(Subtype.val : O→productOpen U) ⁻¹' liftedCarrier A,[],J,d⟩
  let VS:=MarkedIdealBiholomorphism.MarkedIdeal.pullback incS S
  let VP:=MarkedIdealBiholomorphism.MarkedIdeal.pullback incC PC
  have hpC : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ (windowProjection U W) := by
    apply (ContMDiff.subtypeVal_comp_iff W _).mp
    exact (projection_contMDiff U).comp contMDiff_subtype_val
  have hVPRecord : VP=(⟨(Subtype.val : V→productOpen U) ⁻¹' liftedCarrier A,[],
      GermIdeal.pullback (m := n+1) (overlapProjection U O) B.ideal,d⟩ : MarkedIdeals.MarkedIdeal (n+1) V) := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · ext z
      change (incC z∈PC.N) ↔ z.val∈liftedCarrier A
      rw [hPCN]
      rfl
    · rfl
    · change GermIdeal.pullback (m := n+1) incC PC.ideal=
        GermIdeal.pullback (m := n+1) (overlapProjection U O) B.ideal
      rw [hPCI,←coherent_pullback_comp hpC (contMDiff_inclusion hVC) B.ideal hB.isWellFormed.isCoherent]
      rfl
    · rfl
  have hEq : MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv VS VP := by
    rw [hVPRecord]
    exact restrictEquiv_actual_mask_section U O A [] d J
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hS.isWellFormed.isCoherent hg)

  let v : V:=⟨zeroSection U x.val,x.property,by
    change projection U (zeroSection U x.val)∈W
    rw [projection_section]
    exact x.property⟩
  have hvc : incC v=c:=rfl
  have hvs : incS v=sectionToMask U O x:=rfl
  obtain ⟨hVS,hVSMax,hVSCos,hVSVal⟩:=maximal_values_open_inclusion (Nat.succ_pos n) q
    (X := CMfd.of (n := n+1) (productOpen U)) O V hVO S hS hMaxS
  obtain ⟨hVP,hVPMax,hVPCos,hVPVal⟩:=maximal_values_open_inclusion (Nat.succ_pos n) q
    (X := CMfd.of (n := n+1) (productOpen U)) C V hVC PC hPC hPCMax
  have hvP : v∈VP.cosupp := by
    rw [hVPCos]
    change incC v∈PC.cosupp
    rw [hvc]
    exact hpc
  have hvS : v∈VS.cosupp := by
    rw [hEq.cosupp_eq]
    exact hvP
  have hspt : incS v∈S.cosupp := by
    rw [hVSCos] at hvS
    exact hvS
  have hRep:=hFS.representative (X := CMfd.of (n := n+1) V) VS VP hVS hVSMax hVP hVPMax hEq .refl trivial v hvS
  have hSValue : Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) V) VS .refl v=
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) O) S .refl (sectionToMask U O x) := by
    have h:=hVSVal v hspt
    change Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) V) VS .refl v=
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) O) S .refl (incS v) at h
    rwa [hvs] at h
  have hPValue : Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) V) VP .refl v=
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) C) PC .refl c := by
    have h:=hVPVal v (show incC v∈PC.cosupp from by rw [hvc];exact hpc)
    change Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) V) VP .refl v=
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) C) PC .refl (incC v) at h
    rwa [hvc] at h
  change Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) (X := CMfd.of (n := n) W0) B0 .refl x0=
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) (X := CMfd.of (n := n) W) B .refl x at hBaseValue
  change Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) O) S .refl (sectionToMask U O x)=
    Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) (X := CMfd.of (n := n) W) B .refl x
  calc
    _=Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) V) VS .refl v := hSValue.symm
    _=Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) V) VP .refl v := hRep
    _=Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) C) PC .refl c := hPValue
    _=Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) (X := CMfd.of (n := n+1) (productOpen W0)) P0 .refl (zeroSection W0 x0) := hPCValue
    _=Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) (X := CMfd.of (n := n) W0) B0 .refl x0 := hIH
    _=Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) (X := CMfd.of (n := n) W) B .refl x := hBaseValue

open CompanionRebase CompanionReductionAlong MonomialPartAlong RestrictedIdealExtension

private theorem companion_empty_primary_equivalence {r : ℕ} {X : CMfd.{0} r}
    (M : MarkedIdeals.MarkedIdeal r X) (hE : M.E=[]) (hc : M.ideal.IsCoherent)
    (o : ℕ) (hod : M.d≤o) :
    MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv (compAt M o .refl)
      (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : ordMask M o→X)
        (⟨M.N,[],M.ideal,o⟩ : MarkedIdeals.MarkedIdeal r X)) := by
  rcases M with ⟨N,E,I,d⟩
  change E=[] at hE
  subst E
  let W:=ordMask (M := X) (⟨N,[],I,d⟩ : MarkedIdeals.MarkedIdeal r X) o
  change MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv
    (companionAlong (X := CMfd.of (n := r) W) ((Subtype.val : W→X) ⁻¹' N) []
      (nonmonomialPartAlong r ((Subtype.val : W→X) ⁻¹' N) (GermIdeal.pullback (m := r) (Subtype.val : W→X) I) [])
      (monomialPartAlong r ((Subtype.val : W→X) ⁻¹' N) (GermIdeal.pullback (m := r) (Subtype.val : W→X) I) []) o d)
    (⟨(Subtype.val : W→X) ⁻¹' N,[],GermIdeal.pullback (m := r) (Subtype.val : W→X) I,o⟩ :
      MarkedIdeals.MarkedIdeal r W)
  rw [companionAlong,if_neg (Nat.not_lt.mpr hod),nonmonomialPartAlong_nil_eq_restrictOn]
  exact ⟨rfl,rfl,rfl,restrictLe_restrictOn,restrictLe_self_restrictOn (isCoherent_pullback contMDiff_subtype_val hc)⟩

private theorem maximalOrder_of_restricted_equivalence {r : ℕ} {X : CMfd.{0} r}
    {M P : MarkedIdeals.MarkedIdeal r X}
    (hEq : MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv M P)
    (hMax : IsMaximalOrderAlong M.N M.ideal M.d) :
    IsMaximalOrderAlong P.N P.ideal P.d := by
  intro x hx
  rw [←hEq.N_eq] at hx
  have hs:=MarkedIdealOperationsAlong.cosupport_subset_of_restrictLe hEq.le (P.d+1) hx
  rw [←hEq.d_eq] at hs
  exact hMax x hs

private theorem initial_section_all_indices (q : ℕ) : InitialSectionValueProperty q := by
  induction q with
  | zero =>
    intro n U hn A J d hM hB x hx
    rfl
  | succ q ih =>
    intro n U hn A J d hM hB x hx
    rw [invFamily_succ,generalStep_inv,invFamily_succ,generalStep_inv]
    let M : MarkedIdeals.MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=⟨liftedCarrier A,[],J,d⟩
    let B : MarkedIdeals.MarkedIdeal n (CMfd.of (n := n) U):=⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩
    let F := fun {X : CMfd (n+1)} (K : MarkedIdeals.MarkedIdeal (n+1) X) {Y : CMfd (n+1)} (T : BlowupTower X Y) (y : Y) =>
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q) K T y
    let G := fun {X : CMfd n} (K : MarkedIdeals.MarkedIdeal n X) {Y : CMfd n} (T : BlowupTower X Y) (y : Y) =>
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn q) K T y
    change (genInv F M .refl (zeroSection U x) : ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy q)))) = genInv G B .refl x
    have ho : nmOrd M (zeroSection U x)=nmOrd B x := section_nmOrd_eq A J hM.isWellFormed.isCoherent x d
    have hs : genSecond F M .refl (zeroSection U x)=genSecond G B .refl x := by
      by_cases hzero : nmOrd B x=0
      · simp only [genSecond,geoTransformAlong,ho,hzero,ite_true]
        apply congrArg (fun v : WithBot MonomialInvariant.Val => toLex (Sum.inl v))
        have hγM : gammaAlong (n+1) M.N M.ideal M.E M.d (zeroSection U x)=⊥ := by
          apply MonomialInvariant.inv_eq_bot_iff.mpr
          simpa [M,MonomialCase.memberIdx] using (Nat.lt_of_lt_of_le Nat.zero_lt_one hM.one_le_d)
        have hγB : gammaAlong n B.N B.ideal B.E B.d x=⊥ := by
          apply MonomialInvariant.inv_eq_bot_iff.mpr
          simpa [B,MonomialCase.memberIdx] using (Nat.lt_of_lt_of_le Nat.zero_lt_one hB.one_le_d)
        exact hγM.trans hγB.symm
      · simp only [genSecond,geoTransformAlong,ho,hzero,ite_false]
        simp only [StepOneRegime.regimeRun,BlowupTowerSplit.head,BlowupTowerSplit.tail,BlowupTowerSplit.split]
        have hSM : zeroSection U x∈ordMask M (nmOrd B x) := by
          apply (mem_ordMask_iff (Nat.succ_pos n) hM.isWellFormed hM.isNonzeroAlongAt _ _).mpr
          intro h
          have hle := (mem_ordGe_iff hM.isWellFormed hM.isNonzeroAlongAt
            ((section_mem A x).mpr hx.1) (nmOrd B x+1)).mp h
          omega
        have hBM : x∈ordMask B (nmOrd B x) := by
          apply (mem_ordMask_iff hn hB.isWellFormed hB.isNonzeroAlongAt _ _).mpr
          intro h
          have hle := (mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt hx.1 (nmOrd B x+1)).mp h
          omega
        simp only [genLowerValue,geoTransformAlong,BlowupTower.proj,id_eq]
        apply congrArg (fun v : WithTop (ℕ ×ₗ WithTop (ValTy q)) => toLex (Sum.inr v))
        rw [dif_pos hSM,dif_pos hBM]
        have hPos : 1≤nmOrd B x := Nat.one_le_iff_ne_zero.mpr hzero
        have hxM : zeroSection U x∈M.cosupp :=
          (section_cosupport_iff A J (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hg) x d).mp hx
        have hOrder : nmOrd (geoTransformAlong M BlowupTower.refl) (zeroSection U x)=nmOrd B x := by
          simpa only [geoTransformAlong] using ho
        obtain ⟨hSM0,hKS,hmaxKS,hcanKS,hcosKS⟩ := genLowerData_refl (𝔪 := M) F (Nat.succ_pos n) hM
          BlowupTower.refl trivial hxM hOrder hPos
        obtain ⟨hBM0,hKB,hmaxKB,hcanKB,hcosKB⟩ := genLowerData_refl (𝔪 := B) G hn hB
          BlowupTower.refl trivial hx rfl hPos
        apply congrArg (fun v : ℕ ×ₗ WithTop (ValTy q) => (v : WithTop (ℕ ×ₗ WithTop (ValTy q))))
        change Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) q)
          (compAt M (nmOrd B x) .refl) .refl ⟨zeroSection U x,hSM⟩ =
          Seq.StepOneValueMasked.stepOneInvM (invFamily hn q)
          (compAt B (nmOrd B x) .refl) .refl ⟨x,hBM⟩

        let o:=nmOrd B x
        let OS:=ordMask M o
        let OB:=ordMask B o
        let KS:=compAt M o .refl
        let KB:=compAt B o .refl
        let pS : OS:=⟨zeroSection U x,hSM⟩
        let pB : OB:=⟨x,hBM⟩
        change IsInvDomain (q+1) KS at hKS
        change IsInvDomain (q+1) KB at hKB
        change IsMaximalOrderAlong KS.N KS.ideal KS.d at hmaxKS
        change IsMaximalOrderAlong KB.N KB.ideal KB.d at hmaxKB
        change pS∈KS.cosupp at hcosKS
        change pB∈KB.cosupp at hcosKB
        have hge : x∈ordGe B d := by
          change x∈ordGe (ordinaryTraceMarked (X := CMfd.of (n := n) U) A
            (GermIdeal.pullback (m := n) (zeroSection U) J)) d
          rw [ordGe_ordinaryTraceMarked_eq_cosupport _ _ hB.isWellFormed.isCoherent]
          exact hx
        have hod : d≤o:=(mem_ordGe_iff hB.isWellFormed hB.isNonzeroAlongAt hx.1 d).mp hge
        let MM : MarkedIdeals.MarkedIdeal (n+1) (CMfd.of (n := n+1) (productOpen U)):=⟨liftedCarrier A,[],J,o⟩
        let BM : MarkedIdeals.MarkedIdeal n (CMfd.of (n := n) U):=⟨A,[],B.ideal,o⟩
        have hMM : IsInvDomain (q+1) MM :=
          ⟨⟨hM.isWellFormed.isClosedSubmanifold_N,hM.isWellFormed.isCoherent,
            NormalCrossings.isSNCDivisor_nil,NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hM.isWellFormed.isClosedSubmanifold_N⟩,
            hM.dimLE,hPos,hM.isNonzeroAlongAt⟩
        have hBM0 : IsInvDomain (q+1) BM :=
          ⟨⟨hB.isWellFormed.isClosedSubmanifold_N,hB.isWellFormed.isCoherent,
            NormalCrossings.isSNCDivisor_nil,NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hB.isWellFormed.isClosedSubmanifold_N⟩,
            hB.dimLE,hPos,hB.isNonzeroAlongAt⟩
        let PS:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : OS→productOpen U) MM
        let PB:=MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : OB→U) BM
        have hPS : IsInvDomain (q+1) PS:=isInvDomain_pullback_val OS hMM
        have hPB : IsInvDomain (q+1) PB:=isInvDomain_pullback_val OB hBM0
        have hEqS : MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv KS PS :=
          companion_empty_primary_equivalence (X := CMfd.of (n := n+1) (productOpen U)) M rfl hM.isWellFormed.isCoherent o hod
        have hEqB : MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv KB PB :=
          companion_empty_primary_equivalence (X := CMfd.of (n := n) U) B rfl hB.isWellFormed.isCoherent o hod
        have hPSMax:=maximalOrder_of_restricted_equivalence (X := CMfd.of (n := n+1) OS) hEqS hmaxKS
        have hPBMax:=maximalOrder_of_restricted_equivalence (X := CMfd.of (n := n) OB) hEqB hmaxKB
        have hFS:=StepOneSeq.isMaxOrderValue_stepOneInvM (k := q+1) (invFamily (Nat.succ_pos n) q) (Nat.succ_pos n)
        have hFB:=StepOneSeq.isMaxOrderValue_stepOneInvM (k := q+1) (invFamily hn q) hn
        have hRepS:=hFS.representative (X := CMfd.of (n := n+1) OS) KS PS hKS hmaxKS hPS hPSMax hEqS .refl trivial pS hcosKS
        have hRepB:=hFB.representative (X := CMfd.of (n := n) OB) KB PB hKB hmaxKB hPB hPBMax hEqB .refl trivial pB hcosKB
        let W:=baseMask U OS
        have hWOB : W≤OB := by
          intro y hy
          exact (section_orderMask_iff (q+1) hn A J d o hM hB y).mp hy
        let xW : W:=⟨x,hSM⟩
        let incW : W→OB:=fun y => ⟨y.val,hWOB y.property⟩
        let PBW:=MarkedIdealBiholomorphism.MarkedIdeal.pullback incW PB
        obtain ⟨hPBW,hPBWMax,hPBWCos,hPBWVal⟩:=maximal_values_open_inclusion hn q
          (X := CMfd.of (n := n) U) OB W hWOB PB hPB hPBMax
        let JS:=GermIdeal.pullback (m := n+1) (Subtype.val : OS→productOpen U) J
        let BW : MarkedIdeals.MarkedIdeal n (CMfd.of (n := n) W):=
          ⟨(Subtype.val : W→U) ⁻¹' A,[],GermIdeal.pullback (m := n) (sectionToMask U OS) JS,o⟩
        have hsOS : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel (n+1)) ∞ (sectionToMask U OS) := by
          apply (ContMDiff.subtypeVal_comp_iff OS _).mp
          exact (zeroSection_contMDiff U).comp contMDiff_subtype_val
        have hTrace : GermIdeal.pullback (m := n) (sectionToMask U OS) JS=
            GermIdeal.pullback (m := n) (Subtype.val : W→U) B.ideal := by
          change GermIdeal.pullback (m := n) (sectionToMask U OS)
            (GermIdeal.pullback (m := n+1) (Subtype.val : OS→productOpen U) J)=_
          rw [←coherent_pullback_comp contMDiff_subtype_val hsOS J hM.isWellFormed.isCoherent]
          have heq : (Subtype.val : OS→productOpen U) ∘ sectionToMask U OS=
              zeroSection U ∘ (Subtype.val : W→U) := rfl
          rw [heq,coherent_pullback_comp (zeroSection_contMDiff U) contMDiff_subtype_val J hM.isWellFormed.isCoherent]
        have hBWRecord : BW=PBW := by
          apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
          · rfl
          · rfl
          · change GermIdeal.pullback (m := n) (sectionToMask U OS) JS=
              GermIdeal.pullback (m := n) incW (GermIdeal.pullback (m := n) (Subtype.val : OB→U) B.ideal)
            rw [←coherent_pullback_comp contMDiff_subtype_val (contMDiff_inclusion hWOB) B.ideal hB.isWellFormed.isCoherent]
            exact hTrace
          · rfl
        have hBW : IsInvDomain (q+1) BW := by rw [hBWRecord];exact hPBW
        have hBWMax : IsMaximalOrderAlong BW.N BW.ideal BW.d := by rw [hBWRecord];exact hPBWMax
        have hpB : pB∈PB.cosupp := by rw [←hEqB.cosupp_eq];exact hcosKB
        have hxBW : xW∈BW.cosupp := by
          rw [hBWRecord,hPBWCos]
          exact hpB
        have hMid:=masked_maximal_stepOne_of_induction q ih hn OS A JS o hPS hBW hPSMax hBWMax xW hxBW
        change F (X := CMfd.of (n := n+1) OS) PS .refl pS=
          G (X := CMfd.of (n := n) W) BW .refl xW at hMid
        rw [hBWRecord] at hMid
        have hLocal:=hPBWVal xW hpB
        change G (X := CMfd.of (n := n) W) PBW .refl xW=
          G (X := CMfd.of (n := n) OB) PB .refl pB at hLocal
        exact hRepS.trans (hMid.trans (hLocal.trans hRepB.symm))


    exact congrArg (fun p : ℕ × (WithBot MonomialInvariant.Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy q))) => toLex p)
      (Prod.ext ho hs)


theorem section_domain_of_original_source (q : ℕ) (A : Set U)
    (J : GermIdeal (n+1) (productOpen U)) (d : ℕ)
    (hM : IsInvDomain q (⟨liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (n+1) (productOpen U))) :
    IsInvDomain q (⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeals.MarkedIdeal n U) := by
  have hSrcN:=hM.isWellFormed.isClosedSubmanifold_N
  have hSrcI:=hM.isWellFormed.isCoherent
  have hPre : zeroSection U ⁻¹' liftedCarrier A=A := by
    ext x
    exact section_mem A x
  have hA : IsClosedSubmanifold n A := by
    refine ⟨?_,?_⟩
    · rw [←hPre]
      exact hSrcN.1.preimage (zeroSection_contMDiff U).continuous
    · intro x hx
      obtain ⟨k,hreg⟩:=hSrcN.2 (zeroSection U x) ((section_mem A x).mpr hx)
      exact ⟨k,(regularAtDim_actual_section_iff A x hx k).mp hreg⟩
  have hc:=isCoherent_pullback (zeroSection_contMDiff U) hSrcI
  refine ⟨⟨hA,hc,NormalCrossings.isSNCDivisor_nil,
    NormalCrossings.isTransverse_nil_of_isClosedSubmanifold hA⟩,?_,hM.one_le_d,?_⟩
  · intro x hx
    obtain ⟨k,hk,hreg⟩:=hM.dimLE (zeroSection U x) ((section_mem A x).mpr hx)
    exact ⟨k,hk,(regularAtDim_actual_section_iff A x hx k).mp hreg⟩
  · intro x hx
    obtain ⟨g,hg,hfreq⟩:=hM.isNonzeroAlongAt (zeroSection U x) ((section_mem A x).mpr hx)
    have hPull : (GermIdeal.pullback (m := n) (zeroSection U) J).mem x (g ∘ zeroSection U) :=
      GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self ⟨g,hg,rfl⟩
        ((GermIdeal.IsCoherent.holomorphicAt_mem hSrcI hg).comp_contMDiff
          (Eventually.of_forall fun _ => (zeroSection_contMDiff U).contMDiffAt)))
    refine ⟨g ∘ zeroSection U,hPull,?_⟩
    by_contra hn
    have hn':=not_frequently.mp hn
    apply hfreq
    have ht : Tendsto (projection U) (𝓝 (zeroSection U x)) (𝓝 x) := by
      simpa only [projection_section] using (projection_contMDiff U).continuous.tendsto (zeroSection U x)
    filter_upwards [ht.eventually hn'] with z hz
    rintro ⟨hzA,hzg⟩
    apply hz
    exact ⟨hzA.1,by simpa only [Function.comp_apply,section_projection z hzA] using hzg⟩

theorem actual_initial_family_values (q : ℕ) (hn : 0<n) (A : Set U)
    (J : GermIdeal (n+1) (productOpen U)) (d : ℕ)
    (hM : IsInvDomain q (⟨liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (n+1) (productOpen U)))
    (x : U) (hx : x∈cosupport n A (GermIdeal.pullback (m := n) (zeroSection U) J) d) :
    (invFamily (Nat.succ_pos n) q).inv (X := CMfd.of (n := n+1) (productOpen U))
      (⟨liftedCarrier A,[],J,d⟩ : MarkedIdeals.MarkedIdeal (n+1) (productOpen U)) .refl (zeroSection U x)=
    (invFamily hn q).inv (X := CMfd.of (n := n) U)
      (⟨A,[],GermIdeal.pullback (m := n) (zeroSection U) J,d⟩ : MarkedIdeals.MarkedIdeal n U) .refl x :=
  initial_section_all_indices q hn A J d hM (section_domain_of_original_source q A J d hM) x hx

end
end Hironaka.HironakaActualSectionInitialValues
