/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalAnyTestCurveStepOneValue
import Hironaka.Resolution.HironakaSharpActualCurveExceptionalResidualUnit
import Hironaka.Resolution.HironakaStageCenters
/-! Genuine whole-history empty windows at positive original curve order.
Actual boundary-image geometry and actual nonmonomial units precede the window. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalCurvePositiveEmptyWindow
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  NormalCrossings DivisorExponentAlong GermIdealOrder MonomialPartAlong
  RelativePrincipalizationSpan MarkedIdealBiholomorphism MonomialInvariant MonomialCaseAlong
  NonmonomialTransformAlong NonmonomialOrderLocal GeneralValue CanonicalCentres
  HironakaStageCenters RestrictEmptyTower HironakaLocalPrincipalization
  HironakaSharpActualCurveExceptionalResidualUnit
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem finite_boundary_closed (E : List (Set Y))
    (hE : ∀ H ∈ E,IsClosed H) : IsClosed (⋃ H ∈ E,H) := by
  induction E with
  | nil => simp
  | cons H E ih =>
    have he : (⋃ K ∈ H::E,K)=H ∪ ⋃ K ∈ E,K := by ext y;simp
    rw [he]
    exact (hE H (List.mem_cons_self)).union (ih (fun K hK => hE K (List.mem_cons_of_mem H hK)))

private theorem boundary_image_subset_step (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    T.proj '' (⋃ H ∈ (geoTransformAlong M T).E,H) ⊆
      (T.step C π hπ).proj '' (⋃ H ∈ (geoTransformAlong M (T.step C π hπ)).E,H) := by
  rintro _ ⟨y,hy,rfl⟩
  obtain ⟨z,hz⟩ := surjective_of_isBlowupAlong hπ y
  refine ⟨z,?_,?_⟩
  · exact preimage_boundary_subset_boundary_geoTransform (geoTransformAlong M T) (show π z ∈ _ from hz.symm ▸ hy)
  · change T.proj (π z)=T.proj y
    rw [hz]

private theorem centre_image_subset_step (M : MarkedIdeal n X) (T : BlowupTower X Y)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) :
    T.proj '' C ⊆ (T.step C π hπ).proj ''
      (⋃ H ∈ (geoTransformAlong M (T.step C π hπ)).E,H) := by
  rintro _ ⟨y,hy,rfl⟩
  obtain ⟨z,hz⟩ := surjective_of_isBlowupAlong hπ y
  refine ⟨z,?_,?_⟩
  · rw [geoTransformAlong_step,geoTransform_E]
    exact mem_iUnion₂.mpr ⟨π ⁻¹' C,List.mem_append_right _ (List.mem_singleton_self _),(show π z ∈ C from hz.symm ▸ hy)⟩
  · change T.proj (π z)=T.proj y
    rw [hz]

private theorem centresAvoid_of_disjoint_boundary_image (M : MarkedIdeal n X) (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      Disjoint (U : Set X) (T.proj '' (⋃ H ∈ (geoTransformAlong M T).E,H)) → CentresAvoid U T
  | _,.refl,_ => trivial
  | _,.step T C π hπ,hU => by
    refine ⟨centresAvoid_of_disjoint_boundary_image M U T (Set.disjoint_left.mpr ?_),
      Set.disjoint_left.mpr ?_⟩
    · intro x hxU hxB
      exact Set.disjoint_left.mp hU hxU (boundary_image_subset_step M T C π hπ hxB)
    · intro y hyC hyU
      exact Set.disjoint_left.mp hU hyU (centre_image_subset_step M T C π hπ ⟨y,hyC,rfl⟩)

/-- The true proper closed boundary image and actual singleton fibre give a
base window on which the SAME ENTIRE original tower has only empty centres. -/
theorem exists_actual_off_boundary_empty_window (M : MarkedIdeal n X)
    (hE : ∀ H ∈ M.E,IsClosed H) (T : BlowupTower X Y) (y : Y)
    (hy : y ∉ ⋃ H ∈ (geoTransformAlong M T).E,H) :
    ∃ U : Opens X,T.proj y ∈ U ∧ ResolutionInvariantExt.IsEmptyTower (restrict U T) := by
  have hF := finite_boundary_closed (geoTransformAlong M T).E
    (HironakaPrincipalization.isClosed_of_mem_E_geoTransformAlong M hE T)
  have hImage := (HironakaAdmissibleCalculus.isProperMap_of_isBlowupSequence T.isBlowupSequence).isClosedMap _ hF
  let U : Opens X := ⟨(T.proj '' (⋃ H ∈ (geoTransformAlong M T).E,H))ᶜ,hImage.isOpen_compl⟩
  have hyU : T.proj y ∈ U := by
    rintro ⟨z,hz,hEq⟩
    have hyExc : y ∉ exceptionalLocus n T.proj := fun he => hy (exceptionalLocus_subset_boundary M T he)
    have hzy := BlowupSequenceIsomorphismOff.eq_of_apply_eq_of_not_mem_exceptionalLocus
      T.isBlowupSequence hyExc hEq
    exact hy (hzy ▸ hz)
  refine ⟨U,hyU,(isEmptyTower_restrict_iff U T).mpr
    (centresAvoid_of_disjoint_boundary_image M U T ?_)⟩
  exact Set.disjoint_left.mpr fun _ hxU hxF => hxU hxF

private theorem unit_mem_regular_zero {N : Set Y} {x : Y}
    (hr : RegularAtDim (n := n) N x 0) {I : GermIdeal n Y} (hI : I.IsCoherent)
    (hnz : IsNonzeroAlongAt N I x) : I.mem x (1 : Y → ℂ) := by
  obtain ⟨U,hU,hxU,hsub⟩ := PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hr
  obtain ⟨g,hg,hfreq⟩ := hnz
  obtain ⟨z,⟨hzN,hzg⟩,hzU⟩ := (hfreq.and_eventually (hU.mem_nhds hxU)).exists
  have hzx : z=x := mem_singleton_iff.mp (hsub ⟨hzN,hzU⟩)
  have hgx : g x ≠ 0 := hzx ▸ hzg
  have hgh := GermIdeal.IsCoherent.holomorphicAt_mem hI hg
  apply HomogenizedIdeal.mem_of_isInSpanAt hI
  refine isInSpanAt_of_eq_mul hg (holomorphicAt_const 1) (holomorphicAt_inv hgh hgx) ?_
  filter_upwards [hgh.continuousAt.eventually_ne hgx] with z hz
  exact (inv_mul_cancel₀ hz).symm

/-- Real parts construct no-factor/nonzero data internally, BEFORE dimension
zero or one geometry supplies the actual unit and zero nonmonomial order. -/
theorem curve_domain_nonmonomial_unit_on_boundary (hn : 0<n) (M : MarkedIdeal n Y)
    (hM : IsInvDomain 1 M) (y : Y) (hy : y ∈ M.N) (hyE : y ∈ ⋃ H ∈ M.E,H) :
    (nmPart M).mem y (1 : Y → ℂ) ∧ nmOrd M y=0 := by
  obtain ⟨hc,_hcMono,_hnzMono,_hMono,hnd,hnz,_hFactor⟩ :=
    parts_hypotheses hn M hM.isWellFormed hM.isNonzeroAlongAt
  obtain ⟨j,hj,hr⟩ := hM.dimLE y hy
  have hUnit : (nmPart M).mem y (1 : Y → ℂ) := by
    by_cases hj0 : j=0
    · exact unit_mem_regular_zero (hj0 ▸ hr) hc (hnz y hy)
    · have hj1 : j=1 := by omega
      obtain ⟨H,hH,hyH⟩ := mem_iUnion₂.mp hyE
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hH
      exact actual_curve_no_factor_member_unit hn hM.isWellFormed.isSNCDivisor hM.isWellFormed.isTransverse
        hc (hj1 ▸ hr) i hyH (hnd y hy i hyH)
  refine ⟨hUnit,Nat.le_zero.mp (nmOrd_le_of_notMem ?_)⟩
  intro hOrder
  exact one_ne_zero ((vanishesToOrderOn_one_iff hy (holomorphicAt_const 1)).mp (hOrder.2 1 hUnit))

/-- The ACTUAL unchanged full original general invariant takes its literal
monomial branch on EVERY current boundary point of ANY original curve TEST. -/
theorem original_test_curve_boundary_full_monomial_value (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain 1 M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).N)
    (hyE : y ∈ ⋃ H ∈ (geoTransformAlong M T).E,H) :
    (invFamily hn 1).inv M T y=toLex (0,toLex (Sum.inl
      (gammaAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal
        (geoTransformAlong M T).E (geoTransformAlong M T).d y))) := by
  have hQ := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hZero := (curve_domain_nonmonomial_unit_on_boundary hn (geoTransformAlong M T) hQ y hy hyE).2
  exact genInv_of_nmOrd_eq_zero _ M T hZero

/-- ONLY original domain/ANY TEST/positive current order internally supplies
an actual base open and SAME ENTIRE empty original TEST with its true domain. -/
theorem exists_original_test_positive_curve_empty_window (hn : 0<n) (M : MarkedIdeal n X)
    (hM : IsInvDomain 1 M) (T : BlowupTower X Y) (hT : IsGeoTestTower M T)
    (y : Y) (hy : y ∈ (geoTransformAlong M T).cosupp) (hpos : 0<nmOrd (geoTransformAlong M T) y) :
    ∃ U : Opens X,T.proj y ∈ U ∧ ResolutionInvariantExt.IsEmptyTower (restrict U T) ∧
      IsInvDomain 1 (MarkedIdeal.pullback (Subtype.val : U → X) M) ∧
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) (restrict U T) := by
  have hQ := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM T hT
  have hyE : y ∉ ⋃ H ∈ (geoTransformAlong M T).E,H := by
    intro h
    have hz := (curve_domain_nonmonomial_unit_on_boundary hn (geoTransformAlong M T) hQ y hy.1 h).2
    omega
  obtain ⟨U,hyU,hEmpty⟩ := exists_actual_off_boundary_empty_window M hM.isWellFormed.isSNCDivisor.1 T y hyE
  exact ⟨U,hyU,hEmpty,InvDomainTowerAlong.isInvDomain_pullback_val U hM,
    MarkedIdealRestrictOpen.isGeoTestTower_restrict U hM.isWellFormed.isClosedSubmanifold_N
      hM.isWellFormed.isCoherent T hT⟩

end
end Hironaka.HironakaOriginalCurvePositiveEmptyWindow
