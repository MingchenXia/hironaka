/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualInitialFullCompatibility
import Hironaka.Resolution.HironakaSharpActualCurveFirstDefectErasure
import Hironaka.Resolution.HironakaAdmissibleCalculus

/-! Finite genuine ORIGINAL deep-product histories bound the literal actual
chronological order, preserve the entire original good locus, and erase FIRST
for at most one original member. General sharp terminal resolution, full
recursive intersection decrease and original-plus-born joint SNC remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFiniteDeepPhase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualOriginalControlledHistory
  HironakaSharpActualCurveFirstDefectErasure HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalRestrictedDistinctDefectCentre HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpOriginalProductTraceOrder RelativePrincipalizationSpan DivisorExponentAlong
  GermIdealOrder NormalCrossings RestrictedIdealWeight MarkedIdealOperationsAlong
  HironakaCoherentTransformExtension RestrictEmptyTower MonomialPartAlong InvertibleIdealQuotient
  HironakaAdmissibleSequence HironakaAdmissibleCalculus CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem centresOver_mono {F G : Set X} (hFG : F ⊆ G) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),CentresOver F T → CentresOver G T
  | _, .refl, _ => trivial
  | _, .step T _C _π _hπ, hT => ⟨centresOver_mono hFG T hT.1,fun _ hy => hFG (hT.2 hy)⟩

/-- A genuine ORIGINAL terminal marked resolution bounds the ACTUAL entire
chronological product order, without a current-reflexive invariant rebase. -/
theorem terminal_original_marking_bounds_actual_product (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {q : ℕ} (_hq : 1 ≤ q)
    (T : BlowupTower X Y) (hT : IsGeoResolution (originalMemberProductMarked W E q) T) :
    ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) y < q := by
  let M := originalMemberProductMarked W E q
  have hw : M.IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,
      isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwQ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT.1
  have hGeom := actual_original_test_history_template M hw T hT.1
  have hN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
  have hResidual := (original_product_controlled_history_residual_dictionary hn hW hE hdense q T hT.1).1
  obtain ⟨hc,hnz,_⟩ := original_chronological_full_product_actual_geometry hn hW hE hdense T hGeom
  have hwTemp : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,
      isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwTempQ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwTemp T hGeom
  intro y hy
  apply Nat.lt_of_not_ge
  intro hord
  have hyP := (ordinaryTraceOrder_cosupport_iff hwTempQ.isClosedSubmanifold_N hc hnz hy q).mpr hord
  have hle : RestrictLe (geoTransformAlong M T).N (geoTransformAlong M T).ideal
      (nonmonomialPartAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal
        (geoTransformAlong M T).E) := by
    intro x _ f hf
    exact IsInSpanAt.restrict (isInSpanAt_self
      (NonmonomialTransformAlong.le_nonmonomialPartAlong_self hwQ.isCoherent x f hf)
      (RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwQ.isCoherent hf))
  have hyResidual : y ∈ cosupport n (geoTransformAlong M T).N
      (nonmonomialPartAlong n (geoTransformAlong M T).N (geoTransformAlong M T).ideal
        (geoTransformAlong M T).E) q := by
    rw [hResidual,hN]
    exact hyP
  have hyQ := cosupport_subset_of_restrictLe hle q hyResidual
  have hdQ : (geoTransformAlong M T).d = q := d_geoTransformAlong M T
  change y ∈ cosupport n (geoTransformAlong M T).N (geoTransformAlong M T).ideal q at hyQ
  rw [←hdQ] at hyQ
  change y ∈ (geoTransformAlong M T).cosupp at hyQ
  rw [hT.2] at hyQ
  exact hyQ

/-- Original compact deep cosupport constructs a finite actual chronological
phase, with EVERY centre over original sharp bad and entire good preserved. -/
theorem exists_actual_finite_deep_phase (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {d : ℕ} (hd : d ≤ n)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x d)
    (hK : IsCompact (originalMemberProductMarked W E (E.length+1)).cosupp) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsCanonical (originalMemberProductMarked W E (E.length+1))
        ((canonicalInvariant n).inv (originalMemberProductMarked W E (E.length+1))) T ∧
      IsGeoResolution (originalMemberProductMarked W E (E.length+1)) T ∧
      IsGeoTestTower (geometricTemplate W []) T ∧
      CentresOver (originalSharpBadLocus (n := n) W E) T ∧
      IsProperMap T.proj ∧ IsIsomorphismOver n T.proj (originalGoodLocus (n := n) W E) ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) y ≤ E.length) ∧
      IsClosedSubmanifold n (geoTransformAlong (geometricTemplate W []) T).N ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate W []) T).E ∧
      IsTransverse n (geoTransformAlong (geometricTemplate W []) T).N
        (geoTransformAlong (geometricTemplate W []) T).E := by
  let M := originalMemberProductMarked W E (E.length+1)
  have hdom := originalMemberProductMarked_isInvDomain hn hW hE hd hr hdense
    (q := E.length+1) (Nat.succ_le_succ (Nat.zero_le _))
  obtain ⟨Y,T,hcan,hres⟩ := exists_isGeoResolution_isCanonical_of_isCompact (canonicalInvariant n) hdom hK
  have hGeom := actual_original_test_history_template M hdom.isWellFormed T hres.1
  have hdeep : M.cosupp ⊆ originalSharpBadLocus (n := n) W E :=
    (originalDeepProduct_cosupp_subset_distinctDefectPhase hn hW hE hdense).trans
      (originalDistinctDefectPhase_subset_sharpBad hn hW hE hdense)
  have hOver := centresOver_cosupp M hW hdom.isWellFormed.isCoherent T hres.1
  have hAdm := (isAdmissibleBlowupSequence_proj M M.cosupp T hres.1 hOver).mono hdeep
  have hOverBad : CentresOver (originalSharpBadLocus (n := n) W E) T :=
    centresOver_mono hdeep T hOver
  have hIso := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hAdm
  rw [originalSharpBadLocus_eq_compl_good,compl_compl] at hIso
  have hwTemp : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,
      isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwTempQ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwTemp T hGeom
  refine ⟨Y,T,hcan,hres,hGeom,hOverBad,isProperMap_of_isBlowupSequence T.isBlowupSequence,hIso,
    ?_,hwTempQ.isClosedSubmanifold_N,hwTempQ.isSNCDivisor,hwTempQ.isTransverse⟩
  intro y hy
  have hlt := terminal_original_marking_bounds_actual_product hn hW hE hdense
    (show 1 ≤ E.length+1 by omega) T hres y hy
  omega

/-- The whole actual small-order quotient dictionary erases literal FIRST
along every terminal original deep-phase history for at most one member. -/
theorem deep_phase_erases_first_defect_of_length_le_one (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hlen : E.length ≤ 1)
    (T : BlowupTower X Y) (hT : IsGeoResolution (originalMemberProductMarked W E (E.length+1)) T) :
    chronologicalDistinctDefect W E T = ∅ := by
  let M := originalMemberProductMarked W E (E.length+1)
  have hw : M.IsWellFormed :=
    ⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,
      isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hGeom := actual_original_test_history_template M hw T hT.1
  have hwTemp : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,
      isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwQ := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hwTemp T hGeom
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hfam : ∀ i : Fin E.length,(F i).IsCoherent ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
        IsNonzeroAlongAt (geoTransformAlong (geometricTemplate W []) T).N (F i) y) ∧
      ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ a,(F i).mem y a ↔ HolomorphicAt n a y ∧
          IsInSpanOnAt (n := n) (geoTransformAlong (geometricTemplate W []) T).N (·=f) y a := by
    intro i
    obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense i T hGeom
    rw [hNi] at hnzi hpri
    exact ⟨hwi.isCoherent,hnzi,hpri⟩
  apply eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hlt := terminal_original_marking_bounds_actual_product hn hW hE hdense
    (show 1 ≤ E.length+1 by omega) T hT y hy.1
  have hle : ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (relativeIdealListProduct (geoTransformAlong (geometricTemplate W []) T).N (List.ofFn F)) y ≤ 1 := by
    rw [←chronological_product_eq_actual_family_product W E T]
    omega
  exact (actual_product_order_le_one_count_dictionary hwQ.isClosedSubmanifold_N
    (fun i => (hfam i).1) (fun i => (hfam i).2.1) (fun i => (hfam i).2.2) hy.1 hle).2.2 hy

/-- The original finite canonical driver, actual residual comparison and true
quotient-image counts together produce a good-preserving FIRST-erasing history. -/
theorem exists_actual_finite_one_member_first_erasure (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {d : ℕ} (hd : d ≤ n)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x d) (hlen : E.length ≤ 1)
    (hK : IsCompact (originalMemberProductMarked W E (E.length+1)).cosupp) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoResolution (originalMemberProductMarked W E (E.length+1)) T ∧
      CentresOver (originalSharpBadLocus (n := n) W E) T ∧
      IsProperMap T.proj ∧ IsIsomorphismOver n T.proj (originalGoodLocus (n := n) W E) ∧
      chronologicalDistinctDefect W E T = ∅ := by
  obtain ⟨Y,T,_hcan,hres,_hGeom,hOver,hproper,hIso,_⟩ :=
    exists_actual_finite_deep_phase hn hW hE hdense hd hr hK
  exact ⟨Y,T,hres,hOver,hproper,hIso,
    deep_phase_erases_first_defect_of_length_le_one hn hW hE hdense hlen T hres⟩

end
end Hironaka.HironakaSharpActualFiniteDeepPhase
