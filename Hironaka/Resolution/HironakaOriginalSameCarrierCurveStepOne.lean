/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalCurvePositiveEmptyWindow
/-! Genuine same-carrier candidate geometry and actual curve special leaves.
No global candidate TEST or canonical value locality is supplied. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalSameCarrierCurveStepOne
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen RelativePrincipalizationSpan
  HomogenizedIdealAlong HomogenizedIdealAlongTower StepOneValue StepOneValueMasked
  StepOneLowerDomain
  HironakaCoherentTransformExtension HironakaOriginalCurvePositiveEmptyWindow
  HironakaOriginalAnyTestCurveStepOneValue HironakaStageCenters CanonicalCentres
  CodimOneSupportAlong MemberInterLocusAlong
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual WHOLE coefficient record/coherence precedes original prefix,
level and SPECIAL open geometry, without a candidate TEST hypothesis. -/
theorem same_carrier_step_geometry_restrict (M J : MarkedIdeal n X)
    (hJ : J.IsWellFormed) (hd : 1≤J.d) (hN : J.N=M.N)
    (U : Opens X) (T : BlowupTower X Y) (hT : IsGeoTestTower M T) :
    (geoTransformAlong (barMarked (MarkedIdeal.pullback (Subtype.val : U → X) J)) (restrict U T)).cosupp=
      (Subtype.val : openPreimage T U → Y) ⁻¹' (geoTransformAlong (barMarked J) T).cosupp ∧
      ∀ p : openPreimage T U,
        level (MarkedIdeal.pullback (Subtype.val : U → X) J) (restrict U T) p=level J T p ∧
        (IsSpecial (MarkedIdeal.pullback (Subtype.val : U → X) J) (restrict U T) p ↔ IsSpecial J T p) := by
  have hB := isWellFormed_barMarked J hJ
  have hBN : (barMarked J).N=M.N := by simpa only [barMarked_N] using hN
  obtain ⟨_hNT,hcT⟩ := isClosedSubmanifold_and_isCoherent_geoTransformAlong_sameCarrier
    hB.isClosedSubmanifold_N hB.isCoherent hBN T hT
  have hg : geoTransformAlong (barMarked (MarkedIdeal.pullback (Subtype.val : U → X) J)) (restrict U T)=
      MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong (barMarked J) T) := by
    rw [show barMarked (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) J)=
      MarkedIdeal.pullback (Subtype.val : U → X) (barMarked J) from
      ContactStageKept.barMarked_pullback_val U hJ.isCoherent hJ.isClosedSubmanifold_N hd]
    exact geoTransformAlong_restrict_sameCarrier hB.isClosedSubmanifold_N hB.isCoherent hBN U T hT
  have hO : origMembers (MarkedIdeal.pullback (Subtype.val : U → X) J) (restrict U T)=
      (origMembers J T).map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·) := by
    unfold origMembers
    rw [hg]
    change ((geoTransformAlong (barMarked J) T).E.map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·)).take
      (J.E.map ((Subtype.val : U → X) ⁻¹' ·)).length=_
    rw [List.length_map,←List.map_take]
  have hc : (geoTransformAlong (barMarked (MarkedIdeal.pullback (Subtype.val : U → X) J)) (restrict U T)).cosupp=
      (Subtype.val : openPreimage T U → Y) ⁻¹' (geoTransformAlong (barMarked J) T).cosupp := by
    rw [hg]
    exact cosupp_pullback_val _ (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcT hg) _
  refine ⟨hc,fun p => ?_⟩
  have hl : level (MarkedIdeal.pullback (Subtype.val : U → X) J) (restrict U T) p=level J T p := by
    unfold level
    rw [hO]
    exact CodimOnePartCanonical.boundaryCount_map_preimage _ _ p
  refine ⟨hl,?_⟩
  have hcod := CodimOnePartCanonical.codimOnePartAlong_pullback_val (openPreimage T U)
    (𝔞 := (geoTransformAlong (barMarked J) T).ideal)
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcT hg)
    (N := (geoTransformAlong (barMarked J) T).N) (geoTransformAlong (barMarked J) T).d
  have hmem := memberInterLocus_preimage (Subtype.val : openPreimage T U → Y)
    (fun z => (openPreimage T U).isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq z)
    (geoTransformAlong (barMarked J) T).N (origMembers J T) (geoTransformAlong (barMarked J) T).cosupp
  unfold IsSpecial
  rw [hl,hO,hg]
  rw [←hc,hg] at hmem
  refine or_congr (and_congr_right fun _ => ?_) (and_congr_right fun _ => ?_)
  · rw [show codimOnePartAlong (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
        (geoTransformAlong (barMarked J) T)).N (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
        (geoTransformAlong (barMarked J) T)).ideal (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y)
        (geoTransformAlong (barMarked J) T)).d=_ from hcod]
    rfl
  · show p ∈ memberInterLocus ((Subtype.val : openPreimage T U → Y) ⁻¹' (geoTransformAlong (barMarked J) T).N)
      ((origMembers J T).map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·))
      (MarkedIdeal.pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong (barMarked J) T)).cosupp ↔ _
    rw [hmem]
    rfl

/-- Actual candidate coherence at every source prefix precedes both directions
of real cosupport transport; candidate admissibility is unnecessary. -/
theorem same_carrier_cosupport_off_boundary_iff (M J : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n J.N) (hI : J.ideal.IsCoherent) (hEq : J.N=M.N) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower M T → ∀ y : Y,
      y ∉ ⋃ H ∈ (geoTransformAlong M T).E,H →
      (y ∈ (geoTransformAlong J T).cosupp ↔ T.proj y ∈ J.cosupp)
  | _,.refl,_,_,_ => Iff.rfl
  | _,.step T C π hπ,ht,y,hy => by
    have hOff := notMem_boundary_geoTransform (geoTransformAlong M T) hy
    obtain ⟨hNT,hIT⟩ := isClosedSubmanifold_and_isCoherent_geoTransformAlong_sameCarrier hN hI hEq T ht.1
    exact (TransformOffCentre.mem_cosupp_geoTransform_iff (geoTransformAlong J T) hNT.1
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hIT hg) hπ hOff.1).trans
      (same_carrier_cosupport_off_boundary_iff M J hN hI hEq T ht.1 (π y) hOff.2)

/-- ONLY actual independent same-carrier curve data build a genuine local
candidate TEST before SPECIAL and the actual (zero,top) non-test Step One leaf. -/
theorem same_carrier_curve_step_one_off_boundary (hn : 0<n) (M J : MarkedIdeal n X)
    (hM : M.IsWellFormed) (hJ : IsInvDomain 1 J)
    (hmax : IsMaximalOrderAlong J.N J.ideal J.d) (hN : J.N=M.N) (hE : J.E=M.E)
    (T : BlowupTower X Y) (hT : IsGeoTestTower M T) (y : Y)
    (hy : T.proj y ∈ J.cosupp) (hyE : y ∉ ⋃ H ∈ (geoTransformAlong M T).E,H) :
    y ∈ (geoTransformAlong J T).cosupp ∧ IsSpecial J T y ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily hn 0) J T y=toLex (0,⊤) := by
  have hCurrent := (same_carrier_cosupport_off_boundary_iff M J hJ.isWellFormed.isClosedSubmanifold_N
    hJ.isWellFormed.isCoherent hN T hT y hyE).mpr hy
  have hB := isWellFormed_barMarked J hJ.isWellFormed
  have hBN : (barMarked J).N=M.N := by simpa only [barMarked_N] using hN
  have he := coeff_homAlong_wEquiv J hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d
  have hyBar : T.proj y ∈ (barMarked J).cosupp := by
    change T.proj y ∈ (geoTransformAlong (barMarked J) (.refl : BlowupTower X X)).cosupp
    rw [(he.2 .refl).2 trivial]
    exact hy
  have hBarCurrent := (same_carrier_cosupport_off_boundary_iff M (barMarked J) hB.isClosedSubmanifold_N
    hB.isCoherent hBN T hT y hyE).mpr hyBar
  obtain ⟨U,hyU,hEmpty⟩ := exists_actual_off_boundary_empty_window M hM.isSNCDivisor.1 T y hyE
  let p : openPreimage T U := ⟨y,hyU⟩
  have hJU := InvDomainTowerAlong.isInvDomain_pullback_val U hJ
  have hMaxU := (StepOneRestrictOpen.hypotheses_restrict J U hJ.isWellFormed hJ.one_le_d hmax hJ.dimLE).2.2.1
  have hTestU := ResolutionInvariantExt.isGeoTestTower_of_isEmptyTower
    (MarkedIdeal.pullback (Subtype.val : U → X) J) (restrict U T) hEmpty
  have hGeom := same_carrier_step_geometry_restrict M J hJ.isWellFormed hJ.one_le_d hN U T hT
  have hpBar : p ∈ (geoTransformAlong (barMarked (MarkedIdeal.pullback (Subtype.val : U → X) J)) (restrict U T)).cosupp := by
    rw [hGeom.1]
    exact hBarCurrent
  have heU := coeff_homAlong_wEquiv (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) J)
    hJU.isWellFormed.isClosedSubmanifold_N hJU.isWellFormed.isCoherent hJU.one_le_d
  have hBarU := (heU.2 (restrict U T)).1.mpr hTestU
  have hp : p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) J) (restrict U T)).cosupp := by
    rw [←(heU.2 (restrict U T)).2 hBarU]
    exact hpBar
  have hSpecialU := original_curve_step_one_special_of_test hn _ hJU hMaxU (restrict U T) hTestU p hp
  have hSpecial : IsSpecial J T y := (hGeom.2 p).2.mp hSpecialU
  have hEE : (geoTransformAlong (barMarked J) T).E=(geoTransformAlong M T).E :=
    geoTransformAlong_E_eq_of_E_eq (by simpa only [barMarked_E] using hE) T
  have hLevel : level J T y=0 := by
    unfold level BoundaryCount.boundaryCount
    apply Finset.card_eq_zero.mpr
    ext i
    constructor
    · intro hi
      have hPass := (Finset.mem_filter.mp hi).2
      have hMember : (origMembers J T).get i ∈ (geoTransformAlong (barMarked J) T).E :=
        List.mem_of_mem_take (List.get_mem _ i)
      rw [hEE] at hMember
      exact (hyE (mem_iUnion₂.mpr ⟨_,hMember,hPass⟩)).elim
    · intro hi
      simp at hi
  refine ⟨hCurrent,hSpecial,?_⟩
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_pos hSpecial,hLevel]

end
end Hironaka.HironakaOriginalSameCarrierCurveStepOne
