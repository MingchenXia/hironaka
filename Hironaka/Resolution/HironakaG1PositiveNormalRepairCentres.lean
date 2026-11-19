import Hironaka.Resolution.HironakaG1PositiveNormalSpecialStep

/-!
# The padded lower centre of the actual positive special repair

The surviving cosupport projects exactly onto the complement of the repair
centre in the padded lower cosupport. Canonicality can therefore be tested
from the original lower value at the anchor, on the repair centre and on
the projections of the actual surviving points.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalRepairCentres

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealRestrictOpen ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  StepOneValue StepOneValueMasked StepOneLowerDomain InvDomainMemberRestriction
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaActualNativeSectionFiniteHistory
  HironakaActualNativeSectionInitialBar HironakaDisjointNativeOpenLift
  HironakaActualSectionBoundaryGeometry HironakaActualOpenZeroSectionDifferentials
  HironakaG1PositiveNormalSpecialStep HironakaG8HomStable MemberInterLocusAlong BoundaryCount
  RelativePrincipalizationSpan
open HomogenizedGlueingTower (strictAlong)

/-- Canonicality and value invariance for a repair on its surviving cosupport. -/
structure RepairCentreComparison {d : ℕ} (k : ℕ) (hd : 0 < d) {X Z : CMfd.{0} d}
    (L : MarkedIdeal d X) (D : Set X) (a : X) (π : Z → X) (hπ : IsBlowupAlong d D π) : Prop where
  cosupport_preimage : (L.geoTransform D π).cosupp = π ⁻¹' (L.cosupp \ D)
  cosupport_image : π '' (L.geoTransform D π).cosupp = L.cosupp \ D
  canonical_iff :
    let R := invFamily hd k
    let f := R.inv L (.refl : BlowupTower X X)
    IsCanonical L (R.inv L) (.step .refl D π hπ) ↔
      (∀ x ∈ D, f x = f a) ∧ ∀ z ∈ (L.geoTransform D π).cosupp, f (π z) < f a
  value_eq :
    let R := invFamily hd k
    let f := R.inv L (.refl : BlowupTower X X)
    (∀ x ∈ D, f x = f a) →
      (∀ z ∈ (L.geoTransform D π).cosupp, f (π z) < f a) →
      ∀ z ∈ (L.geoTransform D π).cosupp, R.inv L (.step .refl D π hπ) z = f (π z)

/-- An admissible nonempty repair whose transformed cosupport avoids its
exceptional inverse image has the stated canonicality and off-centre comparison. -/
theorem repair_centre_criterion {d k : ℕ} (hd : 0 < d) {X Z : CMfd.{0} d}
    (L : MarkedIdeal d X) (hDom : IsInvDomain k L) {D : Set X} (hAdm : L.IsAdmissibleCentre D)
    (a : X) (haD : a ∈ D) (π : Z → X) (hπ : IsBlowupAlong d D π)
    (hAvoid : (L.geoTransform D π).cosupp ⊆ π ⁻¹' Dᶜ) :
    RepairCentreComparison k hd L D a π hπ := by
  let F := invFamily hd k
  let f := F.inv L (.refl : BlowupTower X X)
  let S := (L.geoTransform D π).cosupp
  have hL := hDom.isWellFormed
  have hPre : S = π ⁻¹' (L.cosupp \ D) := by
    have hDiff := TransformOffCentre.cosupp_geoTransform_diff_preimage L
      hL.isClosedSubmanifold_N.1
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hL.isCoherent hg) hπ
    change S \ π ⁻¹' D = _ at hDiff
    have hDisjoint : Disjoint S (π ⁻¹' D) := disjoint_left.mpr fun z hz hzD => hAvoid hz hzD
    rw [sdiff_eq_left.mpr hDisjoint] at hDiff
    exact hDiff
  have hImage : π '' S = L.cosupp \ D := by
    rw [hPre, (HironakaLocalPrincipalization.surjective_of_isBlowupAlong hπ).image_preimage]
  have hCriterion : D = maxLocus f L.cosupp ↔
      (∀ x ∈ D, f x = f a) ∧ ∀ z ∈ S, f (π z) < f a := by
    constructor
    · intro hMax
      have hqMax : a ∈ maxLocus f L.cosupp := hMax ▸ haD
      refine ⟨fun x hx => ?_, fun z hz => ?_⟩
      · have hxMax : x ∈ maxLocus f L.cosupp := hMax ▸ hx
        exact le_antisymm (hqMax.2 x hxMax.1) (hxMax.2 a hqMax.1)
      · have hzDiff : π z ∈ L.cosupp \ D := hImage ▸ mem_image_of_mem π hz
        refine lt_of_le_of_ne (hqMax.2 _ hzDiff.1) (fun hEq => hzDiff.2 ?_)
        rw [hMax]
        exact ⟨hzDiff.1, fun y hy => hEq.symm ▸ hqMax.2 y hy⟩
    · rintro ⟨hCentre, hOff⟩
      have hLe (y : X) (hy : y ∈ L.cosupp) : f y ≤ f a := by
        by_cases hyD : y ∈ D
        · exact (hCentre y hyD).le
        · obtain ⟨z, hz, rfl⟩ : y ∈ π '' S := hImage.symm ▸ (show y ∈ L.cosupp \ D from ⟨hy, hyD⟩)
          exact (hOff z hz).le
      ext x
      constructor
      · intro hx
        exact ⟨hAdm.2.1 hx, fun y hy => (hLe y hy).trans_eq (hCentre x hx).symm⟩
      · intro hx
        by_contra hxD
        obtain ⟨z, hz, rfl⟩ : x ∈ π '' S :=
          hImage.symm ▸ (show x ∈ L.cosupp \ D from ⟨hx.1, hxD⟩)
        exact (not_lt_of_ge (hx.2 a (hAdm.2.1 haD))) (hOff z hz)
  refine ⟨hPre, hImage, ?_, ?_⟩
  · change (True ∧ (D = ∅ ∨ D = maxLocus f L.cosupp)) ↔ _
    have hNonempty : D.Nonempty := ⟨a, haD⟩
    simpa only [true_and, nonempty_iff_ne_empty.mp hNonempty, false_or] using hCriterion
  · change (∀ x ∈ D, f x = f a) → (∀ z ∈ S, f (π z) < f a) → _
    intro hCentre hOff z hz
    exact ((F.isInvValue.decrease L hDom .refl D π hπ trivial ⟨a, haD⟩
      (hCriterion.mpr ⟨hCentre, hOff⟩) z hz).2) (hAvoid hz)

set_option backward.isDefEq.respectTransparency false in
/-- The actual padded positive lower cut at the head has invariant bound `k`. -/
theorem padded_lower_isInvDomain {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (H : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hLevel : level (properNormalMarked Q) H p = s + 1) :
    IsInvDomain k (lowerMarkedM (properNormalMarked Q) (s + 1) H p) := by
  let X := CMfd.of (n := n+1) (productOpen U)
  let P := properNormalMarked Q
  have hP := properNormalMarked_isInvDomain Q hQ
  have hBarTest := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  rw [lowerMarkedM_succ]
  simpa only [Nat.add_sub_cancel] using
    (isInvDomain_lowerMarked_succ (X := X) P hP.isWellFormed hP.one_le_d
      (Nat.succ_pos n) H hBarTest hP.dimLE hLevel)

set_option maxHeartbeats 250000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual repair has an admissible image centre through the anchor and
its entire transformed padded lower cosupport lies over the complement. -/
theorem positive_normal_repair_geometry {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hLevel : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) H p)
    (hSpecial : IsSpecial (sectionMarked Q) H p) :
    let O := maskA (properNormalMarked Q) H p
    let W := openSection (strictAlong H (zeroPlane U)) O
    let M := MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong (barMarked (sectionMarked Q)) H)
    let L := lowerMarkedM (properNormalMarked Q) (s + 1) H p
    ∃ (D : Set O) (a : O) (Z : CMfd.{0} (n + 1)) (π : Z → O),
      IsBlowupAlong (n + 1) D π ∧ a.val = p ∧ a ∈ D ∧ L.IsAdmissibleCentre D ∧
        (L.geoTransform D π).cosupp ⊆ π ⁻¹' Dᶜ ∧
        ∃ (hW : ∀ z ∈ W, RegularAtDim (n := n + 1) W z n),
          let A := nativePullback (Nat.le_succ n) W hW M
          let E := ((origMembers (sectionMarked Q) H).map ((Subtype.val : O → Y) ⁻¹' ·)).map
            ((Subtype.val : W → O) ⁻¹' ·)
          D = (Subtype.val : W → O) ''
            (memberInterLocus A.N E A.cosupp ∩ {z | boundaryCount E z = s + 1}) := by
  let O := maskA (properNormalMarked Q) H p
  let W := openSection (strictAlong H (zeroPlane U)) O
  let M := MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong (barMarked (sectionMarked Q)) H)
  obtain ⟨_, hW, q, hqp, hqC, hRepair⟩ :=
    positive_normal_native_special_step Q hQ H hH p hLevel hNS hSpecial
  have hAdm := hRepair.2.2.1
  obtain ⟨Z, π, hπ, hEndpoint⟩ := hRepair.2.2.2.2.2
  have hAvoid := hEndpoint.2.2.2.2.2.2.2.2.2.1
  let A := nativePullback (Nat.le_succ n) W hW M
  let E := ((origMembers (sectionMarked Q) H).map ((Subtype.val : O → Y) ⁻¹' ·)).map
    ((Subtype.val : W → O) ⁻¹' ·)
  let C := memberInterLocus A.N E A.cosupp ∩ {z | boundaryCount E z = s + 1}
  let D := (Subtype.val : W → O) '' C
  exact ⟨D, q.val, Z, π, hπ, hqp, mem_image_of_mem _ hqC, hAdm, hAvoid, hW, rfl⟩

end

end Hironaka.HironakaG1PositiveNormalRepairCentres
