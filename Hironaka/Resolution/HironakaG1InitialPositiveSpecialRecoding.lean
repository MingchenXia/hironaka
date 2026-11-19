import Hironaka.Resolution.HironakaG1InitialSelectedNormalOrder
import Hironaka.Invariant.StepOneRestrictOpen

/-! # The special branch of the first normal contact inside a positive cut -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialPositiveSpecialRecoding

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec HomogenizedIdealAlong GermIdealOrder RelativePrincipalizationSpan
  TangentDirectionAlong CodimOneSupport CodimOneSupportAlong CodimOnePartCanonical CodimOnePartTowerAlong
  BoundaryCount InvDomainMemberRestriction InvDomainRebase MemberInterLocusAlong
  StepOneValue StepOneValueMasked StepOneLowerDomain StepOneRestrictOpen
  MarkedIdealBiholomorphism HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaActualRelativeNormalGeometry HironakaActualOpenZeroSectionDifferentials
  HironakaActualSectionBoundaryGeometry HironakaG1InitialSelectedNormalOrder
  HironakaCoherentTransformExtension

/-- A point of the cosupport is in its codimension-one part precisely
when the cosupport fills the germ of a genuine tangent contact there. -/
theorem codimOnePartAlong_iff_contact_saturated {n : ℕ} {X : CMfd.{0} n}
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hd : 1 ≤ M.d)
    {U : Set X} {u : X → ℂ} (hu : IsTangentDirectionAlong M.N M.ideal M.d U u)
    {x : X} (hx : x ∈ M.cosupp) (hxU : x ∈ U) :
    x ∈ codimOnePartAlong M.N M.ideal M.d ↔
      ∀ᶠ y in 𝓝 x, y ∈ M.N ∩ {z | u z = 0} ∩ U → y ∈ M.cosupp := by
  have hHol : ∀ y g, M.ideal.mem y g → HolomorphicAt n g y := fun _ _ hg =>
    GermIdeal.IsCoherent.holomorphicAt_mem hM.isCoherent hg
  constructor
  · intro hSpecial
    filter_upwards [eventually_mem_codimOnePartAlong_iff_eq_zero hM.isCoherent
      hM.isClosedSubmanifold_N hd hu hxU hSpecial] with y hy hyContact
    exact codimOnePartAlong_subset (hy.mpr hyContact.1)
  · intro hSat
    have hxZero := hu.cosupport_inter_subset hHol hd ⟨hx, hxU⟩
    obtain ⟨k, hN, hContact⟩ := CodimOnePartTowerAlong.IsTangentDirectionAlong.exists_regularAtDim_succ
      hHol hM.isClosedSubmanifold_N hu ⟨⟨hx.1, hxZero⟩, hxU⟩
    refine ⟨k, hN, regularAtDim_of_eventually_mem_iff ?_ hContact⟩
    filter_upwards [hSat, hu.isOpen.mem_nhds hxU] with y hy hyU
    exact ⟨hy, fun hyCos => ⟨⟨hyCos.1, hu.cosupport_inter_subset hHol hd ⟨hyCos, hyU⟩⟩, hyU⟩⟩

set_option maxHeartbeats 1200000 in
/-- At an initial positive anchor, the original section is special
exactly when the padded selected record enters the level-zero special
branch. The comparison uses the actual whole initial coefficient cut. -/
theorem initial_selected_special_iff_section_special {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hp : p ∈ (properNormalMarked Q).cosupp)
    (hLevel : level (properNormalMarked Q) (BlowupTower.refl
      (X := CMfd.of (n := n + 1) (productOpen U))) p = s + 1) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let H := BlowupTower.refl (X := X)
    let B := barMarked (X := X) (properNormalMarked Q)
    let L := memberRestrict B (membersThrough B.E B.E p)
    IsInvDomain k L ∧ level L H p = 0 ∧
      (IsSpecial L H p ↔ IsSpecial (sectionMarked Q) H p) := by
  classical
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let H := BlowupTower.refl (X := X)
  let B := barMarked (X := X) P
  let A := barMarked (X := X) Sec
  let L := memberRestrict B (membersThrough B.E B.E p)
  let D := {z : X | ∀ F ∈ B.E, p ∈ F → z ∈ F}
  have hOldP : origMembers P H = B.E := List.take_length
  have hOldSec : origMembers Sec H = B.E := List.take_length
  have hCount : boundaryCount B.E p = s + 1 := by
    change boundaryCount (origMembers P H) p = s + 1 at hLevel
    rwa [hOldP] at hLevel
  have hLevSec : level Sec H p = s + 1 := by
    change boundaryCount (origMembers Sec H) p = s + 1
    rw [hOldSec, hCount]
  have hP := properNormalMarked_isInvDomain Q hQ
  have hSec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hB := isInvDomain_barMarked (X := X) P hP
  obtain ⟨hL, _, _, hTangent, _⟩ := initial_selected_normal_data Q hQ p
    (show 0 < boundaryCount B.E p from hCount ▸ Nat.succ_pos s)
  have hBp : B.cosupp = P.cosupp := cosupp_barMarked (X := X) P hP.isWellFormed hP.one_le_d
  have hAs : A.cosupp = Sec.cosupp := cosupp_barMarked (X := X) Sec hSec.isWellFormed hSec.one_le_d
  have hBCos : B.cosupp = A.cosupp :=
    hBp.trans ((properNormalMarked_locWPEquiv_section Q hQ).cosupp_eq_base.trans hAs.symm)
  have hCosL : L.cosupp = A.cosupp ∩ D := by
    rw [show L.cosupp = B.cosupp ∩ memberInter B.E (membersThrough B.E B.E p) from
      cosupp_memberRestrict hB.isWellFormed hB.one_le_d _, memberInter_membersThrough (fun _ h => h), hBCos]
  have hpA : p ∈ A.cosupp := hBCos ▸ hBp.symm ▸ hp
  have hpL : p ∈ L.cosupp := hCosL.symm ▸ ⟨hpA, fun _ _ h => h⟩
  have hCarrier : L.N ∩ {z | relativeNormalCoordinate U z = 0} = A.N ∩ D := by
    have hLRaw : L.N = P.N ∩ D := by
      change B.N ∩ memberInter B.E (membersThrough B.E B.E p) = P.N ∩ D
      rw [memberInter_membersThrough (fun _ h => h)]
      rfl
    rw [hLRaw, show A.N = liftedCarrier Q.N from rfl, ← normal_contact_carrier Q]
    ext z
    exact ⟨fun hz => ⟨⟨hz.1.1, hz.2⟩, hz.1.2⟩, fun hz => ⟨⟨hz.1.1, hz.2⟩, hz.1.2⟩⟩
  have hZero : level L H p = 0 := by
    have hOld : origMembers L H = L.E := List.take_length
    unfold level
    rw [hOld]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _ hi
    let F := L.E.get i
    have hMem : F ∈ L.E := List.get_mem _ i
    rw [show L.E = B.E.filter (fun D => decide ¬(D ∈ B.E ∧ p ∈ D)) from
      memberRestrict_membersThrough_E B B.E p] at hMem
    obtain ⟨hE, hnE⟩ := List.mem_filter.mp hMem
    exact (of_decide_eq_true hnE) ⟨hE, hi⟩
  have hBarCodim : codimOnePartAlong (barMarked L).N (barMarked L).ideal (barMarked L).d =
      codimOnePartAlong L.N L.ideal L.d :=
    codimOnePartAlong_congr rfl (cosupp_barMarked (X := X) L hL.isWellFormed hL.one_le_d)
  have hCut := codimOnePartAlong_iff_contact_saturated L hL.isWellFormed hL.one_le_d
    hTangent hpL (mem_univ p)
  have hCompare : p ∈ codimOnePartAlong L.N L.ideal L.d ↔
      p ∈ memberInterLocus A.N B.E A.cosupp := by
    rw [hCut, mem_memberInterLocus_iff]
    rw [inter_univ, hCarrier, hCosL]
    refine ⟨fun h => ⟨hpA, ?_⟩, fun h => ?_⟩
    · filter_upwards [h] with z hz hzA hzD
      exact (hz ⟨hzA, hzD⟩).1
    · filter_upwards [h.2] with z hz hzAD
      exact ⟨hz hzAD.1 hzAD.2, hzAD.2⟩
  refine ⟨hL, hZero, ?_⟩
  constructor
  · rintro (⟨_, hSpecial⟩ | ⟨hPos, _⟩)
    · change p ∈ codimOnePartAlong (barMarked L).N (barMarked L).ideal (barMarked L).d at hSpecial
      rw [hBarCodim] at hSpecial
      have hm := hCompare.mp hSpecial
      refine Or.inr ⟨hLevSec ▸ Nat.succ_pos s, ?_⟩
      change p ∈ memberInterLocus A.N (origMembers Sec H) A.cosupp
      rw [hOldSec]
      exact hm
    · change 1 ≤ level L H p at hPos
      omega
  · rintro (⟨hNone, _⟩ | ⟨_, hSpecial⟩)
    · change level Sec H p = 0 at hNone
      omega
    · have hm : p ∈ memberInterLocus A.N B.E A.cosupp := by
        change p ∈ memberInterLocus A.N (origMembers Sec H) A.cosupp at hSpecial
        rwa [hOldSec] at hSpecial
      refine Or.inl ⟨hZero, ?_⟩
      change p ∈ codimOnePartAlong (barMarked L).N (barMarked L).ideal (barMarked L).d
      rw [hBarCodim]
      exact hCompare.mpr hm

set_option maxHeartbeats 1200000 in
/-- On the actual initial padded mask the selected record has level zero
at the anchor. Its next special branch reads exactly the section's
positive special branch at the preceding level. -/
theorem original_initial_masked_positive_special_iff {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hp : p ∈ (properNormalMarked Q).cosupp)
    (hLevel : level (properNormalMarked Q) (BlowupTower.refl
      (X := CMfd.of (n := n + 1) (productOpen U))) p = s + 1) :
    let P := properNormalMarked Q
    let H := BlowupTower.refl (X := CMfd.of (n := n + 1) (productOpen U))
    let O := maskA P H p
    let L := lowerMarkedM P (s + 1) H p
    let K := BlowupTower.refl (X := CMfd.of (n := n + 1) O)
    ∀ z : O, z.val = p → level L K z = 0 ∧
      (IsSpecial L K z ↔ IsSpecial (sectionMarked Q) H p) := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let H := BlowupTower.refl (X := X)
  let B := barMarked (X := X) P
  let O := maskA P H p
  let L := memberRestrict B (membersThrough B.E B.E p)
  let M := lowerMarkedM P (s + 1) H p
  let K := BlowupTower.refl (X := CMfd.of (n := n + 1) O)
  have hOld : origMembers P H = B.E := List.take_length
  have hM : M = MarkedIdeal.pullback (Subtype.val : O → X) L := by
    change MarkedIdeal.pullback (Subtype.val : O → X)
      (memberRestrict B (membersThrough B.E (origMembers P H) p)) = _
    rw [hOld]
  obtain ⟨hL, hZero, hSpecial⟩ := initial_selected_special_iff_section_special Q hQ p hp hLevel
  change ∀ z : O, z.val = p → level M K z = 0 ∧
    (IsSpecial M K z ↔ IsSpecial (sectionMarked Q) H p)
  rw [hM]
  intro z hz
  have hTest : IsGeoTestTower (barMarked L) H := trivial
  have hOpen := (restrict_facts L O hL.isWellFormed hL.one_le_d H hTest).2.2 z
  have hLevelOpen : level (MarkedIdeal.pullback (Subtype.val : O → X) L) K z = level L H z.val := hOpen.1
  have hSpecialOpen : IsSpecial (MarkedIdeal.pullback (Subtype.val : O → X) L) K z ↔
      IsSpecial L H z.val := hOpen.2.1
  rw [hz] at hLevelOpen hSpecialOpen
  exact ⟨hLevelOpen.trans hZero, hSpecialOpen.trans hSpecial⟩

end
end Hironaka.HironakaG1InitialPositiveSpecialRecoding
