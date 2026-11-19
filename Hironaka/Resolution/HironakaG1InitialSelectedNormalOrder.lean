import Hironaka.Resolution.HironakaG1ProperNormalInitialRegime
import Hironaka.Resolution.HironakaMonomialBlowup

/-! # The actual normal order of an initial positive selected record -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialSelectedNormalOrder

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec HomogenizedIdealAlong IdealWeightPowers DerivativeIdealAlong
  GermIdealOrder RelativePrincipalizationSpan CompanionReduction DivisorExponentAlong
  TangentDirectionAlong BoundaryCount InvDomainMemberRestriction InvDomainRebase
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalInitialRegime
  HironakaActualOpenZeroSectionDifferentials HironakaActualWeightedNormalPadding HironakaActualRelativeNormalGeometry
  HironakaCoherentTransformExtension HironakaMonomialBlowup
  StepOneValue NonmonomialOrderLocal MonomialPartAlong RestrictedIdealExtension
  RestrictLeCalculus CompanionRebase CompanionReductionAlong NonmonomialOrderTail
  MarkedIdealEquivalence MarkedIdealEquivalence.MarkedIdeal MarkedIdealRestrictOpen
  MarkedIdealBiholomorphism MarkedIdealOperationsAlong MarkedIdealOperationsAlong.MarkedIdeal
  InvDomainTowerAlong InvDomainCompanion

private theorem normal_power_nonzero_on_cylinder {n : ℕ} {U : Opens (ComplexModel n)}
    (A : Set U) (J : GermIdeal (n + 1) (productOpen U)) (d : ℕ)
    (hp : ∀ x, J.mem x (fun z => relativeNormalCoordinate U z ^ d))
    (x : productOpen U) (hx : x ∈ projection U ⁻¹' A) :
    IsNonzeroAlongAt (projection U ⁻¹' A) J x := by
  refine ⟨_, hp x, ?_⟩
  by_contra! h
  have hVan : (vanishingIdeal (n := n + 1) (projection U ⁻¹' A)).mem x
      (relativeNormalCoordinate U) := by
    refine ⟨Eventually.of_forall (normalCoordinate_mdifferentiable U), ?_⟩
    filter_upwards [h] with z hz hzA
    exact eq_zero_of_pow_eq_zero (hz hzA)
  obtain ⟨e, ξ, hOne, hAll⟩ := exists_normal_tangent_field U x
  have hDeriv := ((hAll A).preserves _ hVan).2.self_of_nhds hx
  exact one_ne_zero (hOne.symm.trans hDeriv)

set_option maxHeartbeats 1000000 in
/-- Selecting the old members through an initial positive anchor retains
the whole normal power at the new coefficient mark. The unmasked selected
carrier is still a proper cylinder. It is in the tight domain and has
normal contact and zero exponents in all its remaining boundary slots. -/
theorem initial_selected_normal_data {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hp : 0 < boundaryCount (properNormalMarked Q).E p) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let B := barMarked (X := X) (properNormalMarked Q)
    let L := memberRestrict B (membersThrough B.E B.E p)
    IsInvDomain k L ∧ (∀ x, L.ideal.mem x (fun z => relativeNormalCoordinate U z ^ L.d)) ∧
    IsMaximalOrderAlong L.N L.ideal L.d ∧
    IsTangentDirectionAlong L.N L.ideal L.d univ (relativeNormalCoordinate U) ∧
    (∀ D ∈ L.E, ∀ x, divExpAlong (n + 1) L.N L.ideal D x = 0) := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let B := barMarked (X := X) P
  let S := membersThrough B.E B.E p
  let L := memberRestrict B S
  let A := Q.N ∩ ⋂ D : Set U, ⋂ (_ : D ∈ Q.E ∧ projection U p ∈ D), D
  have hA : IsClosed A := hQ.isWellFormed.isClosedSubmanifold_N.1.inter
    (isClosed_iInter fun D => isClosed_iInter fun hD : D ∈ Q.E ∧ projection U p ∈ D =>
      hQ.isWellFormed.isSNCDivisor.1 D hD.1)
  have hE : B.E = Q.E.map (projection U ⁻¹' ·) := rfl
  have hCarrier : L.N = projection U ⁻¹' A := by
    change (memberRestrict B (membersThrough B.E B.E p)).N = _
    rw [memberRestrict_N, memberInter_membersThrough (fun _ h => h)]
    ext z
    change (z ∈ P.N ∧ ∀ D ∈ B.E, p ∈ D → z ∈ D) ↔ z ∈ projection U ⁻¹' A
    rw [hE, List.forall_mem_map]
    simp only [P, properNormalMarked, A, mem_preimage, mem_inter_iff, mem_iInter, and_imp]
  have hBar : IsInvDomain (k + 1) B := isInvDomain_barMarked (X := X) P (properNormalMarked_isInvDomain Q hQ)
  have hL := isWellFormed_memberRestrict (Nat.succ_pos n) hBar.isWellFormed S
  have hPos := one_le_memberRestrict_d B S
  have hS : S.Nonempty := membersThrough_nonempty (fun _ h => h) (show 1 ≤ boundaryCount B.E p from hp)
  have hDim : DimLE (n + 1) L.N k := by
    simpa only [Nat.add_sub_cancel] using dimLE_memberRestrict (Nat.succ_pos n) hBar.isWellFormed hS hBar.dimLE
  have hPow (x : productOpen U) : L.ideal.mem x (fun z => relativeNormalCoordinate U z ^ L.d) :=
    coeffMarkedAlong_normal_power_mem B hBar.one_le_d (normal_power_mem_bar Q hQ) x
  refine ⟨⟨hL, hDim, hPos, ?_⟩, hPow, ?_, ?_, ?_⟩
  · intro x hx
    rw [hCarrier] at hx ⊢
    exact normal_power_nonzero_on_cylinder A L.ideal L.d hPow x hx
  · rw [hCarrier]
    exact normal_power_maximalOrder U A L.ideal hL.isCoherent L.d hPow
  · rw [hCarrier]
    exact normal_tangent_of_power_member U A L.ideal hL.isCoherent L.d hPos hPow
  · intro D hD x
    have hDB : D ∈ B.E := List.mem_of_mem_filter (memberRestrict_membersThrough_E B B.E p ▸ hD)
    rw [hE] at hDB
    obtain ⟨F, hF, rfl⟩ := List.mem_map.mp hDB
    rw [hCarrier]
    exact normal_power_divExpAlong_eq_zero U A hA L.ideal hL.isCoherent L.d hPos hPow F
      (hQ.isWellFormed.isSNCDivisor.1 F hF) x

private theorem tested_order_of_zero_boundary_exponents {m k : ℕ} {X Y : CMfd.{0} m}
    (hm : 0 < m) (M : MarkedIdeal m X) (hM : IsInvDomain k M)
    (hMax : IsMaximalOrderAlong M.N M.ideal M.d)
    (hExp : ∀ D ∈ M.E, ∀ x, divExpAlong m M.N M.ideal D x = 0)
    (T : BlowupTower X Y) (hTest : IsGeoTestTower M T) {x : Y}
    (hx : x ∈ (geoTransformAlong M T).cosupp) :
    nmOrd (geoTransformAlong M T) x = M.d := by
  let C := companionOf m M M.d
  have hNm := nonmonomial_eq_restrictOn_of_boundary_zero M hExp
  have hC := isInvDomain_companionAlong (X := X) (𝔪 := M) hm hM hM.one_le_d
  have hRE : RestrictEquiv C M := by
    change RestrictEquiv (companionAlong M.N M.E (nmPart M)
      (monomialPartAlong m M.N M.ideal M.E) M.d M.d) M
    simp only [companionAlong, lt_self_iff_false, if_false]
    refine ⟨rfl, rfl, rfl, ?_, ?_⟩
    · rw [hNm]
      exact restrictLe_restrictOn
    · rw [hNm]
      exact restrictLe_self_restrictOn hM.isWellFormed.isCoherent
  have hW : WEquiv (X := X) C M := MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.wEquiv
    hRE hC.isWellFormed.isClosedSubmanifold_N.1 hC.isWellFormed.isCoherent hM.isWellFormed.isCoherent
  have hCT := (hW.2 T).1.mpr hTest
  have hBound : ∀ y ∈ M.cosupp, y ∉ ordGe M (M.d + 1) := by
    intro y _ hy
    change y ∈ cosupport m M.N (nmPart M) (M.d + 1) at hy
    rw [hNm] at hy
    exact hMax y (cosupport_subset_of_restrictLe
      (restrictLe_self_restrictOn hM.isWellFormed.isCoherent) _ hy)
  have hFacts := companionOf_tower_facts hm hM hM.one_le_d hBound T hCT
  have hxC : x ∈ (geoTransformAlong C T).cosupp := ((hW.2 T).2 hCT).symm ▸ hx
  have hCur := isInvDomain_geoTransformAlong hM T hTest
  exact Nat.le_antisymm (nmOrd_le_of_notMem (hFacts.2.1 x hx))
    ((mem_ordGe_iff hCur.isWellFormed hCur.isNonzeroAlongAt hx.1 M.d).mp (hFacts.2.2 hxC).1)

set_option maxHeartbeats 1000000 in
/-- On any actual lower test from the initial selected record restricted
to a mask, the first nonmonomial coordinate remains its true coefficient
mark everywhere on the current cosupport. -/
theorem initial_selected_normal_test_order {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hp : 0 < boundaryCount (properNormalMarked Q).E p) (O : Opens (productOpen U))
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) O) Y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let B := barMarked (X := X) (properNormalMarked Q)
    let L := memberRestrict B (membersThrough B.E B.E p)
    let M := MarkedIdeal.pullback (Subtype.val : O → X) L
    IsGeoTestTower M T → ∀ x ∈ (geoTransformAlong M T).cosupp,
      nmOrd (geoTransformAlong M T) x = L.d := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let B := barMarked (X := X) (properNormalMarked Q)
  let L := memberRestrict B (membersThrough B.E B.E p)
  let M := MarkedIdeal.pullback (Subtype.val : O → X) L
  obtain ⟨hL, _, hMax, _, hExp⟩ := initial_selected_normal_data Q hQ p hp
  have hM : IsInvDomain k M := isInvDomain_pullback_val O hL
  have hMaxM : IsMaximalOrderAlong M.N M.ideal M.d := by
    intro z hz
    let P' : MarkedIdeal (n + 1) X := ⟨L.N, L.E, L.ideal, L.d + 1⟩
    have hCos := cosupp_pullback_val P'
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hL.isWellFormed.isCoherent hg) O
    change z ∈ (MarkedIdeal.pullback (Subtype.val : O → X) P').cosupp at hz
    rw [hCos] at hz
    exact hMax z.val hz
  have hExpM : ∀ D ∈ M.E, ∀ z, divExpAlong (n + 1) M.N M.ideal D z = 0 := by
    intro D hD z
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hD
    have hi : i.val < L.E.length := by simpa only [M, MarkedIdeal.pullback, List.length_map] using i.isLt
    exact (divExpAlong_pullback_val_get L hL.isWellFormed.isCoherent O z i.isLt hi).trans
      (hExp _ (List.get_mem L.E ⟨i.val, hi⟩) z.val)
  change IsGeoTestTower M T → ∀ x ∈ (geoTransformAlong M T).cosupp,
    nmOrd (geoTransformAlong M T) x = L.d
  intro hTest x hx
  exact tested_order_of_zero_boundary_exponents (Nat.succ_pos n) M hM hMaxM hExpM T hTest hx

/-- The first recursive coordinate of an actual initial positive Step~1
cut is the cut's own mark along every subsequent lower test on its mask. -/
theorem original_initial_positive_lower_test_order {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) (p : productOpen U)
    (hLevel : level (properNormalMarked Q) (BlowupTower.refl
      (X := CMfd.of (n := n + 1) (productOpen U))) p = s + 1) :
    let P := properNormalMarked Q
    let H := BlowupTower.refl (X := CMfd.of (n := n + 1) (productOpen U))
    let O := maskA P H p
    let L := StepOneValueMasked.lowerMarkedM P (s + 1) H p
    ∀ {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) O) Y),
      IsGeoTestTower L T → ∀ x ∈ (geoTransformAlong L T).cosupp, nmOrd (geoTransformAlong L T) x = L.d := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let H := BlowupTower.refl (X := X)
  let B := barMarked (X := X) P
  let O := maskA P H p
  let L := StepOneValueMasked.lowerMarkedM P (s + 1) H p
  have hOld : origMembers P H = B.E := by
    change B.E.take B.E.length = B.E
    simp only [List.take_length]
  have hp : 0 < boundaryCount P.E p := by
    change boundaryCount (origMembers P H) p = s + 1 at hLevel
    change 0 < boundaryCount B.E p
    rw [hOld] at hLevel
    rw [hLevel]
    exact Nat.succ_pos s
  have hL : L = MarkedIdeal.pullback (Subtype.val : O → X)
      (memberRestrict B (membersThrough B.E B.E p)) := by
    change MarkedIdeal.pullback (Subtype.val : O → X)
      (memberRestrict B (membersThrough B.E (origMembers P H) p)) = _
    rw [hOld]
  change ∀ {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) O) Y),
    IsGeoTestTower L T → ∀ x ∈ (geoTransformAlong L T).cosupp, nmOrd (geoTransformAlong L T) x = L.d
  rw [hL]
  intro Y T
  exact initial_selected_normal_test_order Q hQ p hp O T

end
end Hironaka.HironakaG1InitialSelectedNormalOrder
