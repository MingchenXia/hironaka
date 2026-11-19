import Hironaka.Resolution.HironakaG1ProperNormalPhaseNative
import Hironaka.Resolution.HironakaG1SeparateCarrierMemberCut
import Hironaka.Resolution.HironakaG1RecursiveMemberValueTransport
import Hironaka.Resolution.HironakaActualNativeSectionPositiveLowerRecords

/-!
# The positive selected-member phase of a normally padded marked ideal

On the actual positive-level mask, the lower cosupport is the trace of the
upper bar cosupport on the selected original divisors. The upper test supplies
the strict normal section containing this entire cosupport.
-/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalPhase

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalPhaseNative
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualSectionBoundaryGeometry HironakaActualNativeSectionInitialBar
  HironakaActualOpenZeroSectionDifferentials HironakaDisjointNativeOpenLift
  HironakaG1SeparateCarrierMemberCut
  HironakaG1RecursiveMemberValueTransport
  HironakaActualNativeSectionPositiveLowerRecords HironakaActualNativeSectionNormalCrossings
  HironakaG8HomStable HironakaG8CoefficientBoundaryLocal HironakaG8LocalHistory
  RelativePrincipalizationSpan
  NormalCrossings BoundaryCount InvDomainMemberRestriction MarkedIdealRestrictOpen
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain
  InvDomainRebase NormalCrossingsComparison NormalCrossingsInvariance
  HironakaActualNativeInvariantDomain
open HomogenizedGlueingTower (N_geoTransformAlong strictAlong)

theorem bar_cosupport_subset_strict_zeroPlane {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) :
    (geoTransformAlong (barMarked (properNormalMarked Q)) T).cosupp ⊆ strictAlong T (zeroPlane U) := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let S := sectionMarked Q
  let V := sectionBarCoefficient Q
  have hP := properNormalMarked_isInvDomain Q hQ
  have hS : IsInvDomain k S := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hBS := HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) S hS
  have hPV : LocWPEquiv (X := X) P V :=
    (properNormalMarked_locWPEquiv_section Q hQ).trans
      ((bar_local_any_boundary (X := X) S hS).trans
        (coefficient_local_any_boundary (X := X) _ hBS))
  have hPB := bar_local_any_boundary (X := X) P hP
  obtain ⟨C, _, _, _, hLift, _, _, _, _, _, _⟩ := exists_upper_native_test_history Q hQ T hT
  have hSupport : V.N ⊆ zeroPlane U := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hC := HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hLift V hSupport
  have hEq : (geoTransformAlong (barMarked P) T).cosupp = (geoTransformAlong V T).cosupp :=
    ((hPB.wEquiv.2 T).2 hT).symm.trans ((hPV.wEquiv.2 T).2 hT)
  rw [hEq, ← hLift.carrier]
  exact subset_trans (geoTransformAlong V T).cosupp_subset_N hC

/-- In the positive branch, the entire lower cosupport has exactly the head
point's original boundary membership and lies in the actual strict section. -/
theorem positive_lower_cosupport {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y) :
    let P := properNormalMarked Q
    let O := lowerMask P (s + 1) H p
    let L := lowerMarkedM P (s + 1) H p
    L.cosupp = (Subtype.val : O → Y) ⁻¹'
      ((geoTransformAlong (barMarked P) H).cosupp ∩
        {x | ∀ D ∈ origMembers P H, p ∈ D → x ∈ D}) ∧
    ∀ x ∈ L.cosupp, (x : Y) ∈ strictAlong H (zeroPlane U) ∧
      ∀ D ∈ origMembers P H, (x : Y) ∈ D ↔ p ∈ D := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let O := maskA P H p
  let A := geoTransformAlong (barMarked P) H
  let E₀ := origMembers P H
  let J := memberRestrict A (membersThrough A.E E₀ p)
  have hP := properNormalMarked_isInvDomain Q hQ
  have hBarTest := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  have hA : A.IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (isWellFormed_barMarked P hP.isWellFormed) H hBarTest
  have hdA : 1 ≤ A.d := by
    rw [show A = geoTransformAlong (barMarked P) H from rfl, d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hJ : J.IsWellFormed := isWellFormed_memberRestrict (Nat.succ_pos n) hA _
  have hE : ∀ D ∈ E₀, D ∈ A.E := fun _ hD => List.mem_of_mem_take hD
  have hL : (lowerMarkedM P (s + 1) H p).cosupp =
      (Subtype.val : O → Y) ⁻¹' (A.cosupp ∩ {x | ∀ D ∈ E₀, p ∈ D → x ∈ D}) := by
    change (MarkedIdeal.pullback (Subtype.val : O → Y) J).cosupp = _
    rw [cosupp_pullback_val J (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ.isCoherent hg) O]
    rw [show J.cosupp = A.cosupp ∩ memberInter A.E (membersThrough A.E E₀ p) from
      cosupp_memberRestrict hA hdA _, memberInter_membersThrough hE p]
  refine ⟨hL, fun x hx => ?_⟩
  have hx' : (x : Y) ∈ A.cosupp ∩ {x | ∀ D ∈ E₀, p ∈ D → x ∈ D} := by
    rw [hL] at hx
    exact hx
  exact ⟨bar_cosupport_subset_strict_zeroPlane Q hQ H hH hx'.1,
    fun D hD => ⟨(interior_subset x.property).1 D hD, hx'.2 D hD⟩⟩

/-- The phase head and tail come from the supplied original upper history,
with the original positive lower record and the actual strict section. -/
theorem original_normal_positive_phase_head {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let P := properNormalMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let L := lowerMarkedM P (s + 1) H p
    let W := strictAlong H (zeroPlane U)
    IsClosed W ∧ (∀ z ∈ W, RegularAtDim (n := n + 1) W z n) ∧
      IsTransverse (n + 1) W (geoTransformAlong (barMarked P) H).E ∧ p ∈ W ∧
      ∃ hp : p ∈ O,
        (⟨p, hp⟩ : O) ∈ L.cosupp ∧ IsInvDomain k L ∧
        IsCanonical L ((invFamily (Nat.succ_pos n) k).inv L) (restrict O S) ∧
        (⟨y, hp⟩ : openPreimage S O) ∈ (geoTransformAlong L (restrict O S)).cosupp := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let R := invFamily (Nat.succ_pos n) k
  let r := regimeRun (stepRegime P (s + 1)) T y
  let H := head T r
  let S := tail T r
  let p := S.proj y
  let O := maskA P H p
  let L := lowerMarkedM P (s + 1) H p
  have hP := properNormalMarked_isInvDomain Q hQ
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  have hTest := (StepOneSeq.isMaxOrderValue_stepOneInvM (k := k + 1) R
    (Nat.succ_pos n)).isGeoTestTower_of_isCanonical hP hMax T hCan
  have hBarEq := bar_local_any_boundary (X := X) P hP
  have hBarTest := (hBarEq.wEquiv.2 T).1.mp hTest
  have hyBar : y ∈ (geoTransformAlong (barMarked P) T).cosupp :=
    (hBarEq.wEquiv.2 T).2 hTest ▸ hy
  have hLower := Seq.StepOneAdmissible.hasLowerDataL_stepOneInvM_of_isCanonical P R
    hP.isWellFormed hP.one_le_d (Nat.succ_pos n) hMax hP.dimLE T
    ((Seq.StepOneBridge.isCanonical_iff R P hP hMax (Nat.succ_pos n) T).mp hCan) y hyBar hNS
  have hHead := stepRegime_and_mem_cosupp_head P hP.isWellFormed T hBarTest hyBar hNS
  rw [hLevel] at hLower hHead
  obtain ⟨hp, hL, hLCan, hyL⟩ := hLower
  have hpBar : p ∈ (geoTransformAlong (barMarked P) H).cosupp := hHead.2
  have hH : IsGeoTestTower P H := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
  obtain ⟨W, hWc, hW, _, hLift, _, _, _, hWTrans, _, _⟩ :=
    exists_upper_native_test_history Q hQ H hH
  have hE : (geoTransformAlong (barMarked P) H).E =
      (geoTransformAlong (sectionBarCoefficient Q) H).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := barMarked (X := X) P) (𝔫 := sectionBarCoefficient Q) rfl H
  have hWTrans' : IsTransverse (n + 1) W (geoTransformAlong (barMarked P) H).E := by
    rw [hE]
    exact hWTrans
  have hpW := bar_cosupport_subset_strict_zeroPlane Q hQ H hH hpBar
  have hpL : (⟨p, hp⟩ : O) ∈ L.cosupp := by
    rw [show L.cosupp = (Subtype.val : O → _) ⁻¹'
      ((geoTransformAlong (barMarked P) H).cosupp ∩
        {x | ∀ D ∈ origMembers P H, p ∈ D → x ∈ D}) from
          (positive_lower_cosupport (s := s) Q hQ H hH p).1]
    exact ⟨hpBar, fun _ _ h => h⟩
  exact ⟨hLift.carrier ▸ hWc, hLift.carrier ▸ hW, hLift.carrier ▸ hWTrans',
    hpW, hp, hpL, hL, hLCan, hyL⟩

set_option maxHeartbeats 1000000 in
/-- The two positive member cuts on the upper mask have the same full weak
class. The section cut uses its own transformed section-supported carrier. -/
theorem positive_lower_section_class {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y) :
    let P := properNormalMarked Q
    let S := sectionMarked Q
    let O := maskA P H p
    let B := geoTransformAlong (barMarked P) H
    let A := geoTransformAlong (barMarked S) H
    let L := MarkedIdeal.pullback (M' := CMfd.of (n := n + 1) O) (Subtype.val : O → Y)
      (memberRestrict B (membersThrough B.E (origMembers P H) p))
    let L' := MarkedIdeal.pullback (M' := CMfd.of (n := n + 1) O) (Subtype.val : O → Y)
      (memberRestrict A (membersThrough A.E (origMembers S H) p))
    let W := openSection (strictAlong H (zeroPlane U)) O
    LocWPEquiv (X := CMfd.of (n := n + 1) O) L L' ∧
      L'.N ⊆ W ∧
      ∃ hW : ∀ x ∈ W, RegularAtDim (n := n + 1) W x n,
        (nativePullback (Nat.le_succ n) W hW L').cosupp = (Subtype.val : W → O) ⁻¹' L.cosupp := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let S := sectionMarked Q
  let O := maskA P H p
  let B := geoTransformAlong (barMarked P) H
  let A := geoTransformAlong (barMarked S) H
  let L := MarkedIdeal.pullback (M' := CMfd.of (n := n + 1) O) (Subtype.val : O → Y)
    (memberRestrict B (membersThrough B.E (origMembers P H) p))
  let L' := MarkedIdeal.pullback (M' := CMfd.of (n := n + 1) O) (Subtype.val : O → Y)
    (memberRestrict A (membersThrough A.E (origMembers S H) p))
  let W := openSection (strictAlong H (zeroPlane U)) O
  have hP := properNormalMarked_isInvDomain Q hQ
  have hS : IsInvDomain k S := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hPS := properNormalMarked_locWPEquiv_section Q hQ
  have hClass : LocWPEquiv (X := CMfd.of (n := n + 1) O) L L' :=
    member_stage_local_of_local (X := X) (Nat.succ_pos n) P S hP hS hPS H hH O p
  have hSupport : L'.N ⊆ W := by
    intro x hx
    have hxS : (x : Y) ∈ (geoTransformAlong (barMarked S) H).N := hx.1
    rw [N_geoTransformAlong] at hxS
    exact MemberInterTowerAlong.strictAlong_mono H
      (show (barMarked S).N ⊆ zeroPlane U from fun _ hz => ⟨mem_univ _, hz.2⟩) hxS
  have hST := (hPS.wEquiv.2 H).1.mp hH
  have hBarST := ((bar_local_any_boundary (X := X) S hS).wEquiv.2 H).1.mp hST
  have hA : A.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked S hS.isWellFormed) H hBarST
  have hL' : L'.IsWellFormed :=
    IsWellFormed.pullback_val (isWellFormed_memberRestrict (Nat.succ_pos n) hA _) O
  obtain ⟨V, _, hV, _, hLift, _, _, _, _, _, _⟩ := exists_upper_native_test_history Q hQ H hH
  have hW : ∀ x ∈ W, RegularAtDim (n := n + 1) W x n :=
    openSection_regular (hLift.carrier ▸ hV) O
  refine ⟨hClass, hSupport, hW, ?_⟩
  change (nativePullback (Nat.le_succ n) W hW L').cosupp = (Subtype.val : W → O) ⁻¹' L.cosupp
  rw [cosupp_nativePullback (Nat.le_succ n) W hW L' hSupport
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hL'.isCoherent hg), ← hClass.cosupp_eq_base]

private theorem positiveMemberOn_boundary_sublist {n : ℕ} {X Y : CMfd.{0} n}
    (P : MarkedIdeal n X) (H : BlowupTower X Y) (p : Y) (O : Opens Y) :
    (positiveMemberOn P H p O).E.Sublist
      ((geoTransformAlong (barMarked P) H).E.map ((Subtype.val : O → Y) ⁻¹' ·)) := by
  let B := geoTransformAlong (barMarked P) H
  have hSub : (memberRestrict B (membersThrough B.E (origMembers P H) p)).E.Sublist B.E := by
    rw [memberRestrict_membersThrough_E]
    exact List.filter_sublist
  exact hSub.map ((Subtype.val : O → Y) ⁻¹' ·)

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual upper lift supplies the thin centres of the native positive
tail. The native record uses the selected member cut on the original mask. -/
theorem original_normal_positive_phase_native_test_tail {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let P := properNormalMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let M := positiveMemberOn (sectionMarked Q) H p O
    let V := openPreimage S O
    ∃ (W : Set (CMfd.of (n := n + 1) O)) (hWc : IsClosed W)
      (hW : ∀ z ∈ W, RegularAtDim (n := n + 1) W z n)
      (Z : Set (CMfd.of (n := n + 1) V)) (hZc : IsClosed Z)
      (hZ : ∀ z ∈ Z, RegularAtDim (n := n + 1) Z z n)
      (N : BlowupTower (nativeManifold (Nat.le_succ n) W hW)
        (nativeManifold (Nat.le_succ n) Z hZ)),
      W = openSection (strictAlong H (zeroPlane U)) O ∧
      Lift (Nat.le_succ n) W hWc hW M.E (restrict O S) Z hZc hZ N ∧
      IsGeoTestTower (nativePullback (Nat.le_succ n) W hW M) N ∧
      (geoTransformAlong (nativePullback (Nat.le_succ n) W hW M) N =
        nativePullback (Nat.le_succ n) Z hZ (geoTransformAlong M (restrict O S))) ∧
      ∃ z : nativeManifold (Nat.le_succ n) Z hZ,
        z.val.val = y ∧ z ∈ (geoTransformAlong (nativePullback (Nat.le_succ n) W hW M) N).cosupp := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let R := invFamily (Nat.succ_pos n) k
  let r := regimeRun (stepRegime P (s + 1)) T y
  let H := head T r
  let S := tail T r
  let p := S.proj y
  let O := maskA P H p
  let Sec := sectionMarked Q
  let B := geoTransformAlong (barMarked Sec) H
  let M := positiveMemberOn Sec H p O
  have hP := properNormalMarked_isInvDomain Q hQ
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  have hTest := (StepOneSeq.isMaxOrderValue_stepOneInvM (k := k + 1) R
    (Nat.succ_pos n)).isGeoTestTower_of_isCanonical hP hMax T hCan
  have hH : IsGeoTestTower P H := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
  obtain ⟨_, _, hTrans, _, hp, _, hLD, hLC, hyL⟩ :=
    original_normal_positive_phase_head Q hQ T hCan y hy hLevel hNS
  have hLowerTest := R.isInvValue.isGeoTestTower_of_isCanonical hLD (restrict O S) hLC
  have hClass := positive_lower_section_class Q hQ H hH p
  have hMTest : IsGeoTestTower M (restrict O S) :=
    (hClass.1.wEquiv.2 (restrict O S)).1.mp hLowerTest
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hSecT := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hH
  have hSB := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hSecT
  have hB : B.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked Sec hSec.isWellFormed) H hSB
  have hM : M.IsWellFormed :=
    IsWellFormed.pullback_val (isWellFormed_memberRestrict (Nat.succ_pos n) hB _) O
  have hHol : ∀ x f, M.ideal.mem x f → HolomorphicAt (n + 1) f x :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hM.isCoherent hf
  have hBoundary : B.E = boundary (sectionBarCoefficient Q).E H :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := barMarked Sec)
      (𝔫 := (⟨univ, (sectionBarCoefficient Q).E, IdealWeightPowers.unitIdeal (n + 1) X, 1⟩ :
        MarkedIdeal (n + 1) X)) rfl H
  have hSameE : B.E = (geoTransformAlong (barMarked P) H).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := barMarked Sec) (𝔫 := barMarked P) rfl H
  let F := ((Subtype.val : O → (split T r).1) ⁻¹' ·)
  have hSub : M.E.Sublist (B.E.map F) := positiveMemberOn_boundary_sublist Sec H p O
  obtain ⟨C, _, _, _, hLift, _, _, _, _, _, _⟩ := exists_upper_native_test_history Q hQ T hTest
  obtain ⟨A, hAc, hAr, _, hHead, _, hOpen⟩ := exists_original_reference_lift hLift r
  obtain ⟨hZc, hZr, N, hGeo, _⟩ := hOpen O
  let W := openSection A O
  have hW : W = openSection (strictAlong H (zeroPlane U)) O :=
    congrArg (fun A => openSection A O) hHead.carrier
  have hTrA : IsTransverse (n + 1) A B.E := by
    rw [hHead.carrier, hSameE]
    exact hTrans
  have hTrW : IsTransverse (n + 1) W (B.E.map F) :=
    isTransverse_preimage (pullsBackCoordinates_val O) hTrA
  have hMN : M.N ⊆ W := hW.symm ▸ hClass.2.1
  have hSub' : M.E.Sublist ((boundary (sectionBarCoefficient Q).E H).map F) := by
    rw [← hBoundary]
    exact hSub
  have hSmall := Lift.forget_boundary hGeo (E' := M.E) hSub'
  have hMTr := isTransverse_of_forall_mem hTrW hSub.subset
  have hyBar : y ∈ (geoTransformAlong (barMarked P) T).cosupp :=
    ((bar_local_any_boundary (X := X) P hP).wEquiv.2 T).2 hTest ▸ hy
  have hyC : y ∈ C := by
    rw [hLift.carrier]
    exact bar_cosupport_subset_strict_zeroPlane Q hQ T hTest hyBar
  let Z := openSection C (openPreimage S O)
  let z : nativeManifold (Nat.le_succ n) Z hZr := ⟨⟨y, hp⟩, hyC⟩
  have hCos := (hClass.1.wEquiv.2 (restrict O S)).2 hLowerTest
  have hyM : (⟨y, hp⟩ : openPreimage S O) ∈ (geoTransformAlong M (restrict O S)).cosupp :=
    hCos ▸ hyL
  refine ⟨W, hAc.preimage continuous_subtype_val, openSection_regular hAr O,
    Z, hZc, hZr, N, hW, hSmall, ?_, ?_, z, rfl, ?_⟩
  · exact HironakaActualNativeSectionNormalCrossings.Lift.native_test hSmall
      (Nat.succ_pos n) hM.isSNCDivisor hMTr M rfl hMN hHol hMTest
  · exact hSmall.whole_records (Nat.succ_pos n) hM.isSNCDivisor hMTr M rfl hMN hHol
  · rw [HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hSmall
      (Nat.succ_pos n) hM.isSNCDivisor hMTr M rfl hMN hHol]
    exact hyM

/-- A positive padded special point stays special on the section, since
the bar cosupport is unchanged and the parent carrier shrinks. -/
theorem positive_normal_special_of_padded {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hp : 0 < level (properNormalMarked Q) H p) (hs : IsSpecial (properNormalMarked Q) H p) :
    IsSpecial (sectionMarked Q) H p := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let A := geoTransformAlong (barMarked P) H
  let B := geoTransformAlong (barMarked Sec) H
  have hP := properNormalMarked_isInvDomain Q hQ
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hPS := properNormalMarked_locWPEquiv_section Q hQ
  have hE : P.E = Sec.E := rfl
  have hOrig := HironakaG8MemberLoci.origMembers_eq_of_E_eq hE H
  have hLevel := HironakaG8MemberLoci.level_eq_of_E_eq hE H
  have hPB := bar_local_any_boundary (X := X) P hP
  have hSB := bar_local_any_boundary (X := X) Sec hSec
  have hCos : A.cosupp = B.cosupp :=
    ((hPB.wEquiv.2 H).2 hH).symm.trans (((hPS.trans hSB).wEquiv.2 H).2 hH)
  have hInitial : (barMarked (X := X) Sec).N ⊆ (barMarked (X := X) P).N := by
    change liftedCarrier Q.N ⊆ projection U ⁻¹' Q.N
    exact fun _ hx => hx.1
  have hN : B.N ⊆ A.N := by
    change (geoTransformAlong (barMarked Sec) H).N ⊆ (geoTransformAlong (barMarked P) H).N
    rw [N_geoTransformAlong, N_geoTransformAlong]
    exact MemberInterTowerAlong.strictAlong_mono H hInitial
  rcases hs with ⟨h0, _⟩ | ⟨hpos, hMem⟩
  · exact ((Nat.ne_of_gt hp) h0).elim
  · refine Or.inr ⟨(hLevel p) ▸ hpos, ?_⟩
    change p ∈ MemberInterLocusAlong.memberInterLocus B.N (origMembers Sec H) B.cosupp
    rw [← hOrig, ← hCos]
    exact ⟨hMem.1, hMem.2.mono fun _ hy hyN hyE => hy (hN hyN) hyE⟩

/-- For positive levels, shrinking the parent carrier adds possible special
points and makes the section mask smaller. The original boundary is fixed. -/
theorem positive_normal_section_mask_subset {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hp : 0 < level (properNormalMarked Q) H p) :
    (maskA (sectionMarked Q) H p : Set Y) ⊆ maskA (properNormalMarked Q) H p := by
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  have hE : P.E = Sec.E := rfl
  have hOrig := HironakaG8MemberLoci.origMembers_eq_of_E_eq hE H
  have hLevel := HironakaG8MemberLoci.level_eq_of_E_eq hE H
  change (maskA Sec H p : Set Y) ⊆ maskA P H p
  unfold maskA
  apply interior_mono
  intro z hz
  refine ⟨fun D hD hzD => hz.1 D (hOrig ▸ hD) hzD, ?_⟩
  rintro ⟨hL, hs⟩
  exact hz.2 ⟨(hLevel z).symm.trans (hL.trans (hLevel p)),
    positive_normal_special_of_padded Q hQ H hH z (hL.symm ▸ hp) hs⟩

private theorem positiveMemberOn_domain {n k s : ℕ} {X Y : CMfd.{0} n}
    (hn : 0 < n) (P : MarkedIdeal n X) (hP : IsInvDomain k P)
    (H : BlowupTower X Y) (hH : IsGeoTestTower (barMarked P) H)
    (p : Y) (hLevel : level P H p = s + 1) :
    IsInvDomain (k - 1) (positiveMemberOn P H p (maskA P H p)) :=
  isInvDomain_lowerMarked_succ (X := X) P hP.isWellFormed hP.one_le_d hn H hH hP.dimLE hLevel

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- At a nonspecial section point, its actual positive lower record has the
original native domain on the section mask inside the padded mask. -/
theorem positive_normal_native_domain_on_section_mask {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hLevel : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (sectionMarked Q) H p) :
    let Sec := sectionMarked Q
    let O := maskA Sec H p
    let W := openSection (strictAlong H (zeroPlane U)) O
    let M := positiveMemberOn Sec H p O
    p ∈ O ∧
      ∃ hW : ∀ z ∈ W, RegularAtDim (n := n + 1) W z n,
        IsInvDomain (k - 1) (nativePullback (Y := CMfd.of (n := n + 1) O) (Nat.le_succ n) W hW M) := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let Sec := sectionMarked Q
  let O := maskA Sec H p
  let M := positiveMemberOn Sec H p O
  let B := geoTransformAlong (barMarked Sec) H
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hSecTest := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hH
  have hBarTest := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hSecTest
  have hE : (properNormalMarked Q).E = Sec.E := rfl
  have hLevelSec := (HironakaG8MemberLoci.level_eq_of_E_eq hE H p).symm.trans hLevel
  have hPositive : 1 ≤ level Sec H p := by rw [hLevelSec]; exact Nat.succ_le_succ (Nat.zero_le s)
  have hp : p ∈ O :=
    mem_maskA (X := X) Sec hSec.isWellFormed hSec.one_le_d (Nat.succ_pos n) H hBarTest hPositive hNS
  have hM : IsInvDomain (k - 1) M :=
    positiveMemberOn_domain (X := X) (Nat.succ_pos n) Sec hSec H hBarTest p hLevelSec
  let V := strictAlong H (zeroPlane U)
  let W := openSection V O
  have hMN : M.N ⊆ W := by
    intro x hx
    have hxS : (x : Y) ∈ B.N := hx.1
    change (x : Y) ∈ (geoTransformAlong (barMarked Sec) H).N at hxS
    rw [N_geoTransformAlong] at hxS
    exact MemberInterTowerAlong.strictAlong_mono H
      (show (barMarked Sec).N ⊆ zeroPlane U from fun _ hz => ⟨mem_univ _, hz.2⟩) hxS
  obtain ⟨A, _, hA, _, hLift, _, _, _, hATr, _, _⟩ :=
    exists_upper_native_test_history Q hQ H hH
  have hAeq : A = V := hLift.carrier
  have hBoundary : B.E = (geoTransformAlong (sectionBarCoefficient Q) H).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := barMarked Sec) (𝔫 := sectionBarCoefficient Q) rfl H
  have hVTr : IsTransverse (n + 1) V B.E := by rw [← hAeq, hBoundary]; exact hATr
  have hWTr : IsTransverse (n + 1) W (B.E.map ((Subtype.val : O → Y) ⁻¹' ·)) :=
    isTransverse_preimage (pullsBackCoordinates_val O) hVTr
  have hSub : M.E.Sublist (B.E.map ((Subtype.val : O → Y) ⁻¹' ·)) :=
    positiveMemberOn_boundary_sublist Sec H p O
  have hV : ∀ z ∈ V, RegularAtDim (n := n + 1) V z n := hAeq ▸ hA
  have hW : ∀ z ∈ W, RegularAtDim (n := n + 1) W z n := openSection_regular hV O
  exact ⟨hp, hW, isInvDomain_nativePullback (X := CMfd.of (n := n + 1) O) (W := W)
    (Nat.succ_pos n) (Nat.le_succ n) hW M hM hMN
    (isTransverse_of_forall_mem hWTr hSub.subset)⟩

end

end Hironaka.HironakaG1PositiveNormalPhase
