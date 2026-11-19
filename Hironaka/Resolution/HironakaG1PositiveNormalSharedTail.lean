import Hironaka.Resolution.HironakaG1PositiveNormalPhase
import Hironaka.Resolution.HironakaActualRawRecordPullbacks
import Hironaka.Invariant.MaxLocusLocal

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalSharedTail

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
  HironakaG1PositiveNormalPhase HironakaG1SeparateCarrierMemberCut
  HironakaG1RecursiveMemberValueTransport
  HironakaActualNativeSectionPositiveLowerRecords HironakaActualNativeSectionNormalCrossings
  HironakaG8HomStable HironakaG8CoefficientBoundaryLocal HironakaG8LocalHistory
  RelativePrincipalizationSpan
  NormalCrossings BoundaryCount InvDomainMemberRestriction MarkedIdealRestrictOpen
  StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain
  InvDomainRebase NormalCrossingsComparison NormalCrossingsInvariance
  HironakaActualNativeInvariantDomain
open HomogenizedGlueingTower (N_geoTransformAlong strictAlong)

set_option maxHeartbeats 4000000 in
set_option backward.isDefEq.respectTransparency false in
/-- The shared positive tail restricts to the section mask with the padded
canonicality intact. The corresponding selected section record has an actual
native test tail with the same lifted centres. -/
theorem original_normal_positive_shared_tail {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y)
    (hShared : ¬ IsSpecial (sectionMarked Q)
      (head T (regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T y))
      ((tail T (regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T y)).proj y)) :
    let P := properNormalMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA (sectionMarked Q) H p
    let L := positiveMemberOn P H p O
    let M := positiveMemberOn (sectionMarked Q) H p O
    let V := openPreimage S O
    IsInvDomain k L ∧ IsCanonical L ((invFamily (Nat.succ_pos n) k).inv L) (restrict O S) ∧
    LocWPEquiv (X := CMfd.of (n := n + 1) O) L M ∧
    ∃ (W : Set (CMfd.of (n := n + 1) O)) (hWc : IsClosed W)
      (hW : ∀ z ∈ W, RegularAtDim (n := n + 1) W z n)
      (Z : Set (CMfd.of (n := n + 1) V)) (hZc : IsClosed Z)
      (hZ : ∀ z ∈ Z, RegularAtDim (n := n + 1) Z z n)
      (N : BlowupTower (nativeManifold (Nat.le_succ n) W hW)
        (nativeManifold (Nat.le_succ n) Z hZ)),
      W = openSection (strictAlong H (zeroPlane U)) O ∧
      IsInvDomain (k - 1) (nativePullback (Nat.le_succ n) W hW M) ∧
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
  let O := maskA (sectionMarked Q) H p
  let Sec := sectionMarked Q
  let B := geoTransformAlong (barMarked Sec) H
  let M := positiveMemberOn Sec H p O
  have hP := properNormalMarked_isInvDomain Q hQ
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  have hTest := (StepOneSeq.isMaxOrderValue_stepOneInvM (k := k + 1) R
    (Nat.succ_pos n)).isGeoTestTower_of_isCanonical hP hMax T hCan
  have hH : IsGeoTestTower P H := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
  obtain ⟨_, _, hTrans, _, hpBig, _, hLD, hLC, hyBig⟩ :=
    original_normal_positive_phase_head Q hQ T hCan y hy hLevel hNS
  have hBarTest := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 T).1.mp hTest
  have hyBar : y ∈ (geoTransformAlong (barMarked P) T).cosupp :=
    ((bar_local_any_boundary (X := X) P hP).wEquiv.2 T).2 hTest ▸ hy
  have hPRegime := stepRegime_and_mem_cosupp_head P hP.isWellFormed T hBarTest hyBar hNS
  rw [hLevel] at hPRegime
  have hHeadLevel : level P H p = s + 1 := hPRegime.1.1
  obtain ⟨hp, _, hDomain⟩ :=
    positive_normal_native_domain_on_section_mask Q hQ H hH p hHeadLevel hShared
  let Bp := geoTransformAlong (barMarked P) H
  let Mp := memberRestrict Bp (membersThrough Bp.E (origMembers P H) p)
  let L := positiveMemberOn P H p O
  have hBarPT := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 H).1.mp hH
  have hBp := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked P hP.isWellFormed) H hBarPT
  have hMp : Mp.IsWellFormed := isWellFormed_memberRestrict (Nat.succ_pos n) hBp _
  have hHolMp : ∀ x g, Mp.ideal.mem x g → HolomorphicAt (n + 1) g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hMp.isCoherent hg
  have hSubset : O ≤ maskA P H p :=
    positive_normal_section_mask_subset Q hQ H hH p (hHeadLevel ▸ Nat.succ_pos s)
  obtain ⟨hL, hCanL, _⟩ := Seq.MaxLocusLocal.restrict_nestedOpens R hMp.isCoherent hSubset hLD S hLC
  have hLowerTest := R.isInvValue.isGeoTestTower_of_isCanonical hL (restrict O S) hCanL
  have hyRaw : y ∈ (geoTransformAlong Mp S).cosupp := by
    change (⟨y, hpBig⟩ : openPreimage S (maskA P H p)) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : maskA P H p → _) Mp)
        (restrict (maskA P H p) S)).cosupp at hyBig
    rw [HironakaActualRawRecordPullbacks.geoTransformAlong_restrict_of_hhol
      Mp hHolMp, cosupp_pullback_val _ (HironakaActualRawRecordPullbacks.holomorphic_geoTransformAlong Mp hHolMp S)] at hyBig
    exact hyBig
  have hyL : (⟨y, hp⟩ : openPreimage S O) ∈ (geoTransformAlong L (restrict O S)).cosupp := by
    change (⟨y, hp⟩ : openPreimage S O) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → _) Mp) (restrict O S)).cosupp
    rw [HironakaActualRawRecordPullbacks.geoTransformAlong_restrict_of_hhol
      Mp hHolMp, cosupp_pullback_val _ (HironakaActualRawRecordPullbacks.holomorphic_geoTransformAlong Mp hHolMp S)]
    exact hyRaw
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hClass : LocWPEquiv (X := CMfd.of (n := n + 1) O) L M :=
    member_stage_local_of_local (X := X) (Nat.succ_pos n) P Sec hP hSec
      (properNormalMarked_locWPEquiv_section Q hQ) H hH O p
  have hMTest : IsGeoTestTower M (restrict O S) :=
    (hClass.wEquiv.2 (restrict O S)).1.mp hLowerTest
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
  have hSub : M.E.Sublist (B.E.map F) := by
    have hs : (memberRestrict B (membersThrough B.E (origMembers Sec H) p)).E.Sublist B.E := by
      rw [memberRestrict_membersThrough_E]
      exact List.filter_sublist
    exact hs.map F
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
  have hMN : M.N ⊆ W := by
    intro x hx
    rw [hW]
    have hxS : (x : (split T r).1) ∈ B.N := hx.1
    change (x : (split T r).1) ∈ (geoTransformAlong (barMarked Sec) H).N at hxS
    rw [N_geoTransformAlong] at hxS
    exact MemberInterTowerAlong.strictAlong_mono H
      (show (barMarked Sec).N ⊆ zeroPlane U from fun _ hz => ⟨mem_univ _, hz.2⟩) hxS
  have hSub' : M.E.Sublist ((boundary (sectionBarCoefficient Q).E H).map F) := by
    rw [← hBoundary]
    exact hSub
  have hSmall := Lift.forget_boundary hGeo (E' := M.E) hSub'
  have hMTr := isTransverse_of_forall_mem hTrW hSub.subset
  have hyC : y ∈ C := by
    rw [hLift.carrier]
    exact bar_cosupport_subset_strict_zeroPlane Q hQ T hTest hyBar
  let Z := openSection C (openPreimage S O)
  let z : nativeManifold (Nat.le_succ n) Z hZr := ⟨⟨y, hp⟩, hyC⟩
  have hCos := (hClass.wEquiv.2 (restrict O S)).2 hLowerTest
  have hyM : (⟨y, hp⟩ : openPreimage S O) ∈ (geoTransformAlong M (restrict O S)).cosupp :=
    hCos ▸ hyL
  refine ⟨hL, hCanL, hClass, W, hAc.preimage continuous_subtype_val, openSection_regular hAr O,
    Z, hZc, hZr, N, hW, ?_, hSmall, ?_, ?_, z, rfl, ?_⟩
  · have hWReg := openSection_regular hAr O
    change IsInvDomain (k - 1) (nativePullback (Nat.le_succ n) W hWReg M)
    let W' := openSection (strictAlong H (zeroPlane U)) O
    have hEq : W = W' := hW
    exact @Eq.rec _ W' (fun V h => IsInvDomain (k - 1)
      (nativePullback (Nat.le_succ n) V (h ▸ (hEq ▸ hWReg)) M)) hDomain W hEq.symm
  · exact HironakaActualNativeSectionNormalCrossings.Lift.native_test hSmall
      (Nat.succ_pos n) hM.isSNCDivisor hMTr M rfl hMN hHol hMTest
  · exact hSmall.whole_records (Nat.succ_pos n) hM.isSNCDivisor hMTr M rfl hMN hHol
  · rw [HironakaActualNativeSectionOrderHistory.Lift.current_cosupport hSmall
      (Nat.succ_pos n) hM.isSNCDivisor hMTr M rfl hMN hHol]
    exact hyM

end

end Hironaka.HironakaG1PositiveNormalSharedTail
