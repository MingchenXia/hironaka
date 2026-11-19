import Hironaka.Resolution.HironakaG1NormalCentreTransport
import Hironaka.Resolution.HironakaG1PositiveNormalSharedTail

/-! Unequal recursive bounds for a supported whole-record native lift. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1NormalUnequalDepth

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec ResolutionDriver
  ResolutionInvariantExt CanonicalCentres NormalCrossings RelativePrincipalizationSpan
  HironakaOriginalFamilyDepthStability HironakaActualSectionBoundaryDimension
  HironakaActualNativeSectionFiniteHistory HironakaG1NormalCentreTransport

/-- On the actual tight domain, increasing the depth bound preserves and
reflects canonicality of the same chronological tower. -/
theorem original_family_depth_canonical_iff {n : ℕ} {X Y : CMfd.{0} n}
    (hn : 0 < n) (a q : ℕ) (M : MarkedIdeal n X) (hM : IsInvDomain q M)
    (T : BlowupTower X Y) :
    IsCanonical M ((invFamily hn (a + q)).inv M) T ↔
      IsCanonical M ((invFamily hn q).inv M) T := by
  refine ⟨?_, fun hCan => (original_family_depth_stability hn a q M hM T hCan).1⟩
  induction T with
  | refl => exact fun _ => trivial
  | @step Y Z T C π hπ ih =>
    rintro ⟨hPrefix, hEmpty | hCentre⟩
    · exact ⟨ih hPrefix, Or.inl hEmpty⟩
    · have hT := ih hPrefix
      have hMax := maxLocus_congr (original_family_depth_stability hn a q M hM T hT).2
      have hPad := MaxLocusLocal.maxLocus_comp_strictMono (strictMono_depthPadMap a q)
        ((invFamily hn q).inv M T) (geoTransformAlong M T).cosupp
      exact ⟨hT, Or.inr (hCentre.trans (hMax.trans hPad))⟩

section Lift

variable {n k q : ℕ} {X : CMfd.{0} n} {hk : k ≤ n}
  {W : Set X} {hWc : IsClosed W} {hW : ∀ x ∈ W, RegularAtDim (n := n) W x k}
  {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
  {hV : ∀ y ∈ V, RegularAtDim (n := n) V y k}
  {Q : BlowupTower (nativeManifold hk W hW) (nativeManifold hk V hV)}

/-- Compare the actual supported pullback at its tight bound with the ambient
record at any larger bound. Canonicality is equivalent on the same towers.
The values on the whole current cosupport are related by the ambient shift
at fixed depth followed by depth padding. -/
theorem Lift.original_padded_bound_comparison
    (hn : 0 < n) (hkpos : 0 < k) (a : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain q M)
    (hMN : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (h : Lift hk W hWc hW M.E T V hVc hV Q) :
    let B := nativePullback hk W hW M
    let f : ∀ {Y' : CMfd.{0} n}, BlowupTower X Y' → Y' → ValTy (a + q) :=
        (invFamily hn (a + q)).inv M
    let g : ∀ {V' : CMfd.{0} k}, BlowupTower (nativeManifold hk W hW) V' →
        V' → ValTy q := (invFamily hkpos q).inv B
    (IsCanonical B g Q ↔ IsCanonical M f T) ∧
    (IsCanonical M f T → ∀ z : nativeManifold hk V hV,
      z.val ∈ (geoTransformAlong M T).cosupp →
        f T z.val = depthPadMap a q (sameIndexMap (n - k) q (g Q z))) := by
  intro B f g
  have hDepth := original_family_depth_canonical_iff hn a q M hM T
  refine ⟨(Lift.original_same_bound_canonical_iff hn hkpos M hM hMN hTrans h).trans
    hDepth.symm, fun hCan z hz => ?_⟩
  have hT := hDepth.mp hCan
  have hPad := (original_family_depth_stability hn a q M hM T hT).2 z.val hz
  have hValue := (HironakaOriginalFamilyDepthStability.Lift.original_same_bound_values
    hn hkpos M hM hMN hTrans h hT).2 z hz
  exact hPad.trans (congrArg (depthPadMap a q) hValue)

/-- The adjacent-bound case for a supported record with tight depth d - 1
and ambient recursion at depth d. -/
theorem Lift.original_adjacent_bound_comparison
    (hn : 0 < n) (hkpos : 0 < k) (d : ℕ) (hd : 0 < d)
    (M : MarkedIdeal n X) (hM : IsInvDomain (d - 1) M)
    (hMN : M.N ⊆ W) (hTrans : IsTransverse n W M.E)
    (h : Lift hk W hWc hW M.E T V hVc hV Q) :
    let B := nativePullback hk W hW M
    let f : ∀ {Y' : CMfd.{0} n}, BlowupTower X Y' → Y' → ValTy d :=
        (invFamily hn d).inv M
    let g : ∀ {V' : CMfd.{0} k}, BlowupTower (nativeManifold hk W hW) V' →
        V' → ValTy (d - 1) := (invFamily hkpos (d - 1)).inv B
    (IsCanonical B g Q ↔ IsCanonical M f T) ∧
    (IsCanonical M f T → ∀ z : nativeManifold hk V hV,
      z.val ∈ (geoTransformAlong M T).cosupp →
        f T z.val = cast (congrArg ValTy (show 1 + (d - 1) = d by omega))
          (depthPadMap 1 (d - 1) (sameIndexMap (n - k) (d - 1) (g Q z)))) := by
  have hBound (p : ℕ) (hp : 1 + (d - 1) = p) :
      let B := nativePullback hk W hW M
      let f : ∀ {Y' : CMfd.{0} n}, BlowupTower X Y' → Y' → ValTy p :=
        (invFamily hn p).inv M
      let g : ∀ {V' : CMfd.{0} k}, BlowupTower (nativeManifold hk W hW) V' →
        V' → ValTy (d - 1) := (invFamily hkpos (d - 1)).inv B
      (IsCanonical B g Q ↔ IsCanonical M f T) ∧
      (IsCanonical M f T → ∀ z : nativeManifold hk V hV,
        z.val ∈ (geoTransformAlong M T).cosupp →
          f T z.val = cast (congrArg ValTy hp)
            (depthPadMap 1 (d - 1) (sameIndexMap (n - k) (d - 1) (g Q z)))) := by
    cases hp
    exact Lift.original_padded_bound_comparison hn hkpos 1 M hM hMN hTrans h
  exact hBound d (by omega)

end Lift

open Hironaka.HolomorphicIdealSheaves BlowupTowerSplit MarkedIdealBiholomorphism
  HironakaG1PositiveNormalSharedTail HironakaG1PositiveNormalPhase
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1SeparateCarrierMemberCut
  HironakaG1RecursiveMemberValueTransport HironakaActualNativeInvariantDomain
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalLocalClass
  HironakaG1ProperNormalPhaseNative HironakaActualNativeSectionInitialBar
  HironakaActualOpenZeroSectionDifferentials HironakaDisjointNativeOpenLift
  HironakaActualNativeSectionPositiveLowerRecords HironakaActualSectionBoundaryGeometry
  HironakaG8CoefficientBoundaryLocal HironakaG8LocalHistory HironakaG8HomStable
  BoundaryCount StepOneValue StepOneValueMasked StepOneRegime StepOneLowerDomain
  NormalCrossingsComparison NormalCrossingsInvariance InvDomainMemberRestriction InvDomainRebase
open HomogenizedGlueingTower (strictAlong N_geoTransformAlong)
open HomogenizedIdealAlong

set_option maxHeartbeats 4000000 in
/-- The shared positive tail on the literal section cut compares ambient and
native canonicality at adjacent recursive bounds. The value formula holds
on its entire current cosupport whenever those histories are canonical. -/
theorem original_positive_shared_tail_adjacent_bound {n k s : ℕ}
    {U : Opens (ComplexModel n)} (hn : 0 < n) (hk : 0 < k)
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
    let M := positiveMemberOn (sectionMarked Q) H p O
    let V := openPreimage S O
    IsInvDomain (k - 1) M ∧
    ∃ (W : Set (CMfd.of (n := n + 1) O)) (hWc : IsClosed W)
      (hW : ∀ z ∈ W, RegularAtDim (n := n + 1) W z n)
      (Z : Set (CMfd.of (n := n + 1) V)) (hZc : IsClosed Z)
      (hZ : ∀ z ∈ Z, RegularAtDim (n := n + 1) Z z n)
      (N : BlowupTower (nativeManifold (Nat.le_succ n) W hW)
        (nativeManifold (Nat.le_succ n) Z hZ)),
      let B := nativePullback (Nat.le_succ n) W hW M
      let J := restrict O S
      W = openSection (strictAlong H (zeroPlane U)) O ∧
      Lift (Nat.le_succ n) W hWc hW M.E J Z hZc hZ N ∧
      IsInvDomain (k - 1) B ∧
      (IsCanonical B ((invFamily hn (k - 1)).inv B) N ↔
        IsCanonical M ((invFamily (Nat.succ_pos n) k).inv M) J) ∧
      (IsCanonical M ((invFamily (Nat.succ_pos n) k).inv M) J →
        ∀ z : nativeManifold (Nat.le_succ n) Z hZ,
          z ∈ (geoTransformAlong B N).cosupp →
            (invFamily (Nat.succ_pos n) k).inv M J z.val =
              cast (congrArg ValTy (show 1 + (k - 1) = k by omega))
                (depthPadMap 1 (k - 1)
                  (sameIndexMap 1 (k - 1) ((invFamily hn (k - 1)).inv B N z)))) ∧
      ∃ z : nativeManifold (Nat.le_succ n) Z hZ,
        z.val.val = y ∧ z ∈ (geoTransformAlong B N).cosupp := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let r := regimeRun (stepRegime P (s + 1)) T y
  let H := head T r
  let S := tail T r
  let p := S.proj y
  let O := maskA Sec H p
  let M := positiveMemberOn Sec H p O
  let G := geoTransformAlong (barMarked Sec) H
  have hP := properNormalMarked_isInvDomain Q hQ
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  have hTest := (StepOneSeq.isMaxOrderValue_stepOneInvM (k := k + 1)
    (invFamily (Nat.succ_pos n) k) (Nat.succ_pos n)).isGeoTestTower_of_isCanonical hP hMax T hCan
  have hHeadTest : IsGeoTestTower P H := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
  have hBarTest := ((bar_local_any_boundary (X := X) P hP).wEquiv.2 T).1.mp hTest
  have hyBar : y ∈ (geoTransformAlong (barMarked P) T).cosupp :=
    ((bar_local_any_boundary (X := X) P hP).wEquiv.2 T).2 hTest ▸ hy
  have hRegime := stepRegime_and_mem_cosupp_head P hP.isWellFormed T hBarTest hyBar hNS
  rw [hLevel] at hRegime
  have hHeadLevel : level P H p = s + 1 := hRegime.1.1
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hSecTest := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hHeadTest
  have hSecBarTest := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hSecTest
  have hE : P.E = Sec.E := rfl
  have hSecLevel := (HironakaG8MemberLoci.level_eq_of_E_eq hE H p).symm.trans hHeadLevel
  have hM : IsInvDomain (k - 1) M :=
    isInvDomain_lowerMarked_succ (X := X) Sec hSec.isWellFormed hSec.one_le_d
      (Nat.succ_pos n) H hSecBarTest hSec.dimLE hSecLevel
  obtain ⟨_, _, _, W, hWc, hW, Z, hZc, hZ, N, hWEq, hNative, hLift, _, _, hPoint⟩ :=
    original_normal_positive_shared_tail Q hQ T hCan y hy hLevel hNS hShared
  have hMN : M.N ⊆ W := by
    intro x hx
    rw [hWEq]
    have hxG : (x : (split T r).1) ∈ G.N := hx.1
    rw [show G.N = strictAlong H (barMarked Sec).N from N_geoTransformAlong _ _] at hxG
    exact MemberInterTowerAlong.strictAlong_mono H
      (show (barMarked Sec).N ⊆ zeroPlane U from fun _ hz => ⟨mem_univ _, hz.2⟩) hxG
  obtain ⟨A, _, _, _, hHead, _, _, _, hATr, _, _⟩ :=
    exists_upper_native_test_history Q hQ H hHeadTest
  have hBoundary : G.E = (geoTransformAlong (sectionBarCoefficient Q) H).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := barMarked Sec) (𝔫 := sectionBarCoefficient Q) rfl H
  have hStrictTr : IsTransverse (n + 1) (strictAlong H (zeroPlane U)) G.E := by
    rw [← hHead.carrier, hBoundary]
    exact hATr
  have hSectionTr : IsTransverse (n + 1) W (G.E.map ((Subtype.val : O → _) ⁻¹' ·)) := by
    rw [hWEq]
    exact isTransverse_preimage (pullsBackCoordinates_val O) hStrictTr
  have hSub : M.E.Sublist (G.E.map ((Subtype.val : O → _) ⁻¹' ·)) := by
    have hMember : (memberRestrict G (membersThrough G.E (origMembers Sec H) p)).E.Sublist G.E := by
      rw [memberRestrict_membersThrough_E]
      exact List.filter_sublist
    exact hMember.map ((Subtype.val : O → _) ⁻¹' ·)
  have hTr : IsTransverse (n + 1) W M.E := isTransverse_of_forall_mem hSectionTr hSub.subset
  obtain ⟨hIff, hValue⟩ :=
    Lift.original_adjacent_bound_comparison (Nat.succ_pos n) hn k hk M hM hMN hTr hLift
  refine ⟨hM, W, hWc, hW, Z, hZc, hZ, N, hWEq, hLift, hNative, hIff, ?_, hPoint⟩
  intro hCanM z hz
  have hHol : ∀ x f, M.ideal.mem x f → HolomorphicAt (n + 1) f x :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hM.isWellFormed.isCoherent hf
  have hCos := HironakaActualNativeSectionOrderHistory.Lift.current_cosupport
    hLift (Nat.succ_pos n) hM.isWellFormed.isSNCDivisor hTr M rfl hMN hHol
  rw [hCos] at hz
  have hCodim : n + 1 - n = 1 := by omega
  simpa only [hCodim] using hValue hCanM z hz

end Hironaka.HironakaG1NormalUnequalDepth
