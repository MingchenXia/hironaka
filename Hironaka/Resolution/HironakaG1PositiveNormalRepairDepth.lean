import Hironaka.Resolution.HironakaG1NormalUnequalDepth
import Hironaka.Resolution.HironakaG1PositiveNormalRepairCentres

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1PositiveNormalRepairDepth

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionInvariantExt CanonicalCentres RelativePrincipalizationSpan
  GermIdealPullbackCalculus DivisorExponentAlong SubmanifoldChartedSpace NormalCrossings
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionRegularity HironakaOriginalFamilyDepthStability
  HironakaActualSectionBoundaryDimension HironakaG1NormalUnequalDepth

/-- The exact bound and nonzero-along condition of a literal native pullback
reflect to its supported ambient record, given ambient well-formedness. -/
theorem isInvDomain_of_supported_nativePullback {n m q : ℕ} {X : CMfd.{0} n}
    {W : Set X} (hm : m ≤ n) (hW : ∀ z ∈ W, RegularAtDim (n := n) W z m)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed) (hMN : M.N ⊆ W)
    (hNative : IsInvDomain q (nativePullback hm W hW M)) : IsInvDomain q M := by
  let := chartedSpace hm hW
  have := isComplexManifold_chartedSpace hm hW
  let K := nativePullback hm W hW M
  have hImage : (Subtype.val : nativeManifold hm W hW → X) '' K.N = M.N := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hx
      exact ⟨⟨x, hMN hx⟩, hx, rfl⟩
  refine ⟨hM, ?_, hNative.one_le_d, ?_⟩
  · intro x hx
    let z : nativeManifold hm W hW := ⟨x, hMN hx⟩
    obtain ⟨j, hj, hReg⟩ := hNative.dimLE z (show z ∈ K.N from hx)
    have hReflect := (regularAtDim_native_image_iff hm hW K.N z j).mpr hReg
    rw [hImage] at hReflect
    exact ⟨j, hj, hReflect⟩
  · intro x hx
    let z : nativeManifold hm W hW := ⟨x, hMN hx⟩
    obtain ⟨g, hg, hFreq⟩ := hNative.isNonzeroAlongAt z (show z ∈ K.N from hx)
    by_contra! hZero
    have hgSpan := GermIdeal.mem_pullback_iff.mp hg
    have hVan : (vanishingIdeal (n := m) K.N).mem z g := by
      apply BlowupStrictIdeal.mem_vanishingIdeal_of_isInSpanAt' _ hgSpan
      rintro _ ⟨f, hf, rfl⟩
      have hFreqZero : ∀ᶠ y in 𝓝 x, y ∈ M.N → f y = 0 := by
        by_contra! hNonzero
        exact hZero ⟨f, hf, hNonzero⟩
      refine ⟨(GermIdeal.IsCoherent.holomorphicAt_mem hM.isCoherent hf).comp_contMDiff
        (Eventually.of_forall fun _ => (contMDiff_val hm hW).contMDiffAt), ?_⟩
      have hCont : ContinuousAt (Subtype.val : W → X) z := continuous_subtype_val.continuousAt
      exact hCont.eventually hFreqZero
    obtain ⟨p, hp, hEq⟩ := (hFreq.and_eventually hVan.2).exists
    exact hp.2 (hEq hp.1)

/-- The repaired ambient record and its literal supported native pullback
both have the lower recursive bound. -/
structure RepairDepthData {n m : ℕ} {X : CMfd.{0} n} (k : ℕ) (hm : m ≤ n)
    (W : Set X) (hW : ∀ z ∈ W, RegularAtDim (n := n) W z m)
    (M : MarkedIdeal n X) : Prop where
  ambient_domain : IsInvDomain (k - 1) M
  native_domain : IsInvDomain (k - 1) (nativePullback hm W hW M)
  support : M.N ⊆ W
  transverse : IsTransverse n W M.E

/-- An actual continuation lift of the repaired records transports canonicality
in both directions, at section depth k - 1 and ambient depth k. -/
theorem RepairDepthData.compare_continuation {n m k : ℕ} {X : CMfd.{0} n}
    {hm : m ≤ n} {W : Set X} {hWc : IsClosed W}
    {hW : ∀ z ∈ W, RegularAtDim (n := n) W z m} {M : MarkedIdeal n X}
    (hR : RepairDepthData k hm W hW M) (hn : 0 < n) (hmpos : 0 < m) (hk : 0 < k)
    {Y : CMfd.{0} n} {T : BlowupTower X Y} {V : Set Y} {hVc : IsClosed V}
    {hV : ∀ z ∈ V, RegularAtDim (n := n) V z m}
    {N : BlowupTower (nativeManifold hm W hW) (nativeManifold hm V hV)}
    (h : Lift hm W hWc hW M.E T V hVc hV N) :
    let B := nativePullback hm W hW M
    (IsCanonical B ((invFamily hmpos (k - 1)).inv B) N ↔
      IsCanonical M ((invFamily hn k).inv M) T) ∧
    (IsCanonical M ((invFamily hn k).inv M) T →
      ∀ z : nativeManifold hm V hV, z ∈ (geoTransformAlong B N).cosupp →
        (invFamily hn k).inv M T z.val =
          cast (congrArg ValTy (show 1 + (k - 1) = k by omega))
            (depthPadMap 1 (k - 1) (sameIndexMap (n - m) (k - 1)
              ((invFamily hmpos (k - 1)).inv B N z)))) := by
  obtain ⟨hIff, hValues⟩ :=
    Lift.original_adjacent_bound_comparison hn hmpos k hk M hR.ambient_domain
      hR.support hR.transverse h
  refine ⟨hIff, fun hCan z hz => hValues hCan z ?_⟩
  have hCos := HironakaActualNativeSectionOrderHistory.Lift.current_cosupport
    h hn hR.ambient_domain.isWellFormed.isSNCDivisor hR.transverse M rfl hR.support
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hR.ambient_domain.isWellFormed.isCoherent hg)
  change z ∈ (Subtype.val : nativeManifold hm V hV → Y) ⁻¹' (geoTransformAlong M T).cosupp
  rw [← hCos]
  exact hz

/-- An actual ambient canonical continuation of the repaired record constructs
its native continuation at the strictly smaller depth on the same clock. -/
theorem RepairDepthData.exists_native_continuation {n m k : ℕ} {X : CMfd.{0} n}
    {hm : m ≤ n} {W : Set X} (hWc : IsClosed W)
    {hW : ∀ z ∈ W, RegularAtDim (n := n) W z m} {M : MarkedIdeal n X}
    (hR : RepairDepthData k hm W hW M) (hn : 0 < n) (hmpos : 0 < m) (hk : 0 < k)
    {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hCan : IsCanonical M ((invFamily hn k).inv M) T) :
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ z ∈ V, RegularAtDim (n := n) V z m)
      (N : BlowupTower (nativeManifold hm W hW) (nativeManifold hm V hV)),
      let B := nativePullback hm W hW M
      Lift hm W hWc hW M.E T V hVc hV N ∧ N.length = T.length ∧
      IsCanonical B ((invFamily hmpos (k - 1)).inv B) N ∧
      IsGeoTestTower B N ∧
      geoTransformAlong B N = nativePullback hm V hV (geoTransformAlong M T) := by
  have hDomain : IsInvDomain k M := by
    refine ⟨hR.ambient_domain.isWellFormed, ?_, hR.ambient_domain.one_le_d,
      hR.ambient_domain.isNonzeroAlongAt⟩
    intro x hx
    obtain ⟨j, hj, hReg⟩ := hR.ambient_domain.dimLE x hx
    exact ⟨j, hj.trans (Nat.sub_le k 1), hReg⟩
  have hTest := ResolutionInvariantSeq.IsInvValue.isGeoTestTower_of_isCanonical
    (invFamily hn k).isInvValue hDomain T hCan
  obtain ⟨V, hVc, hV, N, hLift, hNativeTest⟩ :=
    HironakaActualNativeHistoryExistence.exists_native_history_of_original_test
      hn hm W hWc hW M hR.ambient_domain hR.support hR.transverse T hTest
  have hNativeCan := (hR.compare_continuation hn hmpos hk hLift).1.mpr hCan
  refine ⟨V, hVc, hV, N, hLift, hLift.length, hNativeCan, hNativeTest, ?_⟩
  exact hLift.whole_records hn hDomain.isWellFormed.isSNCDivisor hR.transverse M rfl hR.support
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hDomain.isWellFormed.isCoherent hg)

open MarkedIdealBiholomorphism MarkedIdealRestrictOpen MemberInterLocusAlong BlowupStrictSubmanifold ResolutionInvariantDriver StepOneLowerDomain
  StepOneValue StepOneValueMasked BoundaryCount InvDomainMemberRestriction InvDomainRebase
  HironakaActualNativeSectionInitialBar HironakaActualSectionBoundaryGeometry
  HironakaActualNativeSectionPositiveLowerRecords
  HironakaActualOpenZeroSectionDifferentials HironakaDisjointNativeOpenLift
  HironakaG1ProperCarrierNormalContact HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperCarrierNormalLocalClass HironakaG1ProperNormalPhaseNative
  HironakaG1PositiveNormalPhase HironakaG1PositiveNormalSpecialStep
  HironakaG1SeparateCarrierMemberCut HironakaG1RecursiveMemberValueTransport
  HironakaG8HomStable NormalCrossingsComparison NormalCrossingsInvariance
open HomogenizedIdealAlong HomogenizedGlueingTower

set_option maxHeartbeats 3000000 in
/-- The actual auxiliary selected repair gives the tight ambient and native
domains on its repaired section, using the same blowup and strict transform. -/
theorem positive_normal_repair_depth_data {n k s : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n + 1)} (H : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hH : IsGeoTestTower (properNormalMarked Q) H) (p : Y)
    (hLevel : level (properNormalMarked Q) H p = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) H p)
    (hSpecial : IsSpecial (sectionMarked Q) H p) :
    let O := maskA (properNormalMarked Q) H p
    let W := openSection (strictAlong H (zeroPlane U)) O
    let M := MarkedIdeal.pullback (Subtype.val : O → Y) (geoTransformAlong (barMarked (sectionMarked Q)) H)
    let J := positiveMemberOn (sectionMarked Q) H p O
    let L := lowerMarkedM (properNormalMarked Q) (s + 1) H p
    ∃ (hWc : IsClosed W) (hW : ∀ z ∈ W, RegularAtDim (n := n + 1) W z n)
      (q : nativeManifold (Nat.le_succ n) W hW),
      let A := nativePullback (Nat.le_succ n) W hW M
      let E := ((origMembers (sectionMarked Q) H).map ((Subtype.val : O → Y) ⁻¹' ·)).map
        ((Subtype.val : W → O) ⁻¹' ·)
      let C := memberInterLocus A.N E A.cosupp ∩ {z | boundaryCount E z = s + 1}
      let D := (Subtype.val : W → O) '' C
      q.val.val = p ∧ q ∈ C ∧ L.IsAdmissibleCentre D ∧
      ∃ (Z : CMfd.{0} (n + 1)) (π : Z → O) (hπ : IsBlowupAlong (n + 1) D π),
        let V := geoStrictTransform π D W
        let hV := strictRegular hWc hW C π hπ
        let J' := J.geoTransform D π
        let ρ := nativeProjection (Nat.le_succ n) hWc hW C π hπ
        let K := memberRestrict A (membersThrough A.E E q)
        IsBlowupAlong n C ρ ∧
        K.geoTransform C ρ = nativePullback (Nat.le_succ n) V hV J' ∧
        RepairDepthData k (Nat.le_succ n) V hV J' := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let Sec := sectionMarked Q
  let O := maskA P H p
  let W := openSection (strictAlong H (zeroPlane U)) O
  let B := geoTransformAlong (barMarked Sec) H
  let M := MarkedIdeal.pullback (Subtype.val : O → Y) B
  let J := positiveMemberOn Sec H p O
  let L := lowerMarkedM P (s + 1) H p
  obtain ⟨hWc, hW, q, hqp, hq, hC, hAmbient, hL, _, _, Z, π, hπ, hρ, _, _, _, _, hExact,
    hKDomain, _, _, _, _⟩ :=
    positive_normal_native_special_step Q hQ H hH p hLevel hNS hSpecial
  let A := nativePullback (Nat.le_succ n) W hW M
  let E := ((origMembers Sec H).map ((Subtype.val : O → Y) ⁻¹' ·)).map
    ((Subtype.val : W → O) ⁻¹' ·)
  let C := memberInterLocus A.N E A.cosupp ∩ {z | boundaryCount E z = s + 1}
  let D := (Subtype.val : W → O) '' C
  let T : BlowupTower (CMfd.of (n := n + 1) O) Z := .step .refl D π hπ
  let V := geoStrictTransform π D W
  let hV := strictRegular hWc hW C π hπ
  have hClass := (positive_lower_section_class Q hQ H hH p).1
  have hSupport : J.N ⊆ W := (positive_lower_section_class Q hQ H hH p).2.1
  have hSec : IsInvDomain k Sec := section_projected_domain k Q.N Q.E Q.ideal Q.d hQ
  have hSecTest := ((properNormalMarked_locWPEquiv_section Q hQ).wEquiv.2 H).1.mp hH
  have hBarTest := ((bar_local_any_boundary (X := X) Sec hSec).wEquiv.2 H).1.mp hSecTest
  have hB : B.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (isWellFormed_barMarked Sec hSec.isWellFormed) H hBarTest
  have hJ : J.IsWellFormed :=
    IsWellFormed.pullback_val (isWellFormed_memberRestrict (Nat.succ_pos n) hB _) O
  have hSub : J.E.Sublist M.E := by
    have hList : (memberRestrict B (membersThrough B.E (origMembers Sec H) p)).E.Sublist B.E := by
      rw [memberRestrict_membersThrough_E]
      exact List.filter_sublist
    exact hList.map ((Subtype.val : O → Y) ⁻¹' ·)
  obtain ⟨F, _, _, _, hHead, _, _, _, hFTr, _, _⟩ :=
    exists_upper_native_test_history Q hQ H hH
  have hBoundary : B.E = (geoTransformAlong (sectionBarCoefficient Q) H).E :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := barMarked Sec) (𝔫 := sectionBarCoefficient Q) rfl H
  have hTr : IsTransverse (n + 1) W M.E := by
    have hStrict : IsTransverse (n + 1) (strictAlong H (zeroPlane U)) B.E := by
      rw [← hHead.carrier, hBoundary]
      exact hFTr
    exact isTransverse_preimage (pullsBackCoordinates_val O) hStrict
  have hMSupp : M.N ⊆ W := by
    intro z hz
    have hzB : (z : Y) ∈ (geoTransformAlong (barMarked Sec) H).N := hz
    rw [N_geoTransformAlong] at hzB
    exact MemberInterTowerAlong.strictAlong_mono H
      (show (barMarked Sec).N ⊆ zeroPlane U from fun _ hz => ⟨mem_univ _, hz.2⟩) hzB
  have hMDomain : IsInvDomain k M :=
    InvDomainTowerAlong.isInvDomain_pullback_val O
      (InvDomainTowerAlong.isInvDomain_geoTransformAlong
        (HironakaCoherentTransformExtension.isInvDomain_barMarked (X := X) Sec hSec) H hBarTest)
  have hADomain : IsInvDomain k A := HironakaActualNativeInvariantDomain.isInvDomain_nativePullback
    (Nat.succ_pos n) (Nat.le_succ n) hW M hMDomain hMSupp hTr
  have hCThin : interior C = ∅ :=
    eq_empty_of_subset_empty ((interior_mono hC.2.1).trans (interior_cosupp_eq_empty hADomain).subset)
  let ρ := nativeProjection (Nat.le_succ n) hWc hW C π hπ
  have hStep : Lift (Nat.le_succ n) W hWc hW M.E T V isClosed_closure hV
      (.step .refl C ρ hρ) :=
    Lift.step Lift.refl C hC.1 hCThin π hπ hAmbient.2.2
  have hSmall := Lift.forget_boundary hStep hSub
  have hJTr := isTransverse_of_forall_mem hTr hSub.subset
  have hJTest := (hClass.wEquiv.2 T).1.mp (show IsGeoTestTower L T from ⟨trivial, hL⟩)
  have hAfter : (J.geoTransform D π).IsWellFormed :=
    GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hJ hJTest.2 hπ
  have hAfterSupp : (J.geoTransform D π).N ⊆ V :=
    HironakaActualNativeSectionOrderHistory.Lift.current_carrier_subset hSmall J hSupport
  have hAfterTr : IsTransverse (n + 1) V (J.geoTransform D π).E :=
    (hSmall.geometry (Nat.succ_pos n) hJ.isSNCDivisor hJTr).2
  have hNative : IsInvDomain (k - 1) (nativePullback (Nat.le_succ n) V hV (J.geoTransform D π)) := by
    rw [← hExact]
    simpa only [Nat.pred_eq_sub_one] using hKDomain
  have hAfterDomain :=
    isInvDomain_of_supported_nativePullback (Nat.le_succ n) hV _ hAfter hAfterSupp hNative
  exact ⟨hWc, hW, q, hqp, hq, hL, Z, π, hπ, hρ, hExact,
    ⟨hAfterDomain, hNative, hAfterSupp, hAfterTr⟩⟩

end Hironaka.HironakaG1PositiveNormalRepairDepth
