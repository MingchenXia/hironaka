import Hironaka.Resolution.HironakaG1NormalUnequalDepth
import Hironaka.Resolution.HironakaG1ProperNormalOriginalTest
import Hironaka.Resolution.HironakaG3RWindowLowerData

/-! Full original invariant comparison for the literal transported input
on the actual supported normal history. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1LiteralSupportedGeneralValue
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  ResolutionInvariantSpec ResolutionInvariantSegments CanonicalCentres ResolutionDriver
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeInvariantDomain
  HironakaActualNativeSectionInitialBar HironakaActualOpenZeroSectionDifferentials
  HironakaActualSectionBoundaryGeometry HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperNormalOriginalTest HironakaActualOpenSectionRepresentative
  HironakaG1NormalUnequalDepth HironakaOriginalFamilyDepthStability
  HironakaActualSectionBoundaryDimension HironakaG3RWindowLowerData NormalCrossings

private theorem max_locus_of_exact_comparison {X Y Λ Γ : Type*}
    [LinearOrder Λ] [LinearOrder Γ] {A : Set X} {B : Set Y}
    {j : X → Y} (hPre : A = j ⁻¹' B) (hImage : j '' A = B)
    {f : Y → Λ} {g : X → Γ} {d : Γ → Λ} (hd : StrictMono d)
    (hVal : ∀ x ∈ A, f (j x) = d (g x)) :
    maxLocus g A = j ⁻¹' maxLocus f B ∧ j '' maxLocus g A = maxLocus f B := by
  have hMax : maxLocus g A = j ⁻¹' maxLocus f B := by
    ext x
    constructor
    · rintro ⟨hx, h⟩
      refine ⟨(Set.ext_iff.mp hPre x).mp hx, fun y hy => ?_⟩
      obtain ⟨z, hz, rfl⟩ := hImage.symm ▸ hy
      rw [hVal z hz, hVal x hx]
      exact hd.monotone (h z hz)
    · rintro ⟨hx, h⟩
      have hxA : x ∈ A := hPre.symm ▸ (show x ∈ j ⁻¹' B from hx)
      refine ⟨hxA, fun z hz => hd.le_iff_le.mp ?_⟩
      rw [← hVal z hz, ← hVal x hxA]
      exact h (j z) ((Set.ext_iff.mp hPre z).mp hz)
  refine ⟨hMax, ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Set.ext_iff.mp hMax x).mp hx
  · intro hy
    obtain ⟨x, _, rfl⟩ := hImage.symm ▸ hy.1
    exact ⟨x, hMax.symm ▸ (show x ∈ j ⁻¹' maxLocus f B from hy), rfl⟩

set_option maxHeartbeats 1100000 in
/-- A padded ordinary test produces a literal original native test. At any
additional ambient recursive depth, the full supported invariant is
canonical precisely when the literal original invariant is canonical.
The entire values and maximum loci correspond on the same endpoint;
the comparison applies to the monomial and positive branches alike. -/
theorem exists_literal_supported_general_history {n q : ℕ} {U : Opens (ComplexModel n)}
    (hn : 0 < n) (a : ℕ) (Q : MarkedIdeal n U) (hQ : IsInvDomain q Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T) :
    let M := supportedNormalMarked Q
    IsInvDomain q M ∧ IsGeoTestTower M T ∧
    ∃ (V : Set Y) (hVc : IsClosed V) (hV : ∀ y ∈ V, RegularAtDim (n := n+1) V y n)
      (N : BlowupTower
        (nativeManifold (Y := CMfd.of (n := n+1) (productOpen U))
          (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
        (nativeManifold (Y := Y) (Nat.le_succ n) V hV)),
      (∃ hWc : IsClosed (zeroPlane U),
        Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U) M.E T V hVc hV N) ∧
      let B := nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
        (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
      let H := transport (nativeZeroSectionEquiv U) N
      let j : H.target → Y := fun z => (H.back z).val
      let FN : ∀ {Z : CMfd.{0} n}, BlowupTower (CMfd.of (n := n) U) Z → Z → ValTy q :=
        (invFamily hn q).inv Q
      let FA : ∀ {Z : CMfd.{0} (n+1)}, BlowupTower (CMfd.of (n := n+1) (productOpen U)) Z →
          Z → ValTy (a+q) := (invFamily (Nat.succ_pos n) (a+q)).inv M
      IsInvDomain q B ∧ MarkedIdeal.pullback (nativeZeroSectionEquiv U) B = Q ∧
      H.tower.length = T.length ∧ IsGeoTestTower Q H.tower ∧
      geoTransformAlong Q H.tower = MarkedIdeal.pullback H.back
        (nativePullback (Nat.le_succ n) V hV (geoTransformAlong M T)) ∧
      (IsCanonical Q FN H.tower ↔ IsCanonical M FA T) ∧
      (IsCanonical Q FN H.tower →
        (∀ z ∈ (geoTransformAlong Q H.tower).cosupp,
          FA T (j z) = depthPadMap a q (sameIndexMap 1 q (FN H.tower z))) ∧
        maxLocus (FN H.tower) (geoTransformAlong Q H.tower).cosupp =
          j ⁻¹' maxLocus (FA T) (geoTransformAlong M T).cosupp ∧
        j '' maxLocus (FN H.tower) (geoTransformAlong Q H.tower).cosupp =
          maxLocus (FA T) (geoTransformAlong M T).cosupp) := by
  let M := supportedNormalMarked Q
  let F := nativeZeroSectionEquiv U
  let B := nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
    (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
  obtain ⟨_, hM, hPM⟩ := supported_normal_data Q hQ
  have hMT := (hPM.wEquiv.2 T).1.mp hT
  have hSupport : M.N ⊆ zeroPlane U := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hTrans : IsTransverse (n+1) (zeroPlane U) M.E := by
    change IsTransverse (n+1) (liftedCarrier (univ : Set U)) (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hB : IsInvDomain q B :=
    isInvDomain_nativePullback (X := CMfd.of (n := n+1) (productOpen U)) (W := zeroPlane U)
      (Nat.succ_pos n) (Nat.le_succ n) (zeroPlane_regular U) M hM hSupport hTrans
  have hInput : MarkedIdeal.pullback F B = Q := native_supported_input_record Q hQ
  obtain ⟨V, hVc, hV, N, hLift, hBTest, hWhole, hLen, hQTest, _, _, hPre, hImage, _⟩ :=
    exists_literal_original_native_test_history Q hQ T hT
  let H := transport F N
  let j : H.target → Y := fun z => (H.back z).val
  let R := invFamily hn q
  have hIso := transport_isTowerIso F N
  have hWholeQ : geoTransformAlong Q H.tower = MarkedIdeal.pullback H.back
      (nativePullback (Nat.le_succ n) V hV (geoTransformAlong M T)) := by
    have h := IsTowerIso.geoTransformAlong_eq F hB.isWellFormed.isClosedSubmanifold_N
      hB.isWellFormed.isCoherent hIso hBTest
    rw [hInput, hWhole] at h
    exact h
  have hCanIso : IsCanonical Q (R.inv Q) H.tower ↔ IsCanonical B (R.inv B) N := by
    constructor
    · intro hCan
      have h := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R hQ F.symm hIso.symm hCan
      have hReverse : MarkedIdeal.pullback F.symm Q = B := by
        rw [← hInput, pullback_symm_pullback_of_isCoherent F hB.isWellFormed.isCoherent]
      rwa [hReverse] at h
    · intro hCan
      have h := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso R hB F hIso hCan
      rwa [hInput] at h
  obtain ⟨hCanLift, hValue⟩ := Lift.original_padded_bound_comparison
    (X := CMfd.of (n := n+1) (productOpen U)) (hk := Nat.le_succ n)
    (W := zeroPlane U) (hW := zeroPlane_regular U) (T := T) (V := V) (hV := hV) (Q := N)
    (Nat.succ_pos n) hn a M hM hSupport hTrans hLift
  have hCanBoth := hCanIso.trans hCanLift
  have hCosEq := (hPM.wEquiv.2 T).2 hT
  rw [hCosEq] at hPre hImage
  have hBCos := IsTowerIso.cosupp_geoTransformAlong F hB.isWellFormed.isClosedSubmanifold_N
    hB.isWellFormed.isCoherent hIso hBTest
  rw [hInput] at hBCos
  refine ⟨hM, hMT, V, hVc, hV, N, ⟨_, hLift⟩, hB, hInput, hLen, hQTest, hWholeQ,
    hCanBoth, ?_⟩
  intro hCanQ
  have hCanB := hCanIso.mp hCanQ
  have hCanM := hCanBoth.mp hCanQ
  have hValues : ∀ z ∈ (geoTransformAlong Q H.tower).cosupp,
      (invFamily (Nat.succ_pos n) (a+q)).inv M T (j z) =
        depthPadMap a q (sameIndexMap 1 q (R.inv Q H.tower z)) := by
    intro z hz
    have hzB : H.back z ∈ (geoTransformAlong B N).cosupp := (Set.ext_iff.mp hBCos z).mp hz
    have hzM : j z ∈ (geoTransformAlong M T).cosupp := (Set.ext_iff.mp hPre z).mp hz
    have h := R.isInvValue.towerIso F B hB H.tower N H.back hIso hCanB z hzB
    rw [hInput] at h
    have hCodim : n+1-n = 1 := by omega
    have hV := hValue hCanM (H.back z) hzM
    rw [hCodim] at hV
    exact hV.trans (congrArg (depthPadMap a q ∘ sameIndexMap 1 q) h.symm)
  refine ⟨hValues, ?_⟩
  exact max_locus_of_exact_comparison hPre hImage
    ((strictMono_depthPadMap a q).comp (strictMono_sameIndexMap 1 q)) hValues

end
end Hironaka.HironakaG1LiteralSupportedGeneralValue
