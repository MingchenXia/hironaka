import Hironaka.Resolution.HironakaG1ProperNormalOriginalTest
import Hironaka.Resolution.HironakaActualNativeSectionOrderHistory
import Hironaka.Resolution.HironakaActualNativeSectionNormalCrossings
import Hironaka.Invariant.GeneralCompare

/-! Companion TESTs on the shared order-run split of the actual normal
history and the literal transported input. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1NormalOrderTail
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  ResolutionInvariantSpec InvDomainTowerAlong NonmonomialOrderLocal NonmonomialOrderTail
  NonmonomialOrderCanonical NonmonomialOrderRegime StepOneRegime
  GeneralValue GeneralCompare CanonicalCentres RestrictEmptyTower
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOrderHistory
  HironakaActualNativeSectionInitialBar HironakaActualNativeSectionNormalCrossings
  HironakaActualNativeInvariantDomain HironakaActualOpenZeroSectionDifferentials
  HironakaActualSectionBoundaryGeometry HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperNormalOriginalTest HironakaActualOpenSectionRepresentative NormalCrossings

/-- Test of the actual companion formed on a split's order mask. -/
def IsOrderCompanionTailTest {n : ℕ} {X Y : CMfd.{0} n}
    (M : MarkedIdeal n X) (T : BlowupTower X Y) (o r : ℕ) : Prop :=
  IsGeoTestTower (compAt M o (head T r))
    (restrict (ordMask (geoTransformAlong M (head T r)) o) (tail T r))

set_option maxHeartbeats 800000 in
/-- For a given actual normal Lift and original upper TEST, an order-monotone
CAN of the literal original native input supplies a TEST of its genuine
masked companion on the common order-run tail. The native anchor lies over
that head mask. An order-monotone CAN on the kept ambient history supplies
the corresponding ambient tail TEST at the same split. -/
theorem original_native_order_companion_tail_of_canonical {n k : ℕ}
    {Λ Γ : Type} [LinearOrder Λ] [LinearOrder Γ]
    {U : Opens (ComplexModel n)} (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
    {Y : CMfd.{0} (n+1)} (T : BlowupTower (CMfd.of (n := n+1) (productOpen U)) Y)
    (hT : IsGeoTestTower (properNormalMarked Q) T)
    {C : Set Y} {hCc : IsClosed C} {hC : ∀ y ∈ C, RegularAtDim (n := n+1) C y n}
    {hWc : IsClosed (zeroPlane U)}
    (N : BlowupTower
      (nativeManifold (Y := CMfd.of (n := n+1) (productOpen U))
        (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U))
      (nativeManifold (Y := Y) (Nat.le_succ n) C hC))
    (hLift : Lift (Nat.le_succ n) (zeroPlane U) hWc (zeroPlane_regular U)
      (supportedNormalMarked Q).E T C hCc hC N)
    (f : ∀ {Z : CMfd.{0} n}, BlowupTower (CMfd.of (n := n) U) Z → Z → Λ)
    (hf : OrdMonotone Q f)
    (hfCan : IsCanonical Q f (transport (nativeZeroSectionEquiv U) N).tower)
    (g : ∀ {Z : CMfd.{0} (n+1)}, BlowupTower (CMfd.of (n := n+1) (productOpen U)) Z → Z → Γ)
    (hg : OrdMonotone (supportedNormalMarked Q) g) :
    let H := transport (nativeZeroSectionEquiv U) N
    let M := supportedNormalMarked Q
    IsGeoTestTower Q H.tower ∧
    ∀ (z : H.target) (o : ℕ), z ∈ (geoTransformAlong Q H.tower).cosupp →
      nmOrd (geoTransformAlong Q H.tower) z = o → 0 < o →
      let r := regimeRun (OrdRegime Q o) H.tower z
      r = regimeRun (OrdRegime M o) T (H.back z).val ∧
      z ∈ openPreimage (tail H.tower r) (ordMask (geoTransformAlong Q (head H.tower r)) o) ∧
      IsOrderCompanionTailTest Q H.tower o r ∧
      (IsCanonical M g T → IsOrderCompanionTailTest M T o r) := by
  let M := supportedNormalMarked Q
  let H := transport (nativeZeroSectionEquiv U) N
  obtain ⟨_, hM, hPM⟩ := supported_normal_data Q hQ
  have hMT := (hPM.wEquiv.2 T).1.mp hT
  have hSupport : M.N ⊆ zeroPlane U := fun _ hz => ⟨mem_univ _, hz.2⟩
  have hTrans : IsTransverse (n+1) (zeroPlane U) M.E := by
    change IsTransverse (n+1) (liftedCarrier (univ : Set U)) (Q.E.map (projection U ⁻¹' ·))
    exact isTransverse_liftedCarrier (univ : Set U) Q.E
      (SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hQ.isWellFormed.isSNCDivisor)
  have hHol : ∀ x a, M.ideal.mem x a → HolomorphicAt (n+1) a x :=
    fun _ _ ha => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
      hM.isWellFormed.isCoherent ha
  have hNativeTest := Lift.native_test hLift (Nat.succ_pos n) hM.isWellFormed.isSNCDivisor
    hTrans M rfl hSupport hHol hMT
  let NB := nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
    (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
  have hNB : IsInvDomain k NB :=
    isInvDomain_nativePullback (X := CMfd.of (n := n+1) (productOpen U)) (W := zeroPlane U)
      (Nat.succ_pos n) (Nat.le_succ n) (zeroPlane_regular U) M hM hSupport hTrans
  have hInput : MarkedIdeal.pullback (nativeZeroSectionEquiv U) NB = Q :=
    native_supported_input_record Q hQ
  have hIso := transport_isTowerIso (nativeZeroSectionEquiv U) N
  have hBaseTest : IsGeoTestTower Q H.tower := by
    have h := (IsTowerIso.isGeoTestTower_iff (nativeZeroSectionEquiv U)
      hNB.isWellFormed.isClosedSubmanifold_N hNB.isWellFormed.isCoherent hIso).mpr hNativeTest
    simpa only [hInput] using h
  refine ⟨hBaseTest, ?_⟩
  intro z o hz hoz ho r
  have hRunNative := regimeRun_ordRegime_isTowerIso hn (nativeZeroSectionEquiv U) hNB o hIso hNativeTest z
  rw [hInput] at hRunNative
  have hRun : r = regimeRun (OrdRegime M o) T (H.back z).val :=
    hRunNative.trans (Lift.original_order_regime_run hLift (Nat.succ_pos n)
      hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport hHol o (H.back z)).symm
  refine ⟨hRun, ?_, ?_, ?_⟩
  · exact (proj_tail_mem_ordMask hn hQ H.tower hBaseTest hz hoz).2
  · exact isGeoTestTower_companion_tail_of_canonical hn hQ hf ho H.tower hBaseTest hfCan z
  · intro hgCan
    rw [hRun]
    exact isGeoTestTower_companion_tail_of_canonical (𝔪 := M) (f := g) (Nat.succ_pos n)
      hM hg ho T hMT hgCan (H.back z).val

end
end Hironaka.HironakaG1NormalOrderTail
