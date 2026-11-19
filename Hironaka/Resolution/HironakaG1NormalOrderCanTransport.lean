import Hironaka.Resolution.HironakaG1NormalOrderTail
import Hironaka.Resolution.HironakaActualNativeSectionOriginalCuts
import Hironaka.Resolution.HironakaActualNativeCompanionHistories
import Hironaka.Resolution.HironakaDisjointRecursiveNativeHistory
import Hironaka.Invariant.CompanionTowerIso

/-! The actual supported companion tail inherits TEST from the literal
native original CAN along the same normal Lift. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1NormalOrderCanTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  ResolutionInvariantSpec InvDomainTowerAlong NonmonomialOrderCanonical NonmonomialOrderLocal
  NonmonomialOrderRegime NonmonomialOrderTail NonmonomialOrderTransport StepOneRegime CanonicalCentres
  GeneralValue GeneralCompare CompanionRebase CompanionReductionAlong CompanionTowerIso InvDomainCompanion
  HironakaActualNativeSectionFiniteHistory HironakaActualNativeSectionOriginalCuts
  HironakaActualNativeSectionOrderHistory HironakaActualNativeSectionNormalCrossings
  HironakaActualNativeCompanionHistories HironakaActualNativeInvariantDomain
  HironakaActualNativeSectionInitialBar HironakaActualOpenZeroSectionDifferentials
  HironakaActualSectionBoundaryGeometry HironakaG1ProperCarrierNormalDerivativeTrace
  HironakaG1ProperNormalOriginalTest HironakaActualOpenSectionRepresentative HironakaG1NormalOrderTail
  HironakaDisjointRecursiveNativeHistory HironakaDisjointNativeReferenceWindow
  StepOneTangentChange NormalCrossings

private theorem recast_split_iso {n : ℕ} {X' X Y' Y W' W V : CMfd.{0} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    {P' : BlowupTower X' W'} {P : BlowupTower X W}
    {S' : BlowupTower W' Y'} {S : BlowupTower W Y}
    {ψ : W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ W}
    (hP : IsTowerIso Φ P' P ψ) (hS : IsTowerIso ψ S' S χ) (e : W = V) :
    ∃ η : W' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ V,
      IsTowerIso Φ P' (recastTarget e P) η ∧ IsTowerIso η S' (recastSource e S) χ := by
  cases e
  exact ⟨ψ, hP, hS⟩

set_option maxHeartbeats 1200000 in
/-- Order-monotone CAN of the transported original (Q) suffices for
companion TEST on the literal supported ambient tail. The ambient input is
the ordinary padded original TEST and the actual geometric normal Lift. -/
theorem supported_order_companion_tail_of_native_canonical {n k : ℕ}
    {Λ : Type} [LinearOrder Λ] {U : Opens (ComplexModel n)}
    (hn : 0 < n) (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q)
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
    (hfCan : IsCanonical Q f (transport (nativeZeroSectionEquiv U) N).tower) :
    let H := transport (nativeZeroSectionEquiv U) N
    let M := supportedNormalMarked Q
    ∀ (z : H.target) (o : ℕ), z ∈ (geoTransformAlong Q H.tower).cosupp →
      nmOrd (geoTransformAlong Q H.tower) z = o → 0 < o →
      let r := regimeRun (OrdRegime Q o) H.tower z
      r = regimeRun (OrdRegime M o) T (H.back z).val ∧
      IsOrderCompanionTailTest M T o r := by
  let M := supportedNormalMarked Q
  let H := transport (nativeZeroSectionEquiv U) N
  let g : ∀ {Z : CMfd.{0} (n+1)}, BlowupTower (CMfd.of (n := n+1) (productOpen U)) Z → Z → ℕ :=
    fun S p => nmOrd (geoTransformAlong M S) p
  have hg : OrdMonotone M g := fun _ _ _ _ _ _ h => h
  obtain ⟨hBaseTest, hNative⟩ :=
    original_native_order_companion_tail_of_canonical hn Q hQ T hT N hLift f hf hfCan g hg
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
  let NB := nativePullback (Y := CMfd.of (n := n+1) (productOpen U))
    (Nat.le_succ n) (zeroPlane U) (zeroPlane_regular U) M
  have hNB : IsInvDomain k NB :=
    isInvDomain_nativePullback (X := CMfd.of (n := n+1) (productOpen U)) (W := zeroPlane U)
      (Nat.succ_pos n) (Nat.le_succ n) (zeroPlane_regular U) M hM hSupport hTrans
  have hInput : MarkedIdeal.pullback (nativeZeroSectionEquiv U) NB = Q :=
    native_supported_input_record Q hQ
  have hIso := transport_isTowerIso (nativeZeroSectionEquiv U) N
  intro H0 M0 z o hz hoz ho r
  obtain ⟨hRun, _, hJTest, _⟩ := hNative z o hz hoz ho
  refine ⟨hRun, ?_⟩
  obtain ⟨P, hPc, hP, e, hHead, hTail⟩ := Lift.original_head_tails hLift r
  obtain ⟨ψ, hIsoHead, hIsoTail⟩ := BlowupTowerSplitIso.IsTowerIso.exists_split hIso r
  obtain ⟨η, hHeadIso, hTailIso⟩ := recast_split_iso hIsoHead hIsoTail e
  let A := geoTransformAlong M (head T r)
  let Nh := recastTarget e (head N r)
  let Nt := recastSource e (tail N r)
  let B := geoTransformAlong NB Nh
  let L := companionOf (n+1) A o
  let Bc := companionOf n B o
  let W := ordMask A o
  let V := ordMask (geoTransformAlong Q (head H.tower r)) o
  let F := nativeWindow (Nat.le_succ n) P hP W
  have hMHead := ((isGeoTestTower_iff_head_tail M T r).mp hMT).1
  have hA := isInvDomain_geoTransformAlong hM (head T r) hMHead
  have hNBHead := Lift.native_test hHead (Nat.succ_pos n)
    hM.isWellFormed.isSNCDivisor hTrans M rfl hSupport hHol hMHead
  have hB := isInvDomain_geoTransformAlong hNB Nh hNBHead
  have hBC := isInvDomain_companionAlong hn hB ho
  have hL := isInvDomain_companionAlong (Nat.succ_pos n) hA ho
  obtain ⟨hComp, hMask, _⟩ :=
    Lift.original_current_companion_masks (X := CMfd.of (n := n+1) (productOpen U))
      (Y := (split T r).1) (T := head T r) (Q := Nh)
      (Nat.succ_pos n) hn (supportedNormalMarked Q) hM hSupport hTrans hHead hMHead
  have hMatch (p : (split H.tower r).1) : p ∈ V ↔ η p ∈ F := by
    have h := mem_ordMask_isTowerIso_iff hn (nativeZeroSectionEquiv U) hNB
      hHeadIso hNBHead o p
    rw [hInput] at h
    exact h.trans (hMask o (η p)).symm
  let α := diffeoOpens η V F hMatch
  have hMaskIso := isTowerIso_restrictOpens hMatch hTailIso
    (isTowerIso_mem_openPreimage_iff hTailIso hMatch)
  have hRec := companionOf_isTowerIso (nativeZeroSectionEquiv U) hn hNB ho
    hHeadIso hNBHead V F α (fun _ => rfl)
  rw [hInput] at hRec
  have hJT : IsGeoTestTower
      (MarkedIdeal.pullback (Subtype.val : V → (split H.tower r).1)
        (companionOf n (geoTransformAlong Q (head H.tower r)) o)) (restrict V (tail H.tower r)) := by
    have hQHead := ((isGeoTestTower_iff_head_tail Q H.tower r).mp hBaseTest).1
    rw [← compAt_eq_pullback hn o (head H.tower r)
      (isInvDomain_geoTransformAlong hQ (head H.tower r) hQHead)]
    exact hJTest
  rw [hRec] at hJT
  have hBF := isInvDomain_pullback_val F hBC
  have hRaw := (IsTowerIso.isGeoTestTower_iff α
    hBF.isWellFormed.isClosedSubmanifold_N hBF.isWellFormed.isCoherent hMaskIso).mp hJT
  have hNativeComp : nativePullback (Nat.le_succ n) P hP L = Bc := hComp o
  have hBWF : (nativePullback (Nat.le_succ n) P hP L).IsWellFormed :=
    hNativeComp.symm ▸ hBC.isWellFormed
  have hRawTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : F → _) Bc) (restrict F Nt) := hRaw
  rw [← hNativeComp] at hRawTest
  have hEN : A.E = boundary M.E (head T r) :=
    MarkedIdealEquivalence.MarkedIdeal.E_geoTransformAlong_eq
      (𝔪 := M) (𝔫 := (⟨univ,M.E,IdealWeightPowers.unitIdeal (n+1) _,1⟩ : MarkedIdeal (n+1) _))
      rfl (head T r)
  obtain ⟨hSNC, hTr⟩ := hHead.geometry (Nat.succ_pos n) hM.isWellFormed.isSNCDivisor hTrans
  have hLE : L.E = boundary M.E (head T r) := (companionAlong_E _ _ _ _ _ _).trans hEN
  have hLN : L.N ⊆ P :=
    (companionAlong_N _ _ _ _ _ _).symm ▸ Lift.current_carrier_subset hHead M hSupport
  have hAmbient := ambient_test_on_native_reference hTail (Nat.succ_pos n) hSNC hTr
    L hLE hLN hL.isWellFormed.isCoherent hBWF W hRawTest
  rw [← compAt_eq_pullback (Nat.succ_pos n) o (head T r) hA] at hAmbient
  exact hAmbient

end
end Hironaka.HironakaG1NormalOrderCanTransport
