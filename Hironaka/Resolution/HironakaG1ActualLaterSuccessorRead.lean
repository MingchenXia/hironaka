import Hironaka.Resolution.HironakaG1LaterSelectedActualOrder
import Hironaka.Resolution.HironakaG1LaterPositiveSuccessorRead
import Hironaka.Resolution.HironakaG3RRawRegimeLocality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1ActualLaterSuccessorRead
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism
  ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong
  StepOneValue StepOneValueMasked StepOneRegime
  NonmonomialOrderLocal HironakaG3RRawRegimeLocality
  HironakaG1LaterSelectedActualOrder HironakaG1LaterPositiveSuccessorRead
  HironakaG1PositiveNormalPhase HironakaActualOpenZeroSectionDifferentials
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  InvDomainMemberRestriction BoundaryCount RelativePrincipalizationSpan

set_option maxHeartbeats 900000 in
/-- Order on a canonical open restriction can be read on a smaller
actual restriction through the same endpoint. The ambient record only
needs a coherent ideal. -/
theorem order_of_canonical_restriction_of_test_window {n q : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (K : MarkedIdeal n X) (hK : K.ideal.IsCoherent)
    {O W : Opens X} (hWO : W ≤ O) (S : BlowupTower X Y)
    (hL : IsInvDomain q (MarkedIdeal.pullback (Subtype.val : O → X) K))
    (hCan : IsCanonical (MarkedIdeal.pullback (Subtype.val : O → X) K)
      ((invFamily hn q).inv (MarkedIdeal.pullback (Subtype.val : O → X) K)) (restrict O S))
    (y : openPreimage S O) (hyW : S.proj y.val ∈ W)
    (hy : y ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) K) (restrict O S)).cosupp)
    (o : ℕ)
    (hOrder : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → X) K) (restrict W S) →
      ∀ z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) K) (restrict W S)).cosupp,
        nmOrd (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) K) (restrict W S)) z = o) :
    nmOrd (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : O → X) K) (restrict O S)) y = o := by
  let R := invFamily hn q
  obtain ⟨hW, hWCan, _⟩ := Seq.MaxLocusLocal.restrict_nestedOpens R hK hWO hL S hCan
  have hTestW := R.isInvValue.isGeoTestTower_of_isCanonical hW (restrict W S) hWCan
  have hHol : ∀ p f, K.ideal.mem p f → HolomorphicAt n f p :=
    fun _ _ hf => GermIdeal.IsCoherent.holomorphicAt_mem hK hf
  have hSpan : ∀ p f, IsInSpanAt (n := n) (K.ideal.mem p) p f → K.ideal.mem p f :=
    fun _ _ hf => GermIdealTotalTransform.mem_of_isInSpanAt_mem hK hf
  let z : openPreimage S W := ⟨y.val, hyW⟩
  rw [cosupp_restrict_raw K hHol O S] at hy
  have hz : z ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) K) (restrict W S)).cosupp := by
    rw [cosupp_restrict_raw K hHol W S]
    exact hy
  have hOrderW := hOrder hTestW z hz
  exact (nmOrd_restrict_raw K hHol hSpan O S y).trans
    ((nmOrd_restrict_raw K hHol hSpan W S z).symm.trans hOrderW)

set_option maxHeartbeats 1800000 in
/-- The actual selected lower endpoint of a positive nonspecial canonical
upper history has raw order equal to its true coefficient mark. The
actual contact subwindow is used only to prove the full-mask order. -/
theorem original_upper_positive_lower_raw_mark {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H p
    let Z := CMfd.of (n := n + 1) (openPreimage S O)
    let T' : BlowupTower A Z := restrict O S
    0 < L.d ∧ (∀ z : openPreimage S O, z.val = y →
      nmOrd (geoTransformAlong (X := A) (Y := Z) L T') z = L.d) := by
  intro X P r H S p O A L Z T'
  let R := invFamily (Nat.succ_pos n) (k + 1)
  have hP := properNormalMarked_isInvDomain Q hQ
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  obtain ⟨hBarTest, hTest, hCos⟩ :=
    Seq.StepOneBridge.isGeoTestTower_of_isCanonical R P hP hMax (Nat.succ_pos n) T hCan
  have hyBar := hCos.symm ▸ hy
  obtain ⟨hReg, hpBar⟩ :=
    stepRegime_and_mem_cosupp_head P hP.isWellFormed T hBarTest hyBar hNS
  rw [hLevel] at hReg hpBar
  have hHeadTest := ((isGeoTestTower_iff_head_tail P T r).mp hTest).1
  obtain ⟨W, _, hpW, hWO, _, _, _, _, hOrderW⟩ :=
    exists_later_selected_actual_normal_order Q hQ H hHeadTest p hpBar hReg.1 hReg.2
  obtain ⟨_, _, _, _, hpO, _, hL, hLCan, hyL⟩ :=
    original_normal_positive_phase_head Q hQ T hCan y hy hLevel hNS
  let B := geoTransformAlong (barMarked P) H
  let K := memberRestrict B (membersThrough B.E (origMembers P H) p)
  have hB : B.IsWellFormed := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (StepOneLowerDomain.isWellFormed_barMarked P hP.isWellFormed) H
      ((isGeoTestTower_iff_head_tail (barMarked P) T r).mp hBarTest).1
  have hK : K.IsWellFormed := isWellFormed_memberRestrict (Nat.succ_pos n) hB _
  let z : openPreimage S O := ⟨y, hpO⟩
  have hOrder : nmOrd (geoTransformAlong L T') z = L.d :=
    order_of_canonical_restriction_of_test_window (Nat.succ_pos n) K hK.isCoherent hWO S
      hL hLCan z hpW hyL L.d (hOrderW (restrict W S))
  refine ⟨hL.one_le_d, fun w hw => ?_⟩
  have heq : w = z := Subtype.ext hw
  exact heq.symm ▸ hOrder

set_option maxHeartbeats 1400000 in
/-- The literal full-mask upper finite successor read at its actual
companion cut, with the true positive order derived internally. -/
theorem original_upper_positive_successor_at_true_mark {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H p
    let Z := CMfd.of (n := n + 1) (openPreimage S O)
    let T' : BlowupTower A Z := restrict O S
    ∃ hp : p ∈ O,
        let z : openPreimage S O := ⟨y, hp⟩
        IsCanonical L ((invFamily (Nat.succ_pos n) (k + 1)).inv L) T' ∧
        PositiveOrderCompanionWitness (k := k) (Nat.succ_pos n) L T' z L.d
          (fun v => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T y =
            toLex (s + 1, (v : WithTop (ValTy (k + 1))))) := by
  intro X P r H S p O A L Z T'
  obtain ⟨hPos, hOrd⟩ := original_upper_positive_lower_raw_mark Q hQ T hCan y hy hLevel hNS
  exact original_upper_positive_successor_read Q hQ T hCan y hy hLevel hNS L.d hPos hOrd

end
end Hironaka.HironakaG1ActualLaterSuccessorRead
