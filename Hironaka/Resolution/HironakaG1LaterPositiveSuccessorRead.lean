import Hironaka.Resolution.HironakaG1InitialPositiveGeneralRead
import Hironaka.Resolution.HironakaG1PositiveNormalPhase

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.HironakaG1LaterPositiveSuccessorRead
noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong
  StepOneValue StepOneValueMasked StepOneRegime
  GeneralValue GeneralCanonicalTail NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime
  HironakaG1InitialPositiveGeneralRead HironakaG1PositiveNormalPhase
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaActualOpenZeroSectionDifferentials

set_option backward.isDefEq.respectTransparency false in
/-- The actual companion at the positive order-run cut and the resulting
original successor value. -/
abbrev PositiveOrderCompanionWitness {n k : ℕ} (hn : 0 < n) {X Y : CMfd.{0} n}
    (L : MarkedIdeal n X) (T : BlowupTower X Y) (y : Y) (o : ℕ)
    (Read : ValTy (k + 1) → Prop) : Prop :=
    let r := regimeRun (OrdRegime L o) T y
    let H := head T r
    let S := tail T r
    let O := ordMask (geoTransformAlong L H) o
    let J := compAt L o H
    ∃ hp : S.proj y ∈ O,
      let U := restrict O S
      let z : openPreimage S O := ⟨y, hp⟩
      IsInvDomain (k + 1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J) U ∧
      z ∈ (geoTransformAlong J U).cosupp ∧
      Read (positiveSuccessorRead o (Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J U z))

set_option maxHeartbeats 900000 in
set_option backward.isDefEq.respectTransparency false in
/-- Read the original successor invariant at the actual start of the
positive order run of a canonical lower history. -/
theorem original_positive_order_successor_read {n k : ℕ} (hn : 0 < n)
    {X Y : CMfd.{0} n} (L : MarkedIdeal n X) (hL : IsInvDomain (k + 1) L)
    (T : BlowupTower X Y) (hCan : IsCanonical L ((invFamily hn (k + 1)).inv L) T)
    (y : Y) (hy : y ∈ (geoTransformAlong L T).cosupp) (o : ℕ)
    (hOrder : nmOrd (geoTransformAlong L T) y = o) (ho : 0 < o) :
    PositiveOrderCompanionWitness (k := k) hn L T y o
      (fun v => (invFamily hn (k + 1)).inv L T y = v) := by
  let R := invFamily hn k
  let F : ∀ {A : CMfd.{0} n}, MarkedIdeal n A →
      ∀ {B : CMfd.{0} n}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy k) :=
    fun {A} M {B} S z => Seq.StepOneValueMasked.stepOneInvM (X := A) R M (Y := B) S z
  let r := regimeRun (OrdRegime L o) T y
  let H := head T r
  let S := tail T r
  have hTest := (invFamily hn (k + 1)).isInvValue.isGeoTestTower_of_isCanonical hL T hCan
  have hCanF : IsCanonical L (genInv F L) T := hCan
  obtain ⟨hp, hJ, hMax, hJCan, hz⟩ := GeneralCanonicalTail.hasGenLowerData_of_isCanonical F
    (StepOneSeq.isMaxOrderValue_stepOneInvM (k := k + 1) R hn) hn hL T hTest hCanF
    y hy o hOrder ho
  refine ⟨hp, hJ, hMax, hJCan, hz, ?_⟩
  change genInv F L T y = positiveSuccessorRead o
    (F (compAt L o H) (restrict (ordMask (geoTransformAlong L H) o) S) ⟨y, hp⟩)
  rw [genInv_of_nmOrd_ne_zero F L T hOrder (Nat.ne_of_gt ho)]
  rw [genLowerValue_eq_of_mem F L (o := o) (T₀ := H) (T₁ := S) (y := y) hp]
  rfl

set_option maxHeartbeats 1700000 in
set_option backward.isDefEq.respectTransparency false in
/-- The upper finite positive Step One value reads the successor
invariant on its literal selected lower tail at any original upper cut.
Positive order is required at the lower endpoint itself. -/
theorem original_upper_positive_successor_read {n k s : ℕ}
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
    ∀ o : ℕ, 0 < o →
      (∀ w : openPreimage S O, w.val = y → nmOrd (geoTransformAlong (X := A) (Y := Z) L T') w = o) →
      ∃ hp : p ∈ O,
        let z : openPreimage S O := ⟨y, hp⟩
        IsCanonical L ((invFamily (Nat.succ_pos n) (k + 1)).inv L) T' ∧
        PositiveOrderCompanionWitness (k := k) (Nat.succ_pos n) L T' z o
          (fun v => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T y =
            toLex (s + 1, (v : WithTop (ValTy (k + 1))))) := by
  intro X P r H S p O A L Z T' o ho hOrder
  obtain ⟨_, _, _, _, hp, _, hL, hLCan, hz⟩ :=
    original_normal_positive_phase_head Q hQ T hCan y hy hLevel hNS
  let z : openPreimage S O := ⟨y, hp⟩
  have hzOrder := hOrder z rfl
  obtain ⟨hq, hJ, hMaxJ, hJCan, hw, hv⟩ :=
    original_positive_order_successor_read (k := k) (Nat.succ_pos n) (X := A)
      (Y := CMfd.of (n := n + 1) (openPreimage S O)) L hL T' hLCan z hz o hzOrder ho
  refine ⟨hp, hLCan, hq, hJ, hMaxJ, hJCan, hw, ?_⟩
  let R := invFamily (Nat.succ_pos n) (k + 1)
  have hUpper : Seq.StepOneValueMasked.stepOneInvM R P T y =
      toLex (s + 1, (R.inv L T' z : WithTop (ValTy (k + 1)))) := by
    have hp' : (tail T (regimeRun (stepRegime P (s + 1)) T y)).proj y ∈
        lowerMask P (s + 1) (head T (regimeRun (stepRegime P (s + 1)) T y))
          ((tail T (regimeRun (stepRegime P (s + 1)) T y)).proj y) := hp
    unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
    rw [if_neg hNS, hLevel]
    unfold Seq.StepOneValueMasked.lowerValueL
    rw [dif_pos hp']
    rfl
  exact hUpper.trans
    (congrArg (fun v : ValTy (k + 1) => toLex (s + 1, (v : WithTop (ValTy (k + 1))))) hv)

end
end Hironaka.HironakaG1LaterPositiveSuccessorRead
