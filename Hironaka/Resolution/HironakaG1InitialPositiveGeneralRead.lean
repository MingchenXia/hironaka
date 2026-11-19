import Hironaka.Resolution.HironakaG1InitialSelectedOrderPhase
import Hironaka.Invariant.GeneralCanonicalTail
import Hironaka.Invariant.StepOneEmptyPrefix

set_option autoImplicit false

open Set TopologicalSpace

namespace Hironaka.HironakaG1InitialPositiveGeneralRead
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerSplit MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec CanonicalCentres HomogenizedIdealAlong
  StepOneValue StepOneValueMasked StepOneRegime StepOneEmptyPrefix
  GeneralValue GeneralCanonicalTail NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime
  HironakaG1InitialSelectedOrderPhase HironakaG1PositiveNormalRepairCentres
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaActualOpenZeroSectionDifferentials

/-- The positive summand of an original successor recursive value. -/
def positiveSuccessorRead {k : ℕ} (o : ℕ) (v : ℕ ×ₗ WithTop (ValTy k)) : ValTy (k + 1) :=
  toLex (o, toLex (Sum.inr (v : WithTop (ℕ ×ₗ WithTop (ValTy k)))))

set_option maxHeartbeats 1400000 in
set_option backward.isDefEq.respectTransparency false in
/-- A canonical history of the literal initially selected lower record
reads its original successor invariant through its initial order companion.
The companion domain, maximal order, canonicality and endpoint are produced. -/
theorem original_initial_positive_lower_successor_read {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    (p : productOpen U)
    (hLevel : level (properNormalMarked Q)
      (.refl : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) _) p = s + 1) :
    let H := BlowupTower.refl (X := CMfd.of (n := n + 1) (productOpen U))
    let O := maskA (properNormalMarked Q) H p
    let X := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) X :=
      lowerMarkedM (X := CMfd.of (n := n + 1) (productOpen U)) (properNormalMarked Q) (s + 1) H p
    let J := compAt (X := X) L L.d (.refl : BlowupTower X X)
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower X X)) L.d
    let R := invFamily (Nat.succ_pos n) k
    ∀ {Y : CMfd.{0} (n + 1)} (T : BlowupTower X Y)
      (_hCan : IsCanonical L ((invFamily (Nat.succ_pos n) (k + 1)).inv L) T)
      (y : Y), y ∈ (geoTransformAlong L T).cosupp →
      ∃ hp : T.proj y ∈ C,
        let S := restrict C T
        let z : openPreimage T C := ⟨y, hp⟩
        IsInvDomain (k + 1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
        IsCanonical J (Seq.StepOneValueMasked.stepOneInvM R J) S ∧
        z ∈ (geoTransformAlong J S).cosupp ∧
        (invFamily (Nat.succ_pos n) (k + 1)).inv L T y =
          positiveSuccessorRead L.d (Seq.StepOneValueMasked.stepOneInvM R J S z) := by
  intro H O X L J C R Y T hCan y hy
  let hn := Nat.succ_pos n
  let F : ∀ {A : CMfd.{0} (n + 1)}, MarkedIdeal (n + 1) A →
      ∀ {B : CMfd.{0} (n + 1)}, BlowupTower A B → B → ℕ ×ₗ WithTop (ValTy k) :=
    fun {A} M {B} S z => Seq.StepOneValueMasked.stepOneInvM (X := A) R M (Y := B) S z
  have hL : IsInvDomain (k + 1) L := padded_lower_isInvDomain Q hQ H trivial p hLevel
  have hT := (invFamily hn (k + 1)).isInvValue.isGeoTestTower_of_isCanonical hL T hCan
  have hPhase := (original_initial_positive_lower_order_phase Q hQ p hLevel).2.2 T hT y hy
  have hOrder : nmOrd (geoTransformAlong L T) y = L.d := hPhase.1.2
  have hRun : regimeRun (OrdRegime L L.d) T y = T.length := hPhase.2
  have hPositive := hL.one_le_d
  have hCanF : IsCanonical L (genInv F L) T := hCan
  have hD := GeneralCanonicalTail.hasGenLowerData_of_isCanonical F
    (StepOneSeq.isMaxOrderValue_stepOneInvM (k := k + 1) R hn) hn hL T hT hCanF y hy L.d hOrder hPositive
  rw [hRun] at hD
  simp only [head, tail] at hD
  rw [split_of_length_le T T.length le_rfl] at hD
  obtain ⟨hp, hJ, hMax, hJCan, hz⟩ := hD
  refine ⟨hp, hJ, hMax, hJCan, hz, ?_⟩
  change genInv F L T y = positiveSuccessorRead L.d (F J (restrict C T) ⟨y, hp⟩)
  rw [genInv_of_nmOrd_ne_zero F L T hOrder (Nat.ne_of_gt hPositive), hRun]
  simp only [head, tail]
  rw [split_of_length_le T T.length le_rfl]
  rw [genLowerValue_eq_of_mem F L (o := L.d) (T₀ := (.refl : BlowupTower X X)) (T₁ := T) (y := y) hp]
  rfl

set_option maxHeartbeats 3000000 in
set_option backward.isDefEq.respectTransparency false in
private theorem upper_initial_lower_data {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y)
    (hRun : regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T y = T.length) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let R := invFamily (Nat.succ_pos n) (k + 1)
    let H := BlowupTower.refl (X := X)
    let O := maskA P H (T.proj y)
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H (T.proj y)
    level P H (T.proj y) = s + 1 ∧
    ∃ hp : T.proj y ∈ O,
      let S := restrict O T
      let z : openPreimage T O := ⟨y, hp⟩
      IsCanonical L (R.inv L) S ∧ z ∈ (geoTransformAlong L S).cosupp ∧
        Seq.StepOneValueMasked.stepOneInvM R P T y =
          toLex (s + 1, (R.inv L S z : WithTop (ValTy (k + 1)))) := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  let R := invFamily (Nat.succ_pos n) (k + 1)
  have hP := properNormalMarked_isInvDomain Q hQ
  have hMax := properNormalMarked_maximalOrder Q hQ.isWellFormed.isCoherent
  obtain ⟨hBarTest, _, hCos⟩ :=
    Seq.StepOneBridge.isGeoTestTower_of_isCanonical R P hP hMax (Nat.succ_pos n) T hCan
  have hyBar := hCos.symm ▸ hy
  have hData := Seq.StepOneAdmissible.hasLowerDataL_stepOneInvM_of_isCanonical (k := (k + 1) + 1)
    P R hP.isWellFormed hP.one_le_d (Nat.succ_pos n) hMax hP.dimLE T
    ((Seq.StepOneBridge.isCanonical_iff R P hP hMax (Nat.succ_pos n) T).mp hCan) y hyBar hNS
  have hReg := (stepRegime_and_mem_cosupp_head P hP.isWellFormed T hBarTest hyBar hNS).1
  rw [hLevel, hRun] at hData hReg
  simp only [head, tail] at hData hReg
  rw [split_of_length_le T T.length le_rfl] at hData hReg
  obtain ⟨hp, _, hLCan, hyL⟩ := hData
  refine ⟨hReg.1, hp, hLCan, hyL, ?_⟩
  unfold Seq.StepOneValueMasked.stepOneInvM Seq.StepOneValueMasked.stepOneInvL
  rw [if_neg hNS, hLevel, hRun]
  simp only [head, tail]
  rw [split_of_length_le T T.length le_rfl]
  unfold Seq.StepOneValueMasked.lowerValueL
  rw [dif_pos hp]
  rfl

set_option maxHeartbeats 1800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The original upper finite branch reads the positive successor value
of the initially selected lower tail, including its actual order companion
and recursive Step One value. The run premise identifies the upper cut. -/
theorem original_upper_initial_positive_successor_read {n k s : ℕ}
    {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U) (hQ : IsInvDomain (k + 1) Q)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hCan : IsCanonical (properNormalMarked Q)
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) (properNormalMarked Q)) T)
    (y : Y) (hy : y ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp)
    (hLevel : level (properNormalMarked Q) T y = s + 1)
    (hNS : ¬ IsSpecial (properNormalMarked Q) T y)
    (hRun : regimeRun (stepRegime (properNormalMarked Q) (s + 1)) T y = T.length) :
    let X := CMfd.of (n := n + 1) (productOpen U)
    let P := properNormalMarked Q
    let p := T.proj y
    let H := BlowupTower.refl (X := X)
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X) P (s + 1) H p
    let S := restrict O T
    let J := compAt (X := A) L L.d (.refl : BlowupTower A A)
    let C := ordMask (geoTransformAlong L (.refl : BlowupTower A A)) L.d
    let R := invFamily (Nat.succ_pos n) k
    level P H p = s + 1 ∧
    ∃ (hp : p ∈ O) (hq : S.proj (⟨y, hp⟩ : openPreimage T O) ∈ C),
      let z : openPreimage S C := ⟨(⟨y, hp⟩ : openPreimage T O), hq⟩
      let V := restrict C S
      IsCanonical L ((invFamily (Nat.succ_pos n) (k + 1)).inv L) S ∧
      IsInvDomain (k + 1) J ∧ IsMaximalOrderAlong J.N J.ideal J.d ∧
      IsCanonical J (Seq.StepOneValueMasked.stepOneInvM R J) V ∧
      z ∈ (geoTransformAlong J V).cosupp ∧
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T y =
        toLex (s + 1, (positiveSuccessorRead L.d (Seq.StepOneValueMasked.stepOneInvM R J V z) :
          WithTop (ValTy (k + 1)))) := by
  let X := CMfd.of (n := n + 1) (productOpen U)
  let P := properNormalMarked Q
  obtain ⟨hInitLevel, hp, hLCan, hyL, hRead⟩ :=
    upper_initial_lower_data Q hQ T hCan y hy hLevel hNS hRun
  let O := maskA P (.refl : BlowupTower X X) (T.proj y)
  let z : openPreimage T O := ⟨y, hp⟩
  obtain ⟨hq, hJ, hMaxJ, hJCan, hz, hv⟩ :=
    original_initial_positive_lower_successor_read Q hQ (T.proj y) hInitLevel
      (Y := CMfd.of (n := n + 1) (openPreimage T O)) (restrict O T) hLCan z hyL
  refine ⟨hInitLevel, hp, hq, hLCan, hJ, hMaxJ, hJCan, hz, ?_⟩
  exact hRead.trans
    (congrArg (fun v : ValTy (k + 1) => toLex (s + 1, (v : WithTop (ValTy (k + 1))))) hv)

end
end Hironaka.HironakaG1InitialPositiveGeneralRead
