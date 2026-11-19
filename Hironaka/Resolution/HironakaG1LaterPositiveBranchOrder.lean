import Hironaka.Resolution.HironakaG1LaterPositiveSuccessorRead

/-!
# Order of realized later positive branches

The order and companion are read at each anchor's own actual cuts.
The inner level is the companion's current level and may be positive.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1LaterPositiveBranchOrder

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  StepOneValue StepOneValueMasked StepOneRegime
  GeneralValue NonmonomialOrderLocal NonmonomialOrderTail NonmonomialOrderRegime
  HironakaG1InitialPositiveGeneralRead HironakaG1LaterPositiveSuccessorRead
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaActualOpenZeroSectionDifferentials

private theorem choose_actual_companion_value {n k : ℕ} (hn : 0 < n) {A B : CMfd.{0} n}
    (L : MarkedIdeal n A) (T : BlowupTower A B) (y : B) (o : ℕ)
    (R : ValTy (k + 1) → Prop)
    (h : PositiveOrderCompanionWitness (k := k) hn L T y o R) :
    ∃ v : ℕ ×ₗ WithTop (ValTy k), R (positiveSuccessorRead o v) ∧
      PositiveOrderCompanionWitness (k := k) hn L T y o
        (fun w => w = positiveSuccessorRead o v) := by
  obtain ⟨hp, hJ, hMax, hCan, hz, hRead⟩ := h
  let r := regimeRun (OrdRegime L o) T y
  let H := head T r
  let S := tail T r
  let W := ordMask (geoTransformAlong L H) o
  let J := compAt L o H
  let U := BlowupTowerTransforms.restrict W S
  let z : openPreimage S W := ⟨y, hp⟩
  let v := Seq.StepOneValueMasked.stepOneInvM (invFamily hn k) J U z
  exact ⟨v, hRead, hp, hJ, hMax, hCan, hz, rfl⟩

section Read

variable {n k s : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
  (y : Y)

local notation "X₀" => CMfd.of (n := n + 1) (productOpen U)
local notation "P" => properNormalMarked Q

/-- The current true order on the actual selected lower tail. The
endpoint is determined by its projection to the original upper point. -/
abbrev LaterPositiveOrderAt (s o : ℕ) : Prop :=
  let r := regimeRun (stepRegime P (s + 1)) T y
  let H := head T r
  let S := tail T r
  let p := S.proj y
  let O := maskA P H p
  let A := CMfd.of (n := n + 1) O
  let B := CMfd.of (n := n + 1) (openPreimage S O)
  let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X₀) P (s + 1) H p
  let V : BlowupTower A B := BlowupTowerTransforms.restrict O S
  ∀ z : openPreimage S O, z.val = y → nmOrd (geoTransformAlong (X := A) (Y := B) L V) z = o

/-- A realized positive branch, retaining its actual selected lower tail
and its actual current order companion. -/
structure LaterPositiveRead (k s : ℕ) where
  order : ℕ
  order_pos : 0 < order
  companion : ℕ ×ₗ WithTop (ValTy k)
  realized :
    let r := regimeRun (stepRegime P (s + 1)) T y
    let H := head T r
    let S := tail T r
    let p := S.proj y
    let O := maskA P H p
    let A := CMfd.of (n := n + 1) O
    let B := CMfd.of (n := n + 1) (openPreimage S O)
    let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X₀) P (s + 1) H p
    let V : BlowupTower A B := BlowupTowerTransforms.restrict O S
    ∃ hp : p ∈ O,
      let z : openPreimage S O := ⟨y, hp⟩
      IsCanonical L ((invFamily (Nat.succ_pos n) (k + 1)).inv L) V ∧
        nmOrd (geoTransformAlong (X := A) (Y := B) L V) z = order ∧
        PositiveOrderCompanionWitness (k := k) (Nat.succ_pos n) (X := A) (Y := B) L V z order
          (fun v => v = positiveSuccessorRead order companion)
  raw_upper : Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T y =
    toLex (s + 1, (positiveSuccessorRead order companion : WithTop (ValTy (k + 1))))

set_option maxHeartbeats 900000 in
/-- The actual positive successor-read producer supplies the three
comparison coordinates. The run may start at any actual cut. -/
theorem exists_laterPositiveRead (hQ : IsInvDomain (k + 1) Q)
    (hCan : IsCanonical P
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P) T)
    (hy : y ∈ (geoTransformAlong P T).cosupp) (hLevel : level P T y = s + 1)
    (hNS : ¬ IsSpecial P T y) (o : ℕ) (ho : 0 < o)
    (hOrder : LaterPositiveOrderAt Q T y s o) :
    ∃ F : LaterPositiveRead Q T y k s, F.order = o := by
  obtain ⟨hp, hCanL, hComp⟩ :=
    original_upper_positive_successor_read Q hQ T hCan y hy hLevel hNS o ho hOrder
  let r := regimeRun (stepRegime P (s + 1)) T y
  let H := head T r
  let S := tail T r
  let p := S.proj y
  let O := maskA P H p
  let A := CMfd.of (n := n + 1) O
  let B := CMfd.of (n := n + 1) (openPreimage S O)
  let L : MarkedIdeal (n + 1) A := lowerMarkedM (X := X₀) P (s + 1) H p
  let V : BlowupTower A B := BlowupTowerTransforms.restrict O S
  let z : openPreimage S O := ⟨y, hp⟩
  let read (v : ValTy (k + 1)) : Prop :=
    Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T y =
      toLex (s + 1, (v : WithTop (ValTy (k + 1))))
  obtain ⟨v, hRaw, hReal⟩ :=
    choose_actual_companion_value (Nat.succ_pos n) (A := A) (B := B) L V z o read hComp
  exact ⟨⟨o, ho, v, ⟨hp, hCanL, hOrder z rfl, hReal⟩, hRaw⟩, rfl⟩

end Read

section Order

variable {n₁ n₂ k s : ℕ} {U₁ : Opens (ComplexModel n₁)} {U₂ : Opens (ComplexModel n₂)}
  {Q₁ : MarkedIdeal n₁ U₁} {Q₂ : MarkedIdeal n₂ U₂}
  {Y₁ : CMfd.{0} (n₁ + 1)} {Y₂ : CMfd.{0} (n₂ + 1)}
  {T₁ : BlowupTower (CMfd.of (n := n₁ + 1) (productOpen U₁)) Y₁}
  {T₂ : BlowupTower (CMfd.of (n := n₂ + 1) (productOpen U₂)) Y₂}
  {y₁ : Y₁} {y₂ : Y₂}
  (F₁ : LaterPositiveRead Q₁ T₁ y₁ k s) (F₂ : LaterPositiveRead Q₂ T₂ y₂ k s)

local notation "a₁" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n₁) (k + 1))
  (properNormalMarked Q₁) T₁ y₁
local notation "a₂" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n₂) (k + 1))
  (properNormalMarked Q₂) T₂ y₂

private theorem successorRead_lt_iff {q : ℕ} (o₁ o₂ : ℕ) (v₁ v₂ : ℕ ×ₗ WithTop (ValTy q)) :
    positiveSuccessorRead o₁ v₁ < positiveSuccessorRead o₂ v₂ ↔
      o₁ < o₂ ∨ o₁ = o₂ ∧ v₁ < v₂ := by
  change toLex (o₁, toLex (Sum.inr (v₁ : WithTop (ℕ ×ₗ WithTop (ValTy q))))) <
    toLex (o₂, toLex (Sum.inr (v₂ : WithTop (ℕ ×ₗ WithTop (ValTy q))))) ↔ _
  rw [Prod.Lex.toLex_lt_toLex, Sum.Lex.inr_lt_inr_iff, WithTop.coe_lt_coe]

/-- On a tied original positive level, strict comparison uses the true
current selected order, then the actual companion level, then its current
leaf. The two chronological cuts and ambient dimensions are independent. -/
theorem LaterPositiveRead.upper_lt_iff :
    a₁ < a₂ ↔
      F₁.order < F₂.order ∨ F₁.order = F₂.order ∧
        ((ofLex F₁.companion).1 < (ofLex F₂.companion).1 ∨
          (ofLex F₁.companion).1 = (ofLex F₂.companion).1 ∧
            (ofLex F₁.companion).2 < (ofLex F₂.companion).2) := by
  rw [F₁.raw_upper, F₂.raw_upper, Prod.Lex.toLex_lt_toLex, WithTop.coe_lt_coe]
  simp only [lt_self_iff_false, true_and, false_or, successorRead_lt_iff]
  exact or_congr Iff.rfl (and_congr Iff.rfl Prod.Lex.lt_iff)

/-- On a shared true order and actual companion level, comparison is
exactly comparison of the current leaves. The companion level is
unrestricted. -/
theorem LaterPositiveRead.upper_leaf_order_iff
    (hOrder : F₁.order = F₂.order)
    (hLevel : (ofLex F₁.companion).1 = (ofLex F₂.companion).1) :
    (a₁ < a₂ ↔ (ofLex F₁.companion).2 < (ofLex F₂.companion).2) ∧
      (a₁ ≤ a₂ ↔ (ofLex F₁.companion).2 ≤ (ofLex F₂.companion).2) ∧
      (a₁ = a₂ ↔ (ofLex F₁.companion).2 = (ofLex F₂.companion).2) := by
  have hLt : a₁ < a₂ ↔ (ofLex F₁.companion).2 < (ofLex F₂.companion).2 := by
    simpa only [hOrder, hLevel, lt_self_iff_false, true_and, false_or] using
      LaterPositiveRead.upper_lt_iff F₁ F₂
  have hLtRev : a₂ < a₁ ↔ (ofLex F₂.companion).2 < (ofLex F₁.companion).2 := by
    simpa only [hOrder, hLevel, lt_self_iff_false, true_and, false_or] using
      LaterPositiveRead.upper_lt_iff F₂ F₁
  have hLe : a₁ ≤ a₂ ↔ (ofLex F₁.companion).2 ≤ (ofLex F₂.companion).2 := by
    simpa only [not_lt] using not_congr hLtRev
  have hLeRev : a₂ ≤ a₁ ↔ (ofLex F₂.companion).2 ≤ (ofLex F₁.companion).2 := by
    simpa only [not_lt] using not_congr hLt
  exact ⟨hLt, hLe, le_antisymm_iff.trans ((and_congr hLe hLeRev).trans le_antisymm_iff.symm)⟩

/-- A higher actual companion level wins at a tied true order regardless
of the leaves. -/
theorem LaterPositiveRead.upper_lt_of_companion_level_lt
    (hOrder : F₁.order = F₂.order)
    (hLevel : (ofLex F₁.companion).1 < (ofLex F₂.companion).1) :
    a₁ < a₂ :=
  (LaterPositiveRead.upper_lt_iff F₁ F₂).mpr (Or.inr ⟨hOrder, Or.inl hLevel⟩)

/-- A finite leaf is strictly below a top leaf at the same actual
companion level and true selected order, including positive levels. -/
theorem LaterPositiveRead.upper_lt_of_finite_top
    (hOrder : F₁.order = F₂.order)
    (hLevel : (ofLex F₁.companion).1 = (ofLex F₂.companion).1)
    (hFinite : (ofLex F₁.companion).2 ≠ ⊤) (hTop : (ofLex F₂.companion).2 = ⊤) :
    a₁ < a₂ := by
  apply (LaterPositiveRead.upper_leaf_order_iff F₁ F₂ hOrder hLevel).1.mpr
  rw [hTop]
  exact lt_top_iff_ne_top.mpr hFinite

end Order

end

end Hironaka.HironakaG1LaterPositiveBranchOrder
