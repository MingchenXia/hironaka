import Hironaka.Resolution.HironakaG1InitialPositiveGeneralRead
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical

/-!
# Order and centre comparison at two positive initial cuts

Each finite padded value reads the genuine companion of its own initial
selected cut. A common-mark comparison on the companion side transfers
orders to normalized companion records at a possibly different mark.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG1InitialPositiveFiniteCentres

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres
  HomogenizedIdealAlong StepOneValue StepOneValueMasked StepOneRegime
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG1ProperCarrierNormalContact
  HironakaG1InitialPositiveGeneralRead HironakaG1InitialSelectedOrderPhase HironakaActualOpenZeroSectionDifferentials
  HironakaG1OriginalUnequalMarkCanonical HironakaG1OriginalTwoPairCanonicalCuts
  HironakaG1OriginalMaxOrderTwoPairCuts HironakaG11InvBMClass HironakaG8LocalHistory
  MarkedIdealEquivalence.MarkedIdeal DivisorExponentAlong GeneralValue NonmonomialOrderTail
  CompanionRebase

section Reads

variable {n k s : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
  {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
  (y : Y)

local notation "X₀" => CMfd.of (n := n + 1) (productOpen U)
local notation "P" => properNormalMarked Q
local notation "I" => BlowupTower.refl (X := X₀)

abbrev initialMask : Opens X₀ := maskA (X := X₀) P I (T.proj y)

abbrev initialSelected (s : ℕ) :
    MarkedIdeal (n + 1) (CMfd.of (n := n + 1) (initialMask Q T y)) :=
  lowerMarkedM (X := X₀) P (s + 1) I (T.proj y)

abbrev initialCompanionMask (s : ℕ) :=
  ordMask (M := CMfd.of (n := n + 1) (initialMask Q T y))
    (initialSelected Q T y s) (initialSelected Q T y s).d

abbrev initialCompanion (s : ℕ) :
    MarkedIdeal (n + 1) (CMfd.of (n := n + 1) (initialCompanionMask Q T y s)) :=
  compAt (X := CMfd.of (n := n + 1) (initialMask Q T y))
    (initialSelected Q T y s) (initialSelected Q T y s).d .refl

abbrev initialCompanionTower (s : ℕ) :=
  BlowupTowerTransforms.restrict (initialCompanionMask Q T y s) (BlowupTowerTransforms.restrict (initialMask Q T y) T)

/-- The actual finite read at an initial cut, on the literal restricted
tower and companion point supplied by the original general read. -/
structure InitialFiniteRead (k s : ℕ) where
  initial_level : level P I (T.proj y) = s + 1
  head_mem : T.proj y ∈ initialMask Q T y
  companion_mem : (restrict (initialMask Q T y) T).proj
    (⟨y, head_mem⟩ : openPreimage T (initialMask Q T y)) ∈ initialCompanionMask Q T y s
  domain : IsInvDomain (k + 1) (initialCompanion Q T y s)
  maximal : IsMaximalOrderAlong (initialCompanion Q T y s).N
    (initialCompanion Q T y s).ideal (initialCompanion Q T y s).d
  canonical : IsCanonical (initialCompanion Q T y s)
    (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) (initialCompanion Q T y s))
    (initialCompanionTower Q T y s)
  cosupp : (⟨⟨y, head_mem⟩, companion_mem⟩ : openPreimage
    (restrict (initialMask Q T y) T) (initialCompanionMask Q T y s)) ∈
    (geoTransformAlong (initialCompanion Q T y s) (initialCompanionTower Q T y s)).cosupp
  upper_eq : Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T y =
    toLex (s + 1, (positiveSuccessorRead (initialSelected Q T y s).d
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k)
        (initialCompanion Q T y s) (initialCompanionTower Q T y s)
        ⟨⟨y, head_mem⟩, companion_mem⟩) : WithTop (ValTy (k + 1))))

variable {Q T y} in
abbrev InitialFiniteRead.point (F : InitialFiniteRead Q T y k s) :
    openPreimage (restrict (initialMask Q T y) T) (initialCompanionMask Q T y s) :=
  ⟨⟨y, F.head_mem⟩, F.companion_mem⟩

variable {Q T y} in
abbrev InitialFiniteRead.value (F : InitialFiniteRead Q T y k s) :
    ℕ ×ₗ WithTop (ValTy k) :=
  Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k)
    (initialCompanion Q T y s) (initialCompanionTower Q T y s) F.point

set_option backward.isDefEq.respectTransparency false in
/-- Produce the actual finite read from a canonical padded history
whose positive run starts at the initial stage. -/
theorem exists_initialFiniteRead (hQ : IsInvDomain (k + 1) Q)
    (hCan : IsCanonical P
      (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P) T)
    (hy : y ∈ (geoTransformAlong P T).cosupp) (hLevel : level P T y = s + 1)
    (hNS : ¬ IsSpecial P T y)
    (hRun : regimeRun (stepRegime P (s + 1)) T y = T.length) :
    Nonempty (InitialFiniteRead Q T y k s) := by
  obtain ⟨hInit, hp, hq, _, hDom, hMax, hCanJ, hz, hRead⟩ :=
    original_upper_initial_positive_successor_read Q hQ T hCan y hy hLevel hNS hRun
  exact ⟨⟨hInit, hp, hq, hDom, hMax, hCanJ, hz, hRead⟩⟩

private theorem initialSelected_mark (s : ℕ) :
    (initialSelected Q T y s).d = (coeffMarkedAlong (barMarked (X := X₀) P)).d :=
  rfl

private theorem compAt_refl_mark {d : ℕ} {A : CMfd.{0} d} (D : MarkedIdeal d A) :
    (compAt (X := A) D D.d (.refl : BlowupTower A A)).d = D.d := by
  simp only [compAt, companionOf, companionAlong_d, geoTransformAlong_refl,
    MarkedIdealBiholomorphism.MarkedIdeal.pullback, lt_self_iff_false, if_false]

private theorem initialCompanion_mark (s : ℕ) :
    (initialCompanion Q T y s).d = (coeffMarkedAlong (barMarked (X := X₀) P)).d :=
  (compAt_refl_mark (initialSelected Q T y s)).trans (initialSelected_mark Q T y s)

/-- A normalized comparison record on the actual initial companion source.
The normalization preserves the weak class and weighted boundary exponents.
Its mark can differ from the literal companion's mark. -/
structure InitialNormalizedCompanion (k s : ℕ) where
  record : MarkedIdeal (n + 1) (CMfd.of (n := n + 1) (initialCompanionMask Q T y s))
  domain : IsInvDomain (k + 1) record
  maximal : IsMaximalOrderAlong record.N record.ideal record.d
  class_eq : LocWPEquiv (initialCompanion Q T y s) record
  same_dim : SameCarrierDim (initialCompanion Q T y s) record
  weighted_exponents : ∀ H ∈ (initialCompanion Q T y s).E,
    ∀ x ∈ (initialCompanion Q T y s).cosupp, x ∈ H →
      record.d * divExpAlong (n + 1) (initialCompanion Q T y s).N (initialCompanion Q T y s).ideal H x =
        (initialCompanion Q T y s).d * divExpAlong (n + 1) record.N record.ideal H x
  canonical : IsCanonical record
    (Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) record)
    (initialCompanionTower Q T y s)

variable {Q T y} in
abbrev InitialNormalizedCompanion.value (G : InitialNormalizedCompanion Q T y k s)
    (F : InitialFiniteRead Q T y k s) : ℕ ×ₗ WithTop (ValTy k) :=
  Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) k) G.record
    (initialCompanionTower Q T y s) F.point

end Reads

private theorem strictMono_positiveSuccessorRead {k : ℕ} (o : ℕ) :
    StrictMono (positiveSuccessorRead (k := k) o) := by
  intro u v huv
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inr
    ⟨rfl, Sum.Lex.inr_lt_inr_iff.mpr (WithTop.coe_lt_coe.mpr huv)⟩)

section Paired

variable {n k s : ℕ} {U : Opens (ComplexModel n)} {Q : MarkedIdeal n U}
  {Y₁ Y₂ : CMfd.{0} (n + 1)}
  {T₁ : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y₁}
  {T₂ : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y₂}
  {y₁ : Y₁} {y₂ : Y₂}
  (F₁ : InitialFiniteRead Q T₁ y₁ k s) (F₂ : InitialFiniteRead Q T₂ y₂ k s)

local notation "R" => invFamily (Nat.succ_pos n) k
local notation "P" => properNormalMarked Q
local notation "J₁" => initialCompanion Q T₁ y₁ s
local notation "J₂" => initialCompanion Q T₂ y₂ s
local notation "S₁" => initialCompanionTower Q T₁ y₁ s
local notation "S₂" => initialCompanionTower Q T₂ y₂ s
local notation "a₁" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T₁ y₁
local notation "a₂" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T₂ y₂

/-- At two realized initial cuts of the same positive level, the original
upper comparison reads exactly the two actual companion values. -/
theorem InitialFiniteRead.upper_lt_iff :
    a₁ < a₂ ↔ F₁.value < F₂.value := by
  have hMark := (initialSelected_mark Q T₁ y₁ s).trans (initialSelected_mark Q T₂ y₂ s).symm
  rw [F₁.upper_eq, F₂.upper_eq, hMark]
  let embed (v : ℕ ×ₗ WithTop (ValTy k)) : ℕ ×ₗ WithTop (ValTy (k + 1)) :=
    toLex (s + 1, (positiveSuccessorRead (initialSelected Q T₂ y₂ s).d v : WithTop (ValTy (k + 1))))
  have hEmbed : StrictMono embed := fun _ _ h => Prod.Lex.toLex_lt_toLex.mpr
    (Or.inr ⟨rfl, WithTop.coe_lt_coe.mpr (strictMono_positiveSuccessorRead _ h)⟩)
  exact hEmbed.lt_iff_lt

set_option maxHeartbeats 600000 in
/-- The two actual upper reads have the same strict comparison as their
normalized companions. The normalization need only have a common mark
across the two anchors. -/
theorem InitialFiniteRead.upper_lt_iff_normalized
    (G₁ : InitialNormalizedCompanion Q T₁ y₁ k s)
    (G₂ : InitialNormalizedCompanion Q T₂ y₂ k s) (hMark : G₁.record.d = G₂.record.d) :
    a₁ < a₂ ↔ G₁.value F₁ < G₂.value F₂ := by
  have hCuts : CanonicalMaxOrderTwoPairCuts (n := n + 1) (k + 1)
      (fun {A} J {B} S y => Seq.StepOneValueMasked.stepOneInvM (X := A) R J (Y := B) S y) :=
    canonicalMaxOrderTwoPairCuts_stepOneInvM (k := k + 1) (Nat.succ_pos n) R
      (canonicalTwoPairCuts_invFamily (Nat.succ_pos n) k)
  have hOriginalMark := (initialCompanion_mark Q T₁ y₁ s).trans (initialCompanion_mark Q T₂ y₂ s).symm
  refine (InitialFiniteRead.upper_lt_iff F₁ F₂).trans ?_
  exact hCuts J₁ G₁.record J₂ G₂.record F₁.domain G₁.domain F₂.domain G₂.domain
    G₁.class_eq G₁.same_dim G₁.weighted_exponents G₂.class_eq G₂.same_dim G₂.weighted_exponents
    hOriginalMark hMark F₁.maximal G₁.maximal F₂.maximal G₂.maximal
    S₁ S₂ F₁.canonical G₁.canonical F₂.canonical G₂.canonical
    F₁.point F₁.cosupp F₂.point F₂.cosupp

/-- Selecting the larger of the two actual anchors uses weak comparison
and treats ties identically before and after normalization. -/
theorem InitialFiniteRead.upper_order_iff_normalized
    (G₁ : InitialNormalizedCompanion Q T₁ y₁ k s)
    (G₂ : InitialNormalizedCompanion Q T₂ y₂ k s) (hMark : G₁.record.d = G₂.record.d) :
    (a₁ < a₂ ↔ G₁.value F₁ < G₂.value F₂) ∧
      (a₁ ≤ a₂ ↔ G₁.value F₁ ≤ G₂.value F₂) ∧
      (a₁ = a₂ ↔ G₁.value F₁ = G₂.value F₂) := by
  have h := InitialFiniteRead.upper_lt_iff_normalized F₁ F₂ G₁ G₂ hMark
  have hRev := InitialFiniteRead.upper_lt_iff_normalized F₂ F₁ G₂ G₁ hMark.symm
  have hLe : a₁ ≤ a₂ ↔ G₁.value F₁ ≤ G₂.value F₂ := by
    simpa only [not_lt] using not_congr hRev
  have hLeRev : a₂ ≤ a₁ ↔ G₂.value F₂ ≤ G₁.value F₁ := by
    simpa only [not_lt] using not_congr h
  exact ⟨h, hLe, le_antisymm_iff.trans ((and_congr hLe hLeRev).trans le_antisymm_iff.symm)⟩

/-- The maximum selector on the two labelled actual anchors. False is
the first anchor and true is the second. -/
theorem InitialFiniteRead.two_anchor_maxLocus_normalized
    (G₁ : InitialNormalizedCompanion Q T₁ y₁ k s)
    (G₂ : InitialNormalizedCompanion Q T₂ y₂ k s) (hMark : G₁.record.d = G₂.record.d) :
    maxLocus (fun b : Bool => if b then a₂ else a₁) univ =
      maxLocus (fun b : Bool => if b then G₂.value F₂ else G₁.value F₁) univ := by
  have hLe := (InitialFiniteRead.upper_order_iff_normalized F₁ F₂ G₁ G₂ hMark).2.1
  have hRev := (InitialFiniteRead.upper_order_iff_normalized F₂ F₁ G₂ G₁ hMark.symm).2.1
  have hPair (a b : Bool) :
      (if a then a₂ else a₁) ≤ (if b then a₂ else a₁) ↔
        (if a then G₂.value F₂ else G₁.value F₁) ≤ (if b then G₂.value F₂ else G₁.value F₁) := by
    cases a <;> cases b <;> simp [hLe, hRev]
  ext b
  exact and_congr Iff.rfl (forall_congr' fun a => imp_congr_right fun _ => hPair a b)

end Paired

/-- When both anchors are on the same current stage, the normalized
selector has exactly the original two-point maximum set as its image.
Coincident anchors and ties require no separate hypotheses. -/
theorem InitialFiniteRead.two_anchor_maxLocus_image {n k s : ℕ} {U : Opens (ComplexModel n)}
    {Q : MarkedIdeal n U} {Y : CMfd.{0} (n + 1)}
    {T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y} {x y : Y}
    (F₁ : InitialFiniteRead Q T x k s) (F₂ : InitialFiniteRead Q T y k s)
    (G₁ : InitialNormalizedCompanion Q T x k s) (G₂ : InitialNormalizedCompanion Q T y k s)
    (hMark : G₁.record.d = G₂.record.d) :
    let i : Bool → Y := fun b => if b then y else x
    let f := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1))
      (properNormalMarked Q) T
    i '' maxLocus (fun b : Bool => if b then G₂.value F₂ else G₁.value F₁) univ =
      maxLocus f (range i) := by
  intro i f
  have hRead (b : Bool) : f (i b) = (if b then f y else f x) := by cases b <;> rfl
  have hMax := InitialFiniteRead.two_anchor_maxLocus_normalized F₁ F₂ G₁ G₂ hMark
  change maxLocus (fun b : Bool => if b then f y else f x) univ = _ at hMax
  rw [← hMax]
  ext z
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨⟨b, rfl⟩, ?_⟩
    rintro _ ⟨c, rfl⟩
    simpa only [hRead] using hb.2 c (mem_univ c)
  · rintro ⟨⟨b, rfl⟩, hb⟩
    refine ⟨b, ⟨mem_univ b, ?_⟩, rfl⟩
    intro c _
    simpa only [hRead] using hb (i c) (mem_range_self c)

end

end Hironaka.HironakaG1InitialPositiveFiniteCentres
