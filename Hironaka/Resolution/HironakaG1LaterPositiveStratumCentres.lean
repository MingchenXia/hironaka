import Hironaka.Resolution.HironakaG1LaterPositiveBranchOrder
import Hironaka.Resolution.HironakaG1NormalCentreComparison

/-!
# Maxima and successor centres from later positive tuples

The true selected order, actual companion level and current leaf are
compared at each stratum anchor on its own actual cuts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace

namespace Hironaka.HironakaG1LaterPositiveStratumCentres

noncomputable section

open Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec ResolutionDriver CanonicalCentres StepOneValue StepOneValueMasked
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaActualOpenZeroSectionDifferentials
  HironakaG1LaterPositiveBranchOrder HironakaG1NormalCentreComparison

/-- The realized order, companion level and leaf in their priority order. -/
abbrev laterTuple {n k s : ℕ} {U : Opens (ComplexModel n)} {Q : MarkedIdeal n U}
    {Y : CMfd.{0} (n + 1)} {T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y}
    {y : Y} (F : LaterPositiveRead Q T y k s) : ℕ ×ₗ (ℕ ×ₗ WithTop (ValTy k)) :=
  toLex (F.order, F.companion)

section OneDepth

variable {n₁ n₂ k s : ℕ} {U₁ : Opens (ComplexModel n₁)} {U₂ : Opens (ComplexModel n₂)}
  {Q₁ : MarkedIdeal n₁ U₁} {Q₂ : MarkedIdeal n₂ U₂}
  {Y₁ : CMfd.{0} (n₁ + 1)} {Y₂ : CMfd.{0} (n₂ + 1)}
  {T₁ : BlowupTower (CMfd.of (n := n₁ + 1) (productOpen U₁)) Y₁}
  {T₂ : BlowupTower (CMfd.of (n := n₂ + 1) (productOpen U₂)) Y₂}
  {x₁ : Y₁} {x₂ : Y₂}
  (F₁ : LaterPositiveRead Q₁ T₁ x₁ k s) (F₂ : LaterPositiveRead Q₂ T₂ x₂ k s)

local notation "a₁" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n₁) (k + 1))
  (properNormalMarked Q₁) T₁ x₁
local notation "a₂" => Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n₂) (k + 1))
  (properNormalMarked Q₂) T₂ x₂

/-- At a tied original upper level, strict comparison is comparison of
the realized tuples. -/
theorem upper_lt_iff_later_tuple_lt :
    a₁ < a₂ ↔ laterTuple F₁ < laterTuple F₂ := by
  simpa only [laterTuple, Prod.Lex.lt_iff, ofLex_toLex] using
    LaterPositiveRead.upper_lt_iff F₁ F₂

/-- Weak comparison also preserves ties of the realized tuples. -/
theorem upper_le_iff_later_tuple_le :
    a₁ ≤ a₂ ↔ laterTuple F₁ ≤ laterTuple F₂ := by
  simpa only [not_lt] using not_congr (upper_lt_iff_later_tuple_lt F₂ F₁)

/-- A larger true order decides the comparison regardless of the two
companion levels and leaves. A companion-level difference can decide it
when the true orders tie, as in the existing companion-level theorem. -/
theorem upper_lt_of_later_true_order_lt (h : F₁.order < F₂.order) :
    a₁ < a₂ :=
  (upper_lt_iff_later_tuple_lt F₁ F₂).mpr (Prod.Lex.toLex_lt_toLex.mpr (Or.inl h))

end OneDepth

/-- The whole realized cosupport slice at the indicated original upper level. -/
def positiveLevelStratum {n : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (s : ℕ) : Set Y :=
  { x | x ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp ∧
    level (properNormalMarked Q) T x = s + 1 }

private theorem maxLocus_top_stratum {n k s : ℕ} {U : Opens (ComplexModel n)} (Q : MarkedIdeal n U)
    {Y : CMfd.{0} (n + 1)} (T : BlowupTower (CMfd.of (n := n + 1) (productOpen U)) Y)
    (hTop : (positiveLevelStratum Q T s).Nonempty)
    (hBound : ∀ x ∈ (geoTransformAlong (properNormalMarked Q) T).cosupp,
      level (properNormalMarked Q) T x ≤ s + 1) :
    let P := properNormalMarked Q
    let f := Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T
    maxLocus f (positiveLevelStratum Q T s) = maxLocus f (geoTransformAlong P T).cosupp := by
  intro P f
  have hDom (x : Y) (hx : x ∈ (geoTransformAlong P T).cosupp)
      (hxOut : x ∉ positiveLevelStratum Q T s)
      (y : Y) (hy : y ∈ positiveLevelStratum Q T s) : f x < f y := by
    have hlt : level P T x < s + 1 :=
      lt_of_le_of_ne (hBound x hx) (fun he => hxOut ⟨hx, he⟩)
    have hxy : level P T x < level P T y := hlt.trans_eq hy.2.symm
    change Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T x <
      Seq.StepOneValueMasked.stepOneInvM (invFamily (Nat.succ_pos n) (k + 1)) P T y
    rw [Prod.Lex.lt_iff, Seq.StepOneValueMasked.stepOneInvL_fst,
      Seq.StepOneValueMasked.stepOneInvL_fst]
    exact Or.inl hxy
  ext x
  constructor
  · rintro ⟨hx, hMax⟩
    refine ⟨hx.1, fun y hy => ?_⟩
    by_cases hyTop : y ∈ positiveLevelStratum Q T s
    · exact hMax y hyTop
    · exact (hDom y hy hyTop x hx).le
  · rintro ⟨hx, hMax⟩
    refine ⟨?_, fun y hy => hMax y hy.1⟩
    by_contra hxOut
    obtain ⟨y, hy⟩ := hTop
    exact (not_lt_of_ge (hMax y hy.1)) (hDom x hx hxOut y hy)

section Stratum

variable {n₁ n₂ k₁ k₂ s : ℕ} {U₁ : Opens (ComplexModel n₁)} {U₂ : Opens (ComplexModel n₂)}
  {Q₁ : MarkedIdeal n₁ U₁} {Q₂ : MarkedIdeal n₂ U₂}
  {Y₁ : CMfd.{0} (n₁ + 1)} {Y₂ : CMfd.{0} (n₂ + 1)}
  {T₁ : BlowupTower (CMfd.of (n := n₁ + 1) (productOpen U₁)) Y₁}
  {T₂ : BlowupTower (CMfd.of (n := n₂ + 1) (productOpen U₂)) Y₂}
  (i : Y₁ → Y₂) (S : Set Y₁)
  (F₁ : ∀ x : S, LaterPositiveRead Q₁ T₁ x.val k₁ s)
  (F₂ : ∀ x : S, LaterPositiveRead Q₂ T₂ (i x.val) k₂ s)

local notation "P₁" => properNormalMarked Q₁
local notation "P₂" => properNormalMarked Q₂
local notation "R₁" => invFamily (Nat.succ_pos n₁) (k₁ + 1)
local notation "R₂" => invFamily (Nat.succ_pos n₂) (k₂ + 1)
local notation "f₁" => Seq.StepOneValueMasked.stepOneInvM R₁ P₁ T₁
local notation "f₂" => Seq.StepOneValueMasked.stepOneInvM R₂ P₂ T₂

/-- A criterion for pairwise order agreement stated separately at each
coordinate. The inner comparison is used only for pairs tied in every
earlier coordinate. The records may have different actual coordinates
and the leaf types may have different recursive depths. -/
theorem later_tuple_order_of_coordinate_comparisons
    (hOrder : ∀ x y : S, (F₁ x).order < (F₁ y).order ↔ (F₂ x).order < (F₂ y).order)
    (hLevel : ∀ x y : S, (F₁ x).order = (F₁ y).order →
      ((ofLex (F₁ x).companion).1 < (ofLex (F₁ y).companion).1 ↔
        (ofLex (F₂ x).companion).1 < (ofLex (F₂ y).companion).1))
    (hLeaf : ∀ x y : S, (F₁ x).order = (F₁ y).order →
      (ofLex (F₁ x).companion).1 = (ofLex (F₁ y).companion).1 →
      ((ofLex (F₁ x).companion).2 < (ofLex (F₁ y).companion).2 ↔
        (ofLex (F₂ x).companion).2 < (ofLex (F₂ y).companion).2)) :
    ∀ x y : S, laterTuple (F₁ x) < laterTuple (F₁ y) ↔ laterTuple (F₂ x) < laterTuple (F₂ y) := by
  intro x y
  have hTie : (F₁ x).order = (F₁ y).order ↔ (F₂ x).order = (F₂ y).order := by
    simp only [le_antisymm_iff, ← not_lt, hOrder]
  simp only [laterTuple, Prod.Lex.lt_iff, ofLex_toLex]
  rw [← hTie]
  refine or_congr (hOrder x y) (and_congr_right fun hxy => ?_)
  have hTieLevel :
      (ofLex (F₁ x).companion).1 = (ofLex (F₁ y).companion).1 ↔
        (ofLex (F₂ x).companion).1 = (ofLex (F₂ y).companion).1 := by
    simp only [le_antisymm_iff, ← not_lt, hLevel x y hxy, hLevel y x hxy.symm]
  rw [← hTieLevel]
  exact or_congr (hLevel x y hxy) (and_congr_right fun h => hLeaf x y hxy h)

/-- The entire actual maximum stratum transports under pairwise tuple
order agreement. The preimage is restricted to the chosen stratum, so
the result also allows noninjective point maps, ties, and empty strata. -/
theorem later_positive_stratum_max_loci
    (hTuple : ∀ x y : S, laterTuple (F₁ x) < laterTuple (F₁ y) ↔ laterTuple (F₂ x) < laterTuple (F₂ y)) :
    i '' maxLocus f₁ S = maxLocus f₂ (i '' S) ∧
      S ∩ i ⁻¹' maxLocus f₂ (i '' S) = maxLocus f₁ S := by
  have hOrder (x y : S) : f₁ x.val ≤ f₁ y.val ↔ f₂ (i x.val) ≤ f₂ (i y.val) := by
    have h : f₁ y.val < f₁ x.val ↔ f₂ (i y.val) < f₂ (i x.val) :=
      (upper_lt_iff_later_tuple_lt (F₁ y) (F₁ x)).trans
        ((hTuple y x).trans (upper_lt_iff_later_tuple_lt (F₂ y) (F₂ x)).symm)
    simpa only [not_lt] using not_congr h
  have hPre : S ∩ i ⁻¹' maxLocus f₂ (i '' S) = maxLocus f₁ S := by
    ext x
    constructor
    · rintro ⟨hx, hMax⟩
      exact ⟨hx, fun y hy => (hOrder ⟨y, hy⟩ ⟨x, hx⟩).mpr
        (hMax.2 (i y) (mem_image_of_mem i hy))⟩
    · rintro ⟨hx, hMax⟩
      refine ⟨hx, ⟨mem_image_of_mem i hx, ?_⟩⟩
      rintro _ ⟨y, hy, rfl⟩
      exact (hOrder ⟨y, hy⟩ ⟨x, hx⟩).mp (hMax y hy)
  refine ⟨?_, hPre⟩
  rw [← hPre]
  ext y
  constructor
  · rintro ⟨x, ⟨_, hx⟩, rfl⟩
    exact hx
  · intro hy
    obtain ⟨x, hx, rfl⟩ := hy.1
    exact ⟨x, ⟨hx, hy⟩, rfl⟩

set_option maxHeartbeats 600000 in
/-- A full, nonempty highest-level stratum controls the whole cosupport
maximum on both histories. If the prefixes have equivalent canonicality,
the two actual image-related blowups have equivalent canonicality as well. -/
theorem later_positive_top_stratum_canonical_step_iff
    (hi : Function.Injective i)
    (hTuple : ∀ x y : S, laterTuple (F₁ x) < laterTuple (F₁ y) ↔
      laterTuple (F₂ x) < laterTuple (F₂ y))
    (hLeft : S = positiveLevelStratum Q₁ T₁ s)
    (hRight : i '' S = positiveLevelStratum Q₂ T₂ s)
    (hS : S.Nonempty)
    (hBound₁ : ∀ x ∈ (geoTransformAlong P₁ T₁).cosupp, level P₁ T₁ x ≤ s + 1)
    (hBound₂ : ∀ x ∈ (geoTransformAlong P₂ T₂).cosupp, level P₂ T₂ x ≤ s + 1)
    (hPrefix : IsCanonical P₁ (Seq.StepOneValueMasked.stepOneInvM R₁ P₁) T₁ ↔
      IsCanonical P₂ (Seq.StepOneValueMasked.stepOneInvM R₂ P₂) T₂)
    {Z₁ : CMfd.{0} (n₁ + 1)} {Z₂ : CMfd.{0} (n₂ + 1)}
    (D : Set Y₁) (π₁ : Z₁ → Y₁) (π₂ : Z₂ → Y₂)
    (hπ₁ : IsBlowupAlong (n₁ + 1) D π₁) (hπ₂ : IsBlowupAlong (n₂ + 1) (i '' D) π₂) :
    IsCanonical P₁ (Seq.StepOneValueMasked.stepOneInvM R₁ P₁) (.step T₁ D π₁ hπ₁) ↔
      IsCanonical P₂ (Seq.StepOneValueMasked.stepOneInvM R₂ P₂) (.step T₂ (i '' D) π₂ hπ₂) := by
  have hMax := (later_positive_stratum_max_loci i S F₁ F₂ hTuple).1
  have hMax₁ : maxLocus f₁ S = maxLocus f₁ (geoTransformAlong P₁ T₁).cosupp :=
    hLeft.symm ▸ maxLocus_top_stratum (k := k₁) Q₁ T₁ (hLeft ▸ hS) hBound₁
  have hMax₂ : maxLocus f₂ (i '' S) = maxLocus f₂ (geoTransformAlong P₂ T₂).cosupp :=
    hRight.symm ▸ maxLocus_top_stratum (k := k₂) Q₂ T₂ (hRight ▸ hS.image i) hBound₂
  have hMaxImage : i '' maxLocus f₁ (geoTransformAlong P₁ T₁).cosupp =
      maxLocus f₂ (geoTransformAlong P₂ T₂).cosupp := by
    rw [← hMax₁, ← hMax₂]
    exact hMax
  change (IsCanonical P₁ (Seq.StepOneValueMasked.stepOneInvM R₁ P₁) T₁ ∧
      (D = ∅ ∨ D = maxLocus f₁ (geoTransformAlong P₁ T₁).cosupp)) ↔
    (IsCanonical P₂ (Seq.StepOneValueMasked.stepOneInvM R₂ P₂) T₂ ∧
      (i '' D = ∅ ∨ i '' D = maxLocus f₂ (geoTransformAlong P₂ T₂).cosupp))
  rw [← hMaxImage]
  refine and_congr hPrefix (or_congr image_eq_empty.symm ?_)
  constructor
  · exact congrArg (fun E => i '' E)
  · intro h
    simpa only [preimage_image_eq _ hi] using congrArg (fun E => i ⁻¹' E) h

end Stratum

end

end Hironaka.HironakaG1LaterPositiveStratumCentres
