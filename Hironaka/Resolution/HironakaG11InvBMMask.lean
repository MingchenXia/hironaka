import Hironaka.Invariant.StepOneValueMasked
import Hironaka.Invariant.StepOneLowerDomain

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The Step 1 value with a mask family as a parameter; Bierstone--Milman's masks (repair (B'), plan module 2)

Blueprint: `hironaka-g11-inv-bm-mask.tex`.  Plan: `work/hironaka-resume-20261111/G11B/BPRIME-PLAN.md` (module 2, design
decision D3).  Source: Bierstone--Milman 2008, §5 Step I.B and §7.2 (the coefficient ideal of `I_∅` on a hypersurface of
maximal contact `P` is used at EVERY level `s` of Step I, with the term `ℰ`), read per point as in their §7.2 ("the values of
the invariants at `x` equal their values in year `q_k`").

`StepOneValueMasked.stepOneInvL` evaluates the lower family on the masks `StepOneValue.lowerMask` (`maskB` at level `0`,
inside the open set of the chosen tangent direction; `maskA` at levels `≥ 1`, not inside it).  Bierstone--Milman's lower
marked ideal lives on a maximal-contact hypersurface at every level, so its masks at levels `≥ 1` must lie inside the open set
of the tangent direction.  This module makes the mask family a parameter:

* `MaskFamily`, `LowerFamilyG`, `lowerValueG`, **`stepOneInvG`**, `LowerDataG`, `HasLowerDataG`;
* the existing value is the instance `Mk = lowerMask`: `lowerValueL_eq_lowerValueG`, **`stepOneInvL_eq_stepOneInvG`**,
  `lowerDataL_iff_lowerDataG` (all `rfl`);
* `tangentOpen` (the preimage, at the stage `T₀`, of the open set of the tangent direction chosen at the base point),
  **`maskBM`** (`maskB` at level `0`, `maskA ⊓ tangentOpen` at levels `≥ 1`), `maskBM_le_lowerMask`,
  **`mem_maskBM_of_stepRegime`** (a cosupport point in the regime of its level lies in its own mask);
* the elementary laws of `stepOneInvG` for every mask and lower family: `stepOneInvG_of_isSpecial`,
  `stepOneInvG_of_not_isSpecial`, `stepOneInvG_fst`, `stepOneInvG_lt_of_level_lt`, `stepOneInvG_le_of_isSpecial`,
  `lowerValueG_eq_of_mem`, `lowerValueG_step_of_notMem`, `lowerValueG_step_lt_of_mem`, `lowerValueG_ne_top`.

Sorry-free.  Import discipline (Hironaka phase): no import of `Hironaka.RelativePrincipalization` or
`Hironaka.EmbeddedResolution`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG11InvBMMask

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime
  Hironaka.StepOneValue Hironaka.StepOneValueMasked
  Hironaka.StepOneLowerDomain Hironaka.MarkedIdealRestrictOpen
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)
open Hironaka.HomogenizedIdealAlong (IsMaximalOrderAlong)
open Hironaka.TangentDirectionAlong (IsTangentDirectionAlong)

noncomputable section

variable {n : ℕ}

/-! ### The value function for a mask family -/

section Defs

variable {X : CMfd.{u} n}

/-- **A family of masks**: an open set of the stage `T₀` for every level `s` and point `y₀`. -/
abbrev MaskFamily (_𝔍 : MarkedIdeal n X) :=
  ∀ (_s : ℕ) {Y₀ : CMfd.{u} n} (_T₀ : BlowupTower X Y₀) (_y₀ : Y₀), Opens Y₀

/-- **A family of lower marked ideals on the masks of `Mk`.** -/
abbrev LowerFamilyG (𝔍 : MarkedIdeal n X) (Mk : MaskFamily 𝔍) :=
  ∀ (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀), MarkedIdeal n (Mk s T₀ y₀)

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

open Classical in
/-- **The lower value for the masks `Mk` and the family `L`** (`StepOneValueMasked.lowerValueL` with `Mk` for `lowerMask`). -/
def lowerValueG (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (Mk : MaskFamily 𝔍)
    (L : LowerFamilyG 𝔍 Mk) (s : ℕ) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y : Y) :
    WithTop Λ :=
  if h : T₁.proj y ∈ Mk s T₀ (T₁.proj y) then
    ((R.inv (L s T₀ (T₁.proj y)) (restrict (Mk s T₀ (T₁.proj y)) T₁)
      (⟨y, h⟩ : openPreimage T₁ (Mk s T₀ (T₁.proj y))) : Λ) : WithTop Λ)
  else ⊤

open Classical in
/-- **The Step 1 value for the masks `Mk` and the family `L`**: `(s(y), ⊤)` at special points, `(s(y), lower value)`
otherwise, the lower value along the part of `T` since the start of the run of `y` in its regime. -/
def stepOneInvG (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (Mk : MaskFamily 𝔍)
    (L : LowerFamilyG 𝔍 Mk) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) : ℕ ×ₗ WithTop Λ :=
  if IsSpecial 𝔍 T y then toLex (level 𝔍 T y, ⊤)
  else toLex (level 𝔍 T y, lowerValueG R 𝔍 Mk L (level 𝔍 T y)
    (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) y)

/-- **Lower data for the masks `Mk` and the family `L`.** -/
def LowerDataG (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (Mk : MaskFamily 𝔍)
    (L : LowerFamilyG 𝔍 Mk) (s : ℕ) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y : Y) :
    Prop :=
  ∃ h : T₁.proj y ∈ Mk s T₀ (T₁.proj y),
    IsInvDomain k (L s T₀ (T₁.proj y)) ∧
    IsCanonical (L s T₀ (T₁.proj y)) (R.inv (L s T₀ (T₁.proj y))) (restrict (Mk s T₀ (T₁.proj y)) T₁) ∧
    (⟨y, h⟩ : openPreimage T₁ (Mk s T₀ (T₁.proj y))) ∈
      (geoTransformAlong (L s T₀ (T₁.proj y)) (restrict (Mk s T₀ (T₁.proj y)) T₁)).cosupp

/-- **Lower data at every non-special point of the cosupport**, at the split at the start of its run. -/
def HasLowerDataG (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (Mk : MaskFamily 𝔍)
    (L : LowerFamilyG 𝔍 Mk) {Y : CMfd.{u} n} (T : BlowupTower X Y) : Prop :=
  ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, ¬ IsSpecial 𝔍 T y →
    LowerDataG R 𝔍 Mk L (level 𝔍 T y) (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y))
      (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) y

/-! The existing masked Step 1 value is the instance `Mk = lowerMask`. -/

theorem lowerValueL_eq_lowerValueG (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X)
    (L : LowerFamily 𝔍) (s : ℕ) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y : Y) :
    lowerValueL R 𝔍 L s T₀ T₁ y = lowerValueG R 𝔍 (fun s _ T₀ y₀ => lowerMask 𝔍 s T₀ y₀) L s T₀ T₁ y := rfl

/-- **The existing masked Step 1 value is the instance `Mk = lowerMask` of `stepOneInvG`.** -/
theorem stepOneInvL_eq_stepOneInvG (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X)
    (L : LowerFamily 𝔍) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    stepOneInvL R 𝔍 L T y = stepOneInvG R 𝔍 (fun s _ T₀ y₀ => lowerMask 𝔍 s T₀ y₀) L T y := rfl

theorem lowerDataL_iff_lowerDataG (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X)
    (L : LowerFamily 𝔍) (s : ℕ) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y : Y) :
    LowerDataL R 𝔍 L s T₀ T₁ y ↔ LowerDataG R 𝔍 (fun s _ T₀ y₀ => lowerMask 𝔍 s T₀ y₀) L s T₀ T₁ y := Iff.rfl

end Defs

/-! ### Bierstone--Milman's masks -/

section Masks

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **The open set of the tangent direction chosen at the base point of `y₀`**, at the stage `T₀`. -/
def tangentOpen {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) : Opens Y₀ :=
  ⟨interior (T₀.proj ⁻¹' (tangentChoice 𝔍 (T₀.proj y₀)).1), isOpen_interior⟩

/-- **Bierstone--Milman's masks**: `maskB` at level `0` (already inside the open set of the tangent direction),
`maskA ⊓ tangentOpen` at the levels `≥ 1` (a hypersurface of maximal contact is used at every level). -/
def maskBM : MaskFamily 𝔍 := fun s _ T₀ y₀ =>
  match s with
  | 0 => maskB 𝔍 T₀ y₀
  | _ + 1 => maskA 𝔍 T₀ y₀ ⊓ tangentOpen 𝔍 T₀ y₀

@[simp] theorem maskBM_zero {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    maskBM 𝔍 0 T₀ y₀ = maskB 𝔍 T₀ y₀ := rfl

@[simp] theorem maskBM_succ (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    maskBM 𝔍 (s + 1) T₀ y₀ = maskA 𝔍 T₀ y₀ ⊓ tangentOpen 𝔍 T₀ y₀ := rfl

/-- **Bierstone--Milman's masks lie in the masks of the existing value.** -/
theorem maskBM_le_lowerMask (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    maskBM 𝔍 s T₀ y₀ ≤ lowerMask 𝔍 s T₀ y₀ := by
  match s with
  | 0 => exact le_rfl
  | _ + 1 => exact inf_le_left

/-- **The anchor lies in the tangent open set** when a tangent direction exists at its base point. -/
theorem mem_tangentOpen {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) {y₀ : Y₀}
    (h : ∃ (U : Set X) (w : X → ℂ), T₀.proj y₀ ∈ U ∧ IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w) :
    y₀ ∈ tangentOpen 𝔍 T₀ y₀ := by
  obtain ⟨hx, hU⟩ := tangentChoice_spec 𝔍 h
  have hopen : IsOpen (T₀.proj ⁻¹' (tangentChoice 𝔍 (T₀.proj y₀)).1) :=
    hU.isOpen.preimage T₀.contMDiff_proj.continuous
  show y₀ ∈ interior (T₀.proj ⁻¹' (tangentChoice 𝔍 (T₀.proj y₀)).1)
  rw [hopen.interior_eq]
  exact hx

/-- **A point of the cosupport in the regime of its level lies in its own Bierstone--Milman mask** (`𝔍` well formed,
`d ≥ 1`, of maximal order, `0 < n`, along a multiple test blow-up of `J̄`). -/
theorem mem_maskBM_of_stepRegime (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀} (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp)
    {s : ℕ} (hreg : stepRegime 𝔍 s T₀ y₀) : y₀ ∈ maskBM 𝔍 s T₀ y₀ := by
  have hmem := mem_lowerMask_of_stepRegime 𝔍 h𝔍 hd hn hmax T₀ hT₀ hy₀ hreg
  match s, hmem with
  | 0, hmem => exact hmem
  | _ + 1, hmem =>
    exact ⟨hmem, mem_tangentOpen 𝔍 T₀ (exists_tangent_of_mem_cosupp 𝔍 h𝔍 hd hmax T₀ hT₀ hy₀)⟩

end Masks

/-! ### The elementary laws, for every mask family and lower family -/

section Laws

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X) (Mk : MaskFamily 𝔍) (L : LowerFamilyG 𝔍 Mk)

theorem stepOneInvG_of_isSpecial {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y} (h : IsSpecial 𝔍 T y) :
    stepOneInvG R 𝔍 Mk L T y = toLex (level 𝔍 T y, ⊤) := by
  classical
  rw [stepOneInvG, if_pos h]

theorem stepOneInvG_of_not_isSpecial {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y} (h : ¬ IsSpecial 𝔍 T y) :
    stepOneInvG R 𝔍 Mk L T y = toLex (level 𝔍 T y, lowerValueG R 𝔍 Mk L (level 𝔍 T y)
      (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y))
      (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) y) := by
  classical
  rw [stepOneInvG, if_neg h]

/-- The first component of the value is the level. -/
theorem stepOneInvG_fst {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    (ofLex (stepOneInvG R 𝔍 Mk L T y)).1 = level 𝔍 T y := by
  classical
  unfold stepOneInvG
  split_ifs <;> rfl

/-- A point of lower level has a smaller value. -/
theorem stepOneInvG_lt_of_level_lt {Y Z : CMfd.{u} n} {T : BlowupTower X Y} {T' : BlowupTower X Z} {y : Y} {z : Z}
    (h : level 𝔍 T' z < level 𝔍 T y) : stepOneInvG R 𝔍 Mk L T' z < stepOneInvG R 𝔍 Mk L T y := by
  rw [Prod.Lex.lt_iff, stepOneInvG_fst, stepOneInvG_fst]
  exact Or.inl h

/-- A special point has the largest value among the points of its level. -/
theorem stepOneInvG_le_of_isSpecial {Y Z : CMfd.{u} n} {T : BlowupTower X Y} {T' : BlowupTower X Z} {y : Y} {z : Z}
    (hy : IsSpecial 𝔍 T y) (hz : level 𝔍 T' z ≤ level 𝔍 T y) :
    stepOneInvG R 𝔍 Mk L T' z ≤ stepOneInvG R 𝔍 Mk L T y := by
  rcases hz.lt_or_eq with hlt | heq
  · exact (stepOneInvG_lt_of_level_lt R 𝔍 Mk L hlt).le
  · rw [stepOneInvG_of_isSpecial R 𝔍 Mk L T hy, Prod.Lex.le_iff, stepOneInvG_fst]
    exact Or.inr ⟨heq, le_top⟩

/-- When the image of `y` lies in its mask, the lower value is the value of `R` along the restricted tail. -/
theorem lowerValueG_eq_of_mem {s : ℕ} {Y₀ Y : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y} {y : Y}
    (h : T₁.proj y ∈ Mk s T₀ (T₁.proj y)) :
    lowerValueG R 𝔍 Mk L s T₀ T₁ y = ((R.inv (L s T₀ (T₁.proj y)) (restrict (Mk s T₀ (T₁.proj y)) T₁)
      (⟨y, h⟩ : openPreimage T₁ (Mk s T₀ (T₁.proj y))) : Λ) : WithTop Λ) := by
  classical
  rw [lowerValueG, dif_pos h]

/-- **Off the centre of a blowup appended to the tail, the lower value does not change** (given `LowerDataG`). -/
theorem lowerValueG_step_of_notMem {s : ℕ} {Y₀ Y Z : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y}
    {C : Set Y} {π : Z → Y} {hπ : IsBlowupAlong n C π} {z : Z}
    (hd : LowerDataG R 𝔍 Mk L s T₀ (.step T₁ C π hπ) z) (hzC : π z ∉ C) :
    lowerValueG R 𝔍 Mk L s T₀ (.step T₁ C π hπ) z = lowerValueG R 𝔍 Mk L s T₀ T₁ (π z) := by
  obtain ⟨h, hdom, hcan, hcos⟩ := hd
  have h' : T₁.proj (π z) ∈ Mk s T₀ (T₁.proj (π z)) := h
  rw [lowerValueG_eq_of_mem R 𝔍 Mk L h, lowerValueG_eq_of_mem R 𝔍 Mk L h']
  congr 1
  exact inv_step_of_notMem R hdom (restrict (Mk s T₀ (T₁.proj (π z))) T₁) _ _ _ hcan hcos hzC

/-- **Over the centre of a blowup appended to the tail, the lower value drops** (given `LowerDataG`). -/
theorem lowerValueG_step_lt_of_mem {s : ℕ} {Y₀ Y Z : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y}
    {C : Set Y} {π : Z → Y} {hπ : IsBlowupAlong n C π} {z : Z}
    (hd : LowerDataG R 𝔍 Mk L s T₀ (.step T₁ C π hπ) z) (hzC : π z ∈ C) :
    lowerValueG R 𝔍 Mk L s T₀ (.step T₁ C π hπ) z < lowerValueG R 𝔍 Mk L s T₀ T₁ (π z) := by
  obtain ⟨h, hdom, hcan, hcos⟩ := hd
  have h' : T₁.proj (π z) ∈ Mk s T₀ (T₁.proj (π z)) := h
  rw [lowerValueG_eq_of_mem R 𝔍 Mk L h, lowerValueG_eq_of_mem R 𝔍 Mk L h', WithTop.coe_lt_coe]
  exact inv_step_lt_of_mem R hdom (restrict (Mk s T₀ (T₁.proj (π z))) T₁) _ _ _ hcan hcos hzC

/-- **The junk value is never reached for Bierstone--Milman's masks**: along a multiple test blow-up of `J̄`, at a
non-special point of the cosupport, the lower value is finite, for every lower family on `maskBM`. -/
theorem lowerValueG_maskBM_ne_top (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (L : LowerFamilyG 𝔍 (maskBM 𝔍)) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T) {y : Y}
    (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (hsp : ¬ IsSpecial 𝔍 T y) :
    lowerValueG R 𝔍 (maskBM 𝔍) L (level 𝔍 T y) (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y))
      (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) y ≠ ⊤ := by
  classical
  obtain ⟨hreg, hcos⟩ := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 T hT hy hsp
  have hTh := ((isGeoTestTower_iff_head_tail (barMarked 𝔍) T
    (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)).mp hT).1
  have hmem := mem_maskBM_of_stepRegime 𝔍 h𝔍 hd hn hmax _ hTh hcos hreg
  rw [lowerValueG, dif_pos hmem]
  exact WithTop.coe_ne_top

end Laws

end

end Hironaka.HironakaG11InvBMMask
