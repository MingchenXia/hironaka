/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneNearby
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.MarkedIdeal.CoefficientIdealRestriction
import Hironaka.Invariant.ContactStageInvDomain
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneMaskTower
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.StepOneValue
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The value function of Step 1 with the original members masked (supersedes Step 1bb of `StepOneValue`)

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1; Step 1bb works with `(V(u)_p,
J̄_{p|V(u)_p}, (E_p ∖ E)_{|V(u)_p}, μ̄)`, the original members removed *as a set*.

**Why this module.** The first form `StepOneValue.lowerMarked 𝔍 0` (kept unchanged) builds Step 1bb's lower marked
ideal from `stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d`, i.e. it *deletes* the `#𝔍.E` original members from the divisor. Here the
original members are **kept and masked**: the lower marked ideal of Step 1bb is `(𝓒_{N_{T₀}}(J̄_{T₀})|_{(N ∩
V(w))_{T₀}})|_W` for `J̄ = 𝓒_N(𝓗_N(𝔍))` with the divisor of `𝔍` (`lowerMarkedB`); the mask `W` misses the original
members, whose traces on it are empty. Step 1ab (`StepOneValue.lowerMarked 𝔍 (s + 1)`, `memberRestrict`) already
keeps the members not through the point and is unchanged.

To make later corrections cheap, the value function is defined for an arbitrary family `L` of lower marked ideals on
the masks (`LowerFamily`): `lowerValueL`, `stepOneInvL`, `LowerDataL`; the first form is the instance `L =
StepOneValue.lowerMarked 𝔍` (by `rfl`), the masked form the instance `L = lowerMarkedM 𝔍` (`stepOneInvM`).

## Main results

* `lowerMarkedB`, `lowerMarkedM`, `LowerFamily`, `lowerValueL`, `stepOneInvL`, `LowerDataL`, `stepOneInvM`;
* `mem_lowerMask_and_isInvDomain_M`: at a point of the cosupport in the regime of its level, the point lies in its
  mask and the masked lower marked ideal lies in the domain in dimension `≤ k - 1` (Step 1bb:
  `ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le`, the E-kept domain lemma);
* the properties under one blowup for every family `L` (the proofs of `StepOneValue`, verbatim):
  `stepOneInvL_step_of_notMem` ((3) "equal off the centre" and (4), given `LowerDataL`),
  `stepOneInvL_step_lt_of_mem`;
* `lowerValueL_ne_top`: along a multiple test blow-up of `J̄`, the lower value at a non-special point of the
  cosupport is finite (its image lies in its own mask), so the junk value `∞` -- which coincides with the special
  value -- is never reached;
* `HasLowerDataL`, `stepOneInvL_lt_of_mem_lowerMask`, `centresAvoid_lowerMaskL`: the comparison tools of
  `StepOneNearby` for every family `L` (the centres between two start stages miss the earlier mask).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneValueMasked

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.StepOneMaskTower Hironaka.BoundaryCount Hironaka.CodimOneSupportAlong Hironaka.MarkedIdealBiholomorphism Hironaka.RestrictEmptyTower Hironaka.MarkedIdealRestrictOpen Hironaka.HomogenizedIdealAlong Hironaka.CoefficientIdealRestriction Hironaka.TangentDirectionAlong
open Hironaka.HomogenizedGlueingTower (strictAlong)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)

noncomputable section

variable {n : ℕ}

/-! ### The masked lower marked ideals and the value function for a family of lower marked ideals -/

section Defs

variable {X : CMfd.{u} n}

/-- **The lower marked ideal of Step 1bb, with the original members kept and masked**: on the mask `maskB 𝔍 T₀ y₀`, the
restriction of `𝓒_{N_{T₀}}(J̄_{T₀})` to the strict transform of `N ∩ V(w)`, `w` the tangent direction chosen at the base point
of `y₀` and `J̄ = 𝓒_N(𝓗_N(𝔍))` carrying the divisor of `𝔍` (whose strict transforms miss the mask). -/
def lowerMarkedB (𝔍 : MarkedIdeal n X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    MarkedIdeal n (maskB 𝔍 T₀ y₀) :=
  MarkedIdeal.pullback (Subtype.val : maskB 𝔍 T₀ y₀ → Y₀)
    (withN (coeffMarkedAlong (geoTransformAlong (barMarked 𝔍) T₀))
      (strictAlong T₀ (𝔍.N ∩ {x | (tangentChoice 𝔍 (T₀.proj y₀)).2 x = 0})))

/-- **The masked lower marked ideal** at level `s`: `lowerMarkedB` for `s = 0`, Step 1ab's `StepOneValue.lowerMarked` for
`s ≥ 1`. -/
def lowerMarkedM (𝔍 : MarkedIdeal n X) (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    MarkedIdeal n (lowerMask 𝔍 s T₀ y₀) :=
  match s with
  | 0 => lowerMarkedB 𝔍 T₀ y₀
  | s + 1 => lowerMarked 𝔍 (s + 1) T₀ y₀

/-- **A family of lower marked ideals on the masks.** -/
abbrev LowerFamily (𝔍 : MarkedIdeal n X) :=
  ∀ (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀), MarkedIdeal n (lowerMask 𝔍 s T₀ y₀)

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

open Classical in
/-- **The lower value for the family `L`**: the inductive invariant of `L s T₀ y₀` (formed at the last stage of `T₀` around
the image `y₀` of `y`) along the restricted tail `T₁`, at `y` (`∞` if the image of `y` is not in its mask). -/
def lowerValueL (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (L : LowerFamily 𝔍) (s : ℕ)
    {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y : Y) : WithTop Λ :=
  if h : T₁.proj y ∈ lowerMask 𝔍 s T₀ (T₁.proj y) then
    ((R.inv (L s T₀ (T₁.proj y)) (restrict (lowerMask 𝔍 s T₀ (T₁.proj y)) T₁)
      (⟨y, h⟩ : openPreimage T₁ (lowerMask 𝔍 s T₀ (T₁.proj y))) : Λ) : WithTop Λ)
  else ⊤

open Classical in
/-- **The value function of Step 1 for the family `L`**: `(s(y), ∞)` at special points, `(s(y), lower value)` otherwise, the
lower value taken along the part of `T` since the start of the run of `y` in its regime. -/
def stepOneInvL (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (L : LowerFamily 𝔍) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (y : Y) : ℕ ×ₗ WithTop Λ :=
  if IsSpecial 𝔍 T y then toLex (level 𝔍 T y, ⊤)
  else toLex (level 𝔍 T y, lowerValueL R 𝔍 L (level 𝔍 T y)
    (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) y)

/-- **Lower data for the family `L`**: the image of `y` lies in its mask, `L` there lies in the domain of `R`, the restricted
tail is one of its canonical segments and `y` lies in its cosupport along it. -/
def LowerDataL (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (L : LowerFamily 𝔍) (s : ℕ)
    {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y : Y) : Prop :=
  ∃ h : T₁.proj y ∈ lowerMask 𝔍 s T₀ (T₁.proj y),
    IsInvDomain k (L s T₀ (T₁.proj y)) ∧
    IsCanonical (L s T₀ (T₁.proj y)) (R.inv (L s T₀ (T₁.proj y))) (restrict (lowerMask 𝔍 s T₀ (T₁.proj y)) T₁) ∧
    (⟨y, h⟩ : openPreimage T₁ (lowerMask 𝔍 s T₀ (T₁.proj y))) ∈
      (geoTransformAlong (L s T₀ (T₁.proj y)) (restrict (lowerMask 𝔍 s T₀ (T₁.proj y)) T₁)).cosupp

/-- **The value function of Step 1, original members masked**. -/
abbrev stepOneInvM (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) {Y : CMfd.{u} n}
    (T : BlowupTower X Y) (y : Y) : ℕ ×ₗ WithTop Λ :=
  stepOneInvL R 𝔍 (lowerMarkedM 𝔍) T y

end Defs

/-! ### The masks and the domain -/

section Domain

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **The masked lower marked ideal lies in the domain**: for `𝔍` well formed with `d ≥ 1`, of maximal order along `N`
with `dim N ≤ k` (`0 < n`), along a multiple test blow-up `T₀` of `J̄`, at a point `y₀` of the cosupport in the
regime of its level `s`, `y₀` lies in its mask and `lowerMarkedM 𝔍 s T₀ y₀` lies in `IsInvDomain (k - 1)` (Step 1bb:
E-kept `isInvDomain_stage_coeffHomAlong_of_le` -- the mask misses `Z₁` and the original members; Step 1ab:
`StepOneLowerDomain`). -/
theorem mem_lowerMask_and_isInvDomain_M (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {k : ℕ} (hk : DimLE n 𝔍.N k) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀}
    (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp) {s : ℕ} (hreg : stepRegime 𝔍 s T₀ y₀) :
    y₀ ∈ lowerMask 𝔍 s T₀ y₀ ∧ IsInvDomain (k - 1) (lowerMarkedM 𝔍 s T₀ y₀) := by
  have hold := mem_lowerMask_and_isInvDomain 𝔍 h𝔍 hd hn hmax hk T₀ hT₀ hy₀ hreg
  match s, hold with
  | s + 1, hold => exact hold
  | 0, hold =>
    refine ⟨hold.1, ?_⟩
    obtain ⟨hxU, hU⟩ := tangentChoice_spec 𝔍 (exists_tangent_of_mem_cosupp 𝔍 h𝔍 hd hmax T₀ hT₀ hy₀)
    exact ContactStageInvDomain.isInvDomain_stage_coeffHomAlong_of_le 𝔍 h𝔍 hd hk
      ⟨(tangentChoice 𝔍 (T₀.proj y₀)).1, hU.isOpen⟩ hU T₀ hT₀ (maskB 𝔍 T₀ y₀)
      (fun z hz => (interior_subset hz).1) (fun z hz _ => (interior_subset hz).2.2)
      (fun H hH z hz _ => (interior_subset hz).2.1 H hH)

/-- **The image of a non-special point of the cosupport at the start of its run is in the regime and in the cosupport.** -/
theorem stepRegime_and_mem_cosupp_head (h𝔍 : 𝔍.IsWellFormed) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp)
    (hsp : ¬ IsSpecial 𝔍 T y) :
    stepRegime 𝔍 (level 𝔍 T y) (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y))
        ((tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)).proj y) ∧
      (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)).proj y ∈
        (geoTransformAlong (barMarked 𝔍) (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y))).cosupp := by
  set r := regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y with hr
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have hsplit := (isGeoTestTower_iff_head_tail (barMarked 𝔍) T r).mp hT
  obtain ⟨hNh, hch⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
    (head T r) hsplit.1
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos r with h0 | hpos
    · rw [h0]
      cases T with
      | refl => exact ⟨rfl, hsp⟩
      | step T C π hπ => exact ⟨rfl, hsp⟩
    · exact regime_head_of_le_regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y r hpos le_rfl
  · rw [geoTransformAlong_head_tail (barMarked 𝔍) T r] at hy
    exact proj_mem_cosupp_of_mem_cosupp hNh hch (tail T r) hsplit.2 hy

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)

/-- **A point of the cosupport in the regime of its level lies in its mask** (`StepOneLowerDomain.mem_maskA`, `mem_maskB`;
no dimension bound needed). -/
theorem mem_lowerMask_of_stepRegime (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (hT₀ : IsGeoTestTower (barMarked 𝔍) T₀) {y₀ : Y₀} (hy₀ : y₀ ∈ (geoTransformAlong (barMarked 𝔍) T₀).cosupp)
    {s : ℕ} (hreg : stepRegime 𝔍 s T₀ y₀) : y₀ ∈ lowerMask 𝔍 s T₀ y₀ := by
  obtain ⟨hl, hsp⟩ := hreg
  match s, hl with
  | 0, hl => exact mem_maskB 𝔍 h𝔍 hd hmax T₀ hT₀ hy₀ hl fun hZ => hsp (Or.inl ⟨hl, hZ⟩)
  | s + 1, hl => exact mem_maskA 𝔍 h𝔍 hd hn T₀ hT₀ (by omega) hsp

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)

/-- **The junk value is never reached**: along a multiple test blow-up of `J̄` (`𝔍` well formed, `d ≥ 1`, of maximal
order, `0 < n`), at a non-special point of the cosupport the lower value is finite, for every family `L` -- the
image of the point at the start of its run is in the regime and in the cosupport, hence in its own mask. -/
theorem lowerValueL_ne_top (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (L : LowerFamily 𝔍) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp)
    (hsp : ¬ IsSpecial 𝔍 T y) :
    lowerValueL R 𝔍 L (level 𝔍 T y) (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y))
      (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) y ≠ ⊤ := by
  classical
  obtain ⟨hreg, hcos⟩ := stepRegime_and_mem_cosupp_head 𝔍 h𝔍 T hT hy hsp
  have hTh := ((isGeoTestTower_iff_head_tail (barMarked 𝔍) T
    (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)).mp hT).1
  have hmem := mem_lowerMask_of_stepRegime 𝔍 h𝔍 hd hn hmax _ hTh hcos hreg
  rw [lowerValueL, dif_pos hmem]
  exact WithTop.coe_ne_top

end Domain

/-! ### The value function under one blowup, for every family -/

section Step

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X) (L : LowerFamily 𝔍)

theorem stepOneInvL_of_isSpecial {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y} (h : IsSpecial 𝔍 T y) :
    stepOneInvL R 𝔍 L T y = toLex (level 𝔍 T y, ⊤) := by
  classical
  rw [stepOneInvL, if_pos h]

theorem stepOneInvL_of_not_isSpecial {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y} (h : ¬ IsSpecial 𝔍 T y) :
    stepOneInvL R 𝔍 L T y = toLex (level 𝔍 T y, lowerValueL R 𝔍 L (level 𝔍 T y)
      (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y))
      (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) y) := by
  classical
  rw [stepOneInvL, if_neg h]

/-- The first component of the value is the level. -/
theorem stepOneInvL_fst {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    (ofLex (stepOneInvL R 𝔍 L T y)).1 = level 𝔍 T y := by
  classical
  unfold stepOneInvL
  split_ifs <;> rfl

/-- A point of lower level has a smaller value. -/
theorem stepOneInvL_lt_of_level_lt {Y Z : CMfd.{u} n} {T : BlowupTower X Y} {T' : BlowupTower X Z} {y : Y} {z : Z}
    (h : level 𝔍 T' z < level 𝔍 T y) : stepOneInvL R 𝔍 L T' z < stepOneInvL R 𝔍 L T y := by
  rw [Prod.Lex.lt_iff, stepOneInvL_fst, stepOneInvL_fst]
  exact Or.inl h

/-- A special point has the largest value among the points of its level. -/
theorem stepOneInvL_le_of_isSpecial {Y Z : CMfd.{u} n} {T : BlowupTower X Y} {T' : BlowupTower X Z} {y : Y} {z : Z}
    (hy : IsSpecial 𝔍 T y) (hz : level 𝔍 T' z ≤ level 𝔍 T y) : stepOneInvL R 𝔍 L T' z ≤ stepOneInvL R 𝔍 L T y := by
  rcases hz.lt_or_eq with hlt | heq
  · exact (stepOneInvL_lt_of_level_lt R 𝔍 L hlt).le
  · rw [stepOneInvL_of_isSpecial R 𝔍 L T hy, Prod.Lex.le_iff, stepOneInvL_fst]
    exact Or.inr ⟨heq, le_top⟩

/-- When the image of `y` lies in its mask, the lower value is the value of `R` along the restricted tail. -/
theorem lowerValueL_eq_of_mem {s : ℕ} {Y₀ Y : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y} {y : Y}
    (h : T₁.proj y ∈ lowerMask 𝔍 s T₀ (T₁.proj y)) :
    lowerValueL R 𝔍 L s T₀ T₁ y = ((R.inv (L s T₀ (T₁.proj y)) (restrict (lowerMask 𝔍 s T₀ (T₁.proj y)) T₁)
      (⟨y, h⟩ : openPreimage T₁ (lowerMask 𝔍 s T₀ (T₁.proj y))) : Λ) : WithTop Λ) := by
  classical
  rw [lowerValueL, dif_pos h]

/-- **Off the centre of a blowup appended to the tail, the lower value does not change** (given `LowerDataL`). -/
theorem lowerValueL_step_of_notMem {s : ℕ} {Y₀ Y Z : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y}
    {C : Set Y} {π : Z → Y} {hπ : IsBlowupAlong n C π} {z : Z} (hd : LowerDataL R 𝔍 L s T₀ (.step T₁ C π hπ) z)
    (hzC : π z ∉ C) : lowerValueL R 𝔍 L s T₀ (.step T₁ C π hπ) z = lowerValueL R 𝔍 L s T₀ T₁ (π z) := by
  obtain ⟨h, hdom, hcan, hcos⟩ := hd
  have h' : T₁.proj (π z) ∈ lowerMask 𝔍 s T₀ (T₁.proj (π z)) := h
  rw [lowerValueL_eq_of_mem R 𝔍 L h, lowerValueL_eq_of_mem R 𝔍 L h']
  congr 1
  exact inv_step_of_notMem R hdom (restrict (lowerMask 𝔍 s T₀ (T₁.proj (π z))) T₁) _ _ _ hcan hcos hzC

/-- **Over the centre of a blowup appended to the tail, the lower value drops** (given `LowerDataL`). -/
theorem lowerValueL_step_lt_of_mem {s : ℕ} {Y₀ Y Z : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y}
    {C : Set Y} {π : Z → Y} {hπ : IsBlowupAlong n C π} {z : Z} (hd : LowerDataL R 𝔍 L s T₀ (.step T₁ C π hπ) z)
    (hzC : π z ∈ C) : lowerValueL R 𝔍 L s T₀ (.step T₁ C π hπ) z < lowerValueL R 𝔍 L s T₀ T₁ (π z) := by
  obtain ⟨h, hdom, hcan, hcos⟩ := hd
  have h' : T₁.proj (π z) ∈ lowerMask 𝔍 s T₀ (T₁.proj (π z)) := h
  rw [lowerValueL_eq_of_mem R 𝔍 L h, lowerValueL_eq_of_mem R 𝔍 L h', WithTop.coe_lt_coe]
  exact inv_step_lt_of_mem R hdom (restrict (lowerMask 𝔍 s T₀ (T₁.proj (π z))) T₁) _ _ _ hcan hcos hzC

/-- **The value after a blowup at a point whose image keeps its regime** is computed from the same stage, along the tail
extended by the blowup. -/
theorem stepOneInvL_step_eq_of_regime {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) {z : Z} (hz : ¬ IsSpecial 𝔍 (.step T C π hπ) z)
    (hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z)) :
    stepOneInvL R 𝔍 L (.step T C π hπ) z = toLex (level 𝔍 (.step T C π hπ) z,
      lowerValueL R 𝔍 L (level 𝔍 (.step T C π hπ) z)
        (head T (regimeRun (stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z)) T (π z)))
        (.step (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z)) T (π z))) C π hπ) z) := by
  rw [stepOneInvL_of_not_isSpecial R 𝔍 L _ hz, regimeRun_step_of _ T C π hπ hreg]
  rfl

/-- **Properties (3) "equal off the centre" and (4) of the Step 1 value function, for every family**: along a multiple test
blow-up `T` of `J̄` followed by a blowup `π` along `C`, at `z` with `π z ∉ C` the value at `z` is that at `π z`, provided, if
`π z` is not special, `z` has lower data at the split of `T` at the start of the run of `π z` followed by `π`. -/
theorem stepOneInvL_step_of_notMem (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent)
    (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) {z : Z} (hzC : π z ∉ C)
    (hd : ¬ IsSpecial 𝔍 T (π z) → LowerDataL R 𝔍 L (level 𝔍 T (π z))
      (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T (π z))) T (π z)))
      (.step (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T (π z))) T (π z))) C π hπ) z) :
    stepOneInvL R 𝔍 L (.step T C π hπ) z = stepOneInvL R 𝔍 L T (π z) := by
  have hl := level_step_of_notMem 𝔍 hE T C π hπ hzC
  have hs := isSpecial_step_iff_of_notMem 𝔍 hN h𝔞 hE T hT C π hπ hzC
  by_cases hsp : IsSpecial 𝔍 T (π z)
  · rw [stepOneInvL_of_isSpecial R 𝔍 L _ (hs.mpr hsp), stepOneInvL_of_isSpecial R 𝔍 L _ hsp, hl]
  · have hz : ¬ IsSpecial 𝔍 (.step T C π hπ) z := fun h => hsp (hs.mp h)
    have hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z) := ⟨hl.symm, hsp⟩
    rw [stepOneInvL_step_eq_of_regime R 𝔍 L T C π hπ hz hreg, stepOneInvL_of_not_isSpecial R 𝔍 L _ hsp, hl,
      lowerValueL_step_of_notMem R 𝔍 L (hd hsp) hzC]

/-- **Property (3), drop over the centre, at a point keeping its regime** (given lower data). -/
theorem stepOneInvL_step_lt_of_mem {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) {z : Z} (hzC : π z ∈ C) (hz : ¬ IsSpecial 𝔍 (.step T C π hπ) z)
    (hzT : ¬ IsSpecial 𝔍 T (π z)) (hl : level 𝔍 (.step T C π hπ) z = level 𝔍 T (π z))
    (hd : LowerDataL R 𝔍 L (level 𝔍 T (π z))
      (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T (π z))) T (π z)))
      (.step (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T (π z))) T (π z))) C π hπ) z) :
    stepOneInvL R 𝔍 L (.step T C π hπ) z < stepOneInvL R 𝔍 L T (π z) := by
  have hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z) := ⟨hl.symm, hzT⟩
  rw [stepOneInvL_step_eq_of_regime R 𝔍 L T C π hπ hz hreg, stepOneInvL_of_not_isSpecial R 𝔍 L _ hzT, hl,
    Prod.Lex.toLex_lt_toLex]
  right
  exact ⟨rfl, lowerValueL_step_lt_of_mem R 𝔍 L hd hzC⟩

end Step

/-! ### The steps between two start stages, for every family -/

section Avoid

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X) (L : LowerFamily 𝔍)

/-- **Every non-special point of the cosupport has lower data** for the family `L`, at the split of the tower at the start
of its run (the conclusion of the canonical-tail theorem). -/
def HasLowerDataL {Y : CMfd.{u} n} (T : BlowupTower X Y) : Prop :=
  ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, ¬ IsSpecial 𝔍 T y →
    LowerDataL R 𝔍 L (level 𝔍 T y) (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y))
      (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) y

/-- Under lower data the value at a non-special point is below `(s(y), ∞)`. -/
theorem stepOneInvL_lt_top_of_hasLowerData {Y : CMfd.{u} n} {T : BlowupTower X Y} (hD : HasLowerDataL R 𝔍 L T)
    {y : Y} (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (hsp : ¬ IsSpecial 𝔍 T y) :
    stepOneInvL R 𝔍 L T y < toLex (level 𝔍 T y, (⊤ : WithTop Λ)) := by
  obtain ⟨h, -⟩ := hD y hy hsp
  rw [stepOneInvL_of_not_isSpecial R 𝔍 L T hsp, lowerValueL_eq_of_mem R 𝔍 L h, Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, WithTop.coe_lt_top _⟩

/-- Out of the regime of level `s`, at level at least `s`, the value is at least `(s, ∞)`. -/
theorem toLex_top_le_stepOneInvL {Y : CMfd.{u} n} (T : BlowupTower X Y) {s : ℕ} {w : Y} (hl : s ≤ level 𝔍 T w)
    (hn : ¬ stepRegime 𝔍 s T w) : toLex (s, (⊤ : WithTop Λ)) ≤ stepOneInvL R 𝔍 L T w := by
  by_cases hsp : IsSpecial 𝔍 T w
  · rw [stepOneInvL_of_isSpecial R 𝔍 L T hsp, Prod.Lex.toLex_le_toLex]
    rcases hl.lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, le_rfl⟩
  · have hlt : s < level 𝔍 T w := hl.lt_of_ne fun heq => hn ⟨heq.symm, hsp⟩
    rw [stepOneInvL_of_not_isSpecial R 𝔍 L T hsp, Prod.Lex.toLex_le_toLex]
    exact Or.inl hlt

/-- **Over an earlier mask the values stay below a point out of the regime** (for every family `L`). -/
theorem stepOneInvL_lt_of_mem_lowerMask (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {s : ℕ} {Y₁ Y₂ : CMfd.{u} n} (T₀ : BlowupTower X Y₁)
    (M : BlowupTower Y₁ Y₂) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append M)) {p₁ : Y₁}
    (hp₁ : level 𝔍 T₀ p₁ = s) (hD : HasLowerDataL R 𝔍 L (T₀.append M)) {q : Y₂}
    (hq : q ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp) (hqW : M.proj q ∈ lowerMask 𝔍 s T₀ p₁)
    {w : Y₂} (hw : s ≤ level 𝔍 (T₀.append M) w) (hnw : ¬ stepRegime 𝔍 s (T₀.append M) w) :
    stepOneInvL R 𝔍 L (T₀.append M) q < stepOneInvL R 𝔍 L (T₀.append M) w := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  have hle : level 𝔍 (T₀.append M) q ≤ s := by
    match s, hp₁, hqW with
    | 0, _, hqW => exact (level_eq_zero_of_mem_maskB 𝔍 hE T₀ M hqW).le
    | _ + 1, hp₁, hqW => exact (level_le_of_mem_maskA 𝔍 hE T₀ M hqW).trans hp₁.le
  rcases hle.lt_or_eq with hlt | heq
  · exact stepOneInvL_lt_of_level_lt R 𝔍 L (hlt.trans_le hw)
  · have hreg := (stepRegime_and_le_regimeRun_of_mem_lowerMask 𝔍 h𝔍 hd hmax T₀ M hT hp₁ hqW heq).1
    have h1 := stepOneInvL_lt_top_of_hasLowerData R 𝔍 L hD hq hreg.2
    rw [heq] at h1
    exact h1.trans_le (toLex_top_le_stepOneInvL R 𝔍 L _ hw hnw)

/-- **The last centre misses the earlier mask** (for every family `L`). -/
theorem disjoint_lowerMask_of_isCanonicalL (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {s : ℕ} {Y₁ Y₂ Z : CMfd.{u} n} (T₀ : BlowupTower X Y₁)
    {p₁ : Y₁} (hp₁ : level 𝔍 T₀ p₁ = s) (M : BlowupTower Y₁ Y₂) (C : Set Y₂) (π : Z → Y₂)
    (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append M))
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInvL R 𝔍 L) (T₀.append (.step M C π hπ)))
    (hD : HasLowerDataL R 𝔍 L (T₀.append M)) {w : Y₂}
    (hw : w ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp) (hlw : s ≤ level 𝔍 (T₀.append M) w)
    (hnw : ¬ stepRegime 𝔍 s (T₀.append M) w) :
    Disjoint C (M.proj ⁻¹' (lowerMask 𝔍 s T₀ p₁ : Set Y₁)) := by
  obtain ⟨-, hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInvL R 𝔍 L) (T₀.append M) ∧
      (C = ∅ ∨ C = maxLocus (stepOneInvL R 𝔍 L (T₀.append M))
        (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp) := hcan
  rcases hC with hC | hC
  · rw [hC]
    exact Set.empty_disjoint _
  · rw [Set.disjoint_left]
    intro q hqC hqW
    rw [hC] at hqC
    have hlt := stepOneInvL_lt_of_mem_lowerMask R 𝔍 L h𝔍 hd hmax T₀ M hT hp₁ hD hqC.1 hqW hlw hnw
    exact absurd (hqC.2 w hw) (not_le.mpr hlt)

/-- **The centres between two start stages miss the earlier mask** (for every family `L`): along a multiple test
blow-up `T₀ M σ` of `J̄` which is a canonical segment of `stepOneInvL R 𝔍 L`, with lower data along the prefixes `T₀
M'`, for `p₁` of level `s` at `T₀` and `w` of level at least `s` at `T₀ M`, in the cosupport and out of the regime
of level `s`, the centres of `M σ` miss the mask of `p₁`. -/
theorem centresAvoid_lowerMaskL (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {k' : ℕ} (hk : DimLE n 𝔍.N k') {s : ℕ} {Y₁ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₁) {p₁ : Y₁} (hp₁ : level 𝔍 T₀ p₁ = s) :
    ∀ {Y₂ Z : CMfd.{u} n} (M : BlowupTower Y₁ Y₂) (C : Set Y₂) (π : Z → Y₂) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower (barMarked 𝔍) (T₀.append (.step M C π hπ)) →
      IsCanonical (barMarked 𝔍) (stepOneInvL R 𝔍 L) (T₀.append (.step M C π hπ)) →
      (∀ {Y₃ : CMfd.{u} n} (M' : BlowupTower Y₁ Y₃), M'.length ≤ M.length →
        IsGeoTestTower (barMarked 𝔍) (T₀.append M') → IsCanonical (barMarked 𝔍) (stepOneInvL R 𝔍 L) (T₀.append M') →
        HasLowerDataL R 𝔍 L (T₀.append M')) →
      ∀ w ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp, s ≤ level 𝔍 (T₀.append M) w →
        ¬ stepRegime 𝔍 s (T₀.append M) w → CentresAvoid (lowerMask 𝔍 s T₀ p₁) (.step M C π hπ)
  | _, _, .refl, C, π, hπ, hT, hcan, hD, w, hw, hlw, hnw => by
      have hT' : IsGeoTestTower (barMarked 𝔍) (T₀.append .refl) := hT.1
      have hcan' : IsCanonical (barMarked 𝔍) (stepOneInvL R 𝔍 L) (T₀.append .refl) := hcan.1
      exact ⟨trivial, disjoint_lowerMask_of_isCanonicalL R 𝔍 L h𝔍 hd hmax T₀ hp₁ .refl C π hπ hT' hcan
        (hD .refl le_rfl hT' hcan') hw hlw hnw⟩
  | _, _, .step M₂ C₂ π₂ hπ₂, C, π, hπ, hT, hcan, hD, w, hw, hlw, hnw => by
      have hT' : IsGeoTestTower (barMarked 𝔍) (T₀.append (.step M₂ C₂ π₂ hπ₂)) := hT.1
      have hcan' : IsCanonical (barMarked 𝔍) (stepOneInvL R 𝔍 L) (T₀.append (.step M₂ C₂ π₂ hπ₂)) := hcan.1
      obtain ⟨hw₂, hl₂, hn₂⟩ := StepOneNearby.not_stepRegime_proj 𝔍 h𝔍 hd hn hmax hk (T₀.append M₂) C₂ π₂ hπ₂ hT' hw
        hlw hnw
      refine ⟨centresAvoid_lowerMaskL h𝔍 hd hn hmax hk T₀ hp₁ M₂ C₂ π₂ hπ₂ hT' hcan'
        (fun M' hM' => hD M' (hM'.trans (by rw [BlowupTower.length_step]; omega))) (π₂ w) hw₂ hl₂ hn₂, ?_⟩
      exact disjoint_lowerMask_of_isCanonicalL R 𝔍 L h𝔍 hd hmax T₀ hp₁ (.step M₂ C₂ π₂ hπ₂) C π hπ hT' hcan
        (hD _ le_rfl hT' hcan') hw hlw hnw

end Avoid

end

end Hironaka.StepOneValueMasked
