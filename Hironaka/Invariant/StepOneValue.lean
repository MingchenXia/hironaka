import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.InvDomainMemberRestriction
import Hironaka.Invariant.CodimOnePartCanonical

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The value function of Step 1 (marked ideals of maximal order)

Blueprint `hir:step-one-value`, `hir:step-one-value-off-centre` (`blueprint/src/hironaka.tex`, Hironaka phase H4, pieces of
`hir:maximal-order-step`).  Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1: the
invariant `inv̄(x) = (s(x), ∞, 0, …)` on the intersections of `s` original divisors contained in the support (Step 1aa) and on
the codimension-one components (Step 1ba), `inv̄(x) = (s(x), inv_{J̄|H^s_α}(x))` in Step 1ab and `inv̄(x) = (0, inv_{J̄|V(u)}(x))`
in Step 1bb; the invariants are "assigned at the moment [the points] are getting blown-up" and "remain unchanged when the
points are transformed isomorphically".

Let `R` be a resolution invariant in dimension `≤ k` (`ResolutionInvariantExt.ResolutionInvariant`, the inductive hypothesis)
and `𝔍 = (X, N, E, 𝔞, d)` a marked ideal (of maximal order in the intended use), `J̄ = 𝓒_N(𝓗_N(𝔍))` (`barMarked`, carrying the
divisor `E` of `𝔍`).  For a tower `T` and a point `y` of its last stage:

* `origMembers 𝔍 T`: the strict transforms of the `#E` original members (the first `#E` members of `E_T`);
  `level 𝔍 T y`: the number `s(y)` of them through `y`;
* `IsSpecial 𝔍 T y`: `y` lies in the part of the cosupport blown up first at its level -- the codimension-one part `Z₁` of
  `cosupp J̄_T` along `N_T` if `s(y) = 0` (Step 1ba), the member locus of the cosupport if `s(y) ≥ 1` (Step 1aa;
  TN3's `MemberInterLocusAlong.memberInterLocus`);
* `stepRegime 𝔍 s`: level `s` and not special; the run of `y` in its regime (`StepOneRegime.regimeRun`) splits `T = T₀ T₁` at
  the stage at which the images of `y` entered it;
* the **mask** `lowerMask 𝔍 s T₀ y₀ : Opens Y₀` around the image `y₀` of `y` at that stage, and the **lower marked ideal**
  `lowerMarked 𝔍 s T₀ y₀` on it: for `s ≥ 1`, the points on no original member missing `y₀` and off the level-`s` member
  locus (`maskA`), with TN3's `memberRestrict` of `J̄_{T₀}` at the members through `y₀` (Step 1ab); for `s = 0`, the points
  over the open set of the tangent direction chosen at the base point (`tangentChoice`), off the original members and off
  `Z₁` (`maskB`), with `MaximalOrderStepOneB.contactMarked` (Step 1bb; the original members deleted,
  `StepOneRegime.geoTransformAlong_coeffHom_dropE`);
* `lowerValue R 𝔍 s T₀ T₁ y`: `R` of the lower marked ideal along the restricted tail at `y`;
  `stepOneInv R 𝔍 T y = (s(y), ∞)` at special points and `(s(y), lowerValue …)` otherwise, in `ℕ ×ₗ WithTop Λ`.

**The value function of this module is superseded, kept** (blueprint `hir:step-one-value`, first form): its Step 1bb lower marked
ideal `lowerMarked 𝔍 0` deletes the `#E` original members, so `stepOneInv` is not invariant under re-basing along empty prefixes
(the orchestrator's independent review of the Step 1 value, 3 October 2026, finding H1).  The route uses the masked form
`StepOneValueMasked.stepOneInvM` (`hir:step-one-value-masked`), which keeps the original members, masked, at level `0` and uses
`lowerMarked 𝔍 (s + 1)` at the levels `s + 1`; the levels, special points, regimes, masks and tangent choices of this module are
those of the masked form.  `stepOneInv`, `lowerValue`, `LowerData` and their lemmas lie outside the constant cone of the main
theorem.

## Main results

* `inv_step_of_notMem`, `inv_step_lt_of_mem`: for `R`, off the centre of the last blowup of a canonical segment the value
  is unchanged, over it the value drops (properties (3) and (4) of `R`, combined);
* `LowerData`: the restricted tail is a canonical segment of the lower marked ideal, which lies in the domain of `R`, and the
  point lies in its cosupport (`hir:maximal-order-step`: "along `T₁|_W`, which is a canonical segment of it");
  `lowerValue_eq_of_lowerData`, `lowerValue_step_of_notMem`, `lowerValue_step_lt_of_mem`;
* `level_step_of_notMem`, `isSpecial_step_iff_of_notMem`, `stepRegime_step_iff_of_notMem`: off the centre of a blowup the
  level, the special part and the regime do not change (TN3's `BoundaryCount`, `CodimOnePartCanonical`,
  `MemberInterLocusAlong`);
* `stepOneInv_step_eq_of_regime`: the value after a blowup, at a point whose image keeps its regime, is computed from the
  same stage along the tail extended by the blowup;
* **`stepOneInv_step_of_notMem`**: properties (3) "equal off the centre" and (4) (empty steps) of the Step 1 value function,
  given `LowerData` at the point (to be supplied along canonical segments of the Step 1 value function);
  `stepOneInv_step_lt_of_level_lt`, `stepOneInv_step_lt_of_mem`: property (3) "drop over the centre" when the level drops,
  resp. when the point keeps its regime (given `LowerData`).

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneValue

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.HomogenizedIdealAlong
  Hironaka.MaximalOrderStepOneB Hironaka.StepOneRegime
  Hironaka.BoundaryCount Hironaka.CodimOneSupportAlong
  Hironaka.MemberInterLocusAlong Hironaka.InvDomainMemberRestriction
  Hironaka.TangentDirectionAlong Hironaka.ResolutionDriver
  Hironaka.MarkedIdealBiholomorphism
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant)

noncomputable section

variable {n : ℕ}

/-! ### Two consequences of properties (3) and (4) of a resolution invariant -/

section Generic

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **Off the centre of the last blowup of a canonical segment the value does not change** (properties (3) and (4) of
`R`: the centre is empty, or the nonempty maximum locus, or the maximum locus and empty). -/
theorem inv_step_of_notMem (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hcan : IsCanonical 𝔪 (R.inv 𝔪) (.step T C π hπ)) {z : Z}
    (hz : z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp) (hzC : π z ∉ C) :
    R.inv 𝔪 (.step T C π hπ) z = R.inv 𝔪 T (π z) := by
  obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (R.inv 𝔪) T ∧
      (C = ∅ ∨ C = maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
  by_cases hne : C.Nonempty
  · rcases hC with hC | hC
    · exact R.emptyStep 𝔪 h T C π hπ hC hT z hz
    · exact (R.decrease 𝔪 h T C π hπ hT hne hC z hz).2 hzC
  · exact R.emptyStep 𝔪 h T C π hπ (not_nonempty_iff_eq_empty.mp hne) hT z hz

/-- **Over the centre of the last blowup of a canonical segment the value drops** (property (3) of `R`). -/
theorem inv_step_lt_of_mem (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hcan : IsCanonical 𝔪 (R.inv 𝔪) (.step T C π hπ)) {z : Z}
    (hz : z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp) (hzC : π z ∈ C) :
    R.inv 𝔪 (.step T C π hπ) z < R.inv 𝔪 T (π z) := by
  obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (R.inv 𝔪) T ∧
      (C = ∅ ∨ C = maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
  rcases hC with hC | hC
  · rw [hC] at hzC
    exact absurd hzC (notMem_empty _)
  · exact (R.decrease 𝔪 h T C π hπ hT ⟨π z, hzC⟩ hC z hz).1 hzC

end Generic

/-! ### The ingredients -/

section Defs

variable {X : CMfd.{u} n}

/-- **The marked ideal of Step 1**: `J̄ = 𝓒_N(𝓗_N(𝔍))`, carrying the divisor of `𝔍`. -/
abbrev barMarked (𝔍 : MarkedIdeal n X) : MarkedIdeal n X :=
  coeffMarkedAlong (homMarkedAlong 𝔍)

/-- **The original members at the last stage of `T`**: the first `#𝔍.E` members of the divisor of `J̄_T`, the strict
transforms of the members of `𝔍.E`. -/
def origMembers (𝔍 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) : List (Set Y) :=
  (geoTransformAlong (barMarked 𝔍) T).E.take 𝔍.E.length

/-- **The level** `s(y)`: the number of original members through `y`. -/
def level (𝔍 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) : ℕ :=
  boundaryCount (origMembers 𝔍 T) y

/-- **The special points**: at level `0` the codimension-one part of the cosupport of `J̄_T` along `N_T` (Step 1ba), at
level `≥ 1` the member locus of the cosupport (Step 1aa). -/
def IsSpecial (𝔍 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) : Prop :=
  (level 𝔍 T y = 0 ∧ y ∈ codimOnePartAlong (geoTransformAlong (barMarked 𝔍) T).N
      (geoTransformAlong (barMarked 𝔍) T).ideal (geoTransformAlong (barMarked 𝔍) T).d) ∨
    (1 ≤ level 𝔍 T y ∧ y ∈ memberInterLocus (geoTransformAlong (barMarked 𝔍) T).N (origMembers 𝔍 T)
      (geoTransformAlong (barMarked 𝔍) T).cosupp)

/-- **The regime of level `s`**: level `s` and not special. -/
def stepRegime (𝔍 : MarkedIdeal n X) (s : ℕ) : Regime X :=
  fun {_} T y => level 𝔍 T y = s ∧ ¬ IsSpecial 𝔍 T y

/-- **The mask of Step 1ab** around `y₀`: the points on no original member missing `y₀` and off the special points of the
level of `y₀` (the interior, which is the set itself when the members and the member locus are closed). -/
def maskA (𝔍 : MarkedIdeal n X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) : Opens Y₀ :=
  ⟨interior {z | (∀ H ∈ origMembers 𝔍 T₀, z ∈ H → y₀ ∈ H) ∧ ¬ (level 𝔍 T₀ z = level 𝔍 T₀ y₀ ∧ IsSpecial 𝔍 T₀ z)},
    isOpen_interior⟩

open Classical in
/-- **The tangent direction chosen at a base point** `x`: an open set and a tangent direction of `(𝔍.ideal|_N, 𝔍.d)` on it
containing `x`, if there is one. -/
def tangentChoice (𝔍 : MarkedIdeal n X) (x : X) : Set X × (X → ℂ) :=
  if h : ∃ (U : Set X) (w : X → ℂ), x ∈ U ∧ IsTangentDirectionAlong 𝔍.N 𝔍.ideal 𝔍.d U w then
    (h.choose, h.choose_spec.choose)
  else (∅, 0)

/-- **The mask of Step 1bb** around `y₀`: the points over the open set of the tangent direction chosen at the base point of
`y₀`, on no original member and off the codimension-one part. -/
def maskB (𝔍 : MarkedIdeal n X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) : Opens Y₀ :=
  ⟨interior {z | T₀.proj z ∈ (tangentChoice 𝔍 (T₀.proj y₀)).1 ∧ (∀ H ∈ origMembers 𝔍 T₀, z ∉ H) ∧
      z ∉ codimOnePartAlong (geoTransformAlong (barMarked 𝔍) T₀).N (geoTransformAlong (barMarked 𝔍) T₀).ideal
        (geoTransformAlong (barMarked 𝔍) T₀).d}, isOpen_interior⟩

/-- **The mask** at level `s`: `maskB` for `s = 0`, `maskA` for `s ≥ 1`. -/
def lowerMask (𝔍 : MarkedIdeal n X) (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) : Opens Y₀ :=
  match s with
  | 0 => maskB 𝔍 T₀ y₀
  | _ + 1 => maskA 𝔍 T₀ y₀

/-- **The lower marked ideal** at level `s` on the mask: `contactMarked` (Step 1bb, original members deleted) for `s = 0`,
TN3's `memberRestrict` at the members through `y₀` (Step 1ab) for `s ≥ 1`. -/
def lowerMarked (𝔍 : MarkedIdeal n X) (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    MarkedIdeal n (lowerMask 𝔍 s T₀ y₀) :=
  match s with
  | 0 => contactMarked 𝔍.N 𝔍.ideal 𝔍.d (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀ (maskB 𝔍 T₀ y₀)
  | _ + 1 => MarkedIdeal.pullback (Subtype.val : maskA 𝔍 T₀ y₀ → Y₀)
      (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
        (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) y₀))

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

open Classical in
/-- **The lower value**: the inductive invariant of the lower marked ideal formed at the last stage of `T₀` around the image
of `y`, along the restricted tail `T₁`, at `y` (`∞` if the image of `y` is not in the mask, which does not happen for
well-formed marked ideals). -/
def lowerValue (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (s : ℕ) {Y₀ Y : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y : Y) : WithTop Λ :=
  if h : T₁.proj y ∈ lowerMask 𝔍 s T₀ (T₁.proj y) then
    ((R.inv (lowerMarked 𝔍 s T₀ (T₁.proj y)) (restrict (lowerMask 𝔍 s T₀ (T₁.proj y)) T₁)
      (⟨y, h⟩ : openPreimage T₁ (lowerMask 𝔍 s T₀ (T₁.proj y))) : Λ) : WithTop Λ)
  else ⊤

open Classical in
/-- **The value function of Step 1**: `(s(y), ∞)` at special points, `(s(y), lowerValue)` otherwise, the lower value taken
along the part of `T` since the stage at which the images of `y` entered its regime. -/
def stepOneInv (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (y : Y) : ℕ ×ₗ WithTop Λ :=
  if IsSpecial 𝔍 T y then toLex (level 𝔍 T y, ⊤)
  else toLex (level 𝔍 T y, lowerValue R 𝔍 (level 𝔍 T y)
    (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) y)

/-- **The data under which the lower value is the value of a canonical segment**: the image of `y` lies in its mask, the
lower marked ideal lies in the domain of `R`, the restricted tail is one of its canonical segments, and `y` lies in its
cosupport along it. -/
def LowerData (R : ResolutionInvariant.{u, v} n k Λ) (𝔍 : MarkedIdeal n X) (s : ℕ) {Y₀ Y : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y : Y) : Prop :=
  ∃ h : T₁.proj y ∈ lowerMask 𝔍 s T₀ (T₁.proj y),
    IsInvDomain k (lowerMarked 𝔍 s T₀ (T₁.proj y)) ∧
    IsCanonical (lowerMarked 𝔍 s T₀ (T₁.proj y)) (R.inv (lowerMarked 𝔍 s T₀ (T₁.proj y)))
      (restrict (lowerMask 𝔍 s T₀ (T₁.proj y)) T₁) ∧
    (⟨y, h⟩ : openPreimage T₁ (lowerMask 𝔍 s T₀ (T₁.proj y))) ∈
      (geoTransformAlong (lowerMarked 𝔍 s T₀ (T₁.proj y)) (restrict (lowerMask 𝔍 s T₀ (T₁.proj y)) T₁)).cosupp

end Defs

/-! ### Unfolding -/

section Unfold

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X)

theorem stepOneInv_of_isSpecial {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y} (h : IsSpecial 𝔍 T y) :
    stepOneInv R 𝔍 T y = toLex (level 𝔍 T y, ⊤) := by
  classical
  rw [stepOneInv, if_pos h]

theorem stepOneInv_of_not_isSpecial {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y} (h : ¬ IsSpecial 𝔍 T y) :
    stepOneInv R 𝔍 T y = toLex (level 𝔍 T y, lowerValue R 𝔍 (level 𝔍 T y)
      (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y))
      (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) y) := by
  classical
  rw [stepOneInv, if_neg h]

/-- The first component of the value is the level. -/
theorem stepOneInv_fst {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    (ofLex (stepOneInv R 𝔍 T y)).1 = level 𝔍 T y := by
  classical
  unfold stepOneInv
  split_ifs <;> rfl

/-- A point of lower level has a smaller value. -/
theorem stepOneInv_lt_of_level_lt {Y Z : CMfd.{u} n} {T : BlowupTower X Y} {T' : BlowupTower X Z} {y : Y} {z : Z}
    (h : level 𝔍 T' z < level 𝔍 T y) : stepOneInv R 𝔍 T' z < stepOneInv R 𝔍 T y := by
  rw [Prod.Lex.lt_iff, stepOneInv_fst, stepOneInv_fst]
  exact Or.inl h

/-- A special point has the largest value among the points of its level. -/
theorem stepOneInv_le_of_isSpecial {Y Z : CMfd.{u} n} {T : BlowupTower X Y} {T' : BlowupTower X Z} {y : Y} {z : Z}
    (hy : IsSpecial 𝔍 T y) (hz : level 𝔍 T' z ≤ level 𝔍 T y) : stepOneInv R 𝔍 T' z ≤ stepOneInv R 𝔍 T y := by
  rcases hz.lt_or_eq with hlt | heq
  · exact (stepOneInv_lt_of_level_lt R 𝔍 hlt).le
  · rw [stepOneInv_of_isSpecial R 𝔍 T hy]
    rw [Prod.Lex.le_iff, stepOneInv_fst]
    exact Or.inr ⟨heq, le_top⟩

/-- Under `LowerData`, the lower value is the value of the inductive invariant along the restricted tail. -/
theorem lowerValue_eq_of_lowerData {s : ℕ} {Y₀ Y : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y} {y : Y}
    (h : T₁.proj y ∈ lowerMask 𝔍 s T₀ (T₁.proj y)) :
    lowerValue R 𝔍 s T₀ T₁ y = ((R.inv (lowerMarked 𝔍 s T₀ (T₁.proj y)) (restrict (lowerMask 𝔍 s T₀ (T₁.proj y)) T₁)
      (⟨y, h⟩ : openPreimage T₁ (lowerMask 𝔍 s T₀ (T₁.proj y))) : Λ) : WithTop Λ) := by
  classical
  rw [lowerValue, dif_pos h]

/-- **Off the centre of a blowup appended to the tail, the lower value does not change** (given `LowerData` for the
extended tail). -/
theorem lowerValue_step_of_notMem {s : ℕ} {Y₀ Y Z : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y}
    {C : Set Y} {π : Z → Y} {hπ : IsBlowupAlong n C π} {z : Z} (hd : LowerData R 𝔍 s T₀ (.step T₁ C π hπ) z)
    (hzC : π z ∉ C) : lowerValue R 𝔍 s T₀ (.step T₁ C π hπ) z = lowerValue R 𝔍 s T₀ T₁ (π z) := by
  obtain ⟨h, hdom, hcan, hcos⟩ := hd
  have h' : T₁.proj (π z) ∈ lowerMask 𝔍 s T₀ (T₁.proj (π z)) := h
  rw [lowerValue_eq_of_lowerData R 𝔍 h, lowerValue_eq_of_lowerData R 𝔍 h']
  congr 1
  exact inv_step_of_notMem R hdom (restrict (lowerMask 𝔍 s T₀ (T₁.proj (π z))) T₁) _ _ _ hcan hcos hzC

/-- **Over the centre of a blowup appended to the tail, the lower value drops** (given `LowerData` for the extended
tail). -/
theorem lowerValue_step_lt_of_mem {s : ℕ} {Y₀ Y Z : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y}
    {C : Set Y} {π : Z → Y} {hπ : IsBlowupAlong n C π} {z : Z} (hd : LowerData R 𝔍 s T₀ (.step T₁ C π hπ) z)
    (hzC : π z ∈ C) : lowerValue R 𝔍 s T₀ (.step T₁ C π hπ) z < lowerValue R 𝔍 s T₀ T₁ (π z) := by
  obtain ⟨h, hdom, hcan, hcos⟩ := hd
  have h' : T₁.proj (π z) ∈ lowerMask 𝔍 s T₀ (T₁.proj (π z)) := h
  rw [lowerValue_eq_of_lowerData R 𝔍 h, lowerValue_eq_of_lowerData R 𝔍 h', WithTop.coe_lt_coe]
  exact inv_step_lt_of_mem R hdom (restrict (lowerMask 𝔍 s T₀ (T₁.proj (π z))) T₁) _ _ _ hcan hcos hzC

end Unfold

/-! ### Off the centre of a blowup: level, special points, regime -/

section OffCentre

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- The divisor of `J̄` is that of `𝔍`. -/
theorem barMarked_E : (barMarked 𝔍).E = 𝔍.E := rfl

/-- `J̄` has the submanifold of `𝔍`. -/
theorem barMarked_N : (barMarked 𝔍).N = 𝔍.N := rfl

/-- `J̄` has a coherent ideal (`𝔞` coherent, `N` a closed submanifold). -/
theorem isCoherent_barMarked (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent) :
    (barMarked 𝔍).ideal.IsCoherent :=
  isCoherent_coeffMarkedAlong (isCoherent_homMarkedAlong h𝔞 hN) hN

/-- The original members at the last stage are the strict transforms of the members of `𝔍.E`. -/
theorem origMembers_eq {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    origMembers 𝔍 T = 𝔍.E.map (HomogenizedGlueingTower.strictAlong T) :=
  MemberInterTowerAlong.take_E_geoTransformAlong (barMarked 𝔍) T

/-- **Off the centre the level does not change** (closed members). -/
theorem level_step_of_notMem (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y)
    (π : Z → Y) (hπ : IsBlowupAlong n C π) {z : Z} (hz : π z ∉ C) :
    level 𝔍 (.step T C π hπ) z = level 𝔍 T (π z) :=
  CodimOnePartCanonical.boundaryCount_take_E_geoTransformAlong_step_of_notMem (𝔪 := barMarked 𝔍) hE T C π hπ hz

/-- **The level does not increase under a blowup** (closed members). -/
theorem level_step_le (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y)
    (π : Z → Y) (hπ : IsBlowupAlong n C π) (z : Z) :
    level 𝔍 (.step T C π hπ) z ≤ level 𝔍 T (π z) := by
  have hlen : (barMarked 𝔍).E.length ≤
      ((geoTransformAlong (barMarked 𝔍) T).E.map (BlowupStrictSubmanifold.geoStrictTransform π C)).length := by
    rw [List.length_map, MarkedIdeal.length_E_geoTransformAlong]; omega
  show boundaryCount ((geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).E.take (barMarked 𝔍).E.length) z ≤
    boundaryCount ((geoTransformAlong (barMarked 𝔍) T).E.take (barMarked 𝔍).E.length) (π z)
  rw [MarkedIdeal.geoTransformAlong_step, MarkedIdeal.geoTransform_E, List.take_append_of_le_length hlen,
    ← List.map_take]
  exact boundaryCount_map_geoStrictTransform_le hπ.contMDiff.continuous
    (isClosed_of_mem_take_E_geoTransformAlong (barMarked 𝔍) hE T) z

/-- **Off the centre the special points do not change**: along a multiple test blow-up `T` of `J̄`, for `π z ∉ C`. -/
theorem isSpecial_step_iff_of_notMem (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent)
    (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) {z : Z} (hz : π z ∉ C) :
    IsSpecial 𝔍 (.step T C π hπ) z ↔ IsSpecial 𝔍 T (π z) := by
  have hl := level_step_of_notMem 𝔍 hE T C π hπ hz
  have h1 := CodimOnePartCanonical.mem_codimOnePartAlong_geoTransformAlong_step_iff (𝔪 := barMarked 𝔍) hN
    (isCoherent_barMarked 𝔍 hN h𝔞) T hT C π hπ hz
  have h2 := mem_memberInterLocus_geoTransformAlong_step_iff (𝔪 := barMarked 𝔍) hN (isCoherent_barMarked 𝔍 hN h𝔞)
    hE T hT C π hπ hz
  unfold IsSpecial
  rw [hl]
  exact or_congr (and_congr Iff.rfl h1) (and_congr Iff.rfl h2)

/-- **Off the centre the regime does not change.** -/
theorem stepRegime_step_iff_of_notMem (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent)
    (hE : ∀ H ∈ 𝔍.E, IsClosed H) (s : ℕ) {Y Z : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (barMarked 𝔍) T) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) {z : Z}
    (hz : π z ∉ C) : stepRegime 𝔍 s (.step T C π hπ) z ↔ stepRegime 𝔍 s T (π z) := by
  show (level 𝔍 (.step T C π hπ) z = s ∧ ¬ IsSpecial 𝔍 (.step T C π hπ) z) ↔
    (level 𝔍 T (π z) = s ∧ ¬ IsSpecial 𝔍 T (π z))
  rw [level_step_of_notMem 𝔍 hE T C π hπ hz, isSpecial_step_iff_of_notMem 𝔍 hN h𝔞 hE T hT C π hπ hz]

end OffCentre

/-! ### The value after a blowup -/

section Step

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X)

/-- **The value after a blowup at a point whose image keeps its regime**: if `z` is not special and the image `π z` is in
the regime of `z`, the value at `z` is computed from the same stage as the value at `π z`, along the tail extended by the
blowup. -/
theorem stepOneInv_step_eq_of_regime {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) {z : Z} (hz : ¬ IsSpecial 𝔍 (.step T C π hπ) z)
    (hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z)) :
    stepOneInv R 𝔍 (.step T C π hπ) z = toLex (level 𝔍 (.step T C π hπ) z,
      lowerValue R 𝔍 (level 𝔍 (.step T C π hπ) z)
        (head T (regimeRun (stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z)) T (π z)))
        (.step (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z)) T (π z))) C π hπ) z) := by
  rw [stepOneInv_of_not_isSpecial R 𝔍 _ hz, regimeRun_step_of _ T C π hπ hreg]
  rfl

/-- **Properties (3) "equal off the centre" and (4) (empty steps) of the Step 1 value function**: along a multiple test
blow-up `T` of `J̄`, followed by a blowup `π` along `C`, at a point `z` with `π z ∉ C` the value at `z` is the value at
`π z` -- provided, if `π z` is not special, the lower value at `z` is computed along a canonical segment of the lower
marked ideal (`LowerData`; supplied along canonical segments of the Step 1 value function). -/
theorem stepOneInv_step_of_notMem (hN : IsClosedSubmanifold n 𝔍.N) (h𝔞 : 𝔍.ideal.IsCoherent)
    (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (barMarked 𝔍) T)
    (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) {z : Z} (hzC : π z ∉ C)
    (hd : ¬ IsSpecial 𝔍 T (π z) → LowerData R 𝔍 (level 𝔍 T (π z))
      (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T (π z))) T (π z)))
      (.step (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T (π z))) T (π z))) C π hπ) z) :
    stepOneInv R 𝔍 (.step T C π hπ) z = stepOneInv R 𝔍 T (π z) := by
  have hl := level_step_of_notMem 𝔍 hE T C π hπ hzC
  have hs := isSpecial_step_iff_of_notMem 𝔍 hN h𝔞 hE T hT C π hπ hzC
  by_cases hsp : IsSpecial 𝔍 T (π z)
  · rw [stepOneInv_of_isSpecial R 𝔍 _ (hs.mpr hsp), stepOneInv_of_isSpecial R 𝔍 _ hsp, hl]
  · have hz : ¬ IsSpecial 𝔍 (.step T C π hπ) z := fun h => hsp (hs.mp h)
    have hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z) := ⟨hl.symm, hsp⟩
    rw [stepOneInv_step_eq_of_regime R 𝔍 T C π hπ hz hreg, stepOneInv_of_not_isSpecial R 𝔍 _ hsp, hl,
      lowerValue_step_of_notMem R 𝔍 (hd hsp) hzC]

/-- **Property (3), drop over the centre, when the level drops.** -/
theorem stepOneInv_step_lt_of_level_lt {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) {z : Z} (h : level 𝔍 (.step T C π hπ) z < level 𝔍 T (π z)) :
    stepOneInv R 𝔍 (.step T C π hπ) z < stepOneInv R 𝔍 T (π z) :=
  stepOneInv_lt_of_level_lt R 𝔍 h

/-- **Property (3), drop over the centre, at a point keeping its regime**: if `π z ∈ C`, `z` and `π z` are not special and
have the same level, the value drops -- provided the lower value at `z` is computed along a canonical segment of the lower
marked ideal (`LowerData`). -/
theorem stepOneInv_step_lt_of_mem {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) {z : Z} (hzC : π z ∈ C) (hz : ¬ IsSpecial 𝔍 (.step T C π hπ) z)
    (hzT : ¬ IsSpecial 𝔍 T (π z)) (hl : level 𝔍 (.step T C π hπ) z = level 𝔍 T (π z))
    (hd : LowerData R 𝔍 (level 𝔍 T (π z))
      (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T (π z))) T (π z)))
      (.step (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T (π z))) T (π z))) C π hπ) z) :
    stepOneInv R 𝔍 (.step T C π hπ) z < stepOneInv R 𝔍 T (π z) := by
  have hreg : stepRegime 𝔍 (level 𝔍 (.step T C π hπ) z) T (π z) := ⟨hl.symm, hzT⟩
  rw [stepOneInv_step_eq_of_regime R 𝔍 T C π hπ hz hreg, stepOneInv_of_not_isSpecial R 𝔍 _ hzT, hl,
    Prod.Lex.toLex_lt_toLex]
  right
  exact ⟨rfl, lowerValue_step_lt_of_mem R 𝔍 hd hzC⟩

end Step

end

end Hironaka.StepOneValue
