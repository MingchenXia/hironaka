/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.InvDomainMemberRestriction
import Hironaka.Invariant.CodimOnePartCanonical
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaximalOrderStepOneB
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Invariant.MemberInterTowerAlong
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.MarkedIdeal.TangentDirectionAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The value function of Step 1 (marked ideals of maximal order)

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1: the invariant `inv̄(x) =
(s(x), ∞, 0, …)` on the intersections of `s` original divisors contained in the support (Step 1aa) and on the
codimension-one components (Step 1ba), `inv̄(x) = (s(x), inv_{J̄|H^s_α}(x))` in Step 1ab and `inv̄(x) = (0,
inv_{J̄|V(u)}(x))` in Step 1bb; the invariants are "assigned at the moment [the points] are getting blown-up" and
"remain unchanged when the points are transformed isomorphically".

Let `R` be a resolution invariant in dimension `≤ k` (`ResolutionInvariantExt.ResolutionInvariant`, the inductive hypothesis)
and `𝔍 = (X, N, E, 𝔞, d)` a marked ideal (of maximal order in the intended use), `J̄ = 𝓒_N(𝓗_N(𝔍))` (`barMarked`, carrying the
divisor `E` of `𝔍`).  For a tower `T` and a point `y` of its last stage:

* `origMembers 𝔍 T`: the strict transforms of the `#E` original members (the first `#E` members of `E_T`);
  `level 𝔍 T y`: the number `s(y)` of them through `y`;
* `IsSpecial 𝔍 T y`: `y` lies in the part of the cosupport blown up first at its level -- the codimension-one part
  `Z₁` of `cosupp J̄_T` along `N_T` if `s(y) = 0` (Step 1ba), the member locus of the cosupport if `s(y) ≥ 1` (Step
  1aa; `MemberInterLocusAlong.memberInterLocus`);
* `stepRegime 𝔍 s`: level `s` and not special; the run of `y` in its regime (`StepOneRegime.regimeRun`) splits `T = T₀ T₁` at
  the stage at which the images of `y` entered it;
* the **mask** `lowerMask 𝔍 s T₀ y₀: Opens Y₀` around the image `y₀` of `y` at that stage, and the **lower marked
  ideal** `lowerMarked 𝔍 s T₀ y₀` on it: for `s ≥ 1`, the points on no original member missing `y₀` and off the
  level-`s` member locus (`maskA`), with `memberRestrict` of `J̄_{T₀}` at the members through `y₀` (Step 1ab); for
  `s = 0`, the points over the open set of the tangent direction chosen at the base point (`tangentChoice`), off the
  original members and off `Z₁` (`maskB`), with `MaximalOrderStepOneB.contactMarked` (Step 1bb; the original members
  deleted, `StepOneRegime.geoTransformAlong_coeffHom_dropE`);

The route uses the masked form `StepOneValueMasked.stepOneInvM` (`hir:step-one-value-masked`), which keeps the
original members, masked, at level `0` and uses `lowerMarked 𝔍 (s + 1)` at the levels `s + 1`; the levels, special
points, regimes, masks and tangent choices of this module are those of the masked form.

## Main results

* `inv_step_of_notMem`, `inv_step_lt_of_mem`: for `R`, off the centre of the last blowup of a canonical segment the value
  is unchanged, over it the value drops (properties (3) and (4) of `R`, combined);
* `level_step_of_notMem`, `isSpecial_step_iff_of_notMem`: off the centre of a blowup the level, the special part and
  the regime do not change (`BoundaryCount`, `CodimOnePartCanonical`, `MemberInterLocusAlong`);
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneValue

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.HomogenizedIdealAlong Hironaka.MaximalOrderStepOneB Hironaka.StepOneRegime Hironaka.BoundaryCount Hironaka.CodimOneSupportAlong Hironaka.MemberInterLocusAlong Hironaka.InvDomainMemberRestriction Hironaka.TangentDirectionAlong Hironaka.ResolutionDriver Hironaka.MarkedIdealBiholomorphism
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

/-- **The lower marked ideal** at level `s` on the mask: `contactMarked` (Step 1bb, original members deleted) for `s =
0`, `memberRestrict` at the members through `y₀` (Step 1ab) for `s ≥ 1`. -/
def lowerMarked (𝔍 : MarkedIdeal n X) (s : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (y₀ : Y₀) :
    MarkedIdeal n (lowerMask 𝔍 s T₀ y₀) :=
  match s with
  | 0 => contactMarked 𝔍.N 𝔍.ideal 𝔍.d (tangentChoice 𝔍 (T₀.proj y₀)).2 T₀ (maskB 𝔍 T₀ y₀)
  | _ + 1 => MarkedIdeal.pullback (Subtype.val : maskA 𝔍 T₀ y₀ → Y₀)
      (memberRestrict (geoTransformAlong (barMarked 𝔍) T₀)
        (membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) y₀))

end Defs

/-! ### Off the centre of a blowup: level, special points, regime -/

section OffCentre

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

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

end OffCentre

end

end Hironaka.StepOneValue
