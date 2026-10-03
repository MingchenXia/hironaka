/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupTowerSplitIso
import Hironaka.Invariant.MaximalOrderStepOneB
import Hironaka.Blowup.NormalCrossingsComparison
import Hironaka.Blowup.BlowupSequences
import Hironaka.Blowup.BlowupStrictSubmanifold
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The point-dependent split stage of Step 1, and the original members of `E` dropped

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1: the invariants of a point are
"assigned at the moment [it is] getting blown-up" and "remain unchanged when the points are transformed
isomorphically"; Step 1b works with `(X, J̄, ∅, μ̄)` and, at the stage `p` where it starts, with `(V(u)_p,
J̄_{p|V(u)_p}, (E_p ∖ E)_{|V(u)_p}, μ̄)`, i.e. with the original members `E` removed.

## The regime run

The value of the Step 1 invariant at a point `y` of the last stage of a tower `T` is computed along the part of `T` since the
stage at which the images of `y` entered the regime of `y` (its number `s` of original members, and whether it lies in the
part of the cosupport that is blown up first).  For a predicate `P` on the points of the stages of towers over `X` (a
*regime*), `regimeRun P T y` is the number of trailing blowups of `T` along which the images of `y` (before the last stage)
satisfy `P`; the tail of `BlowupTowerSplit.split T (regimeRun P T y)` is then the part of `T` since the start of the regime.

* `regimeRun`, `regimeRun_refl`, `regimeRun_step`, `regimeRun_le_length`;
* `regime_head_of_le_regimeRun`: at every stage of the run the image of `y` satisfies `P`;
  `not_regime_head_regimeRun`: the run is maximal;

## The original members dropped

* `geoTransformAlong_dropE`: along every tower, dropping the first `m ≤ #E` members commutes with the transform (the
  transform appends the exceptional divisor after the strict transforms of the members);
* `isGeoTestTower_dropE`: a multiple test blow-up stays one after dropping members (normal crossings with fewer members);
* `coeffHom_dropE`, `geoTransformAlong_coeffHom_dropE`, `isGeoTestTower_stepOneMarked_of_coeffHom`,
  `cosupp_geoTransformAlong_stepOneMarked`: for `J̄ = 𝓒_N(𝓗_N(𝔍))` (any `E`) with its `#𝔍.E` original members
  dropped one gets `stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d` (`E = []`), along every tower; so Step 1b's marked ideals are
  `MaximalOrderStepOneB.contactMarked` and the results proved for them (independence of the hypersurface of maximal
  contact, domain lemmas) apply unchanged. Dropping the fixed number `#𝔍.E` of original members (not the number of
  members at the stage where Step 1b starts) keeps re-basing consistent: the members appended along a part with
  empty centres are the same on both sides.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StepOneRegime

open Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerIsomorphism Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.HomogenizedIdealAlong Hironaka.MaximalOrderStepOneB Hironaka.NormalCrossingsComparison
open Hironaka.HomogenizedGlueingAlongTower (homogenizedMarkedAlong)

noncomputable section

variable {n : ℕ}

/-! ### The regime run -/

section Run

variable {X : CMfd.{u} n}

/-- **A regime**: a predicate on the points of the stages of the towers over `X`. -/
abbrev Regime (X : CMfd.{u} n) : Type (u + 1) := ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Prop

open Classical in
/-- **The regime run** of `y`: the number of trailing blowups of `T` along which the images of `y` before the last stage
satisfy `P` (`0` if the image of `y` under the last blowup does not). -/
def regimeRun (P : Regime X) : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → ℕ
  | _, .refl, _ => 0
  | _, .step T _ π _, z => if P T (π z) then regimeRun P T (π z) + 1 else 0

variable (P : Regime X)

@[simp] theorem regimeRun_refl (y : X) : regimeRun P (BlowupTower.refl : BlowupTower X X) y = 0 := rfl

open Classical in
theorem regimeRun_step {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (z : Z) : regimeRun P (.step T C π hπ) z = if P T (π z) then regimeRun P T (π z) + 1 else 0 := rfl

theorem regimeRun_step_of {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    {z : Z} (h : P T (π z)) : regimeRun P (.step T C π hπ) z = regimeRun P T (π z) + 1 := by
  classical
  rw [regimeRun_step, if_pos h]

theorem regimeRun_step_of_not {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) {z : Z} (h : ¬ P T (π z)) : regimeRun P (.step T C π hπ) z = 0 := by
  classical
  rw [regimeRun_step, if_neg h]

/-- The run is at most the length of the tower. -/
theorem regimeRun_le_length : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y), regimeRun P T y ≤ T.length
  | _, .refl, _ => le_rfl
  | _, .step T C π hπ, z => by
      classical
      rw [regimeRun_step, BlowupTower.length_step]
      split_ifs
      · exact Nat.succ_le_succ (regimeRun_le_length T (π z))
      · exact Nat.zero_le _

/-- **Along the run the images satisfy the regime**: for `1 ≤ i ≤ regimeRun P T y`, the image of `y` at the stage before
the last `i` blowups satisfies `P`. -/
theorem regime_head_of_le_regimeRun : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) (i : ℕ), 1 ≤ i →
    i ≤ regimeRun P T y → P (head T i) ((tail T i).proj y)
  | _, .refl, _, i, hi, hle => absurd (hle.trans_eq (regimeRun_refl P _)) (by omega)
  | _, .step T C π hπ, z, i, hi, hle => by
      by_cases hP : P T (π z)
      · rw [regimeRun_step_of P T C π hπ hP] at hle
        obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
        show P (head T i) ((BlowupTower.step (tail T i) C π hπ).proj z)
        rw [BlowupTower.proj_step]
        rcases Nat.eq_zero_or_pos i with rfl | hi'
        · cases T <;> exact hP
        · exact regime_head_of_le_regimeRun T (π z) i hi' (by omega)
      · rw [regimeRun_step_of_not P T C π hπ hP] at hle
        omega

/-- **The run is maximal**: if it is shorter than the tower, the image of `y` one stage before its start does not satisfy
the regime. -/
theorem not_regime_head_regimeRun : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y),
    regimeRun P T y < T.length →
      ¬ P (head T (regimeRun P T y + 1)) ((tail T (regimeRun P T y + 1)).proj y)
  | _, .refl, _, h => absurd h (by simp)
  | _, .step T C π hπ, z, h => by
      by_cases hP : P T (π z)
      · have hrun := regimeRun_step_of P T C π hπ hP
        rw [hrun, BlowupTower.length_step] at h
        rw [hrun]
        show ¬ P (head T (regimeRun P T (π z) + 1))
          ((BlowupTower.step (tail T (regimeRun P T (π z) + 1)) C π hπ).proj z)
        rw [BlowupTower.proj_step]
        exact not_regime_head_regimeRun T (π z) (by omega)
      · rw [regimeRun_step_of_not P T C π hπ hP]
        show ¬ P (head T 0) ((BlowupTower.step (tail T 0) C π hπ).proj z)
        rw [BlowupTower.proj_step]
        cases T <;> exact hP

end Run

/-! ### Dropping the original members -/

section Drop

variable {X : CMfd.{u} n}

/-- **Dropping the first `m ≤ #E` members commutes with the transform along a tower.** -/
theorem geoTransformAlong_dropE (𝔪 : MarkedIdeal n X) {m : ℕ} (hm : m ≤ 𝔪.E.length) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      geoTransformAlong ({ 𝔪 with E := 𝔪.E.drop m } : MarkedIdeal n X) T =
        { geoTransformAlong 𝔪 T with E := (geoTransformAlong 𝔪 T).E.drop m }
  | _, .refl => rfl
  | _, .step T C π hπ => by
      have ih := geoTransformAlong_dropE 𝔪 hm T
      have hlen : m ≤ (geoTransformAlong 𝔪 T).E.length := by
        rw [length_E_geoTransformAlong]
        omega
      rw [geoTransformAlong_step, ih, geoTransformAlong_step, geoTransform_withE]
      rw [geoTransform_E, List.drop_append_of_le_length (by rwa [List.length_map]), List.map_drop]

/-- **A multiple test blow-up stays one after dropping members** (admissibility only asks normal crossings with the
members, and the remaining members are members). -/
theorem isGeoTestTower_dropE (𝔪 : MarkedIdeal n X) {m : ℕ} (hm : m ≤ 𝔪.E.length) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
      IsGeoTestTower ({ 𝔪 with E := 𝔪.E.drop m } : MarkedIdeal n X) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, h => by
      obtain ⟨hT, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp h
      refine (isGeoTestTower_step_iff _ T C π hπ).mpr ⟨isGeoTestTower_dropE 𝔪 hm T hT, ?_⟩
      rw [geoTransformAlong_dropE 𝔪 hm T]
      exact ⟨hC.1, hC.2.1, hasNormalCrossings_of_forall_mem hC.2.2 fun H hH => List.mem_of_mem_drop hH⟩

/-- **`J̄ = 𝓒_N(𝓗_N(𝔍))` with its original members dropped is `stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d`** (`E = []`). -/
theorem coeffHom_dropE (𝔍 : MarkedIdeal n X) :
    ({ coeffMarkedAlong (homMarkedAlong 𝔍) with
        E := (coeffMarkedAlong (homMarkedAlong 𝔍)).E.drop 𝔍.E.length } : MarkedIdeal n X) =
      stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d := by
  have hE : (coeffMarkedAlong (homMarkedAlong 𝔍)).E = 𝔍.E := rfl
  rw [hE, List.drop_length]
  rfl

/-- **Along every tower, the transform of `stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d` is that of `J̄ = 𝓒_N(𝓗_N(𝔍))` with its first
`#𝔍.E` members (the strict transforms of the original members) dropped.** -/
theorem geoTransformAlong_coeffHom_dropE (𝔍 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    geoTransformAlong (stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d) T =
      { geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T with
        E := (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T).E.drop 𝔍.E.length } := by
  rw [← coeffHom_dropE 𝔍]
  exact geoTransformAlong_dropE _ le_rfl T

/-- The multiple test blow-ups of `J̄ = 𝓒_N(𝓗_N(𝔍))` are multiple test blow-ups of `stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d`. -/
theorem isGeoTestTower_stepOneMarked_of_coeffHom (𝔍 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (h : IsGeoTestTower (coeffMarkedAlong (homMarkedAlong 𝔍)) T) :
    IsGeoTestTower (stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d) T := by
  rw [← coeffHom_dropE 𝔍]
  exact isGeoTestTower_dropE _ le_rfl T h

/-- Along every tower, `stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d` and `J̄ = 𝓒_N(𝓗_N(𝔍))` have the same cosupport. -/
theorem cosupp_geoTransformAlong_stepOneMarked (𝔍 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (geoTransformAlong (stepOneMarked 𝔍.N 𝔍.ideal 𝔍.d) T).cosupp =
      (geoTransformAlong (coeffMarkedAlong (homMarkedAlong 𝔍)) T).cosupp := by
  rw [geoTransformAlong_coeffHom_dropE 𝔍 T]
  rfl

end Drop

end

end Hironaka.StepOneRegime
