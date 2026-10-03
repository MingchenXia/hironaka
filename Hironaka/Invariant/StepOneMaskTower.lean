/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Blowup.BlowupSequences
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.BoundaryCount
import Hironaka.Invariant.CodimOnePartTowerAlong
import Hironaka.MarkedIdeal.CodimOneSupportAlong
import Hironaka.Invariant.ContactIndependenceAlong
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MemberInterLocusAlong
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.StepOneValue
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Points over a mask of Step 1 keep the regime along the tail

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1a ("by the maximality condition
... the set `supp(J̄_i) ∩ H^{s_i}_{α' i}` is either disjoint from `H^{s_{j_1}}_{α i}` or contained in it") and Step
1b ("for any tangent direction `u`, the restriction of `(X_i)_{p ≤ i ≤ m}` to `(V(u)_i)` is an extension of the
canonical resolution").

The value of Step 1 at a point is computed from the stage `T₀` at which it entered its regime, on a mask `W` around
its image there (`StepOneValue`). Along a multiple test blow-up `T₀ T₁` of `J̄`, a point `z` of the last stage lying
over the mask `W` of a point `y₀` of level `s` at `T₀`, and of level `s` itself, keeps that regime at every stage of
`T₁`: over `W` the level is at most `s` (the original members missing `y₀` miss `W`, and the level does not increase
along the tower), and no point over `W` of level `s` is special (along a multiple test blow-up the special points of
level `s` lie over the closure of those at `T₀`, resp. over the codimension-one part at `T₀` --
`MemberInterLocusAlong.memberInterLocus_level_geoTransformAlong_subset` and
`CodimOnePartTowerAlong.codimOnePartAlong_geoTransformAlong_subset` -- which the mask misses). Hence **its run is at
least the length of `T₁`: it entered the regime at `T₀` or before.** This is the first half of the comparison of
nearby points in the Step 1 value function.

## Main results

* `origMembers_append`, `level_append_le`: the original members along a concatenation, and the level does not increase;
* `level_le_of_mem_maskA`, `level_eq_zero_of_mem_maskB`: over the mask the level is at most `s`, resp. `0`;
* `not_isSpecial_of_mem_maskA`, `not_isSpecial_of_mem_maskB`: over the mask no point of level `s` is special;
* `le_regimeRun_append`: a generic criterion for a run to cover a tail;
* `stepRegime_and_le_regimeRun_of_mem_lowerMask`: **a point over the mask, of the level of the mask, is in the regime and its
  run covers the tail.**
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneMaskTower

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.HomogenizedIdealAlong Hironaka.StepOneRegime Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.BoundaryCount Hironaka.CodimOneSupportAlong Hironaka.MemberInterLocusAlong Hironaka.MarkedIdealRestrictOpen
open Hironaka.HomogenizedGlueingTower (strictAlong)

noncomputable section

variable {n : ℕ}

/-! ### A generic criterion for runs -/

section Run

variable {X : CMfd.{u} n}

/-- **A run covering a tail**: let `G` be a regime of the towers over `Y₀` inherited by the images under each blowup, such
that `G S w` gives `P (T₀ S) w`.  Then a point `z` with `G T₁ z` has a run in `P` along `T₀ T₁` at least the length of
`T₁`. -/
theorem le_regimeRun_append (P : Regime X) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (G : Regime Y₀)
    (hG : ∀ {Y Z : CMfd.{u} n} (S : BlowupTower Y₀ Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) (w : Z),
      G (.step S C π hπ) w → G S (π w))
    (hGP : ∀ {Y : CMfd.{u} n} (S : BlowupTower Y₀ Y) (w : Y), G S w → P (T₀.append S) w) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y) (z : Y), G T₁ z → T₁.length ≤ regimeRun P (T₀.append T₁) z
  | _, .refl, _, _ => Nat.zero_le _
  | _, .step T₁ C π hπ, z, hz => by
      have hz' := hG T₁ C π hπ z hz
      have hP := hGP T₁ (π z) hz'
      rw [BlowupTower.length_step, BlowupTower.append_step, regimeRun_step_of P _ C π hπ hP]
      exact Nat.succ_le_succ (le_regimeRun_append P T₀ G hG hGP T₁ (π z) hz')

end Run

/-! ### Levels along a concatenation -/

section Level

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- The original members along a concatenation are the strict transforms along the tail of those at its base. -/
theorem origMembers_append {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) :
    origMembers 𝔍 (T₀.append T₁) = (origMembers 𝔍 T₀).map (strictAlong T₁) := by
  rw [origMembers_eq, origMembers_eq, List.map_map]
  exact List.map_congr_left fun H _ => strictAlong_append T₀ H T₁

/-- **The level does not increase along a tail** (closed members). -/
theorem level_append_le (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y) (z : Y), level 𝔍 (T₀.append T₁) z ≤ level 𝔍 T₀ (T₁.proj z)
  | _, .refl, _ => le_rfl
  | _, .step T₁ C π hπ, z => by
      rw [BlowupTower.append_step]
      exact (level_step_le 𝔍 hE (T₀.append T₁) C π hπ z).trans (level_append_le hE T₀ T₁ (π z))

open Classical in
/-- A point on no original member missing `y₀` has level at most that of `y₀`. -/
theorem level_le_of_forall_mem_imp {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) {w y₀ : Y₀}
    (h : ∀ H ∈ origMembers 𝔍 T₀, w ∈ H → y₀ ∈ H) : level 𝔍 T₀ w ≤ level 𝔍 T₀ y₀ := by
  show (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length => w ∈ (origMembers 𝔍 T₀).get i).card ≤
    (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length => y₀ ∈ (origMembers 𝔍 T₀).get i).card
  exact Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact h _ (List.get_mem _ _) hi

/-- **Over the mask of Step 1ab the level is at most that of `y₀`.** -/
theorem level_le_of_mem_maskA (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) {y₀ : Y₀} {z : Y} (hz : T₁.proj z ∈ maskA 𝔍 T₀ y₀) :
    level 𝔍 (T₀.append T₁) z ≤ level 𝔍 T₀ y₀ :=
  (level_append_le 𝔍 hE T₀ T₁ z).trans (level_le_of_forall_mem_imp 𝔍 T₀ (interior_subset hz).1)

/-- **Over the mask of Step 1bb the level is `0`.** -/
theorem level_eq_zero_of_mem_maskB (hE : ∀ H ∈ 𝔍.E, IsClosed H) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) {y₀ : Y₀} {z : Y} (hz : T₁.proj z ∈ maskB 𝔍 T₀ y₀) :
    level 𝔍 (T₀.append T₁) z = 0 := by
  classical
  have h0 : level 𝔍 T₀ (T₁.proj z) = 0 := by
    show (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length =>
      T₁.proj z ∈ (origMembers 𝔍 T₀).get i).card = 0
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun i _ hi => (interior_subset hz).2.1 _ (List.get_mem _ _) hi
  exact Nat.eq_zero_of_le_zero ((level_append_le 𝔍 hE T₀ T₁ z).trans h0.le)

end Level

/-! ### No special points over the masks -/

section Special

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X) (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)

include h𝔍 in
/-- **Over the mask of Step 1ab no point of the level of `y₀` is special**: the special points of that level lie over
the closure of those at `T₀`, and the mask is an open set missing those. -/
theorem not_isSpecial_of_mem_maskA {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y)
    (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀} (hl : 1 ≤ level 𝔍 T₀ y₀) {z : Y}
    (hz : T₁.proj z ∈ maskA 𝔍 T₀ y₀) (hlz : level 𝔍 (T₀.append T₁) z = level 𝔍 T₀ y₀) :
    ¬ IsSpecial 𝔍 (T₀.append T₁) z := by
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff (barMarked 𝔍) T₀ T₁).mp hT
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔪 := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hE₀ : ∀ H ∈ origMembers 𝔍 T₀, H ∈ (geoTransformAlong (barMarked 𝔍) T₀).E :=
    fun H hH => List.mem_of_mem_take hH
  rintro (⟨h0, -⟩ | ⟨-, hL⟩)
  · omega
  · have hsub := memberInterLocus_level_geoTransformAlong_subset (geoTransformAlong (barMarked 𝔍) T₀) h𝔪 hE₀
      (level 𝔍 T₀ y₀) T₁ hT₁
    have hzL : z ∈ memberInterLocus (geoTransformAlong (geoTransformAlong (barMarked 𝔍) T₀) T₁).N
        ((origMembers 𝔍 T₀).map (strictAlong T₁)) (geoTransformAlong (geoTransformAlong (barMarked 𝔍) T₀) T₁).cosupp ∩
        {w | boundaryCount ((origMembers 𝔍 T₀).map (strictAlong T₁)) w = level 𝔍 T₀ y₀} := by
      rw [← geoTransformAlong_append, ← origMembers_append]
      exact ⟨hL, hlz⟩
    have hcl := hsub hzL
    -- the mask is an open neighbourhood of `T₁.proj z` missing the special points of the level of `y₀` at `T₀`
    obtain ⟨w, hwW, hwL⟩ := mem_closure_iff.mp hcl _ isOpen_interior hz
    exact (interior_subset hwW).2 ⟨hwL.2, Or.inr ⟨hl.trans_eq hwL.2.symm, hwL.1⟩⟩

include h𝔍 hd in
/-- **Over the mask of Step 1bb no point is special**: along a multiple test blow-up the codimension-one part lies over
the codimension-one part at `T₀` (maximal order), which the mask misses. -/
theorem not_isSpecial_of_mem_maskB (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₀ Y : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀}
    {z : Y} (hz : T₁.proj z ∈ maskB 𝔍 T₀ y₀) : ¬ IsSpecial 𝔍 (T₀.append T₁) z := by
  obtain ⟨hT₀, hT₁⟩ := (isGeoTestTower_append_iff (barMarked 𝔍) T₀ T₁).mp hT
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  have h𝔪 := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hJ T₀ hT₀
  have hd𝔪 : 1 ≤ (geoTransformAlong (barMarked 𝔍) T₀).d := by
    rw [d_geoTransformAlong]
    exact ContactIndependenceAlong.one_le_coeffMarkedAlong_d _
  have hmax𝔪 := isMaximalOrderAlong_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent
    (isMaximalOrderAlong_barMarked 𝔍 h𝔍 hd hmax) T₀ hT₀
  have hl0 := level_eq_zero_of_mem_maskB 𝔍 (fun H hH => h𝔍.isSNCDivisor.1 H hH) T₀ T₁ hz
  rintro (⟨-, hZ⟩ | ⟨h1, -⟩)
  · have hsub := CodimOnePartTowerAlong.codimOnePartAlong_geoTransformAlong_subset
      (geoTransformAlong (barMarked 𝔍) T₀) h𝔪 hd𝔪 hmax𝔪 T₁ hT₁
    rw [geoTransformAlong_append] at hZ
    exact (interior_subset hz).2.2 (hsub hZ)
  · omega

end Special

/-! ### Points over a mask keep the regime -/

section Regime

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

/-- **A point over the mask, of the level of the mask, is in the regime and its run covers the tail**: along a multiple
test blow-up `T₀ T₁` of `J̄` (`𝔍` well formed, `d ≥ 1`, of maximal order), let `y₀` be a point of `T₀` of level `s` and `z` a
point of the last stage over the mask `lowerMask 𝔍 s T₀ y₀`, of level `s`.  Then `z` is in the regime of level `s`, and the
run of `z` in it is at least the length of `T₁` (`z` entered the regime at `T₀` or before). -/
theorem stepRegime_and_le_regimeRun_of_mem_lowerMask (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {s : ℕ} {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append T₁)) {y₀ : Y₀} (hy₀ : level 𝔍 T₀ y₀ = s)
    {z : Y} (hz : T₁.proj z ∈ lowerMask 𝔍 s T₀ y₀) (hlz : level 𝔍 (T₀.append T₁) z = s) :
    stepRegime 𝔍 s (T₀.append T₁) z ∧ T₁.length ≤ regimeRun (stepRegime 𝔍 s) (T₀.append T₁) z := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  -- the regime holds at every point over the mask of level at least `s`, along every multiple test blow-up
  have key : ∀ {Y' : CMfd.{u} n} (S : BlowupTower Y₀ Y') (w : Y'), IsGeoTestTower (barMarked 𝔍) (T₀.append S) →
      S.proj w ∈ lowerMask 𝔍 s T₀ y₀ → s ≤ level 𝔍 (T₀.append S) w → stepRegime 𝔍 s (T₀.append S) w := by
    intro Y' S w hS hw hlw
    match s, hy₀, hw, hlw with
    | 0, _, hw, _ =>
      exact ⟨level_eq_zero_of_mem_maskB 𝔍 hE T₀ S hw, not_isSpecial_of_mem_maskB 𝔍 h𝔍 hd hmax T₀ S hS hw⟩
    | s' + 1, hy₀, hw, hlw =>
      have hle := level_le_of_mem_maskA 𝔍 hE T₀ S hw
      have heq : level 𝔍 (T₀.append S) w = level 𝔍 T₀ y₀ := by omega
      exact ⟨by omega, not_isSpecial_of_mem_maskA 𝔍 h𝔍 T₀ S hS (by omega) hw heq⟩
  refine ⟨key T₁ z hT hz hlz.ge, ?_⟩
  refine le_regimeRun_append (stepRegime 𝔍 s) T₀
    (fun {_} S w => IsGeoTestTower (barMarked 𝔍) (T₀.append S) ∧ S.proj w ∈ lowerMask 𝔍 s T₀ y₀ ∧
      s ≤ level 𝔍 (T₀.append S) w) ?_ ?_ T₁ z ⟨hT, hz, hlz.ge⟩
  · intro Y Z S C π hπ w ⟨hS, hw, hlw⟩
    rw [BlowupTower.append_step] at hS hlw
    exact ⟨((isGeoTestTower_step_iff _ _ C π hπ).mp hS).1, hw,
      hlw.trans (level_step_le 𝔍 hE (T₀.append S) C π hπ w)⟩
  · intro Y S w ⟨hS, hw, hlw⟩
    exact key S w hS hw hlw

end Regime

end

end Hironaka.StepOneMaskTower
