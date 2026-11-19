import Hironaka.Invariant.StepOneMaskTower
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.RestrictEmptyTower

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Comparing nearby points in Step 1: splits at two stages, two open sets, the steps between two starts

Blueprint `hir:step-one-nearby` (`blueprint/src/hironaka.tex`, Hironaka phase H4, a piece of `hir:maximal-order-step`).
Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1, and the lemma on the commutativity of
the resolution procedure with étale morphisms (the invariants of points "remain unchanged when the points are transformed
isomorphically"; blow-ups whose centres miss an open set restrict to isomorphisms over it).

The value `StepOneValue.stepOneInv R 𝔍 T y` of the Step 1 invariant at a point `y` of a tower `T` is computed from the
stage at which the images of `y` entered the regime of its level (`regimeRun`), on a neighbourhood (the *mask*) of the
image of `y` there.  The canonical-tail theorem compares the value of a nearby point `p`, computed from its own (possibly
earlier) start stage and its own mask, with the lower-dimensional invariant of the reference point.  This module provides
the tools of that comparison which do not depend on the step (1ab or 1bb):

* `exists_split_le`: **the split at two indices** -- for `a ≤ b` the head at `b` followed by a middle part `M` is the head
  at `a`, and `M` followed by the tail at `a` is the tail at `b`;
* `mem_cosupp_restrict_nested_iff`, `inv_eq_of_two_opens`: **values of a resolution invariant on two open sets** of one
  stage agree at the points of the cosupport over both (TN3's `MaxLocusLocal.restrict_nestedOpens`, applied to the
  intersection);
* `mem_origMembers_iff_of_mem_maskA`, `membersThrough_eq_of_mem_maskA`: **same-level points of a Step 1ab mask lie on the
  same original members**, so their restricted marked ideals (`memberRestrict` at `membersThrough`) coincide;
* `HasLowerData`: every non-special point of the cosupport has `StepOneValue.LowerData` at its split (the conclusion of the
  canonical-tail theorem);
* `stepOneInv_lt_top_of_hasLowerData`, `toLex_top_le_stepOneInv`, `stepOneInv_lt_of_mem_lowerMask`: under lower data the
  values over an earlier mask stay below `(s, ∞)`, and a point of level at least `s` out of the regime of level `s` has value
  at least `(s, ∞)`;
* `not_stepRegime_proj`: a point out of that regime comes from a point out of it (a point in the regime lies in its own
  mask, and the points over the mask of its level stay in the regime, `StepOneMaskTower`);
* **`centresAvoid_lowerMask`**: along a canonical segment of the Step 1 invariant, **the centres of the steps between the
  start of a point `p` and the later start of a point `y` miss the mask of `p`** -- the centre is the maximum locus, the
  image of `y` before its start has value at least `(s, ∞)`, and the points over the mask of `p` have smaller values.  So
  these steps are empty over the mask, and re-basing (`emptyPrefix`) applies.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneNearby

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals
  Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime
  Hironaka.StepOneValue Hironaka.StepOneLowerDomain
  Hironaka.StepOneMaskTower Hironaka.BoundaryCount
  Hironaka.InvDomainMemberRestriction Hironaka.MarkedIdealBiholomorphism
  Hironaka.BlowupTowerIsomorphism Hironaka.MaxLocusLocal
  Hironaka.RestrictEmptyTower Hironaka.MarkedIdealRestrictOpen
  Hironaka.HomogenizedIdealAlong
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant isGeoTestTower_of_isCanonical)

noncomputable section

variable {n : ℕ}

/-! ### The split at two indices -/

section Split

variable {X : CMfd.{u} n}

/-- **The split at two indices**: for `a ≤ b`, the head of the split at `b` followed by a middle part `M` is the head at
`a`, and `M` followed by the tail at `a` is the tail at `b`. -/
theorem exists_split_le : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y) {a b : ℕ}, a ≤ b →
    ∃ M : BlowupTower (split T b).1 (split T a).1,
      (head T b).append M = head T a ∧ M.append (tail T a) = tail T b
  | _, .refl, 0, 0, _ => ⟨.refl, rfl, rfl⟩
  | _, .refl, 0, _ + 1, _ => ⟨.refl, rfl, rfl⟩
  | _, .refl, _ + 1, _ + 1, _ => ⟨.refl, rfl, rfl⟩
  | _, .refl, _ + 1, 0, h => absurd h (by omega)
  | _, .step _ _ _ _, 0, 0, _ => ⟨.refl, rfl, rfl⟩
  | _, .step T C π hπ, 0, j + 1, _ => ⟨.step (tail T j) C π hπ, by
      show (head T j).append (.step (tail T j) C π hπ) = .step T C π hπ
      rw [BlowupTower.append_step, head_append_tail], rfl⟩
  | _, .step T C π hπ, i + 1, j + 1, h => by
      obtain ⟨M, h₁, h₂⟩ := exists_split_le T (a := i) (b := j) (by omega)
      refine ⟨M, h₁, ?_⟩
      show M.append (.step (tail T i) C π hπ) = .step (tail T j) C π hπ
      rw [BlowupTower.append_step, h₂]
  | _, .step _ _ _ _, _ + 1, 0, h => absurd h (by omega)

end Split

/-! ### Values on two open sets -/

section TwoOpens

variable {X : CMfd.{u} n}

/-- **The cosupport along nested open sets**: for `V ⊆ W` open and `T|_W` a multiple test blow-up of `𝔫|_W`, a point over
`V` lies in the cosupport of `𝔫|_V` along `T|_V` iff it lies in that of `𝔫|_W` along `T|_W` (TN3's isomorphism
`isTowerIso_restrict_nestedOpens` and the restriction to `W ∩ V ⊆ W`). -/
theorem mem_cosupp_restrict_nested_iff {𝔫 : MarkedIdeal n X} (hN : IsClosedSubmanifold n 𝔫.N)
    (h𝔫 : 𝔫.ideal.IsCoherent) {W V : Opens X} (hVW : V ≤ W) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫) (restrict W T)) (p : openPreimage T V) :
    p ∈ (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : V → X) 𝔫) (restrict V T)).cosupp ↔
      (⟨(p : Y), openPreimage_mono T hVW p.2⟩ : openPreimage T W) ∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫) (restrict W T)).cosupp := by
  have hNW : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN W
  have hcW : (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val h𝔫
  have hN' : IsClosedSubmanifold n (MarkedIdeal.pullback (Subtype.val : nestedOpens W V → W)
      (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫)).N :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hNW _
  have hc' : (MarkedIdeal.pullback (Subtype.val : nestedOpens W V → W)
      (MarkedIdeal.pullback (Subtype.val : W → X) 𝔫)).ideal.IsCoherent :=
    GermIdealPullbackCalculus.isCoherent_pullback contMDiff_subtype_val hcW
  have hT' := isGeoTestTower_restrict (nestedOpens W V) hNW hcW (restrict W T) hT
  have hiso := (isTowerIso_restrict_nestedOpens (X := X) hVW T).symm
  have hcos := IsTowerIso.cosupp_geoTransformAlong (nestedOpensDiffeo (n := n) hVW).symm hN' hc' hiso hT'
  rw [pullback_symm_nestedOpensDiffeo (M := X) h𝔫 hVW] at hcos
  rw [hcos, mem_preimage, ResolutionInvariantSegments.cosupp_geoTransformAlong_restrict hNW hcW (nestedOpens W V)
    (restrict W T) hT, mem_preimage]
  rfl

variable {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **Values of a resolution invariant on two open sets**: let `𝔫` have a coherent ideal and `N` a closed submanifold, and
`A`, `B` be opens of the base of `T` such that `𝔫|_A`, `𝔫|_B` lie in the domain of `R` and `T|_A`, `T|_B` are canonical
segments of them.  At a point over `A ∩ B` in the cosupport along `T|_A`, the two values agree, and the point lies in the
cosupport along `T|_B` (TN3's `restrict_nestedOpens` for `A ∩ B ⊆ A` and `A ∩ B ⊆ B`). -/
theorem inv_eq_of_two_opens (R : ResolutionInvariant.{u, v} n k Λ) {𝔫 : MarkedIdeal n X}
    (hN : IsClosedSubmanifold n 𝔫.N) (h𝔫 : 𝔫.ideal.IsCoherent) {A B : Opens X} {Y : CMfd.{u} n}
    (T : BlowupTower X Y)
    (hA : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫))
    (hcanA : IsCanonical (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫)
      (R.inv (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫)) (restrict A T))
    (hB : IsInvDomain k (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫))
    (hcanB : IsCanonical (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫)
      (R.inv (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫)) (restrict B T))
    {p : Y} (hpA : T.proj p ∈ A) (hpB : T.proj p ∈ B)
    (hcos : (⟨p, hpA⟩ : openPreimage T A) ∈
      (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫) (restrict A T)).cosupp) :
    R.inv (MarkedIdeal.pullback (Subtype.val : A → X) 𝔫) (restrict A T) ⟨p, hpA⟩ =
        R.inv (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫) (restrict B T) ⟨p, hpB⟩ ∧
      (⟨p, hpB⟩ : openPreimage T B) ∈
        (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : B → X) 𝔫) (restrict B T)).cosupp := by
  have hVA : A ⊓ B ≤ A := inf_le_left
  have hVB : A ⊓ B ≤ B := inf_le_right
  obtain ⟨-, -, hvalA⟩ := restrict_nestedOpens R h𝔫 hVA hA T hcanA
  obtain ⟨-, -, hvalB⟩ := restrict_nestedOpens R h𝔫 hVB hB T hcanB
  have hTA := isGeoTestTower_of_isCanonical R hA _ hcanA
  have hTB := isGeoTestTower_of_isCanonical R hB _ hcanB
  let q : openPreimage T (A ⊓ B) := ⟨p, show T.proj p ∈ (A : Set X) ∩ B from ⟨hpA, hpB⟩⟩
  have hqV := (mem_cosupp_restrict_nested_iff hN h𝔫 hVA T hTA q).mpr hcos
  exact ⟨(hvalA q hqV).symm.trans (hvalB q hqV), (mem_cosupp_restrict_nested_iff hN h𝔫 hVB T hTB q).mp hqV⟩

end TwoOpens

/-! ### Same-level points of a Step 1ab mask -/

section Members

variable {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X)

open Classical in
/-- **Same-level points of a Step 1ab mask lie on the same original members**: a point `w` of the mask of `y₀` lies on no
original member missing `y₀`; with the same number of original members through it, it lies on all of them. -/
theorem mem_origMembers_iff_of_mem_maskA {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) {y₀ w : Y₀}
    (hw : w ∈ maskA 𝔍 T₀ y₀) (hl : level 𝔍 T₀ w = level 𝔍 T₀ y₀) :
    ∀ H ∈ origMembers 𝔍 T₀, w ∈ H ↔ y₀ ∈ H := by
  have himp : ∀ H ∈ origMembers 𝔍 T₀, w ∈ H → y₀ ∈ H := (interior_subset hw).1
  have hsub : (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length => w ∈ (origMembers 𝔍 T₀).get i) ⊆
      (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length => y₀ ∈ (origMembers 𝔍 T₀).get i) :=
    fun i hi => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      exact himp _ (List.get_mem _ _) hi
  have hcard : (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length => y₀ ∈ (origMembers 𝔍 T₀).get i).card ≤
      (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length => w ∈ (origMembers 𝔍 T₀).get i).card :=
    le_of_eq hl.symm
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  intro H hH
  obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
  refine ⟨himp _ hH, fun hy => ?_⟩
  have hi : i ∈ (Finset.univ.filter fun i : Fin (origMembers 𝔍 T₀).length => y₀ ∈ (origMembers 𝔍 T₀).get i) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hy
  rw [← heq] at hi
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi

/-- **Same-level points of a Step 1ab mask have the same original members through them**, so the same restricted marked
ideal `memberRestrict` (Step 1ab). -/
theorem membersThrough_eq_of_mem_maskA {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) {y₀ w : Y₀}
    (hw : w ∈ maskA 𝔍 T₀ y₀) (hl : level 𝔍 T₀ w = level 𝔍 T₀ y₀) :
    membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) w =
      membersThrough (geoTransformAlong (barMarked 𝔍) T₀).E (origMembers 𝔍 T₀) y₀ := by
  ext i
  rw [mem_membersThrough, mem_membersThrough]
  exact and_congr_right fun hi => mem_origMembers_iff_of_mem_maskA 𝔍 T₀ hw hl _ hi

end Members

/-! ### The steps between two start stages are empty over the earlier mask -/

section Avoid

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X)

/-- **Every point of the cosupport which is not special has lower data** at the split of the tower at the start of its
run (`StepOneValue.LowerData`; the conclusion of the canonical-tail theorem). -/
def HasLowerData {Y : CMfd.{u} n} (T : BlowupTower X Y) : Prop :=
  ∀ y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp, ¬ IsSpecial 𝔍 T y →
    LowerData R 𝔍 (level 𝔍 T y) (head T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y))
      (tail T (regimeRun (stepRegime 𝔍 (level 𝔍 T y)) T y)) y

/-- **Under lower data the value at a non-special point is finite in its second component**: `(s, λ) < (s, ∞)`. -/
theorem stepOneInv_lt_top_of_hasLowerData {Y : CMfd.{u} n} {T : BlowupTower X Y} (hD : HasLowerData R 𝔍 T) {y : Y}
    (hy : y ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp) (hsp : ¬ IsSpecial 𝔍 T y) :
    stepOneInv R 𝔍 T y < toLex (level 𝔍 T y, (⊤ : WithTop Λ)) := by
  obtain ⟨h, -⟩ := hD y hy hsp
  rw [stepOneInv_of_not_isSpecial R 𝔍 T hsp, lowerValue_eq_of_lowerData R 𝔍 h, Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, WithTop.coe_lt_top _⟩

/-- **Out of the regime of level `s`, at level at least `s`, the value is at least `(s, ∞)`** (the level is larger, or the
point is special). -/
theorem toLex_top_le_stepOneInv {Y : CMfd.{u} n} (T : BlowupTower X Y) {s : ℕ} {w : Y} (hl : s ≤ level 𝔍 T w)
    (hn : ¬ stepRegime 𝔍 s T w) : toLex (s, (⊤ : WithTop Λ)) ≤ stepOneInv R 𝔍 T w := by
  by_cases hsp : IsSpecial 𝔍 T w
  · rw [stepOneInv_of_isSpecial R 𝔍 T hsp, Prod.Lex.toLex_le_toLex]
    rcases hl.lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq, le_rfl⟩
  · have hlt : s < level 𝔍 T w := hl.lt_of_ne fun heq => hn ⟨heq.symm, hsp⟩
    rw [stepOneInv_of_not_isSpecial R 𝔍 T hsp, Prod.Lex.toLex_le_toLex]
    exact Or.inl hlt

/-- **Over an earlier mask the values stay below a point out of the regime**: along a multiple test blow-up `T₀ M` of `J̄`
(`𝔍` well formed, `d ≥ 1`, of maximal order), let `p₁` be a point of `T₀` of level `s` and `w` a point of the last stage of
level at least `s`, not in the regime of level `s`.  If the non-special points of the cosupport have lower data, every point
of the cosupport over the mask of `p₁` has a smaller value than `w`. -/
theorem stepOneInv_lt_of_mem_lowerMask (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {s : ℕ} {Y₁ Y₂ : CMfd.{u} n} (T₀ : BlowupTower X Y₁)
    (M : BlowupTower Y₁ Y₂) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append M)) {p₁ : Y₁}
    (hp₁ : level 𝔍 T₀ p₁ = s) (hD : HasLowerData R 𝔍 (T₀.append M)) {q : Y₂}
    (hq : q ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp) (hqW : M.proj q ∈ lowerMask 𝔍 s T₀ p₁)
    {w : Y₂} (hw : s ≤ level 𝔍 (T₀.append M) w) (hnw : ¬ stepRegime 𝔍 s (T₀.append M) w) :
    stepOneInv R 𝔍 (T₀.append M) q < stepOneInv R 𝔍 (T₀.append M) w := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  have hle : level 𝔍 (T₀.append M) q ≤ s := by
    match s, hp₁, hqW with
    | 0, _, hqW => exact (level_eq_zero_of_mem_maskB 𝔍 hE T₀ M hqW).le
    | _ + 1, hp₁, hqW => exact (level_le_of_mem_maskA 𝔍 hE T₀ M hqW).trans hp₁.le
  rcases hle.lt_or_eq with hlt | heq
  · exact stepOneInv_lt_of_level_lt R 𝔍 (hlt.trans_le hw)
  · have hreg := (stepRegime_and_le_regimeRun_of_mem_lowerMask 𝔍 h𝔍 hd hmax T₀ M hT hp₁ hqW heq).1
    have h1 := stepOneInv_lt_top_of_hasLowerData R 𝔍 hD hq hreg.2
    rw [heq] at h1
    exact h1.trans_le (toLex_top_le_stepOneInv R 𝔍 _ hw hnw)

/-- **Out of the regime before a blowup**: along a multiple test blow-up `T σ` of `J̄`, if a point `w` of the last stage has
level at least `s` and is not in the regime of level `s`, its image `σ w` lies in the cosupport (if `w` does), has level at
least `s` and is not in the regime either -- a point in the regime lies in its own mask
(`StepOneLowerDomain.mem_lowerMask_and_isInvDomain`), and a point over the mask of its level is in the regime
(`StepOneMaskTower.stepRegime_and_le_regimeRun_of_mem_lowerMask`). -/
theorem not_stepRegime_proj (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {k' : ℕ} (hk : DimLE n 𝔍.N k') {s : ℕ} {Y Z : CMfd.{u} n}
    (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower (barMarked 𝔍) (.step T C π hπ)) {w : Z}
    (hw : w ∈ (geoTransformAlong (barMarked 𝔍) (.step T C π hπ)).cosupp) (hl : s ≤ level 𝔍 (.step T C π hπ) w)
    (hnr : ¬ stepRegime 𝔍 s (.step T C π hπ) w) :
    π w ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp ∧ s ≤ level 𝔍 T (π w) ∧ ¬ stepRegime 𝔍 s T (π w) := by
  have hE : ∀ H ∈ 𝔍.E, IsClosed H := fun H hH => h𝔍.isSNCDivisor.1 H hH
  obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff _ T C π hπ).mp hT
  have hJ := isWellFormed_barMarked 𝔍 h𝔍
  obtain ⟨hNT, hcT⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hTT
  have hcos : π w ∈ (geoTransformAlong (barMarked 𝔍) T).cosupp :=
    proj_mem_cosupp_of_mem_cosupp (𝔪 := geoTransformAlong (barMarked 𝔍) T) hNT hcT
      (.step .refl C π hπ) ⟨trivial, hC⟩ hw
  have hlw := level_step_le 𝔍 hE T C π hπ w
  refine ⟨hcos, hl.trans hlw, fun hreg => hnr ?_⟩
  have hmask := (mem_lowerMask_and_isInvDomain 𝔍 h𝔍 hd hn hmax hk T hTT hcos hreg).1
  exact (stepRegime_and_le_regimeRun_of_mem_lowerMask 𝔍 h𝔍 hd hmax T (.step .refl C π hπ) hT hreg.1 hmask
    (le_antisymm (hlw.trans_eq hreg.1) hl)).1

/-- **The last centre misses the earlier mask**: along a multiple test blow-up `T₀ M σ` of `J̄` which is a canonical segment
of the Step 1 invariant, with `σ` the blowup along `C`, let `p₁` be a point of `T₀` of level `s` and `w` a point of the last
stage of `T₀ M` in the cosupport, of level at least `s` and not in the regime of level `s`.  If the non-special points of the
cosupport along `T₀ M` have lower data, `C` misses the points over the mask of `p₁`: `C` is empty or the maximum locus, which
contains no point of smaller value than `w`. -/
theorem disjoint_lowerMask_of_isCanonical (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {s : ℕ} {Y₁ Y₂ Z : CMfd.{u} n} (T₀ : BlowupTower X Y₁)
    {p₁ : Y₁} (hp₁ : level 𝔍 T₀ p₁ = s) (M : BlowupTower Y₁ Y₂) (C : Set Y₂) (π : Z → Y₂)
    (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower (barMarked 𝔍) (T₀.append M))
    (hcan : IsCanonical (barMarked 𝔍) (stepOneInv R 𝔍) (T₀.append (.step M C π hπ)))
    (hD : HasLowerData R 𝔍 (T₀.append M)) {w : Y₂}
    (hw : w ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp) (hlw : s ≤ level 𝔍 (T₀.append M) w)
    (hnw : ¬ stepRegime 𝔍 s (T₀.append M) w) :
    Disjoint C (M.proj ⁻¹' (lowerMask 𝔍 s T₀ p₁ : Set Y₁)) := by
  obtain ⟨-, hC⟩ : IsCanonical (barMarked 𝔍) (stepOneInv R 𝔍) (T₀.append M) ∧
      (C = ∅ ∨ C = maxLocus (stepOneInv R 𝔍 (T₀.append M)) (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp) :=
    hcan
  rcases hC with hC | hC
  · rw [hC]
    exact Set.empty_disjoint _
  · rw [Set.disjoint_left]
    intro q hqC hqW
    rw [hC] at hqC
    have hlt := stepOneInv_lt_of_mem_lowerMask R 𝔍 h𝔍 hd hmax T₀ M hT hp₁ hD hqC.1 hqW hlw hnw
    exact absurd (hqC.2 w hw) (not_le.mpr hlt)

/-- **The centres between two start stages miss the earlier mask** (`hir:step-one-nearby`): along a multiple test blow-up
`T₀ M σ` of `J̄` (`𝔍` well formed, `d ≥ 1`, of maximal order, `dim N ≤ k'`, `0 < n`) which is a canonical segment of the Step
1 invariant, let `p₁` be a point of `T₀` of level `s` and `w` a point of the last stage of `T₀ M` in the cosupport, of level
at least `s` and not in the regime of level `s` (in the use, the image of a point `y` one stage before the start of its run).
If along every prefix `T₀ M'` (`M'` at most as long as `M`) which is a multiple test blow-up and a canonical segment the
non-special points of the cosupport have lower data, then the centres of `M σ` miss the mask of `p₁`. -/
theorem centresAvoid_lowerMask (h𝔍 : 𝔍.IsWellFormed) (hd : 1 ≤ 𝔍.d) (hn : 0 < n)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {k' : ℕ} (hk : DimLE n 𝔍.N k') {s : ℕ} {Y₁ : CMfd.{u} n}
    (T₀ : BlowupTower X Y₁) {p₁ : Y₁} (hp₁ : level 𝔍 T₀ p₁ = s) :
    ∀ {Y₂ Z : CMfd.{u} n} (M : BlowupTower Y₁ Y₂) (C : Set Y₂) (π : Z → Y₂) (hπ : IsBlowupAlong n C π),
      IsGeoTestTower (barMarked 𝔍) (T₀.append (.step M C π hπ)) →
      IsCanonical (barMarked 𝔍) (stepOneInv R 𝔍) (T₀.append (.step M C π hπ)) →
      (∀ {Y₃ : CMfd.{u} n} (M' : BlowupTower Y₁ Y₃), M'.length ≤ M.length →
        IsGeoTestTower (barMarked 𝔍) (T₀.append M') → IsCanonical (barMarked 𝔍) (stepOneInv R 𝔍) (T₀.append M') →
        HasLowerData R 𝔍 (T₀.append M')) →
      ∀ w ∈ (geoTransformAlong (barMarked 𝔍) (T₀.append M)).cosupp, s ≤ level 𝔍 (T₀.append M) w →
        ¬ stepRegime 𝔍 s (T₀.append M) w → CentresAvoid (lowerMask 𝔍 s T₀ p₁) (.step M C π hπ)
  | _, _, .refl, C, π, hπ, hT, hcan, hD, w, hw, hlw, hnw => by
      have hT' : IsGeoTestTower (barMarked 𝔍) (T₀.append .refl) := hT.1
      have hcan' : IsCanonical (barMarked 𝔍) (stepOneInv R 𝔍) (T₀.append .refl) := hcan.1
      exact ⟨trivial, disjoint_lowerMask_of_isCanonical R 𝔍 h𝔍 hd hmax T₀ hp₁ .refl C π hπ hT' hcan
        (hD .refl le_rfl hT' hcan') hw hlw hnw⟩
  | _, _, .step M₂ C₂ π₂ hπ₂, C, π, hπ, hT, hcan, hD, w, hw, hlw, hnw => by
      have hT' : IsGeoTestTower (barMarked 𝔍) (T₀.append (.step M₂ C₂ π₂ hπ₂)) := hT.1
      have hcan' : IsCanonical (barMarked 𝔍) (stepOneInv R 𝔍) (T₀.append (.step M₂ C₂ π₂ hπ₂)) := hcan.1
      obtain ⟨hw₂, hl₂, hn₂⟩ := not_stepRegime_proj 𝔍 h𝔍 hd hn hmax hk (T₀.append M₂) C₂ π₂ hπ₂ hT' hw hlw hnw
      refine ⟨centresAvoid_lowerMask h𝔍 hd hn hmax hk T₀ hp₁ M₂ C₂ π₂ hπ₂ hT' hcan'
        (fun M' hM' => hD M' (hM'.trans (by rw [BlowupTower.length_step]; omega))) (π₂ w) hw₂ hl₂ hn₂, ?_⟩
      exact disjoint_lowerMask_of_isCanonical R 𝔍 h𝔍 hd hmax T₀ hp₁ (.step M₂ C₂ π₂ hπ₂) C π hπ hT' hcan
        (hD _ le_rfl hT' hcan') hw hlw hnw

end Avoid

end

end Hironaka.StepOneNearby
