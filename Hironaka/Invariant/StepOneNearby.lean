/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneMaskTower
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupRestrictOpen
import Hironaka.Blowup.BlowupTowerIsoTail
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneRegime
import Hironaka.Invariant.StepOneValue
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Comparing nearby points in Step 1: splits at two stages, two open sets, the steps between two starts

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 1, and the lemma on the
commutativity of the resolution procedure with étale morphisms (the invariants of points "remain unchanged when the
points are transformed isomorphically"; blow-ups whose centres miss an open set restrict to isomorphisms over it).

The canonical-tail theorem compares the value of a nearby point `p`, computed from its own (possibly earlier) start
stage and its own mask, with the lower-dimensional invariant of the reference point. This module provides the tools
of that comparison which do not depend on the step (1ab or 1bb):

* `exists_split_le`: **the split at two indices** -- for `a ≤ b` the head at `b` followed by a middle part `M` is the head
  at `a`, and `M` followed by the tail at `a` is the tail at `b`;
* `mem_cosupp_restrict_nested_iff`, `inv_eq_of_two_opens`: **values of a resolution invariant on two open sets** of
  one stage agree at the points of the cosupport over both (`MaxLocusLocal.restrict_nestedOpens`, applied to the
  intersection);
* `mem_origMembers_iff_of_mem_maskA`: **same-level points of a Step 1ab mask lie on the same original members**, so
  their restricted marked ideals (`memberRestrict` at `membersThrough`) coincide;
* `not_stepRegime_proj`: a point out of that regime comes from a point out of it (a point in the regime lies in its own
  mask, and the points over the mask of its level stay in the regime, `StepOneMaskTower`);
* So these steps are empty over the mask, and re-basing (`emptyPrefix`) applies.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneNearby

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneRegime Hironaka.StepOneValue Hironaka.StepOneLowerDomain Hironaka.StepOneMaskTower Hironaka.BoundaryCount Hironaka.InvDomainMemberRestriction Hironaka.MarkedIdealBiholomorphism Hironaka.BlowupTowerIsomorphism Hironaka.MaxLocusLocal Hironaka.RestrictEmptyTower Hironaka.MarkedIdealRestrictOpen Hironaka.HomogenizedIdealAlong
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

/-- **The cosupport along nested open sets**: for `V ⊆ W` open and `T|_W` a multiple test blow-up of `𝔫|_W`, a point
over `V` lies in the cosupport of `𝔫|_V` along `T|_V` iff it lies in that of `𝔫|_W` along `T|_W` (isomorphism
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

/-- **Values of a resolution invariant on two open sets**: let `𝔫` have a coherent ideal and `N` a closed submanifold,
and `A`, `B` be opens of the base of `T` such that `𝔫|_A`, `𝔫|_B` lie in the domain of `R` and `T|_A`, `T|_B` are
canonical segments of them. At a point over `A ∩ B` in the cosupport along `T|_A`, the two values agree, and the
point lies in the cosupport along `T|_B` (`restrict_nestedOpens` for `A ∩ B ⊆ A` and `A ∩ B ⊆ B`). -/
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

end Members

/-! ### The steps between two start stages are empty over the earlier mask -/

section Avoid

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n k Λ)
  (𝔍 : MarkedIdeal n X)

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

end Avoid

end

end Hironaka.StepOneNearby
