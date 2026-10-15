/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Blowup.SharpStrictTransformExact
import Hironaka.Invariant.GeneralValueOrderZero

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The monomial invariant under an empty member inserted in the middle of the divisor

Hironaka phase H2 (TN3), for the human's decision on property (8) of the resolution invariant (inbox I-1139); claim I-0977
C-0208.  Blueprint `bcalc:monomial-invariant-empty-member` (chapter `blowup-calculus.tex`).  Sources: Włodarczyk 2005
(`wlodarczyk05-hironaka`), the extensions of a resolution (isomorphisms inserted anywhere in a sequence of blowups) and Step 2b of
Proposition `pr:resol`; Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), "inserting trivial blowings-up".

A blowup along the empty centre appends an empty member `∅` to the divisor `E`.  If the empty step sits in the MIDDLE of a tower,
every later member comes one position later.  The monomial invariant `γ` (`MonomialCaseAlong.gammaAlong`) records the members
through a point by their ABSOLUTE positions in `E` (`MonomialCase.memberIdx`), compared colexicographically
(`MonomialInvariant.Val`).  This module computes what an inserted empty member does:

* **`gammaAlong_insertIdx_empty`**: inserting `∅` at position `j ≤ #E` changes `γ` by the relabelling `shiftVal j`, which
  replaces the set of positions `K` by its image under `i ↦ if i < j then i else i + 1` (`shiftIdx`) and keeps the two other
  entries; **`strictMono_shiftVal`**: the relabelling is strictly monotone; **`shiftVal_ne_self`**: it is not the identity on a
  value whose set has a position `≥ j`;
* **`nmOrd_insertEmpty`**, `cosupp_insertEmpty`: the order of the nonmonomial part and the cosupport do not change (the monomial
  part only looks at the members through the point);
* **`geoTransformAlong_insertEmpty`**: inserting `∅` commutes with the transforms along every tower, so
  **`towerInvAlong_insertEmpty`**: `γ` of `insertEmpty j 𝔪` along `T` is `shiftVal j ∘ γ` of `𝔪` along `T`;
* **the middle empty step** (`geoTransform_empty_eq_insertEmpty`, **`towerInvAlong_step_empty_append`**,
  `nmOrd_step_empty_append`): along `T₀ σ S` with `σ` a blowup along `∅`, `γ = shiftVal (#E + |T₀|) ∘ γ'` and `ν = ν'`, where
  `γ'`, `ν'` are computed along `S` from `emptyStepBase 𝔪_{T₀} σ`, the transform by `σ` with its new empty member removed
  (restricted-equivalent to the pullback `σ^*𝔪_{T₀}`, `restrictEquiv_emptyStepBase_pullback`, so the comparison is with the
  sequence without the empty step);
* `maxLocus_shiftVal_comp`, `genInv_insertEmpty_of_nmOrd_eq_zero`: maximum loci (hence canonical centres) are unchanged, and the
  general value of TN-CLASSICAL's general step changes by the same relabelling at the points of order `0`.

So, for option (a) of I-1139 ("inserting an empty step anywhere does not change the values"): at the points of order `0` the
values DO change (as soon as a member after the inserted position passes through the point and lies in the set of `γ`), by a
strictly monotone relabelling independent of the point; the maximum loci, hence the canonical centres, are those of the
sequence without the empty step.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff Finset

universe u v

namespace Hironaka.MonomialInvariantEmptyMember

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialInvariant
  Hironaka.MonomialCase Hironaka.MonomialCaseAlong
  Hironaka.MonomialStepAlong Hironaka.MonomialPartAlong
  Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms
  Hironaka.MarkedIdealOperationsAlong.MarkedIdeal
  Hironaka.NonmonomialOrderLocal Hironaka.IdealWeightPowers
  Hironaka.DivisorExponentAlong Hironaka.GermIdealOrder
  Hironaka.BlowupStrictSubmanifold

noncomputable section

/-! ### The relabelling of positions and of values -/

section Shift

/-- **The position of a member after an empty member is inserted at position `j`**: `i` if `i < j`, `i + 1` otherwise. -/
def shiftIdx (j i : ℕ) : ℕ := if i < j then i else i + 1

theorem strictMono_shiftIdx (j : ℕ) : StrictMono (shiftIdx j) := by
  intro a b hab
  unfold shiftIdx
  split_ifs <;> omega

theorem shiftIdx_ne (j i : ℕ) : shiftIdx j i ≠ j := by
  unfold shiftIdx
  split_ifs <;> omega

theorem shiftIdx_of_lt {j i : ℕ} (h : i < j) : shiftIdx j i = i := if_pos h

theorem shiftIdx_of_le {j i : ℕ} (h : j ≤ i) : shiftIdx j i = i + 1 := if_neg (by omega)

/-- **The relabelled set of positions.** -/
def shiftSet (j : ℕ) (K : Finset ℕ) : Finset ℕ := K.image (shiftIdx j)

theorem card_shiftSet (j : ℕ) (K : Finset ℕ) : #(shiftSet j K) = #K :=
  Finset.card_image_of_injective K (strictMono_shiftIdx j).injective

theorem sum_shiftSet (j : ℕ) (K : Finset ℕ) (a : ℕ → ℕ) :
    ∑ i ∈ shiftSet j K, a i = ∑ i ∈ K, a (shiftIdx j i) :=
  Finset.sum_image fun _ _ _ _ h => (strictMono_shiftIdx j).injective h

/-- **The relabelled value**: the set of positions is relabelled by `shiftIdx j`, the two other entries are kept. -/
def shiftKey (j : ℕ) (v : Val) : Val :=
  toLex ((ofLex v).1, toLex ((ofLex (ofLex v).2).1, toColex (shiftSet j (ofColex (ofLex (ofLex v).2).2))))

theorem shiftKey_lt_shiftKey (j : ℕ) {v w : Val} : shiftKey j v < shiftKey j w ↔ v < w := by
  change toLex ((ofLex v).1, toLex ((ofLex (ofLex v).2).1, toColex (shiftSet j (ofColex (ofLex (ofLex v).2).2)))) <
      toLex ((ofLex w).1, toLex ((ofLex (ofLex w).2).1, toColex (shiftSet j (ofColex (ofLex (ofLex w).2).2)))) ↔
    toLex ((ofLex v).1, toLex ((ofLex (ofLex v).2).1, toColex (ofColex (ofLex (ofLex v).2).2))) <
      toLex ((ofLex w).1, toLex ((ofLex (ofLex w).2).1, toColex (ofColex (ofLex (ofLex w).2).2)))
  simp only [Prod.Lex.toLex_lt_toLex, shiftSet, Finset.Colex.toColex_image_lt_toColex_image (strictMono_shiftIdx j)]

theorem strictMono_shiftKey (j : ℕ) : StrictMono (shiftKey j) := fun _ _ h => (shiftKey_lt_shiftKey j).mpr h

/-- **The relabelling of the values of the monomial invariant** (`⊥` is kept). -/
def shiftVal (j : ℕ) : WithBot Val → WithBot Val := WithBot.map (shiftKey j)

theorem strictMono_shiftVal (j : ℕ) : StrictMono (shiftVal j) := (strictMono_shiftKey j).withBot_map

theorem shiftVal_bot (j : ℕ) : shiftVal j ⊥ = ⊥ := rfl

theorem shiftVal_coe (j : ℕ) (v : Val) : shiftVal j (v : WithBot Val) = (shiftKey j v : WithBot Val) := rfl

/-- A set with a position `≥ j` is moved by the relabelling: its largest position `m` goes to `m + 1 ∉ K`. -/
theorem shiftSet_ne_self {j : ℕ} {K : Finset ℕ} (h : ∃ i ∈ K, j ≤ i) : shiftSet j K ≠ K := by
  obtain ⟨i, hi, hji⟩ := h
  have hne : K.Nonempty := ⟨i, hi⟩
  have hm : K.max' hne + 1 ∈ shiftSet j K := by
    refine Finset.mem_image.mpr ⟨K.max' hne, K.max'_mem hne, ?_⟩
    exact shiftIdx_of_le (hji.trans (K.le_max' i hi))
  intro heq
  rw [heq] at hm
  have := K.le_max' _ hm
  omega

/-- **The relabelling is not the identity** on a value whose set of positions has a position `≥ j`. -/
theorem shiftVal_ne_self {j : ℕ} {v : Val} (h : ∃ i ∈ ofColex (ofLex (ofLex v).2).2, j ≤ i) :
    shiftVal j (v : WithBot Val) ≠ v := by
  rw [shiftVal_coe, Ne, WithBot.coe_inj]
  intro heq
  have h3 := congrArg (fun w : Val => ofColex (ofLex (ofLex w).2).2) heq
  exact shiftSet_ne_self h h3

/-- **Maximum loci do not change** under the relabelling. -/
theorem maxLocus_shiftVal_comp {Y : Type*} (j : ℕ) (f : Y → WithBot Val) (s : Set Y) :
    ResolutionDriver.maxLocus (shiftVal j ∘ f) s = ResolutionDriver.maxLocus f s :=
  MaxLocusLocal.maxLocus_comp_strictMono (strictMono_shiftVal j) f s

end Shift

/-! ### The invariant of a set of members with relabelled positions -/

section Inv

variable {n d j : ℕ} {S : Finset ℕ} {a a' : ℕ → ℕ}

/-- The key of a relabelled set, for exponents read at the relabelled positions. -/
theorem key_shiftSet (ha : ∀ i, a' (shiftIdx j i) = a i) (K : Finset ℕ) :
    key n a' (shiftSet j K) = shiftKey j (key n a K) := by
  simp only [key, shiftKey, ofLex_toLex, ofColex_toColex, card_shiftSet, sum_shiftSet, ha]

/-- The feasible sets of the relabelled members are the relabelled feasible sets. -/
theorem feasible_shiftSet (ha : ∀ i, a' (shiftIdx j i) = a i) :
    feasible (shiftSet j S) a' d = (feasible S a d).image (shiftSet j) := by
  ext K'
  simp only [mem_feasible, Finset.mem_image]
  constructor
  · rintro ⟨hK', hd⟩
    refine ⟨S.filter fun i => shiftIdx j i ∈ K', ⟨Finset.filter_subset _ _, ?_⟩, ?_⟩
    · have hset : shiftSet j (S.filter fun i => shiftIdx j i ∈ K') = K' := by
        ext x
        simp only [shiftSet, Finset.mem_image, Finset.mem_filter]
        constructor
        · rintro ⟨i, ⟨-, hi⟩, rfl⟩
          exact hi
        · intro hx
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hK' hx)
          exact ⟨i, ⟨hi, hx⟩, rfl⟩
      rw [← hset, sum_shiftSet] at hd
      simpa only [ha] using hd
    · ext x
      simp only [shiftSet, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨i, ⟨-, hi⟩, rfl⟩
        exact hi
      · intro hx
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hK' hx)
        exact ⟨i, ⟨hi, hx⟩, rfl⟩
  · rintro ⟨K, ⟨hKS, hd⟩, rfl⟩
    refine ⟨Finset.image_subset_image hKS, ?_⟩
    rw [sum_shiftSet]
    simpa only [ha] using hd

/-- The maximum of an image under a monotone map. -/
theorem max_image_of_monotone {α β : Type*} [LinearOrder α] [LinearOrder β] [DecidableEq β] {g : α → β}
    (hg : Monotone g) (s : Finset α) : (s.image g).max = WithBot.map g s.max := by
  rw [Finset.max_eq_sup_withBot, Finset.max_eq_sup_withBot, Finset.sup_image,
    Finset.apply_sup_eq_sup_comp (WithBot.map g) (WithBot.monotone_map_iff.mpr hg).map_sup rfl]
  rfl

/-- **The monomial invariant of relabelled members** is the relabelled invariant. -/
theorem inv_shiftSet (ha : ∀ i, a' (shiftIdx j i) = a i) :
    inv n (shiftSet j S) a' d = shiftVal j (inv n S a d) := by
  classical
  unfold inv
  rw [feasible_shiftSet ha, Finset.image_image]
  have hfun : (key n a' ∘ shiftSet j) = shiftKey j ∘ key n a := by
    funext K
    exact key_shiftSet ha K
  rw [hfun, ← Finset.image_image, max_image_of_monotone (strictMono_shiftKey j).monotone]
  rfl

end Inv

/-! ### One stage: an empty member inserted into the divisor -/

section Stage

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **The members through `x` after inserting `∅` at position `j ≤ #E`** are the relabelled ones. -/
theorem memberIdx_insertIdx_empty (E : List (Set M)) {j : ℕ} (hj : j ≤ E.length) (x : M) :
    memberIdx (E.insertIdx j ∅) x = shiftSet j (memberIdx E x) := by
  have hlen : (E.insertIdx j ∅).length = E.length + 1 := List.length_insertIdx_of_le_length hj ∅
  ext i
  rw [mem_memberIdx, shiftSet, Finset.mem_image]
  constructor
  · rintro ⟨hi, hx⟩
    rw [List.get_eq_getElem] at hx
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [List.getElem_insertIdx_of_lt hij] at hx
      exact ⟨i, (mem_memberIdx E).mpr ⟨by omega, by rwa [List.get_eq_getElem]⟩, shiftIdx_of_lt hij⟩
    · rw [List.getElem_insertIdx_self] at hx
      exact absurd hx (Set.notMem_empty x)
    · rw [List.getElem_insertIdx_of_gt hij] at hx
      exact ⟨i - 1, (mem_memberIdx E).mpr ⟨by omega, by rwa [List.get_eq_getElem]⟩,
        by rw [shiftIdx_of_le (by omega)]; omega⟩
  · rintro ⟨i', hi', rfl⟩
    obtain ⟨hi'E, hx⟩ := (mem_memberIdx E).mp hi'
    rw [List.get_eq_getElem] at hx
    rcases lt_or_ge i' j with hij | hij
    · rw [shiftIdx_of_lt hij]
      refine ⟨by omega, ?_⟩
      simp only [List.get_eq_getElem]
      rw [List.getElem_insertIdx_of_lt hij]
      exact hx
    · rw [shiftIdx_of_le hij]
      refine ⟨by omega, ?_⟩
      simp only [List.get_eq_getElem]
      rw [List.getElem_insertIdx_of_gt (show j < i' + 1 by omega)]
      exact hx

/-- **The exponents at the relabelled positions** are the old ones. -/
theorem expDataAlong_insertIdx_empty (N : Set M) (𝔞 : GermIdeal n M) (E : List (Set M)) {j : ℕ} (hj : j ≤ E.length)
    (x : M) (i : ℕ) :
    expDataAlong n N 𝔞 (E.insertIdx j ∅) x (shiftIdx j i) = expDataAlong n N 𝔞 E x i := by
  have hlen : (E.insertIdx j ∅).length = E.length + 1 := List.length_insertIdx_of_le_length hj ∅
  unfold expDataAlong
  rcases lt_or_ge i j with hij | hij
  · rw [shiftIdx_of_lt hij, dif_pos (by omega), dif_pos (by omega)]
    simp only [List.get_eq_getElem]
    rw [List.getElem_insertIdx_of_lt hij]
  · rw [shiftIdx_of_le hij]
    by_cases hiE : i < E.length
    · rw [dif_pos (by omega), dif_pos hiE]
      simp only [List.get_eq_getElem]
      rw [List.getElem_insertIdx_of_gt (by omega)]
      rfl
    · rw [dif_neg (by omega), dif_neg hiE]

/-- **One stage: inserting an empty member at position `j ≤ #E` relabels the monomial invariant.** -/
theorem gammaAlong_insertIdx_empty (N : Set M) (𝔞 : GermIdeal n M) (E : List (Set M)) {j : ℕ} (hj : j ≤ E.length)
    (d : ℕ) (x : M) :
    gammaAlong n N 𝔞 (E.insertIdx j ∅) d x = shiftVal j (gammaAlong n N 𝔞 E d x) := by
  unfold gammaAlong
  rw [memberIdx_insertIdx_empty E hj x]
  exact inv_shiftSet (expDataAlong_insertIdx_empty N 𝔞 E hj x)

/-- The members of a list after inserting `∅`, for a property that holds at `∅`. -/
theorem forall_get_insertIdx_empty_iff (E : List (Set M)) {j : ℕ} (hj : j ≤ E.length) {Q : Set M → Prop}
    (hQ : Q ∅) :
    (∀ i : Fin (E.insertIdx j ∅).length, Q ((E.insertIdx j ∅).get i)) ↔ ∀ i : Fin E.length, Q (E.get i) := by
  have hiff : ∀ l : List (Set M), (∀ i : Fin l.length, Q (l.get i)) ↔ ∀ H ∈ l, Q H := fun l =>
    ⟨fun h H hH => by obtain ⟨i, rfl⟩ := List.get_of_mem hH; exact h i, fun h i => h _ (List.get_mem l i)⟩
  rw [hiff, hiff]
  constructor
  · intro h H hH
    exact h H ((List.mem_insertIdx hj).mpr (Or.inr hH))
  · intro h H hH
    rcases (List.mem_insertIdx hj).mp hH with rfl | hH
    · exact hQ
    · exact h H hH

/-- **The monomial part does not see an inserted empty member** (it only looks at the members through the point). -/
theorem monomialPartAlong_insertIdx_empty (N : Set M) (𝔞 : GermIdeal n M) (E : List (Set M)) {j : ℕ}
    (hj : j ≤ E.length) : monomialPartAlong n N 𝔞 (E.insertIdx j ∅) = monomialPartAlong n N 𝔞 E := by
  ext y g
  simp only [monomialPartAlong]
  refine and_congr_right fun _ => ?_
  exact forall_get_insertIdx_empty_iff E hj (Q := fun H => y ∈ N → y ∈ H →
    IsInSpanOnAt (n := n) N ((idealPow (vanishingIdeal (n := n) H) (divExpAlong n N 𝔞 H y)).mem y) y g)
    (fun _ hy => absurd hy (Set.notMem_empty y))

end Stage

/-! ### Marked ideals with an inserted empty member, along towers -/

section Marked

variable {n : ℕ}

/-- **The marked ideal with an empty member inserted at position `j`** of its divisor (same `N`, ideal and mark). -/
def insertEmpty {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] (j : ℕ) (𝔪 : MarkedIdeal n M) :
    MarkedIdeal n M :=
  { 𝔪 with E := 𝔪.E.insertIdx j ∅ }

/-- Inserting into the first part of a concatenation. -/
theorem insertIdx_append_of_le_length {α : Type*} (a : α) :
    ∀ (l₁ l₂ : List α) {j : ℕ}, j ≤ l₁.length → (l₁ ++ l₂).insertIdx j a = l₁.insertIdx j a ++ l₂
  | [], l₂, j, hj => by
      obtain rfl : j = 0 := by simpa using hj
      simp
  | x :: l₁, l₂, 0, _ => by simp
  | x :: l₁, l₂, j + 1, hj => by
      rw [List.cons_append, List.insertIdx_succ_cons, List.insertIdx_succ_cons, List.cons_append,
        insertIdx_append_of_le_length a l₁ l₂ (by simpa using hj)]

section Stage

variable {M : CMfd.{u} n} (𝔪 : MarkedIdeal n M) {j : ℕ}

theorem cosupp_insertEmpty : (insertEmpty j 𝔪).cosupp = 𝔪.cosupp := rfl

/-- **The nonmonomial part does not see an inserted empty member.** -/
theorem nmPart_insertEmpty (hj : j ≤ 𝔪.E.length) : nmPart (insertEmpty j 𝔪) = nmPart 𝔪 := by
  show nonmonomialPartAlong n 𝔪.N 𝔪.ideal (𝔪.E.insertIdx j ∅) = nonmonomialPartAlong n 𝔪.N 𝔪.ideal 𝔪.E
  unfold nonmonomialPartAlong
  rw [monomialPartAlong_insertIdx_empty _ _ _ hj]

theorem ordGe_insertEmpty (hj : j ≤ 𝔪.E.length) (q : ℕ) : ordGe (insertEmpty j 𝔪) q = ordGe 𝔪 q := by
  show cosupport n 𝔪.N (nmPart (insertEmpty j 𝔪)) q = cosupport n 𝔪.N (nmPart 𝔪) q
  rw [nmPart_insertEmpty 𝔪 hj]

/-- **The order of the nonmonomial part does not change.** -/
theorem nmOrd_insertEmpty (hj : j ≤ 𝔪.E.length) (y : M) : nmOrd (insertEmpty j 𝔪) y = nmOrd 𝔪 y :=
  nmOrd_congr fun q => by rw [ordGe_insertEmpty 𝔪 hj q]

/-- **The monomial invariant is relabelled.** -/
theorem gammaAlong_insertEmpty (hj : j ≤ 𝔪.E.length) (y : M) :
    gammaAlong n (insertEmpty j 𝔪).N (insertEmpty j 𝔪).ideal (insertEmpty j 𝔪).E (insertEmpty j 𝔪).d y =
      shiftVal j (gammaAlong n 𝔪.N 𝔪.ideal 𝔪.E 𝔪.d y) :=
  gammaAlong_insertIdx_empty 𝔪.N 𝔪.ideal 𝔪.E hj 𝔪.d y

/-- **Inserting an empty member commutes with one transform** (the strict transform of `∅` is `∅`, the exceptional member is
appended at the end). -/
theorem geoTransform_insertEmpty {Z : CMfd.{u} n} (hj : j ≤ 𝔪.E.length) (C : Set M) (π : Z → M) :
    (insertEmpty j 𝔪).geoTransform C π = insertEmpty j (𝔪.geoTransform C π) := by
  have hst : geoStrictTransform π C (∅ : Set M) = ∅ := geoStrictTransform_eq_empty_of_subset (empty_subset C)
  show MarkedIdeal.mk _ ((𝔪.E.insertIdx j ∅).map (geoStrictTransform π C) ++ [π ⁻¹' C]) _ _ =
    MarkedIdeal.mk _ ((𝔪.E.map (geoStrictTransform π C) ++ [π ⁻¹' C]).insertIdx j ∅) _ _
  rw [List.map_insertIdx, hst, insertIdx_append_of_le_length _ _ _ (by rw [List.length_map]; exact hj)]
  rfl

end Stage

section Tower

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) {j : ℕ}

/-- **Inserting an empty member commutes with the transforms along every tower.** -/
theorem geoTransformAlong_insertEmpty (hj : j ≤ 𝔪.E.length) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      geoTransformAlong (insertEmpty j 𝔪) T = insertEmpty j (geoTransformAlong 𝔪 T)
  | _, .refl => rfl
  | _, .step T C π hπ => by
      rw [geoTransformAlong_step, geoTransformAlong_step, geoTransformAlong_insertEmpty hj T]
      exact geoTransform_insertEmpty _ (by rw [length_E_geoTransformAlong]; omega) C π

theorem le_length_E_geoTransformAlong (hj : j ≤ 𝔪.E.length) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    j ≤ (geoTransformAlong 𝔪 T).E.length := by
  rw [length_E_geoTransformAlong]
  omega

/-- **Along every tower the monomial invariant of `insertEmpty j 𝔪` is the relabelled invariant of `𝔪`.** -/
theorem towerInvAlong_insertEmpty (hj : j ≤ 𝔪.E.length) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    towerInvAlong (insertEmpty j 𝔪) T y = shiftVal j (towerInvAlong 𝔪 T y) := by
  unfold towerInvAlong
  rw [geoTransformAlong_insertEmpty 𝔪 hj T]
  exact gammaAlong_insertEmpty _ (le_length_E_geoTransformAlong 𝔪 hj T) y

/-- Along every tower the order of the nonmonomial part does not change. -/
theorem nmOrd_geoTransformAlong_insertEmpty (hj : j ≤ 𝔪.E.length) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    nmOrd (geoTransformAlong (insertEmpty j 𝔪) T) y = nmOrd (geoTransformAlong 𝔪 T) y := by
  rw [geoTransformAlong_insertEmpty 𝔪 hj T]
  exact nmOrd_insertEmpty _ (le_length_E_geoTransformAlong 𝔪 hj T) y

/-- Along every tower the cosupport does not change. -/
theorem cosupp_geoTransformAlong_insertEmpty (hj : j ≤ 𝔪.E.length) {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    (geoTransformAlong (insertEmpty j 𝔪) T).cosupp = (geoTransformAlong 𝔪 T).cosupp := by
  rw [geoTransformAlong_insertEmpty 𝔪 hj T]
  rfl

/-- **Maximum loci of the monomial invariant do not change.** -/
theorem maxLocus_towerInvAlong_insertEmpty (hj : j ≤ 𝔪.E.length) {Y : CMfd.{u} n} (T : BlowupTower X Y) (s : Set Y) :
    ResolutionDriver.maxLocus (towerInvAlong (insertEmpty j 𝔪) T) s = ResolutionDriver.maxLocus (towerInvAlong 𝔪 T) s := by
  rw [show towerInvAlong (insertEmpty j 𝔪) T = shiftVal j ∘ towerInvAlong 𝔪 T from
    funext fun y => towerInvAlong_insertEmpty 𝔪 hj T y]
  exact maxLocus_shiftVal_comp j _ s

end Tower

/-! ### An empty step in the middle of a tower -/

section Middle

/-- **The transform by a blowup `σ` along `∅` with its new (empty) member removed**: the marked ideal "without the empty step",
transported along `σ` (restricted-equivalent to the pullback `σ^*𝔫`, `restrictEquiv_emptyStepBase_pullback`). -/
def emptyStepBase {Y Z : CMfd.{u} n} (𝔫 : MarkedIdeal n Y) (σ : Z → Y) : MarkedIdeal n Z :=
  { 𝔫.geoTransform ∅ σ with E := 𝔫.E.map (geoStrictTransform σ ∅) }

theorem length_E_emptyStepBase {Y Z : CMfd.{u} n} (𝔫 : MarkedIdeal n Y) (σ : Z → Y) :
    (emptyStepBase 𝔫 σ).E.length = 𝔫.E.length :=
  List.length_map _

/-- **The transform along `∅` is the base without the empty step, with the empty member appended.** -/
theorem geoTransform_empty_eq_insertEmpty {Y Z : CMfd.{u} n} (𝔫 : MarkedIdeal n Y) (σ : Z → Y) :
    𝔫.geoTransform ∅ σ = insertEmpty 𝔫.E.length (emptyStepBase 𝔫 σ) := by
  show MarkedIdeal.mk _ (𝔫.E.map (geoStrictTransform σ ∅) ++ [σ ⁻¹' ∅]) _ _ =
    MarkedIdeal.mk _ ((𝔫.E.map (geoStrictTransform σ ∅)).insertIdx 𝔫.E.length ∅) _ _
  have h := List.insertIdx_length_self (l := 𝔫.E.map (geoStrictTransform σ ∅)) (x := (∅ : Set Z))
  rw [List.length_map] at h
  rw [Set.preimage_empty, h]
  rfl

/-- **The base without the empty step is restricted-equivalent to the pullback** along the blowup `σ` along `∅` (for `N` and
the members closed): `N` and the members are their preimages (`ContactCanonicalAlong.geoStrictTransform_empty`), and the
ideals agree on `N'` (`ContactCanonicalAlong.restrictLe_geoTransform_empty_le_pullback`,
`ContactCanonicalAlong.restrictLe_pullback_le_geoTransform`). -/
theorem restrictEquiv_emptyStepBase_pullback {Y Z : CMfd.{u} n} (𝔫 : MarkedIdeal n Y) {σ : Z → Y}
    (hσ : IsBlowupAlong n (∅ : Set Y) σ) (hN : IsClosed 𝔫.N) (hE : ∀ H ∈ 𝔫.E, IsClosed H) :
    RestrictEquiv (emptyStepBase 𝔫 σ) (MarkedIdeal.pullback σ 𝔫) where
  N_eq := ContactCanonicalAlong.geoStrictTransform_empty hσ.contMDiff.continuous hN
  E_eq := List.map_congr_left fun H hH => ContactCanonicalAlong.geoStrictTransform_empty hσ.contMDiff.continuous (hE H hH)
  d_eq := rfl
  le := ContactCanonicalAlong.restrictLe_geoTransform_empty_le_pullback hσ 𝔫
  ge := ContactCanonicalAlong.restrictLe_pullback_le_geoTransform ∅ 𝔫

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) {Y₀ Z₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (σ : Z₀ → Y₀)
  (hσ : IsBlowupAlong n (∅ : Set Y₀) σ) (S : BlowupTower Z₀ Y)

/-- **Along `T₀ σ S` with `σ` a blowup along `∅`**, the transform is that of the base without the empty step along `S`, with
an empty member inserted at position `#E + |T₀|`. -/
theorem geoTransformAlong_step_empty_append :
    geoTransformAlong 𝔪 ((BlowupTower.step T₀ ∅ σ hσ).append S) =
      insertEmpty (𝔪.E.length + T₀.length) (geoTransformAlong (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S) := by
  rw [geoTransformAlong_append, geoTransformAlong_step, geoTransform_empty_eq_insertEmpty,
    geoTransformAlong_insertEmpty _ (le_of_eq (length_E_emptyStepBase _ σ).symm), length_E_geoTransformAlong]

theorem le_length_E_step_empty_append :
    𝔪.E.length + T₀.length ≤ (geoTransformAlong (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S).E.length := by
  rw [length_E_geoTransformAlong, length_E_emptyStepBase, length_E_geoTransformAlong]
  omega

/-- **The monomial invariant after an empty step in the middle of a tower** is the invariant along the rest of the tower from
the base without the empty step, relabelled by `shiftVal (#E + |T₀|)`. -/
theorem towerInvAlong_step_empty_append (z : Y) :
    towerInvAlong 𝔪 ((BlowupTower.step T₀ ∅ σ hσ).append S) z =
      shiftVal (𝔪.E.length + T₀.length) (towerInvAlong (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S z) := by
  unfold towerInvAlong
  rw [geoTransformAlong_step_empty_append]
  exact gammaAlong_insertEmpty _ (le_length_E_step_empty_append 𝔪 T₀ σ S) z

/-- **The order of the nonmonomial part after an empty step in the middle of a tower** is that along the rest of the tower from
the base without the empty step. -/
theorem nmOrd_step_empty_append (z : Y) :
    nmOrd (geoTransformAlong 𝔪 ((BlowupTower.step T₀ ∅ σ hσ).append S)) z =
      nmOrd (geoTransformAlong (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S) z := by
  rw [geoTransformAlong_step_empty_append]
  exact nmOrd_insertEmpty _ (le_length_E_step_empty_append 𝔪 T₀ σ S) z

/-- The cosupport after an empty step in the middle of a tower is that along the rest of the tower from the base without the
empty step. -/
theorem cosupp_step_empty_append :
    (geoTransformAlong 𝔪 ((BlowupTower.step T₀ ∅ σ hσ).append S)).cosupp =
      (geoTransformAlong (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S).cosupp := by
  rw [geoTransformAlong_step_empty_append]
  rfl

/-- **Maximum loci of the monomial invariant after an empty step in the middle of a tower** are those along the rest of the
tower from the base without the empty step. -/
theorem maxLocus_towerInvAlong_step_empty_append (s : Set Y) :
    ResolutionDriver.maxLocus (towerInvAlong 𝔪 ((BlowupTower.step T₀ ∅ σ hσ).append S)) s =
      ResolutionDriver.maxLocus (towerInvAlong (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S) s := by
  rw [show towerInvAlong 𝔪 ((BlowupTower.step T₀ ∅ σ hσ).append S) =
      shiftVal (𝔪.E.length + T₀.length) ∘ towerInvAlong (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S from
    funext fun z => towerInvAlong_step_empty_append 𝔪 T₀ σ hσ S z]
  exact maxLocus_shiftVal_comp _ _ s

/-- **The comparison with the pullback** (the sequence without the empty step): if `N` and the members of `𝔪_{T₀}` are closed
and the ideals of the transform along `σ` and of the pullback `σ^*𝔪_{T₀}` are coherent, the invariant after the empty step is
the relabelled invariant of `σ^*𝔪_{T₀}` along `S` (`NonmonomialOrderMonomialTransport.towerInvAlong_congr`). -/
theorem towerInvAlong_step_empty_append_pullback (hN : IsClosed (geoTransformAlong 𝔪 T₀).N)
    (hE : ∀ H ∈ (geoTransformAlong 𝔪 T₀).E, IsClosed H)
    (hc : ((geoTransformAlong 𝔪 T₀).geoTransform ∅ σ).ideal.IsCoherent)
    (hc' : (MarkedIdeal.pullback σ (geoTransformAlong 𝔪 T₀)).ideal.IsCoherent) (z : Y) :
    towerInvAlong 𝔪 ((BlowupTower.step T₀ ∅ σ hσ).append S) z =
      shiftVal (𝔪.E.length + T₀.length) (towerInvAlong (MarkedIdeal.pullback σ (geoTransformAlong 𝔪 T₀)) S z) := by
  rw [towerInvAlong_step_empty_append,
    NonmonomialOrderMonomialTransport.towerInvAlong_congr
      (restrictEquiv_emptyStepBase_pullback _ hσ hN hE) isClosed_closure hc hc' S]

end Middle

/-! ### The general value at the points of order zero -/

section General

variable {Λ : Type v} [LinearOrder Λ]
  (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)

/-- **The general value of `insertEmpty j 𝔪` at a point of order `0`** is `(0, inl (shiftVal j γ))`. -/
theorem genInv_insertEmpty_of_nmOrd_eq_zero {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) {j : ℕ} (hj : j ≤ 𝔪.E.length)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y} (h0 : nmOrd (geoTransformAlong 𝔪 T) y = 0) :
    GeneralValue.genInv M (insertEmpty j 𝔪) T y =
      toLex ((0 : ℕ), (toLex (Sum.inl (shiftVal j (towerInvAlong 𝔪 T y))) : WithBot Val ⊕ₗ WithTop Λ)) := by
  rw [GeneralValueOrderZero.genInv_eq_towerInvAlong M _ T
    ((nmOrd_geoTransformAlong_insertEmpty 𝔪 hj T y).trans h0), towerInvAlong_insertEmpty 𝔪 hj T y]

variable {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) {Y₀ Z₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (σ : Z₀ → Y₀)
  (hσ : IsBlowupAlong n (∅ : Set Y₀) σ) (S : BlowupTower Z₀ Y)

/-- **The general value after an empty step in the middle of a tower, at a point of order `0`**: it is the general value along
the rest of the tower from the base without the empty step, with `γ` relabelled by `shiftVal (#E + |T₀|)`. -/
theorem genInv_step_empty_append_of_nmOrd_eq_zero {z : Y}
    (h0 : nmOrd (geoTransformAlong (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S) z = 0) :
    GeneralValue.genInv M 𝔪 ((BlowupTower.step T₀ ∅ σ hσ).append S) z =
        toLex ((0 : ℕ), (toLex (Sum.inl (shiftVal (𝔪.E.length + T₀.length)
          (towerInvAlong (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S z))) : WithBot Val ⊕ₗ WithTop Λ)) ∧
      GeneralValue.genInv M (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S z =
        toLex ((0 : ℕ), (toLex (Sum.inl (towerInvAlong (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S z)) :
          WithBot Val ⊕ₗ WithTop Λ)) := by
  refine ⟨?_, GeneralValueOrderZero.genInv_eq_towerInvAlong M _ S h0⟩
  rw [GeneralValueOrderZero.genInv_eq_towerInvAlong M 𝔪 _ ((nmOrd_step_empty_append 𝔪 T₀ σ hσ S z).trans h0),
    towerInvAlong_step_empty_append]

/-- **"Inserting an empty step does not change the values" fails at order `0`**: at a point `z` of order `0` whose invariant
along the rest of the tower from the base without the empty step is a value `v` (not `⊥`) whose set of members has a position
`≥ #E + |T₀|` (a member created after the empty step passes through `z` and is used by `γ`), the general value after the empty
step differs from the general value without it. -/
theorem genInv_step_empty_append_ne {z : Y}
    (h0 : nmOrd (geoTransformAlong (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S) z = 0) {v : Val}
    (hv : towerInvAlong (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S z = v)
    (hpos : ∃ i ∈ ofColex (ofLex (ofLex v).2).2, 𝔪.E.length + T₀.length ≤ i) :
    GeneralValue.genInv M 𝔪 ((BlowupTower.step T₀ ∅ σ hσ).append S) z ≠
      GeneralValue.genInv M (emptyStepBase (geoTransformAlong 𝔪 T₀) σ) S z := by
  obtain ⟨h1, h2⟩ := genInv_step_empty_append_of_nmOrd_eq_zero M 𝔪 T₀ σ hσ S h0
  rw [h1, h2, hv]
  intro heq
  have h := congrArg (fun p : ℕ ×ₗ (WithBot Val ⊕ₗ WithTop Λ) => (ofLex p).2) heq
  simp only [ofLex_toLex] at h
  exact shiftVal_ne_self hpos (Sum.inl_injective (toLex.injective h))

end General

end Marked

end

end Hironaka.MonomialInvariantEmptyMember
