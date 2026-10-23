/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.StableDown

/-!
# The stability criterion along a whole fibre: counting (Temkin, Lemma 4.4.2)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), Lemma 4.4.2
(`stabcritlem`, T:3106–3133) compares a normal curve `C` and a semi-stable modification `C′` at a
point `x`, after shrinking `C` so that `x` is the only point of the modification locus and
compactifying (T:3108–3118). In the de Jong route all curves are projective (plan S5), and we
avoid the compactification by working with all points `x₁, …, x_l` of the modification locus in
a fibre `C_s` at once (blueprint `lem:sm-stability-criterion`): the genus formula (Lemma B.1)
for `C′_s` and `C_s`, whose arithmetic genera agree (`BlowDown.Genus`), gives
`∑_j g(x_j) = ∑_j δ♭(Y_j)` for the connected fibres `Y_j = f⁻¹(x_j)`, and each summand satisfies
`g(x_j) ≥ |x̃_j| − 1 = |∂Y_j| − 1`, `δ♭(Y_j) = |∂Y_j| − 1 + p_a(Y_j)` with `p_a(Y_j) ≥ 0`. Hence
**all `x_j` are ordinary points if and only if all `Y_j` are `ℙ¹`-trees**. This file proves this
counting step (the multi-point form of Corollary B.2, `CurvesField.Genus.stabdown_*`) and the
bookkeeping of marks that turns it into "semi-stable at all `x_j` iff all `Y_j` are exceptional
trees".

## Main results

* `stabdown_numerical_finset`: numerical form for a finite family of points.
* `gluing_iff_delta_of_isAlgClosed`, `stabdown_gluing_iff_finset`: local-algebra form over an
  algebraically closed field (ordinary points as gluing rings, `CurvesField.Delta.gluing`).
* `semistable_iff_exceptional`: with `n = |∂Y| ≥ 1` branches and `m` marks through `x`,
  "`x` ordinary with `n ≤ 2`, at most one mark, and a mark only at a smooth point" is equivalent to
  "`Y` a `ℙ¹`-tree with `n + m ≤ 2`".
-/

namespace DeJongAlterations.StableModification.BlowDown

open Finset Module DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph
open DeJongAlterations.StableModification.CurvesField.Genus

set_option autoImplicit false

universe u v w x₁ x₂

section Numerical

variable {V : Type u} {E : Type v} {M : Type w} {G : IncidenceGraph V E M}
  [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M]

/-- **Corollary B.2 for all contracted points of a fibre, numerical form.** Let `Y_j`, `j ∈ J`,
be connected sets of components (the fibres `f⁻¹(x_j)`), `n_j = #∂Y_j` (the numbers of branches
of `C_s` at `x_j`) and `δ_j ≥ n_j − 1` (the δ-invariants `g(x_j)`). If
`∑_j δ_j = ∑_j δ♭(Y_j)` (equal arithmetic genera of `C′_s` and `C_s`), then every `δ_j` equals
`n_j − 1` if and only if every `Y_j` is a `ℙ¹`-tree. -/
theorem stabdown_numerical_finset {ι : Type x₁} (J : Finset ι) (Y : ι → Finset V)
    (hY : ∀ j ∈ J, G.IsConnected (Y j)) (δ n : ι → ℤ)
    (hn : ∀ j ∈ J, n j = (G.boundary (Y j)).card) (hle : ∀ j ∈ J, n j - 1 ≤ δ j)
    (hsum : ∑ j ∈ J, δ j = ∑ j ∈ J, contractedDelta G (Y j)) :
    (∀ j ∈ J, δ j = n j - 1) ↔ ∀ j ∈ J, G.IsP1Tree (Y j) := by
  -- `a_j = δ_j - (n_j - 1) ≥ 0` and `b_j = p_a(Y_j) ≥ 0` have equal sums
  have hγ : ∀ j ∈ J, 0 ≤ G.combGenus (Y j) := fun j hj => combGenus_nonneg (hY j hj)
  have hab : ∑ j ∈ J, (δ j - (n j - 1)) = ∑ j ∈ J, G.combGenus (Y j) := by
    have : ∀ j ∈ J, contractedDelta G (Y j) = (n j - 1) + G.combGenus (Y j) := fun j hj => by
      rw [contractedDelta_eq, hn j hj]
    rw [sum_sub_distrib, hsum, sum_congr rfl this, sum_add_distrib]
    ring
  have htree : ∀ j ∈ J, (G.IsP1Tree (Y j) ↔ G.combGenus (Y j) = 0) := fun j hj => by
    rw [isP1Tree_iff_combGenus_eq_zero]
    exact ⟨fun h => h.2, fun h => ⟨hY j hj, h⟩⟩
  constructor
  · intro h j hj
    have h0 : ∑ j ∈ J, G.combGenus (Y j) = 0 := by
      rw [← hab]
      exact sum_eq_zero fun i hi => by rw [h i hi]; ring
    rw [htree j hj]
    exact (sum_eq_zero_iff_of_nonneg hγ).1 h0 j hj
  · intro h j hj
    have h0 : ∑ j ∈ J, (δ j - (n j - 1)) = 0 := by
      rw [hab]
      exact sum_eq_zero fun i hi => (htree i hi).1 (h i hi)
    have := (sum_eq_zero_iff_of_nonneg fun i hi => sub_nonneg.2 (hle i hi)).1 h0 j hj
    linarith

end Numerical

section Local

variable {k : Type x₁} [Field k]

/-- Over an algebraically closed field, a local subalgebra `A ⊆ B` (as in `CurvesField.Delta`) is
the gluing ring of `B` (`x` is an ordinary point) exactly when `δ(A) + 1 = |Max B|`. -/
theorem gluing_iff_delta_of_isAlgClosed [IsAlgClosed k] {B : Type x₂} [CommRing B] [Algebra k B]
    [Fintype (MaximalSpectrum B)] (A : Subalgebra k B) [IsLocalRing A] [Algebra.IsIntegral A B]
    (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] :
    A = gluing k B ↔ delta k A + 1 = Fintype.card (MaximalSpectrum B) := by
  rw [delta_add_one_eq_card_iff_of_isLocalRing A hres]
  have : Nonempty (MaximalSpectrum B) := nonempty_maximalSpectrum A
  have hle := le_gluing A hres
  refine ⟨fun h => ⟨fun m => ?_, h⟩, fun h => h.2⟩
  have : FiniteDimensional k (B ⧸ m.asIdeal) := finiteDimensional_residue A hle m
  have : Nontrivial (B ⧸ m.asIdeal) := Ideal.Quotient.nontrivial_iff.2 m.isMaximal.ne_top
  let : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  have : Algebra.IsIntegral k (B ⧸ m.asIdeal) := Algebra.IsIntegral.of_finite k _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := B ⧸ m.asIdeal)).2

variable {V : Type u} {E : Type v} {M : Type w} {G : IncidenceGraph V E M}
  [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M]

/-- **Corollary B.2 for all contracted points of a fibre, local-algebra form** (the counting step
of blueprint `lem:sm-stability-criterion`). Over an algebraically closed field `k`, let
`A_j = 𝒪_{C_s,x_j} ⊆ B_j = 𝒪_{C̃_s,x̃_j}`, `j ∈ J`, be the local rings at the points `x_j` of the
modification locus in `C_s` and their normalizations, and `Y_j = f⁻¹(x_j)` the connected fibres
in the semi-stable `C′_s` (one incidence graph `G` for `C′_s`). If
`∑_j g(x_j) = ∑_j δ♭(Y_j)` (the genus formula for `C′_s` and `C_s` with
`p_a(C′_s) = p_a(C_s)`) and `|x̃_j| = |∂Y_j|`, then all `x_j` are ordinary points if and only if
all `Y_j` are `ℙ¹`-trees. -/
theorem stabdown_gluing_iff_finset [IsAlgClosed k] {ι : Type x₂} (J : Finset ι)
    {B : ι → Type x₂} [∀ j, CommRing (B j)] [∀ j, Algebra k (B j)]
    [∀ j, Fintype (MaximalSpectrum (B j))] (A : ∀ j, Subalgebra k (B j))
    [∀ j, IsLocalRing (A j)] [∀ j, Algebra.IsIntegral (A j) (B j)]
    (hres : ∀ j, ∀ a : A j, ∃ c : k, a - algebraMap k (A j) c ∈ IsLocalRing.maximalIdeal (A j))
    [∀ j, FiniteDimensional k (B j ⧸ Subalgebra.toSubmodule (A j))] (Y : ι → Finset V)
    (hY : ∀ j ∈ J, G.IsConnected (Y j))
    (hδ : ∑ j ∈ J, (delta k (A j) : ℤ) = ∑ j ∈ J, contractedDelta G (Y j))
    (hbr : ∀ j ∈ J, Fintype.card (MaximalSpectrum (B j)) = (G.boundary (Y j)).card) :
    (∀ j ∈ J, A j = gluing k (B j)) ↔ ∀ j ∈ J, G.IsP1Tree (Y j) := by
  have h := stabdown_numerical_finset J Y hY (fun j => (delta k (A j) : ℤ))
    (fun j => (Fintype.card (MaximalSpectrum (B j)) : ℤ)) (fun j hj => by
      simp only [hbr j hj]) (fun j _ => by
      have := card_le_delta_add_one_of_isLocalRing (A j) (hres j)
      omega) hδ
  rw [← h]
  refine forall₂_congr fun j _ => ?_
  rw [gluing_iff_delta_of_isAlgClosed (A j) (hres j)]
  omega

end Local

section Marks

/-- **Marks in the stability criterion.** Let `x` be a point of `C_s` with `n ≥ 1` branches,
`m` the number of marked sections through `x`, `ord` the statement "`x` is an ordinary
`n`-fold point" and `tree` the statement "`f⁻¹(x)` is a `ℙ¹`-tree", and suppose `ord ↔ tree`
(Corollary B.2). Then "`x` is a smooth point or a node (`ord`, `n ≤ 2`) carrying at most one mark,
and only if it is smooth" holds if and only if "`f⁻¹(x)` is a `ℙ¹`-tree with
`|∂f⁻¹(x)| + |marks| = n + m ≤ 2`" (an exceptional tree). -/
theorem semistable_iff_exceptional (n m : ℕ) (hn : 1 ≤ n) {ord tree : Prop} (h : ord ↔ tree) :
    (ord ∧ n ≤ 2 ∧ m ≤ 1 ∧ (m = 1 → n = 1)) ↔ (tree ∧ n + m ≤ 2) := by
  rw [h]
  constructor
  · rintro ⟨ht, h2, h1, h11⟩
    refine ⟨ht, ?_⟩
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h0
    · omega
    · have := h11 h0
      omega
  · rintro ⟨ht, h2⟩
    exact ⟨ht, by omega, by omega, fun h1 => by omega⟩

end Marks

end DeJongAlterations.StableModification.BlowDown
