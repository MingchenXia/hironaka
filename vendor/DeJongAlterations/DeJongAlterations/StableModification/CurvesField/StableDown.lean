/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.Delta
import DeJongAlterations.StableModification.CurvesField.Trees
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Contracting a subcurve to an ordinary point (Temkin, Corollary B.2)

Corollary B.2 (`stabdowncor`) of M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010) (`references/temkin10-stable-modification`, `semi-stable.tex`,
lines 4435–4467): let `f : C' → C` be a morphism of proper reduced curves over `k` with
`p_a(C') = p_a(C)`, an isomorphism off `Z = f⁻¹(x)`, `Z` a connected curve in the semi-stable
locus of `C'`. Then `x` is an ordinary `n`-fold point if and only if `Z` is a `ℙ¹_k`-tree with
`|∂Z| = n`.

Temkin's proof has two parts.

1. *Counting.* The genus formula (Lemma B.1) for `C'` and `C`, the equality of the genera and the
   isomorphism `C' ∖ Z ≅ C ∖ x` give `g(x) = ∑_{z ∈ Z} g_{C'}(z) - |Z⁰|`; since `C'` is
   semi-stable along `Z` (`g = 1` at the double points of `C'` on `Z`, `0` at its smooth points),
   this is `g(x) = |∂Z| + #(double points inside Z) + ∑_{Z⁰} g - |Z⁰|`, and the normalization of `C`
   identifies the branches `x̃` of `C` at `x` with `∂Z` (`|x̃| = |∂Z|`, using that `Z` is connected).
2. *Combinatorics.* `g(x) ≥ |x̃| - 1` with equality iff `x` is ordinary (`CurvesField.Delta`), and
   `|∂Z| + #inner + ∑ g - |Z⁰| ≥ |∂Z| - 1` with equality iff `Z` is a `ℙ¹`-tree
   (`CurvesField.Trees`, `card_boundary_sub_one_eq_iff`).

This file proves part 2 together with its local-algebra translation: `stabdown_iff` (connected
`Z`), `stabdown_gluing_iff` (ordinary points in gluing form; over an algebraically closed field the
residue condition is automatic, `stabdown_gluing_iff_of_isAlgClosed`), and the variant for a
possibly disconnected fibre `stabdown_disconnected` (fibre `Z` = a separated family of connected
curves `Y_j`, `d` isolated double points and `s` isolated smooth points of `C'`): `x` is ordinary
iff `∑_j p_a(Y_j) + 1 = #components(Z)`; in particular, if every `Y_j` is a `ℙ¹`-tree, then `x`
is ordinary and `Z` is connected (`stabdown_connected_of_isP1Tree`). The counting identities of
part 1 are hypotheses (`hδ`, `hbr`); they are the output of the genus formula
(`GenusFormula.arithmeticGenus_eq`) applied to the normalizations of `C'` and `C`.

Blueprint: `sm-curves-fields-genus.tex`, `cor:sm-stabdown`, `cor:sm-stabdown-disconnected`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open Finset Module DeJongAlterations.StableModification.CurvesField
open DeJongAlterations.StableModification.CurvesField.IncidenceGraph

set_option autoImplicit false

universe u v w x₁ x₂

section Combinatorics

variable {V : Type u} {E : Type v} {M : Type w} (G : IncidenceGraph V E M)
  [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M]

/-- The δ-count of the contraction of a subcurve `Y` of the semi-stable locus to a point:
`#∂Y + #inner(Y) + ∑_{v ∈ Y} g(v) - #Y` (the right side of `g(x) = ∑_{z ∈ Z} g(z) - |Z⁰|`, the
double points of `C'` on `Y` being the inner and the boundary ones). -/
noncomputable def contractedDelta (Y : Finset V) : ℤ :=
  (G.boundary Y).card + (G.inner Y).card + ∑ v ∈ Y, (G.genus v : ℤ) - Y.card

omit [DecidableEq E] [Fintype M] [DecidableEq M] in
/-- The δ-count is `#∂Y - 1 + p_a(Y)`, with the combinatorial arithmetic genus `p_a(Y)`. -/
lemma contractedDelta_eq (Y : Finset V) :
    contractedDelta G Y = (G.boundary Y).card - 1 + G.combGenus Y := by
  unfold contractedDelta IncidenceGraph.combGenus
  ring

variable {G}

/-- **Corollary B.2, numerical form.** If `g(x) = #∂Y + #inner + ∑ g - #Y` (the genus formula
with equal genera) and `|x̃| = #∂Y` for a connected subcurve `Y`, then `g(x) ≥ |x̃| - 1`, with
equality if and only if `Y` is a `ℙ¹`-tree. -/
theorem stabdown_numerical {Y : Finset V} (hY : G.IsConnected Y) {δ n : ℤ}
    (hδ : δ = contractedDelta G Y) (hn : n = (G.boundary Y).card) :
    n - 1 ≤ δ ∧ (δ = n - 1 ↔ G.IsP1Tree Y) := by
  subst hδ hn
  refine ⟨?_, ?_⟩
  · exact card_boundary_sub_one_le hY
  · rw [eq_comm]
    exact card_boundary_sub_one_eq_iff hY

omit [DecidableEq E] [Fintype M] [DecidableEq M] in
/-- **Corollary B.2 for a possibly disconnected fibre, numerical form.** Let the curve part of
`Z = f⁻¹(x)` be a separated family `𝒴` of connected subcurves and let `Z` have, besides, `d`
isolated points that are double points of `C'` and `s` isolated points that are smooth points of
`C'`. If `g(x) = ∑_j δ(Y_j) + d` and `|x̃| = ∑_j #∂Y_j + 2d + s`, then
`g(x) - (|x̃| - 1) = ∑_j p_a(Y_j) + 1 - (#𝒴 + d + s)`. -/
theorem stabdown_disconnected_numerical (𝒴 : Finset (Finset V)) (d s : ℕ) {δ n : ℤ}
    (hδ : δ = ∑ Y ∈ 𝒴, contractedDelta G Y + d)
    (hn : n = ∑ Y ∈ 𝒴, ((G.boundary Y).card : ℤ) + 2 * d + s) :
    δ - (n - 1) = ∑ Y ∈ 𝒴, G.combGenus Y + 1 - (𝒴.card + d + s) := by
  subst hδ hn
  rw [Finset.sum_congr rfl fun Y _ => contractedDelta_eq G Y]
  simp only [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, mul_one]
  ring

end Combinatorics

section Local

variable {k : Type x₁} [Field k] {B : Type x₂} [CommRing B] [Algebra k B]
  {V : Type u} {E : Type v} {M : Type w} {G : IncidenceGraph V E M}
  [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M]
  [Fintype (MaximalSpectrum B)]

/-- **Temkin, Corollary B.2** (`stabdowncor`, l. 4435–4467), local-algebra form. Let
`A = 𝒪_{C,x} ⊆ B = 𝒪_{C̃,x̃}` be as in `CurvesField.Delta` (local with residue field `k`, `B`
integral over `A` with finitely many maximal ideals, `B / A` finite-dimensional), and let `Y` be
the connected curve `f⁻¹(x)` in the semi-stable locus of `C'` with the counting identities of the
genus formula: `g(x) = #∂Y + #inner + ∑ g - #Y` and `|x̃| = #∂Y`. Then `x` is an ordinary point in
the sense `g(x) = |x̃| - 1` if and only if `Y` is a `ℙ¹`-tree. -/
theorem stabdown_iff (A : Subalgebra k B) {Y : Finset V} (hY : G.IsConnected Y)
    (hδ : (delta k A : ℤ) = contractedDelta G Y)
    (hbr : Fintype.card (MaximalSpectrum B) = (G.boundary Y).card) :
    delta k A + 1 = Fintype.card (MaximalSpectrum B) ↔ G.IsP1Tree Y := by
  have h := (stabdown_numerical hY hδ (n := Fintype.card (MaximalSpectrum B))
    (by exact_mod_cast hbr)).2
  rw [← h]
  omega

/-- **Corollary B.2 with ordinary points in gluing form**: under the hypotheses of
`stabdown_iff`, all points of `x̃` are `k`-points and `𝒪_{C,x}` is the ring of functions on `C̃`
near `x̃` taking the same value at all points of `x̃` (`x` is an ordinary `|∂Y|`-fold point) if
and only if `Y` is a `ℙ¹`-tree. -/
theorem stabdown_gluing_iff (A : Subalgebra k B) [IsLocalRing A] [Algebra.IsIntegral A B]
    (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] {Y : Finset V} (hY : G.IsConnected Y)
    (hδ : (delta k A : ℤ) = contractedDelta G Y)
    (hbr : Fintype.card (MaximalSpectrum B) = (G.boundary Y).card) :
    ((∀ m : MaximalSpectrum B, Function.Surjective (algebraMap k (B ⧸ m.asIdeal))) ∧
        A = gluing k B) ↔ G.IsP1Tree Y := by
  rw [← delta_add_one_eq_card_iff_of_isLocalRing A hres]
  exact stabdown_iff A hY hδ hbr

/-- Over an algebraically closed field the residue fields of `B` (finite over `k`) are `k`, so
`x` is ordinary exactly when `𝒪_{C,x}` is the gluing ring. -/
theorem stabdown_gluing_iff_of_isAlgClosed [IsAlgClosed k] (A : Subalgebra k B) [IsLocalRing A]
    [Algebra.IsIntegral A B]
    (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] {Y : Finset V} (hY : G.IsConnected Y)
    (hδ : (delta k A : ℤ) = contractedDelta G Y)
    (hbr : Fintype.card (MaximalSpectrum B) = (G.boundary Y).card) :
    A = gluing k B ↔ G.IsP1Tree Y := by
  rw [← stabdown_gluing_iff A hres hY hδ hbr]
  have : Nonempty (MaximalSpectrum B) := nonempty_maximalSpectrum A
  have hle := le_gluing A hres
  refine ⟨fun h => ⟨fun m => ?_, h⟩, fun h => h.2⟩
  have : FiniteDimensional k (B ⧸ m.asIdeal) := finiteDimensional_residue A hle m
  have : Nontrivial (B ⧸ m.asIdeal) := Ideal.Quotient.nontrivial_iff.2 m.isMaximal.ne_top
  let : Field (B ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  have : Algebra.IsIntegral k (B ⧸ m.asIdeal) := Algebra.IsIntegral.of_finite k _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := B ⧸ m.asIdeal)).2

omit [DecidableEq E] [Fintype M] [DecidableEq M] in
/-- **Corollary B.2 for a possibly disconnected fibre.** With `Z = ⋃ 𝒴 ∪ {d double points} ∪
{s smooth points}` as in `stabdown_disconnected_numerical`: `x` is ordinary (`g(x) = |x̃| - 1`) if
and only if `∑_j p_a(Y_j) + 1 = #𝒴 + d + s` (the number of connected components of `Z`). -/
theorem stabdown_disconnected (A : Subalgebra k B) [IsLocalRing A] [Algebra.IsIntegral A B]
    (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] (𝒴 : Finset (Finset V)) (d s : ℕ)
    (hδ : (delta k A : ℤ) = ∑ Y ∈ 𝒴, contractedDelta G Y + d)
    (hbr : (Fintype.card (MaximalSpectrum B) : ℤ) =
      ∑ Y ∈ 𝒴, ((G.boundary Y).card : ℤ) + 2 * d + s) :
    (delta k A + 1 = Fintype.card (MaximalSpectrum B) ↔
      ∑ Y ∈ 𝒴, G.combGenus Y + 1 = 𝒴.card + d + s) ∧
      (𝒴.card + d + s : ℤ) ≤ ∑ Y ∈ 𝒴, G.combGenus Y + 1 := by
  have h := stabdown_disconnected_numerical (G := G) 𝒴 d s hδ hbr
  have hle := card_le_delta_add_one_of_isLocalRing A hres
  refine ⟨⟨fun he => ?_, fun he => ?_⟩, ?_⟩
  · have he' : (delta k A : ℤ) + 1 = Fintype.card (MaximalSpectrum B) := by exact_mod_cast he
    omega
  · have : (delta k A : ℤ) + 1 = Fintype.card (MaximalSpectrum B) := by omega
    exact_mod_cast this
  · have hle' : (Fintype.card (MaximalSpectrum B) : ℤ) ≤ delta k A + 1 := by exact_mod_cast hle
    omega

/-- **If every curve component of the fibre is a `ℙ¹`-tree, the fibre is connected and `x` is
ordinary** (the variant of Corollary B.2 that needs no connectedness of `Z`): under the
hypotheses of `stabdown_disconnected`, if each `Y_j` is a `ℙ¹`-tree then `#𝒴 + d + s ≤ 1` and
`g(x) = |x̃| - 1`. -/
theorem stabdown_connected_of_isP1Tree (A : Subalgebra k B) [IsLocalRing A]
    [Algebra.IsIntegral A B]
    (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] (𝒴 : Finset (Finset V)) (d s : ℕ)
    (hδ : (delta k A : ℤ) = ∑ Y ∈ 𝒴, contractedDelta G Y + d)
    (hbr : (Fintype.card (MaximalSpectrum B) : ℤ) =
      ∑ Y ∈ 𝒴, ((G.boundary Y).card : ℤ) + 2 * d + s)
    (htree : ∀ Y ∈ 𝒴, G.IsP1Tree Y) :
    𝒴.card + d + s ≤ 1 ∧ delta k A + 1 = Fintype.card (MaximalSpectrum B) := by
  obtain ⟨hiff, hle⟩ := stabdown_disconnected A hres 𝒴 d s hδ hbr
  have h0 : ∑ Y ∈ 𝒴, G.combGenus Y = 0 :=
    sum_eq_zero fun Y hY => (isP1Tree_iff_combGenus_eq_zero.1 (htree Y hY)).2
  rw [h0] at hle hiff
  refine ⟨by exact_mod_cast hle, hiff.2 ?_⟩
  have hlower : (Fintype.card (MaximalSpectrum B) : ℤ) ≤ delta k A + 1 := by
    exact_mod_cast card_le_delta_add_one_of_isLocalRing A hres
  have h := stabdown_disconnected_numerical (G := G) 𝒴 d s hδ hbr
  rw [h0] at h
  have : Nonempty (MaximalSpectrum B) := nonempty_maximalSpectrum A
  have hpos : (0 : ℤ) < Fintype.card (MaximalSpectrum B) := by exact_mod_cast Fintype.card_pos
  by_cases h𝒴 : 𝒴.card = 0
  · rw [Finset.card_eq_zero.1 h𝒴] at hbr
    simp only [sum_empty, zero_add] at hbr
    rw [Finset.card_eq_zero.1 h𝒴] at hle ⊢
    simp only [card_empty, CharP.cast_eq_zero, zero_add] at hle ⊢
    omega
  · have : 1 ≤ 𝒴.card := Nat.one_le_iff_ne_zero.2 h𝒴
    have hle' : ((𝒴.card : ℤ) + d + s) ≤ 0 + 1 := hle
    omega

end Local

end DeJongAlterations.StableModification.CurvesField.Genus
