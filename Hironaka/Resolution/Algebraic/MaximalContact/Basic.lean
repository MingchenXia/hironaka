/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Derivative.Sheaf
import Hironaka.Scheme.IdealSheaf.Derivative.Cosupport
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Mathlib.Data.Nat.Choose.Multinomial
/-!
# Hypersurfaces of maximal contact: the definitions

Following [Kol07, 51] and [Kol07, Definitions 78 and 79]. For an ideal sheaf `I` on a smooth
variety `X` with `m = max-ord I`, order reduction for `I` should follow from order reduction for
`(I|_H, m)` on a smooth hypersurface `H`; for this the points where the birational transforms of
`I` have order `≥ m` must stay on the birational transforms of `H` ([Kol07, 13.3 and 51.1]). The
tool is the derivative ideal.

* **The maximal contact ideal** ([Kol07, Definition 79]; also [Kol07, 51.2]):
  `MC(I) := D^{m-1}(I)`, the iterated derivative ideal sheaf `derivativeIter f (m - 1) I`, the
  largest nontrivial derivative ideal. `MC(I)` has order `1` at `x` if `ord_x I = m` and order
  `0` if `ord_x I < m` ([Kol07, Lemma 74 (3)]), so
  `cosupp MC(I) = cosupp (I, m) = {x : ord_x I ≥ m}` (`coe_support_MC`, `ord_MC_eq_one`,
  `ord_MC_eq_zero`).
* **The static form** (the hypothesis of [Kol07, Theorem 80 (1)]; Włodarczyk's tangent direction
  `u ∈ T(I) = D^{μ-1}(I)`, [Wlo05, Definition 2.7.5]; Bierstone–Milman's section
  `z ∈ D^{d-1}_E(I)` of maximum order `1`, [BM08, Corollary 4.1]): `H` is **of maximal contact**
  for `(I, m)` when `𝒪_X(−H) ⊆ MC(I)`, i.e. locally `H = (h = 0)` with `h ∈ MC(I)`
  (`IsMaximalContact`). This form is the primary one in the library: the proof of Theorem 92
  picks local sections `x₁, x₁' ∈ MC(I)` with `H = (x₁ = 0)`, and the order-reduction functor
  produces its hypersurfaces in this form; [Kol07, Theorem 80 (1)]
  (`Hironaka/Resolution/Algebraic/MaximalContact/Sequence.lean`) shows that a smooth static `H` has
  the dynamic property.
* **The dynamic form** ([Kol07, Definition 78]): `H` is a **hypersurface of maximal contact**
  when for every open `X⁰ ⊆ X` and every smooth blow-up sequence of order `m` starting with
  `(X⁰, I|_{X⁰})` (no divisorial part `E`), the center of every blow-up lies in the birational
  transform of `H⁰ := H ∩ X⁰` (`IsDynamicMaximalContact`).

Kollár's standing hypothesis "`H` a smooth hypersurface" is not a clause of either predicate: it
is `AlgebraicGeometry.IsSmoothDivisor H` ([Kol07, Definition 24]), carried as a hypothesis by the
theorems that use it (Theorem 80, going down), so that the predicates have no smoothness clause
whose locality would have to be proved separately. The mark `m` is an explicit parameter and
`m = max-ord I` a hypothesis where used; `MC f I 0 = I`.

`RegularCoords.MC c I m := c.Dpow (m - 1) I` (`Hironaka/Algebra/Local/MaximalContact.lean`) is the
same Definition 79 in coordinates on a regular local ring, not a duplicate: at a stalk the two meet
through `stalkIdeal_derivativeIter` and `derivativeIter_eq_Dpow`.
-/

@[expose] public section

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory Scheme BlowUpSequence

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The maximal contact ideal** `MC(I) := D^{m-1}(I)` of `I` with respect to the mark `m`
(Kollár: `m = max-ord I`), the iterated derivative ideal sheaf ([Kol07, Definition 79]). -/
noncomputable def MC (I : X.IdealSheafData) (m : ℕ) : X.IdealSheafData :=
  derivativeIter f (m - 1) I

/-- `MC(I)` unfolds to `D^{m-1}(I)` (definitional). -/
theorem MC_eq (I : X.IdealSheafData) (m : ℕ) : MC f I m = derivativeIter f (m - 1) I := rfl

/-- With the mark `m + 1`, `MC(I) = D^m(I)` (definitional; `m + 1 - 1 = m` in `ℕ`). -/
theorem MC_succ (I : X.IdealSheafData) (m : ℕ) : MC f I (m + 1) = derivativeIter f m I := rfl

/-- The boundary case `m = 0` (outside Kollár's `m = max-ord I ≥ 1`): `MC f I 0 = I`, since
`0 - 1 = 0` in `ℕ`. -/
@[simp] theorem MC_zero (I : X.IdealSheafData) : MC f I 0 = I := rfl

/-- The case `m = 1`: `MC(I) = D^0(I) = I`. -/
@[simp] theorem MC_one (I : X.IdealSheafData) : MC f I 1 = I := rfl

/-- The static form (the hypothesis of [Kol07, Theorem 80 (1)]; [Wlo05, Definition 2.7.5];
[BM08, Corollary 4.1]): `H` is **of maximal contact** for `(I, m)` when `𝒪_X(−H) ⊆ MC(I)`, i.e.
locally `H = (h = 0)` with `h ∈ MC(I)`. Kollár's "smooth hypersurface" is the separate hypothesis
`AlgebraicGeometry.IsSmoothDivisor H`. -/
def IsMaximalContact (I : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData) : Prop :=
  H ≤ MC f I m

/-- The static form unfolded: `𝒪_X(−H) ⊆ MC(I)` as the inclusion of ideal sheaves
`H ≤ MC f I m`. -/
theorem isMaximalContact_iff (I : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData) :
    IsMaximalContact f I m H ↔ H ≤ MC f I m :=
  Iff.rfl

/-- The dynamic form ([Kol07, Definition 78]): `H` is a **hypersurface of maximal contact** for
`(I, m)` when, for every open subscheme `j : X⁰ ⟶ X` and every smooth blow-up sequence of order `m`
starting with `(X⁰, I|_{X⁰})` (with the empty divisorial part, Kollár's "for now we ignore `E`"),
the center of every blow-up lies in the birational (strict) transform of `H⁰ := H|_{X⁰}`:
`S.strictTransformSeq (H.comap j) i ≤ S.center i` as ideal sheaves (`V(Z_i) ⊆ V(H_i)`). Kollár's
"smooth hypersurface" is the separate hypothesis `AlgebraicGeometry.IsSmoothDivisor H`. -/
def IsDynamicMaximalContact (I : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData) : Prop :=
  ∀ (Y : Scheme.{u}) (j : Y ⟶ X) [IsOpenImmersion j] (S : BlowUpSequence Y),
    S.IsOrderSeq (j ≫ f) (I.comap j) (DivisorFamily.empty Y) m →
      ∀ i : Fin S.length, S.strictTransformSeq (H.comap j) i.castSucc ≤ S.center i

/-- The dynamic form unfolded: for every open immersion `j : Y ⟶ X` and every smooth blow-up
sequence of order `m` for `(Y, I|_Y)` with the empty divisor family, every centre lies in the
strict transform of `H|_Y`. -/
theorem isDynamicMaximalContact_iff (I : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData) :
    IsDynamicMaximalContact f I m H ↔
      ∀ (Y : Scheme.{u}) (j : Y ⟶ X) [IsOpenImmersion j] (S : BlowUpSequence Y),
        S.IsOrderSeq (j ≫ f) (I.comap j) (DivisorFamily.empty Y) m →
          ∀ i : Fin S.length, S.strictTransformSeq (H.comap j) i.castSucc ≤ S.center i :=
  Iff.rfl

/-! ### The order of `MC(I)` ([Kol07, Lemma 74 (3)]) -/

section Order

variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f] (I : X.IdealSheafData) {m : ℕ}

include n

/-- Kollár's "`cosupp MC(I) = cosupp (I, m)`" ([Kol07, Definition 79]): a point lies on `V(MC(I))`
iff `ord_x I ≥ m` (`le_ord_iff_mem_support_derivativeIter`). -/
theorem mem_support_MC_iff (hm : 1 ≤ m) (x : X) :
    x ∈ (MC f I m).support ↔ (m : ℕ∞) ≤ I.ord x :=
  (le_ord_iff_mem_support_derivativeIter f n I x hm).symm

/-- `cosupp MC(I) = cosupp (I, m)` ([Kol07, Definition 79]). -/
theorem coe_support_MC (hm : 1 ≤ m) :
    ((MC f I m).support : Set X) = {x | (m : ℕ∞) ≤ I.ord x} :=
  Set.ext fun x => mem_support_MC_iff f n I hm x

/-- [Kol07, Lemma 74 (3)] at `r = 1`: `MC(I)` has order `≥ 1` at `x` iff `ord_x I ≥ m` (the point
lies on `V(MC(I))`). -/
theorem one_le_ord_MC_iff (hm : 1 ≤ m) (x : X) :
    1 ≤ (MC f I m).ord x ↔ (m : ℕ∞) ≤ I.ord x := by
  rw [one_le_ord_iff, mem_support_MC_iff f n I hm x]

/-- [Kol07, Lemma 74 (3)] at `r = 2`: `MC(I)` has order `≥ 2` at `x` iff `ord_x I ≥ m + 1`; so at
a point of order exactly `m` the order of `MC(I)` is exactly `1`. -/
theorem two_le_ord_MC_iff (hm : 1 ≤ m) (x : X) :
    2 ≤ (MC f I m).ord x ↔ ((m + 1 : ℕ) : ℕ∞) ≤ I.ord x := by
  have h := le_ord_iff_le_ord_derivativeIter f n I x (r := m - 1) (m := m + 1) (by omega)
  rw [show m + 1 - (m - 1) = 2 by omega] at h
  exact_mod_cast h.symm

/-- `MC(I)` has order `1` at a point of order `m`. -/
theorem ord_MC_eq_one (hm : 1 ≤ m) {x : X} (hx : I.ord x = m) : (MC f I m).ord x = 1 := by
  have h1 : 1 ≤ (MC f I m).ord x := (one_le_ord_MC_iff f n I hm x).mpr hx.ge
  have h2 : ¬ 2 ≤ (MC f I m).ord x := by
    rw [two_le_ord_MC_iff f n I hm x, hx]
    exact_mod_cast Nat.not_succ_le_self m
  rw [not_le, ← one_add_one_eq_two, ENat.lt_add_one_iff ENat.one_ne_top] at h2
  exact le_antisymm h2 h1

/-- `MC(I)` has order `0` at a point of order `< m`. -/
theorem ord_MC_eq_zero {x : X} (hx : I.ord x < m) : (MC f I m).ord x = 0 := by
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      exact absurd hx (not_lt.mpr (by simp))
    · exact h
  have h1 : ¬ 1 ≤ (MC f I m).ord x := by
    rw [one_le_ord_MC_iff f n I hm x]
    exact not_le.mpr hx
  rw [not_le, Order.lt_one_iff] at h1
  exact h1

end Order

end AlgebraicGeometry.Scheme.IdealSheafData
