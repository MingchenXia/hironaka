/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineSpace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The shears of affine space are automorphisms

The proof of [Kol07, Lemma 39] uses that `(x, y) ↦ (x, y + j₂(x))` and `(x, y) ↦ (x + j₁(y), y)`
are automorphisms of `𝔸ⁿ⁺ᵐ`. This file proves it for the shears `shearY v` and `shearX w` of
`Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineSpace`: composition of polynomial maps is
substitution (`polynomialMap_comp`), the polynomial map of the coordinates is the identity
(`polynomialMap_X`), and the substitutions of `v` and `-v` cancel on the generators, so `shearY
(-v)` is the inverse of `shearY v` (`shearY_comp_shearY_neg`, `isIso_shearY`), and likewise for
`shearX`.

The `IsIso` instances are used in the proof of Lemma 39 (`exists_aut_conj_embeddings` in
`Hironaka.Resolution.Algebraic.Kol07.Thm36.Lemma39`), where the conjugating automorphism is `shearY
v ≫ inv (shearX w)`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Resolution

variable {k : Type u} [Field k]

/-! ### Composition and identity of polynomial maps -/

/-- Composition of polynomial maps is substitution: `polynomialMap v ≫ polynomialMap w` is the
polynomial map with components `aeval v (w j)`. -/
theorem polynomialMap_comp {n m p : ℕ} (v : Fin m → MvPolynomial (Fin n) k)
    (w : Fin p → MvPolynomial (Fin m) k) :
    polynomialMap v ≫ polynomialMap w = polynomialMap fun j => MvPolynomial.aeval v (w j) := by
  unfold polynomialMap
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun q => ?_
  change MvPolynomial.aeval v (MvPolynomial.aeval w q) =
    MvPolynomial.aeval (fun j => MvPolynomial.aeval v (w j)) q
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]

/-- The polynomial map of the coordinates is the identity. -/
theorem polynomialMap_X {n : ℕ} :
    polynomialMap (fun i : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) k)) = 𝟙 _ := by
  unfold polynomialMap
  rw [← Spec.map_id]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun q => ?_)
  change MvPolynomial.aeval MvPolynomial.X q = q
  exact MvPolynomial.aeval_X_left_apply q

/-- Two polynomial maps with the same components are equal (componentwise extensionality). -/
theorem polynomialMap_congr {n m : ℕ} {v w : Fin m → MvPolynomial (Fin n) k} (h : ∀ j, v j = w j) :
    polynomialMap v = polynomialMap w := by
  rw [funext h]

/-! ### The inverses of the shears -/

/-- Substituting the coordinates of the first block into a polynomial renamed into the first block
gives it back: `aeval (shearY v's components) (rename inl p) = rename inl p`. -/
theorem aeval_shearYFun_rename {n m : ℕ} (v : Fin m → MvPolynomial (Fin n) k)
    (p : MvPolynomial (Fin n) k) :
    MvPolynomial.aeval (fun j => Sum.elim (coordX n m)
        (fun l => coordY n m l + MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) (v l))
        (finSumFinEquiv.symm j))
      (MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) p) =
      MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) p := by
  rw [MvPolynomial.aeval_rename]
  conv_rhs => rw [MvPolynomial.rename_eq_aeval]
  exact congrArg (fun G : Fin n → MvPolynomial (Fin (n + m)) k => MvPolynomial.aeval G p)
    (funext fun i => by simp [coordX])

/-- Substituting the coordinates of the second block into a polynomial renamed into the second
block gives it back. -/
theorem aeval_shearXFun_rename {n m : ℕ} (w : Fin n → MvPolynomial (Fin m) k)
    (p : MvPolynomial (Fin m) k) :
    MvPolynomial.aeval (fun j => Sum.elim
        (fun i => coordX n m i + MvPolynomial.rename (fun l => finSumFinEquiv (Sum.inr l)) (w i))
        (coordY n m) (finSumFinEquiv.symm j))
      (MvPolynomial.rename (fun l => finSumFinEquiv (Sum.inr l)) p) =
      MvPolynomial.rename (fun l => finSumFinEquiv (Sum.inr l)) p := by
  rw [MvPolynomial.aeval_rename]
  conv_rhs => rw [MvPolynomial.rename_eq_aeval]
  exact congrArg (fun G : Fin m → MvPolynomial (Fin (n + m)) k => MvPolynomial.aeval G p)
    (funext fun l => by simp [coordY])

/-- The shear `shearY v` followed by `shearY (-v)` is the identity; so the automorphism
`(x, y) ↦ (x, y + j₂(x))` of the proof of [Kol07, Lemma 39] is inverted by `y ↦ y − j₂(x)`. -/
theorem shearY_comp_shearY_neg {n m : ℕ} (v : Fin m → MvPolynomial (Fin n) k) :
    shearY v ≫ shearY (-v) = 𝟙 _ := by
  unfold shearY
  rw [polynomialMap_comp, ← polynomialMap_X]
  refine polynomialMap_congr fun j => ?_
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with i | l
  · simp [coordX, coordY]
  · simp only [Equiv.symm_apply_apply, Sum.elim_inr, map_add, MvPolynomial.aeval_X, Pi.neg_apply,
      map_neg, aeval_shearYFun_rename, coordY]
    abel

/-- The shear `shearX w` followed by `shearX (-w)` is the identity; so the automorphism
`(x, y) ↦ (x + j₁(y), y)` of the proof of [Kol07, Lemma 39] is inverted by `x ↦ x − j₁(y)`. -/
theorem shearX_comp_shearX_neg {n m : ℕ} (w : Fin n → MvPolynomial (Fin m) k) :
    shearX w ≫ shearX (-w) = 𝟙 _ := by
  unfold shearX
  rw [polynomialMap_comp, ← polynomialMap_X]
  refine polynomialMap_congr fun j => ?_
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  rcases s with i | l
  · simp only [Equiv.symm_apply_apply, Sum.elim_inl, map_add, MvPolynomial.aeval_X, Pi.neg_apply,
      map_neg, aeval_shearXFun_rename, coordX]
    abel
  · simp [coordX, coordY]

/-- `shearY v` is an automorphism of `𝔸ⁿ⁺ᵐ` [Kol07, Lemma 39, proof]. -/
instance isIso_shearY {n m : ℕ} (v : Fin m → MvPolynomial (Fin n) k) : IsIso (shearY v) :=
  ⟨shearY (-v), shearY_comp_shearY_neg v, by
    have := shearY_comp_shearY_neg (-v)
    rwa [neg_neg] at this⟩

/-- `shearX w` is an automorphism of `𝔸ⁿ⁺ᵐ` [Kol07, Lemma 39, proof]. -/
instance isIso_shearX {n m : ℕ} (w : Fin n → MvPolynomial (Fin m) k) : IsIso (shearX w) :=
  ⟨shearX (-w), shearX_comp_shearX_neg w, by
    have := shearX_comp_shearX_neg (-w)
    rwa [neg_neg] at this⟩

end Hironaka.Resolution
