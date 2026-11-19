/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Smooth.Graph
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.BlowUp.CoordinateSubspace.Smooth
public import Hironaka.Scheme.Snc.EmptyFamily
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Affine space over `k`: polynomial maps, coordinate inclusions and shears

Kollár proves that the resolution of an affine scheme `X` does not depend on the embedding
`X ↪ A` by passing to embeddings into affine spaces `X ↪ 𝔸ⁿ`, enlarging `n` at will along the
coordinate inclusion `𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ`, and conjugating two embeddings by a nonlinear automorphism
of `𝔸ⁿ⁺ᵐ` [Kol07, Theorem 36, proof; Lemma 39]. This file defines the affine-space morphisms
those arguments use; the identities between them are proved in
`Hironaka.Resolution.Algebraic.Kol07.Thm36.Shear` and
`Hironaka.Resolution.Algebraic.Kol07.Thm36.Lemma39`.

## Main definitions

* `polynomialMap v : 𝔸ⁿ ⟶ 𝔸ᵐ`, the morphism `x ↦ (v₁(x), …, v_m(x))` given by `m` polynomials in
  `n` variables (`Spec.map` of the evaluation homomorphism `aeval v`); Kollár's extensions `j₁`,
  `j₂` of the embeddings are such maps.
* `coordInclFst n m : 𝔸ⁿ ⟶ 𝔸ⁿ⁺ᵐ`, `x ↦ (x, 0)`, and `coordInclSnd n m : 𝔸ᵐ ⟶ 𝔸ⁿ⁺ᵐ`, `y ↦ (0, y)`,
  the embeddings of the two coordinate subspaces, closed immersions over `k`.
* `shearY v : 𝔸ⁿ⁺ᵐ ⟶ 𝔸ⁿ⁺ᵐ`, `(x, y) ↦ (x, y + v(x))`, and `shearX w`, `(x, y) ↦ (x + w(y), y)`,
  the two automorphisms of the proof of [Kol07, Lemma 39]; their inverses are `shearY (-v)` and
  `shearX (-w)`.
* `prodEmb i₁ i₂ : X ⟶ 𝔸ⁿ⁺ᵐ`, Kollár's `i₁ × i₂ : X → 𝔸ⁿ × 𝔸ᵐ` for a scheme `X` over `k`, defined
  on coordinate rings: the coordinate `x_i` pulls back to `i₁^♯ x_i`, the coordinate `y_l` to
  `i₂^♯ y_l`, and the constants to the structure morphism's (no scheme product is formed).
* `affineSpaceTriple k n I hI : Triple k`, the triple `(𝔸ⁿ_k, I, ∅)` for an ideal sheaf `I` on
  `𝔸ⁿ_k` nonzero on every irreducible component, the ambient of Kollár's `BP(𝔸ⁿ, I_X, ∅)`.

## Conventions

`𝔸ᴺ_k` is `Spec k[Fin N]` with structure morphism `AlgebraicGeometry.affineSpaceToSpec k N`. In
`𝔸ⁿ⁺ᵐ = Spec k[Fin (n + m)]` the first block of coordinates (Kollár's `x`) is indexed through
`finSumFinEquiv (Sum.inl i)` and the second block (Kollár's `y`) through
`finSumFinEquiv (Sum.inr l)`; `coordX` and `coordY` name the two blocks as polynomials.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Hironaka Scheme

namespace Hironaka.Resolution

variable {k : Type u} [Field k]

/-! ### Polynomial maps between affine spaces -/

/-- The morphism `𝔸ⁿ ⟶ 𝔸ᵐ` given by `m` polynomials `v₁, …, v_m` in the `n` coordinates,
`x ↦ (v₁(x), …, v_m(x))`: `Spec.map` of the evaluation homomorphism `y_l ↦ v_l`. Kollár's
extensions `j₁ : 𝔸ᵐ → 𝔸ⁿ` of `i₁` and `j₂ : 𝔸ⁿ → 𝔸ᵐ` of `i₂` in the proof of [Kol07, Lemma 39]
are morphisms of this form. -/
noncomputable def polynomialMap {n m : ℕ} (v : Fin m → MvPolynomial (Fin n) k) :
    Spec (CommRingCat.of (MvPolynomial (Fin n) k)) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin m) k)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval v).toRingHom)

/-- A polynomial map is a morphism over `k`. -/
theorem polynomialMap_comp_affineSpaceToSpec {n m : ℕ} (v : Fin m → MvPolynomial (Fin n) k) :
    polynomialMap v ≫ affineSpaceToSpec k m =
      affineSpaceToSpec k n := by
  unfold polynomialMap affineSpaceToSpec
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact (MvPolynomial.aeval v).comp_algebraMap

/-! ### The coordinate subspaces `𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ`, `𝔸ᵐ ↪ 𝔸ⁿ⁺ᵐ` -/

/-- The first block of coordinates of `𝔸ⁿ⁺ᵐ` (Kollár's `x`), as polynomials in `n + m`
variables. -/
noncomputable abbrev coordX (n m : ℕ) (i : Fin n) : MvPolynomial (Fin (n + m)) k :=
  MvPolynomial.X (finSumFinEquiv (Sum.inl i))

/-- The second block of coordinates of `𝔸ⁿ⁺ᵐ` (Kollár's `y`), as polynomials in `n + m`
variables. -/
noncomputable abbrev coordY (n m : ℕ) (l : Fin m) : MvPolynomial (Fin (n + m)) k :=
  MvPolynomial.X (finSumFinEquiv (Sum.inr l))

/-- The closed immersion `𝔸ⁿ ⟶ 𝔸ⁿ⁺ᵐ`, `x ↦ (x, 0)`, onto the first coordinate subspace: the
polynomial map sending the first block of coordinates to the coordinates of `𝔸ⁿ` and the second
block to `0`. It is the "further embedding `𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ`" of the proof of [Kol07, Theorem 36] and
the first of the two coordinate subspaces of [Kol07, Lemma 39]. -/
noncomputable def coordInclFst (n m : ℕ) :
    Spec (CommRingCat.of (MvPolynomial (Fin n) k)) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin (n + m)) k)) :=
  polynomialMap fun j => Sum.elim MvPolynomial.X (fun _ => 0) (finSumFinEquiv.symm j)

/-- The closed immersion `𝔸ᵐ ⟶ 𝔸ⁿ⁺ᵐ`, `y ↦ (0, y)`, onto the second coordinate subspace. -/
noncomputable def coordInclSnd (n m : ℕ) :
    Spec (CommRingCat.of (MvPolynomial (Fin m) k)) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin (n + m)) k)) :=
  polynomialMap fun j => Sum.elim (fun _ => 0) MvPolynomial.X (finSumFinEquiv.symm j)

theorem coordInclFst_comp_affineSpaceToSpec (n m : ℕ) :
    coordInclFst (k := k) n m ≫ affineSpaceToSpec k (n + m) =
      affineSpaceToSpec k n :=
  polynomialMap_comp_affineSpaceToSpec _

theorem coordInclSnd_comp_affineSpaceToSpec (n m : ℕ) :
    coordInclSnd (k := k) n m ≫ affineSpaceToSpec k (n + m) =
      affineSpaceToSpec k m :=
  polynomialMap_comp_affineSpaceToSpec _

/-- The evaluation defining `coordInclFst` is surjective: `x_i` is the image of the coordinate
`coordX n m i`. -/
theorem surjective_aeval_coordInclFst (n m : ℕ) :
    Function.Surjective
      (MvPolynomial.aeval (R := k) fun j : Fin (n + m) =>
        Sum.elim (MvPolynomial.X : Fin n → MvPolynomial (Fin n) k) (fun _ => 0)
          (finSumFinEquiv.symm j)) := by
  intro p
  refine ⟨MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) p, ?_⟩
  have hfg : ((fun j : Fin (n + m) =>
      Sum.elim (MvPolynomial.X : Fin n → MvPolynomial (Fin n) k) (fun _ => 0)
        (finSumFinEquiv.symm j)) ∘ fun i => finSumFinEquiv (Sum.inl i)) = MvPolynomial.X := by
    funext i
    simp
  rw [MvPolynomial.aeval_rename, hfg, MvPolynomial.aeval_X_left_apply]

/-- The evaluation defining `coordInclSnd` is surjective. -/
theorem surjective_aeval_coordInclSnd (n m : ℕ) :
    Function.Surjective
      (MvPolynomial.aeval (R := k) fun j : Fin (n + m) =>
        Sum.elim (fun _ => 0) (MvPolynomial.X : Fin m → MvPolynomial (Fin m) k)
          (finSumFinEquiv.symm j)) := by
  intro p
  refine ⟨MvPolynomial.rename (fun l => finSumFinEquiv (Sum.inr l)) p, ?_⟩
  have hfg : ((fun j : Fin (n + m) =>
      Sum.elim (fun _ => 0) (MvPolynomial.X : Fin m → MvPolynomial (Fin m) k)
        (finSumFinEquiv.symm j)) ∘ fun l => finSumFinEquiv (Sum.inr l)) = MvPolynomial.X := by
    funext l
    simp
  rw [MvPolynomial.aeval_rename, hfg, MvPolynomial.aeval_X_left_apply]

/-- The coordinate inclusion `𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ` is a closed immersion: its coordinate ring map is
surjective. -/
instance isClosedImmersion_coordInclFst (n m : ℕ) :
    IsClosedImmersion (coordInclFst (k := k) n m) :=
  IsClosedImmersion.spec_of_surjective _ (surjective_aeval_coordInclFst n m)

/-- The coordinate inclusion `𝔸ᵐ ↪ 𝔸ⁿ⁺ᵐ` is a closed immersion. -/
instance isClosedImmersion_coordInclSnd (n m : ℕ) :
    IsClosedImmersion (coordInclSnd (k := k) n m) :=
  IsClosedImmersion.spec_of_surjective _ (surjective_aeval_coordInclSnd n m)

/-! ### The two shears of Lemma 39 -/

/-- The shear of `𝔸ⁿ⁺ᵐ` along the second block by `m` polynomials `v` in the coordinates of the
first block: the polynomial map fixing `x` and sending `y_l ↦ y_l + v_l(x)`. Its inverse is
`shearY (-v)` (`Hironaka.Resolution.isIso_shearY`). This is the automorphism
`(x, y) ↦ (x, y + j₂(x))` of the proof of [Kol07, Lemma 39]. -/
noncomputable def shearY {n m : ℕ} (v : Fin m → MvPolynomial (Fin n) k) :
    Spec (CommRingCat.of (MvPolynomial (Fin (n + m)) k)) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin (n + m)) k)) :=
  polynomialMap fun j =>
    Sum.elim (coordX n m)
      (fun l => coordY n m l + MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) (v l))
      (finSumFinEquiv.symm j)

/-- The shear of `𝔸ⁿ⁺ᵐ` along the first block by `n` polynomials `w` in the coordinates of the
second block: the polynomial map fixing `y` and sending `x_i ↦ x_i + w_i(y)`. Its inverse is
`shearX (-w)` (`Hironaka.Resolution.isIso_shearX`). This is the automorphism
`(x, y) ↦ (x + j₁(y), y)` of the proof of [Kol07, Lemma 39]. -/
noncomputable def shearX {n m : ℕ} (w : Fin n → MvPolynomial (Fin m) k) :
    Spec (CommRingCat.of (MvPolynomial (Fin (n + m)) k)) ⟶
      Spec (CommRingCat.of (MvPolynomial (Fin (n + m)) k)) :=
  polynomialMap fun j =>
    Sum.elim
      (fun i => coordX n m i + MvPolynomial.rename (fun l => finSumFinEquiv (Sum.inr l)) (w i))
      (coordY n m) (finSumFinEquiv.symm j)

theorem shearY_comp_affineSpaceToSpec {n m : ℕ} (v : Fin m → MvPolynomial (Fin n) k) :
    shearY v ≫ affineSpaceToSpec k (n + m) =
      affineSpaceToSpec k (n + m) :=
  polynomialMap_comp_affineSpaceToSpec _

theorem shearX_comp_affineSpaceToSpec {n m : ℕ} (w : Fin n → MvPolynomial (Fin m) k) :
    shearX w ≫ affineSpaceToSpec k (n + m) =
      affineSpaceToSpec k (n + m) :=
  polynomialMap_comp_affineSpaceToSpec _

/-! ### The product embedding `i₁ × i₂` -/

/-- For a scheme `X` over `k` and two morphisms `i₁ : X ⟶ 𝔸ⁿ`, `i₂ : X ⟶ 𝔸ᵐ`, the morphism
`X ⟶ 𝔸ⁿ⁺ᵐ` whose first block of coordinates is `i₁`'s and whose second block is `i₂`'s: on
coordinate rings, the homomorphism `k[Fin (n + m)] → Γ(X, ⊤)` sending `x_i ↦ i₁^♯ x_i`,
`y_l ↦ i₂^♯ y_l` and the constants to the structure morphism's, composed with `X.toSpecΓ`. This
is Kollár's `i₁ × i₂ : X → 𝔸ⁿ × 𝔸ᵐ` in the proof of [Kol07, Lemma 39]; no scheme product
`𝔸ⁿ ×_k 𝔸ᵐ` is formed, `𝔸ⁿ⁺ᵐ` standing in for it. -/
noncomputable def prodEmb {n m : ℕ} {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (i₁ : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) k)))
    (i₂ : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin m) k))) :
    X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin (n + m)) k)) :=
  X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom
    (((X ↘ Spec (CommRingCat.of k)).appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
    (fun j => Sum.elim
      (fun i => i₁.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) k))).inv (MvPolynomial.X i)))
      (fun l => i₂.appTop
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin m) k))).inv (MvPolynomial.X l)))
      (finSumFinEquiv.symm j))))

/-! ### The triple `(𝔸ⁿ_k, I, ∅)` -/

/-- The structure morphism `𝔸ⁿ_k → Spec k` is smooth of relative dimension `n`, as an instance:
the affine space is the ambient of Kollár's `BP(𝔸ⁿ, I_X, ∅)`, a triple in the sense of
[Kol07, Notation 64]. -/
instance affineSpaceToSpec_smoothOfRelativeDimension (k : Type u) [Field k] (n : ℕ) :
    SmoothOfRelativeDimension n (affineSpaceToSpec k n) :=
  CoordinateSubspace.smoothOfRelativeDimension_Spec_map_algebraMap_mvPolynomial k n

/-- The structure morphism `𝔸ⁿ_k → Spec k` is smooth. -/
instance affineSpaceToSpec_smooth (k : Type u) [Field k] (n : ℕ) :
    Smooth (affineSpaceToSpec k n) :=
  SmoothOfRelativeDimension.smooth n _

/-- The triple `(𝔸ⁿ_k, I, ∅)` [Kol07, Notation 64] for an ideal sheaf `I` on `𝔸ⁿ_k` with nonzero
stalk at every point (`IsNonzeroEverywhere`; on the integral `𝔸ⁿ_k` this is Kollár's "nonzero on
every irreducible component"): the structure morphism `affineSpaceToSpec k n` is smooth of relative
dimension `n`, and the empty boundary has simple normal crossings. It is the ambient of the
principalization `BP(𝔸ⁿ, I_X, ∅)` in the proof of [Kol07, Theorem 36]. -/
noncomputable def affineSpaceTriple (k : Type u) [Field k] (n : ℕ)
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) : Triple k where
  X := .ofHom (affineSpaceToSpec k n) inferInstance inferInstance
  smoothOfRelativeDimension := ⟨n, affineSpaceToSpec_smoothOfRelativeDimension k n⟩
  I := I
  isNonzeroEverywhere := hI
  E := DivisorFamily.empty _
  isSnc := isSnc_empty_of_smooth (affineSpaceToSpec k n)

theorem affineSpaceTriple_X (k : Type u) [Field k] (n : ℕ)
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) :
    (affineSpaceTriple k n I hI).X.left = Spec (CommRingCat.of (MvPolynomial (Fin n) k)) := rfl

theorem affineSpaceTriple_I (k : Type u) [Field k] (n : ℕ)
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) : (affineSpaceTriple k n I hI).I = I := rfl

theorem affineSpaceTriple_E (k : Type u) [Field k] (n : ℕ)
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) :
    (affineSpaceTriple k n I hI).E = DivisorFamily.empty _ := rfl

theorem affineSpaceTriple_over (k : Type u) [Field k] (n : ℕ)
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) :
    ((affineSpaceTriple k n I hI).X.left ↘ Spec (CommRingCat.of k)) =
      affineSpaceToSpec k n := rfl

/-- The triple `(𝔸ⁿ_k, I, ∅)` has an affine ambient. -/
instance isAffine_affineSpaceTriple_X (k : Type u) [Field k] (n : ℕ)
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) : IsAffine (affineSpaceTriple k n I hI).X.left :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of (MvPolynomial (Fin n) k))))

/-- The empty boundary of `(𝔸ⁿ_k, I, ∅)` has empty index type. -/
theorem isEmpty_affineSpaceTriple_E_ι (k : Type u) [Field k] (n : ℕ)
    (I : (Spec (CommRingCat.of (MvPolynomial (Fin n) k))).IdealSheafData)
    (hI : IsNonzeroEverywhere I) : IsEmpty (affineSpaceTriple k n I hI).E.ι :=
  inferInstanceAs (IsEmpty PEmpty)

end Hironaka.Resolution
