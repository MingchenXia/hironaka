/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.AffineSpace
import Hironaka.Resolution.Algebraic.Kol07.Thm36.Shear
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Two embeddings into affine space are conjugate by an automorphism

[Kol07, Lemma 39]: for closed embeddings `i₁ : X ↪ 𝔸ⁿ` and `i₂ : X ↪ 𝔸ᵐ` of an affine scheme, the
two embeddings `X ↪ 𝔸ⁿ ↪ 𝔸ⁿ⁺ᵐ` and `X ↪ 𝔸ᵐ ↪ 𝔸ⁿ⁺ᵐ` into the coordinate subspaces are equivalent
under a (nonlinear) automorphism of `𝔸ⁿ⁺ᵐ`. Kollár's proof: extend `i₂` to `j₂ : 𝔸ⁿ → 𝔸ᵐ` (lift
the coordinate functions `y_l ∘ i₂` along the surjection `k[x] → 𝒪(X)`); then the shear
`(x, y) ↦ (x, y + j₂(x))` carries `(i₁, 0)` to `i₁ × i₂`, and symmetrically the shear
`(x, y) ↦ (x + j₁(y), y)` carries `(0, i₂)` to `i₁ × i₂`. The main results:

* `hom_ext_affineSpace`: two morphisms `X ⟶ 𝔸ᴺ` agree once they agree on the constants and on the
  coordinate functions (Mathlib's `ext_of_isAffine` and `MvPolynomial.ringHom_ext` through
  `ΓSpecIso`); every identity of the lemma is checked this way.
* `exists_polynomialMap_comp_eq`: the extensions `j₁`, `j₂`, from the surjectivity of the
  coordinate ring map of a closed immersion between affine schemes.
* `shearY_comp_prodEmb`, `shearX_comp_prodEmb`: the two shears carry the coordinate embeddings
  to the product embedding `prodEmb i₁ i₂`.
* `exists_aut_conj_embeddings`: the lemma, with the automorphism `shearY v ≫ inv (shearX w)`.

The lemma is the step of the proof of [Kol07, Theorem 36] that makes the resolution of an affine
scheme independent of the embedding; see `Hironaka.Resolution.Algebraic.Kol07.Thm36.Assembly`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Resolution

variable {k : Type u} [Field k]

/-! ### Global sections of morphisms into an affine scheme -/

/-- The global sections of `Spec.map φ`, read through `ΓSpecIso`, are `φ`
(`ΓSpecIso_inv_naturality` pointwise). -/
theorem appTop_Spec_map_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
  exact (congrArg (fun g : R ⟶ Γ(Spec S, ⊤) => g r) (Scheme.ΓSpecIso_inv_naturality φ)).symm

/-- Two morphisms from a scheme into the affine space `𝔸ᴺ_k` agree once they agree on the constants
and on the coordinate functions (through `ΓSpecIso`): Mathlib's `ext_of_isAffine` and
`MvPolynomial.ringHom_ext`. -/
theorem hom_ext_affineSpace {X : Scheme.{u}} {N : ℕ}
    {f g : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin N) k))}
    (hC : ∀ c : k, f.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.C c)) =
      g.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.C c)))
    (hX : ∀ j, f.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X j)) =
      g.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X j))) : f = g := by
  apply ext_of_isAffine
  have : (Scheme.ΓSpecIso _).inv ≫ f.appTop = (Scheme.ΓSpecIso _).inv ≫ g.appTop := by
    refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext (fun c => ?_) (fun j => ?_))
    · exact hC c
    · exact hX j
  rwa [Iso.cancel_iso_inv_left] at this

/-- The global sections of a polynomial map on a constant. -/
theorem appTop_polynomialMap_C {n m : ℕ} (v : Fin m → MvPolynomial (Fin n) k) (c : k) :
    (polynomialMap v).appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.C c)) =
      (Scheme.ΓSpecIso _).inv (MvPolynomial.C c) := by
  unfold polynomialMap
  rw [appTop_Spec_map_ΓSpecIso_inv]
  congr 1
  simp [MvPolynomial.algebraMap_eq]

/-- The global sections of a polynomial map on a coordinate: `y_l ↦ v_l`. -/
theorem appTop_polynomialMap_X {n m : ℕ} (v : Fin m → MvPolynomial (Fin n) k) (l : Fin m) :
    (polynomialMap v).appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X l)) =
      (Scheme.ΓSpecIso _).inv (v l) := by
  unfold polynomialMap
  rw [appTop_Spec_map_ΓSpecIso_inv]
  congr 1
  exact MvPolynomial.aeval_X v l

/-- The global sections of a polynomial map on any polynomial: substitution. -/
theorem appTop_polynomialMap {n m : ℕ} (v : Fin m → MvPolynomial (Fin n) k)
    (q : MvPolynomial (Fin m) k) :
    (polynomialMap v).appTop ((Scheme.ΓSpecIso _).inv q) =
      (Scheme.ΓSpecIso _).inv (MvPolynomial.aeval v q) := by
  unfold polynomialMap
  rw [appTop_Spec_map_ΓSpecIso_inv, CommRingCat.ofHom_apply]
  rfl

/-- The global sections of the structure morphism of `𝔸ⁿ_k` on a scalar: the constant polynomial. -/
theorem appTop_affineSpaceToSpec (n : ℕ) (c : k) :
    (affineSpaceToSpec k n).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) =
      (Scheme.ΓSpecIso _).inv (MvPolynomial.C c) := by
  unfold affineSpaceToSpec
  rw [appTop_Spec_map_ΓSpecIso_inv]
  rfl

section ProdEmb

variable {n m : ℕ} {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  (i₁ : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) k)))
  (i₂ : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin m) k)))

/-- The global sections of the product embedding on a constant: the structure morphism's. -/
theorem appTop_prodEmb_C (c : k) :
    (prodEmb i₁ i₂).appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.C c)) =
      (X ↘ Spec (CommRingCat.of k)).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  unfold prodEmb
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_Spec_map_ΓSpecIso_inv,
    Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply]
  simp

/-- The global sections of the product embedding on a coordinate of the first block: `i₁`'s. -/
theorem appTop_prodEmb_X_inl (i : Fin n) :
    (prodEmb i₁ i₂).appTop ((Scheme.ΓSpecIso _).inv (coordX n m i)) =
      i₁.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X i)) := by
  unfold prodEmb
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_Spec_map_ΓSpecIso_inv,
    Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply]
  simp [coordX]

/-- The global sections of the product embedding on a coordinate of the second block: `i₂`'s. -/
theorem appTop_prodEmb_X_inr (l : Fin m) :
    (prodEmb i₁ i₂).appTop ((Scheme.ΓSpecIso _).inv (coordY n m l)) =
      i₂.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X l)) := by
  unfold prodEmb
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_Spec_map_ΓSpecIso_inv,
    Scheme.toSpecΓ_appTop, Iso.inv_hom_id_apply]
  simp [coordY]

end ProdEmb

/-! ### The coordinate inclusions on polynomials -/

/-- Substituting the coordinate inclusion `x ↦ (x, 0)` into a polynomial renamed into the first
block gives the polynomial back. -/
theorem aeval_coordInclFstFun_rename {n m : ℕ} (q : MvPolynomial (Fin n) k) :
    MvPolynomial.aeval
        (fun j : Fin (n + m) => Sum.elim (MvPolynomial.X : Fin n → MvPolynomial (Fin n) k)
          (fun _ => 0) (finSumFinEquiv.symm j))
        (MvPolynomial.rename (fun i => finSumFinEquiv (Sum.inl i)) q) = q := by
  rw [MvPolynomial.aeval_rename]
  conv_rhs => rw [← MvPolynomial.aeval_X_left_apply q]
  exact congrArg (fun G : Fin n → MvPolynomial (Fin n) k => MvPolynomial.aeval G q)
    (funext fun i => by simp)

/-- Substituting the coordinate inclusion `y ↦ (0, y)` into a polynomial renamed into the second
block gives the polynomial back. -/
theorem aeval_coordInclSndFun_rename {n m : ℕ} (q : MvPolynomial (Fin m) k) :
    MvPolynomial.aeval
        (fun j : Fin (n + m) => Sum.elim (fun _ => 0)
          (MvPolynomial.X : Fin m → MvPolynomial (Fin m) k) (finSumFinEquiv.symm j))
        (MvPolynomial.rename (fun l => finSumFinEquiv (Sum.inr l)) q) = q := by
  rw [MvPolynomial.aeval_rename]
  conv_rhs => rw [← MvPolynomial.aeval_X_left_apply q]
  exact congrArg (fun G : Fin m → MvPolynomial (Fin m) k => MvPolynomial.aeval G q)
    (funext fun l => by simp)

/-! ### Morphisms over `k` on constants -/

/-- A morphism `i : X ⟶ 𝔸ⁿ` over `k` sends the constant `c` to the structure morphism's `c`. -/
theorem appTop_C_of_over {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] {n : ℕ}
    (i : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) k)))
    (h : i ≫ affineSpaceToSpec k n = X ↘ Spec (CommRingCat.of k)) (c : k) :
    i.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.C c)) =
      (X ↘ Spec (CommRingCat.of k)).appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c) := by
  rw [← h, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_affineSpaceToSpec]

/-! ### The lifts `j₁`, `j₂` -/

/-- The extension step of the proof of [Kol07, Lemma 39] ("we can extend `i₂` to a morphism
`j₂ : 𝔸ⁿ → 𝔸ᵐ`"): for a closed immersion `i₁ : X ↪ 𝔸ⁿ` over `k` and any morphism `i₂ : X ⟶ 𝔸ᵐ`
over `k`, there is a polynomial map `𝔸ⁿ ⟶ 𝔸ᵐ` through which `i₂` factors: each coordinate
function `y_l ∘ i₂` lifts along the surjective coordinate ring map of the closed immersion `i₁`. -/
theorem exists_polynomialMap_comp_eq {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    {n m : ℕ} (i₁ : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) k))) [IsClosedImmersion i₁]
    (i₂ : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin m) k)))
    (h₁ : i₁ ≫ affineSpaceToSpec k n = X ↘ Spec (CommRingCat.of k))
    (h₂ : i₂ ≫ affineSpaceToSpec k m = X ↘ Spec (CommRingCat.of k)) :
    ∃ v : Fin m → MvPolynomial (Fin n) k, i₁ ≫ polynomialMap v = i₂ := by
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (f := i₁)).2
  choose p hp using fun l : Fin m => hs (i₂.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X l)))
  refine ⟨fun l => (Scheme.ΓSpecIso _).hom (p l), hom_ext_affineSpace (fun c => ?_) (fun l => ?_)⟩
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_polynomialMap_C,
      appTop_C_of_over i₁ h₁, appTop_C_of_over i₂ h₂]
  · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_polynomialMap_X,
      Iso.hom_inv_id_apply]
    exact hp l

/-! ### The two shears carry the coordinate embeddings to the product embedding -/

section Shears

variable {n m : ℕ} {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  (i₁ : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin n) k)))
  (i₂ : X ⟶ Spec (CommRingCat.of (MvPolynomial (Fin m) k)))

/-- The shear `(x, y) ↦ (x, y + j₂(x))` carries `(i₁, 0)` to `i₁ × i₂` when `j₂ = polynomialMap v`
extends `i₂` along `i₁` [Kol07, Lemma 39, proof]. -/
theorem shearY_comp_prodEmb
    (h₁ : i₁ ≫ affineSpaceToSpec k n = X ↘ Spec (CommRingCat.of k))
    (v : Fin m → MvPolynomial (Fin n) k) (hv : i₁ ≫ polynomialMap v = i₂) :
    i₁ ≫ coordInclFst n m ≫ shearY v = prodEmb i₁ i₂ := by
  refine hom_ext_affineSpace (fun c => ?_) (fun j => ?_)
  · rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply]
    unfold shearY coordInclFst
    rw [appTop_polynomialMap_C, appTop_polynomialMap_C, appTop_C_of_over i₁ h₁, appTop_prodEmb_C]
  · rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply]
    unfold shearY coordInclFst
    rw [appTop_polynomialMap_X, appTop_polynomialMap]
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with i | l
    · have e : (prodEmb i₁ i₂).appTop ((Scheme.ΓSpecIso _).inv
          (MvPolynomial.X (finSumFinEquiv (Sum.inl i)))) =
          i₁.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X i)) :=
        appTop_prodEmb_X_inl i₁ i₂ i
      rw [e]
      congr 2
      simp [coordX]
    · have e : (prodEmb i₁ i₂).appTop ((Scheme.ΓSpecIso _).inv
          (MvPolynomial.X (finSumFinEquiv (Sum.inr l)))) =
          i₂.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X l)) :=
        appTop_prodEmb_X_inr i₁ i₂ l
      rw [e, ← hv, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_polynomialMap_X]
      congr 2
      simp only [Equiv.symm_apply_apply, Sum.elim_inr, map_add, coordY, MvPolynomial.aeval_X,
        Sum.elim_inr, aeval_coordInclFstFun_rename]
      simp

/-- The shear `(x, y) ↦ (x + j₁(y), y)` carries `(0, i₂)` to `i₁ × i₂` when `j₁ = polynomialMap w`
extends `i₁` along `i₂` [Kol07, Lemma 39, proof]. -/
theorem shearX_comp_prodEmb
    (h₂ : i₂ ≫ affineSpaceToSpec k m = X ↘ Spec (CommRingCat.of k))
    (w : Fin n → MvPolynomial (Fin m) k) (hw : i₂ ≫ polynomialMap w = i₁) :
    i₂ ≫ coordInclSnd n m ≫ shearX w = prodEmb i₁ i₂ := by
  refine hom_ext_affineSpace (fun c => ?_) (fun j => ?_)
  · rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply]
    unfold shearX coordInclSnd
    rw [appTop_polynomialMap_C, appTop_polynomialMap_C, appTop_C_of_over i₂ h₂, appTop_prodEmb_C]
  · rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      CommRingCat.comp_apply]
    unfold shearX coordInclSnd
    rw [appTop_polynomialMap_X, appTop_polynomialMap]
    obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
    rcases s with i | l
    · have e : (prodEmb i₁ i₂).appTop ((Scheme.ΓSpecIso _).inv
          (MvPolynomial.X (finSumFinEquiv (Sum.inl i)))) =
          i₁.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X i)) :=
        appTop_prodEmb_X_inl i₁ i₂ i
      rw [e, ← hw, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, appTop_polynomialMap_X]
      congr 2
      simp only [Equiv.symm_apply_apply, Sum.elim_inl, map_add, coordX, MvPolynomial.aeval_X,
        aeval_coordInclSndFun_rename]
      simp
    · have e : (prodEmb i₁ i₂).appTop ((Scheme.ΓSpecIso _).inv
          (MvPolynomial.X (finSumFinEquiv (Sum.inr l)))) =
          i₂.appTop ((Scheme.ΓSpecIso _).inv (MvPolynomial.X l)) :=
        appTop_prodEmb_X_inr i₁ i₂ l
      rw [e]
      congr 2
      simp [coordY]

/-- [Kol07, Lemma 39]: for two closed immersions `i₁ : X ↪ 𝔸ⁿ`, `i₂ : X ↪ 𝔸ᵐ` over `k`, the two
coordinate embeddings `X ↪ 𝔸ⁿ⁺ᵐ` are conjugate under an automorphism of `𝔸ⁿ⁺ᵐ` over `k`, namely
`shearY v ≫ inv (shearX w)`, each shear carrying its coordinate embedding to `prodEmb i₁ i₂`. -/
theorem exists_aut_conj_embeddings [IsClosedImmersion i₁] [IsClosedImmersion i₂]
    (h₁ : i₁ ≫ affineSpaceToSpec k n = X ↘ Spec (CommRingCat.of k))
    (h₂ : i₂ ≫ affineSpaceToSpec k m = X ↘ Spec (CommRingCat.of k)) :
    ∃ φ : Spec (CommRingCat.of (MvPolynomial (Fin (n + m)) k)) ≅
        Spec (CommRingCat.of (MvPolynomial (Fin (n + m)) k)),
      φ.hom ≫ affineSpaceToSpec k (n + m) =
          affineSpaceToSpec k (n + m) ∧
        i₁ ≫ coordInclFst n m ≫ φ.hom = i₂ ≫ coordInclSnd n m := by
  obtain ⟨v, hv⟩ := exists_polynomialMap_comp_eq i₁ i₂ h₁ h₂
  obtain ⟨w, hw⟩ := exists_polynomialMap_comp_eq i₂ i₁ h₂ h₁
  have e1 := shearY_comp_prodEmb i₁ i₂ h₁ v hv
  have e2 := shearX_comp_prodEmb i₁ i₂ h₂ w hw
  refine ⟨asIso (shearY v) ≪≫ (asIso (shearX w)).symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, Category.assoc]
    have h1 : inv (shearX w) ≫ affineSpaceToSpec k (n + m) =
        affineSpaceToSpec k (n + m) := by
      conv_lhs => rw [← shearX_comp_affineSpaceToSpec w]
      rw [IsIso.inv_hom_id_assoc]
    rw [h1, shearY_comp_affineSpaceToSpec]
  · simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv]
    rw [reassoc_of% e1, ← e2, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

end Shears

end Hironaka.Resolution
