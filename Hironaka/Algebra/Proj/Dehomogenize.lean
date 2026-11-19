/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Hironaka.Scheme.BlowUp.Rees.Map

/-!
# Dehomogenization: the standard chart of `ℙ^{r-1}_R` is a polynomial ring

The exceptional divisor of the blow-up of a smooth scheme along a smooth centre `Z` of codimension
`r` is locally `(Z ∩ U) ×_k ℙ^{r-1}_k`; establishing this needs the base change of `Proj` along
`k → B` for the polynomial ring `k[u_0, …, u_{r-1}]` with its standard grading
[Sta, Tag 01MX], which Mathlib does not provide. Its local form on the standard chart
`D₊(u_j)` is the ring statement of this file: the degree-zero part of the localization
`R[u]_{u_j}` is the polynomial ring `R[u_i/u_j : i ≠ j]`, naturally in `R`, so that
`B ⊗_k (k[u]_{u_j})₀ ≅ (B[u]_{u_j})₀`.

**Why the theorems hold.**  Every element of `(R[u]_{u_j})₀` is a fraction
`p/u_j^m` with `p` homogeneous of degree `m`, and `p/u_j^m = p(u_i/u_j)` is the polynomial
`p(u_j ↦ 1, u_i ↦ y_i)` in the variables `y_i = u_i/u_j` (dehomogenization); conversely a
polynomial `q(y)` is recovered from `q(u_i/u_j) ∈ R[u]_{u_j}` by the ring map `u_j ↦ 1, u_i ↦ y_i`,
which is defined on the localization because it sends `u_j` to a unit.  So `q ↦ q(u_i/u_j)` is an
isomorphism `R[y_i : i ≠ j] ≅ (R[u]_{u_j})₀`; it commutes with the coefficient maps `R → S`, and
`S ⊗_R R[y] = S[y]` (Mathlib's `MvPolynomial.algebraTensorAlgEquiv`) gives the tensor identity.

## Main declarations

* `AlgebraicGeometry.Proj.dehom R j : MvPolynomial {i // i ≠ j} R ≃ₐ[R] Away (𝒜 R) (X j)` — `y_i ↦
  u_i/u_j`, for `𝒜 R = homogeneousSubmodule σ R` the standard grading of `R[u]`.
* `AlgebraicGeometry.Proj.gradedMap R S : homogeneousSubmodule σ R →+*ᵍ homogeneousSubmodule σ S` —
  the coefficient map `R[u] → S[u]` as a graded ring homomorphism; `awayMap_dehomAux` is the
  naturality of `dehom`.
* `AlgebraicGeometry.Proj.tensorEquiv R j S : S ⊗[R] Away (𝒜 R) (X j) ≃ₐ[S] Away (𝒜 S) (X j)` and
  the pushout square `isPushout_away` in `CommRingCat`.

## Conventions

The variable type `σ` lives in `Type` (the applications use `Fin r`), so that `MvPolynomial σ R`
stays in the universe of `R` for `CommRingCat`.  The chart element is carried as a variable
`f` with `hf : f = X j`, because the base-changed chart is `Away (𝒜 S) (gradedMap R S (X j))`
(the image of `X j`, equal but not definitionally equal to `X j`).
-/

@[expose] public section

universe u

open MvPolynomial HomogeneousLocalization TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.Proj

section Val

variable {ι σ' A : Type*} [AddCommMonoid ι] [DecidableEq ι] [CommRing A] [SetLike σ' A]
  [AddSubgroupClass σ' A] (𝒜 : ι → σ') [GradedRing 𝒜] (x : Submonoid A)

/-- `val` on the constants of degree zero: `f/1`. -/
theorem val_fromZeroRingHom (f : 𝒜 0) :
    (fromZeroRingHom 𝒜 x f).val = algebraMap A (Localization x) f := by
  change (HomogeneousLocalization.mk _).val = _
  rw [val_mk]
  exact Localization.mk_one_eq_algebraMap _

/-- `val` as a ring homomorphism (the `algebraMap` of Mathlib's algebra instance). -/
abbrev valRingHom : HomogeneousLocalization 𝒜 x →+* Localization x :=
  algebraMap (HomogeneousLocalization 𝒜 x) (Localization x)

theorem valRingHom_apply (y : HomogeneousLocalization 𝒜 x) : valRingHom 𝒜 x y = y.val := rfl

end Val

variable {σ : Type} (R : Type u) [CommRing R]

/-- The variables are homogeneous of degree one. -/
theorem X_mem_one (i : σ) : (X i : MvPolynomial σ R) ∈ homogeneousSubmodule σ R 1 :=
  (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i)

theorem X_mem_one_smul (i : σ) : (X i : MvPolynomial σ R) ∈ homogeneousSubmodule σ R (1 • 1) := by
  rw [smul_eq_mul, mul_one]; exact X_mem_one R i

section Algebra

variable (f : MvPolynomial σ R)

/-- The `R`-algebra structure on `(R[u]_f)₀`: Mathlib's scalar action of `R` on the homogeneous
localization (through the numerators) with the constants `R → (R[u])₀ → (R[u]_f)₀` as
`algebraMap` — the composite of Mathlib's `Algebra (𝒜 0) (HomogeneousLocalization 𝒜 x)` with the
grade-zero `Algebra R (𝒜 0)` (the scalar tower `instIsScalarTowerAway` below).  Scoped to
`Hironaka.Proj`, as an instance on a Mathlib type. -/
noncomputable scoped instance instAlgebraAway : Algebra R (Away (homogeneousSubmodule σ R) f) where
  smul := (· • ·)
  algebraMap := (fromZeroRingHom (homogeneousSubmodule σ R) (Submonoid.powers f)).comp
    (algebraMap R (homogeneousSubmodule σ R 0))
  commutes' _ _ := mul_comm _ _
  smul_def' r z := by
    apply val_injective
    change (r • z).val = ((fromZeroRingHom (homogeneousSubmodule σ R) (Submonoid.powers f)).comp
      (algebraMap R (homogeneousSubmodule σ R 0)) r * z).val
    rw [val_smul, val_mul, RingHom.comp_apply, val_fromZeroRingHom,
      SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq, Algebra.smul_def,
      IsScalarTower.algebraMap_apply R (MvPolynomial σ R) (Localization (Submonoid.powers f)),
      MvPolynomial.algebraMap_eq]

theorem algebraMap_away_apply (r : R) :
    algebraMap R (Away (homogeneousSubmodule σ R) f) r =
      fromZeroRingHom _ _ (algebraMap R (homogeneousSubmodule σ R 0) r) := rfl

/-- The `R`-algebra structure on `(R[u]_f)₀` is compatible with Mathlib's `(R[u])₀`-algebra
structure. -/
scoped instance instIsScalarTowerAway :
    IsScalarTower R (homogeneousSubmodule σ R 0) (Away (homogeneousSubmodule σ R) f) :=
  IsScalarTower.of_algebraMap_eq' (show algebraMap R (Away (homogeneousSubmodule σ R) f) =
    (algebraMap (homogeneousSubmodule σ R 0) (Away (homogeneousSubmodule σ R) f)).comp
      (algebraMap R (homogeneousSubmodule σ R 0)) from rfl)

theorem val_algebraMap_away (r : R) :
    (algebraMap R (Away (homogeneousSubmodule σ R) f) r).val =
      algebraMap (MvPolynomial σ R) (Localization (Submonoid.powers f)) (C r) := by
  rw [algebraMap_away_apply, val_fromZeroRingHom]
  rfl

/-- `f ^ n` as an element of the submonoid `powers f`. -/
noncomputable abbrev fpow (n : ℕ) : Submonoid.powers f :=
  ⟨f ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers f) n⟩

end Algebra

/-! ### The chart of `u_j`: `f` is the variable `u_j` (as an element, up to the equation `hf`) -/

variable (j : σ) (f : MvPolynomial σ R) (hf : f = X j)
include hf

theorem f_mem_one : f ∈ homogeneousSubmodule σ R 1 := hf ▸ X_mem_one R j

/-- `u_i / u_j`. -/
noncomputable def mkX (i : σ) : Away (homogeneousSubmodule σ R) f :=
  Away.mk _ (f_mem_one R j f hf) 1 (X i) (X_mem_one_smul R i)

theorem val_mkX (i : σ) : (mkX R j f hf i).val = Localization.mk (X i) (fpow R f 1) :=
  Away.val_mk _ _ _ _ _

theorem mkX_self : mkX R j f hf j = 1 := by
  subst hf
  apply val_injective
  rw [val_mkX, val_one]
  have : fpow R (X j) 1 = ⟨X j, Submonoid.mem_powers _⟩ := Subtype.ext (pow_one _)
  rw [this]
  exact Localization.mk_self
    (⟨X j, Submonoid.mem_powers _⟩ : Submonoid.powers (X j : MvPolynomial σ R))

/-- `R[y_i : i ≠ j] → (R[u]_{u_j})₀`, `y_i ↦ u_i/u_j`. -/
noncomputable def dehomAux :
    MvPolynomial {i : σ // i ≠ j} R →ₐ[R] Away (homogeneousSubmodule σ R) f :=
  aeval fun i => mkX R j f hf i.1

omit hf in
open scoped Classical in
/-- Dehomogenization `u_j ↦ 1`, `u_i ↦ y_i`. -/
noncomputable def dehomogenize : MvPolynomial σ R →ₐ[R] MvPolynomial {i : σ // i ≠ j} R :=
  aeval fun i => if h : i = j then 1 else X ⟨i, h⟩

omit hf in
theorem dehomogenize_X_self : dehomogenize R j (X j) = 1 := by simp [dehomogenize]

omit hf in
theorem dehomogenize_X_of_ne {i : σ} (h : i ≠ j) : dehomogenize R j (X i) = X ⟨i, h⟩ := by
  simp [dehomogenize, h]

omit hf in
/-- For `p` homogeneous of degree `m`, `p(g_i · u) = u^m · p(g_i)`. -/
theorem eval₂_mul_right_of_isHomogeneous {S : Type*} [CommRing S] (φ : R →+* S) (g : σ → S)
    (u : S) {p : MvPolynomial σ R} {m : ℕ} (hp : p.IsHomogeneous m) :
    eval₂ φ (fun i => g i * u) p = u ^ m * eval₂ φ g p := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = m := by
    have h := hp (mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum] at h
    simpa using h
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

/-- The chart computation: a homogeneous `p` of degree `m` evaluated at `u_i/u_j` is the
fraction `p/u_j^m`. -/
theorem aeval_mkX_of_mem {p : MvPolynomial σ R} {m : ℕ} (hp : p ∈ homogeneousSubmodule σ R m) :
    aeval (mkX R j f hf) p = Away.mk _ (f_mem_one R j f hf) m p (by simpa using hp) := by
  subst hf
  apply val_injective
  rw [Away.val_mk, aeval_def, ← valRingHom_apply, eval₂_comp_left]
  have h1 : (valRingHom (homogeneousSubmodule σ R) (Submonoid.powers (X j))).comp
      (algebraMap R (Away (homogeneousSubmodule σ R) (X j))) =
      (algebraMap (MvPolynomial σ R) (Localization (Submonoid.powers (X j)))).comp C :=
    RingHom.ext fun r => val_algebraMap_away R (X j) r
  have h2 : (valRingHom (homogeneousSubmodule σ R) (Submonoid.powers (X j)) ∘ mkX R j (X j) rfl) =
      fun i => algebraMap (MvPolynomial σ R) (Localization (Submonoid.powers (X j))) (X i) *
        Localization.mk 1 (fpow R (X j) 1) := by
    funext i
    rw [Function.comp_apply, valRingHom_apply, val_mkX, ← Localization.mk_one_eq_algebraMap,
      Localization.mk_mul, mul_one, one_mul]
  rw [h1, h2]
  refine (eval₂_mul_right_of_isHomogeneous R _ (fun i => algebraMap _ _ (X i)) _
    ((mem_homogeneousSubmodule _ _).mp hp)).trans ?_
  set L := Localization (Submonoid.powers (X j : MvPolynomial σ R)) with hL
  have h3 : eval₂ ((algebraMap (MvPolynomial σ R) L).comp (C : R →+* MvPolynomial σ R))
      (fun i => algebraMap (MvPolynomial σ R) L (X i : MvPolynomial σ R)) p =
      algebraMap (MvPolynomial σ R) L p := by
    rw [show (fun i => algebraMap (MvPolynomial σ R) L (X i : MvPolynomial σ R)) =
      ⇑(algebraMap (MvPolynomial σ R) L) ∘ X from rfl, ← eval₂_comp_left, eval₂_eta]
  rw [h3, Localization.mk_pow, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, one_pow,
    one_mul, mul_one]
  congr 1
  ext
  simp

theorem dehomAux_dehomogenize (p : MvPolynomial σ R) :
    dehomAux R j f hf (dehomogenize R j p) = aeval (mkX R j f hf) p := by
  rw [dehomAux, dehomogenize, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  split_ifs with h
  · subst h; rw [map_one, mkX_self]
  · rw [aeval_X]

theorem dehomAux_surjective : Function.Surjective (dehomAux R j f hf) := fun z => by
  obtain ⟨m, p, hp, rfl⟩ := Away.mk_surjective _ (f_mem_one R j f hf) z
  exact ⟨dehomogenize R j p, by
    rw [dehomAux_dehomogenize, aeval_mkX_of_mem R j f hf (by simpa using hp)]⟩

theorem isUnit_dehomogenize : IsUnit (dehomogenize R j f) := by
  rw [hf, dehomogenize_X_self]; exact isUnit_one

/-- The map `R[u]_{u_j} → R[y]`, `u_j ↦ 1`, `u_i ↦ y_i`, on the localization. -/
noncomputable def dehomLoc :
    Localization (Submonoid.powers f) →+* MvPolynomial {i : σ // i ≠ j} R :=
  IsLocalization.Away.lift f (g := (dehomogenize R j).toRingHom) (isUnit_dehomogenize R j f hf)

theorem dehomLoc_val_dehomAux (q : MvPolynomial {i : σ // i ≠ j} R) :
    dehomLoc R j f hf (dehomAux R j f hf q).val = q := by
  subst hf
  have : (dehomLoc R j (X j) rfl).comp
      ((valRingHom (homogeneousSubmodule σ R) (Submonoid.powers (X j))).comp
        (dehomAux R j (X j) rfl).toRingHom) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply]
      rw [dehomAux, aeval_C, valRingHom_apply, val_algebraMap_away, dehomLoc,
        IsLocalization.Away.lift_eq]
      simp [dehomogenize]
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.id_apply]
      rw [dehomAux, aeval_X, valRingHom_apply, val_mkX, Localization.mk_eq_mk'_apply, dehomLoc,
        IsLocalization.Away.lift, IsLocalization.lift_mk'_spec]
      simp [dehomogenize_X_of_ne R j i.2, dehomogenize_X_self]
  exact RingHom.congr_fun this q

theorem dehomAux_injective : Function.Injective (dehomAux R j f hf) := fun a b h => by
  have ha := dehomLoc_val_dehomAux R j f hf a
  rw [h, dehomLoc_val_dehomAux] at ha
  exact ha.symm

/-- The dehomogenization isomorphism `R[y_i : i ≠ j] ≅ (R[u]_{u_j})₀`, `y_i ↦ u_i/u_j`: the
standard chart of projective space is an affine space [Sta, Tag 01MX]. -/
noncomputable def dehom :
    MvPolynomial {i : σ // i ≠ j} R ≃ₐ[R] Away (homogeneousSubmodule σ R) f :=
  AlgEquiv.ofBijective (dehomAux R j f hf)
    ⟨dehomAux_injective R j f hf, dehomAux_surjective R j f hf⟩

theorem dehom_apply (q : MvPolynomial {i : σ // i ≠ j} R) :
    dehom R j f hf q = dehomAux R j f hf q := rfl

section BaseChange

omit hf

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The coefficient map `R[u] → S[u]` as a graded ring homomorphism. -/
noncomputable def gradedMap : homogeneousSubmodule σ R →+*ᵍ homogeneousSubmodule σ S :=
  { MvPolynomial.map (algebraMap R S) with
    map_mem := fun hx =>
      (mem_homogeneousSubmodule _ _).mpr (((mem_homogeneousSubmodule _ _).mp hx).map _) }

theorem gradedMap_apply (p : MvPolynomial σ R) :
    gradedMap R S p = MvPolynomial.map (algebraMap R S) p := rfl

theorem gradedMap_X (i : σ) : gradedMap R S (X i) = X i := by
  rw [gradedMap_apply, map_X]

/-- Naturality of dehomogenization in the coefficients. -/
theorem awayMap_dehomAux (q : MvPolynomial {i : σ // i ≠ j} R) :
    Away.map (gradedMap R S) (X j) (dehomAux R j (X j) rfl q) =
      dehomAux S j (gradedMap R S (X j)) (gradedMap_X R S j)
        (MvPolynomial.map (algebraMap R S) q) := by
  have : (Away.map (gradedMap R S) (X j)).comp (dehomAux R j (X j) rfl).toRingHom =
      (dehomAux S j (gradedMap R S (X j)) (gradedMap_X R S j)).toRingHom.comp
        (MvPolynomial.map (algebraMap R S)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_C]
      rw [dehomAux, dehomAux, aeval_C, aeval_C, algebraMap_away_apply, algebraMap_away_apply,
        Away.map_fromZeroRingHom]
      congr 1
      ext
      simp [gradedMap_apply]
    · intro i
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_X]
      rw [dehomAux, dehomAux, aeval_X, aeval_X]
      apply val_injective
      rw [mkX, Away.map_mk, Away.val_mk, val_mkX]
      congr 1
      exact gradedMap_X R S i.1
  exact RingHom.congr_fun this q

/-- `S ⊗_R (R[u]_{u_j})₀ ≅ (S[u]_{u_j})₀`: the base change of the standard chart. -/
noncomputable def tensorEquiv :
    S ⊗[R] Away (homogeneousSubmodule σ R) (X j) ≃ₐ[S]
      Away (homogeneousSubmodule σ S) (gradedMap R S (X j)) :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) (dehom R j (X j) rfl).symm).trans
    ((MvPolynomial.algebraTensorAlgEquiv R S).trans
      (dehom S j (gradedMap R S (X j)) (gradedMap_X R S j)))

theorem tensorEquiv_tmul (s : S) (z : Away (homogeneousSubmodule σ R) (X j)) :
    tensorEquiv R j S (s ⊗ₜ z) = algebraMap S _ s * Away.map (gradedMap R S) (X j) z := by
  obtain ⟨q, rfl⟩ := (dehom R j (X j) rfl).surjective z
  rw [tensorEquiv, AlgEquiv.trans_apply, AlgEquiv.trans_apply, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
    AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq, MvPolynomial.algebraTensorAlgEquiv_tmul,
    Algebra.smul_def, map_mul, AlgEquiv.commutes, dehom_apply, dehom_apply, awayMap_dehomAux]

/-- The standard chart of `ℙ^{r-1}` commutes with base change: the square
`R → S`, `R → (R[u]_{u_j})₀`, `S → (S[u]_{u_j})₀`, `(R[u]_{u_j})₀ → (S[u]_{u_j})₀` is a pushout of
rings — the chart form of the base change of projective space [Sta, Tag 01MX]. -/
theorem isPushout_away :
    CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap R S))
      (CommRingCat.ofHom (algebraMap R (Away (homogeneousSubmodule σ R) (X j))))
      (CommRingCat.ofHom (algebraMap S (Away (homogeneousSubmodule σ S) (gradedMap R S (X j)))))
      (CommRingCat.ofHom (Away.map (gradedMap R S) (X j))) :=
  (CommRingCat.isPushout_tensorProduct R S (Away (homogeneousSubmodule σ R) (X j))).of_iso
    (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _) (CategoryTheory.Iso.refl _)
    (tensorEquiv R j S).toRingEquiv.toCommRingCatIso (by simp) (by simp)
    (by ext s; simp [tensorEquiv_tmul]) (by ext z; simp [tensorEquiv_tmul])

end BaseChange

end AlgebraicGeometry.Proj
