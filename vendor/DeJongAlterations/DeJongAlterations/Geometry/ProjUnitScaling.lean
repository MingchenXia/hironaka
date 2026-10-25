/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import DeJongAlterations.Geometry.ProjClosedImmersion
import Mathlib.RingTheory.GradedAlgebra.AlgHom

/-!
# Degreewise unit scaling is the identity on the actual projective spectrum

A degree-zero unit acts on degree d by its d-th power. This gives an actual
graded automorphism; on homogeneous fractions of degree zero the factors cancel.
-/

open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
open scoped HomogeneousIdeal

set_option autoImplicit false

namespace DeJongAlterations.Geometry.ProjUnitScaling

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

private def scalingFamily (a : 𝒜 0) (d : ℕ) : 𝒜 d →+ A where
  toFun x := (a : A) ^ d * (x : A)
  map_zero' := by simp
  map_add' x y := by simp [mul_add]

/-- The actual additive homogeneous decomposition defines a degreewise scaling ring map. -/
def scaleRingHom (a : 𝒜 0) : A →+* A :=
  (DirectSum.toSemiring (scalingFamily 𝒜 a)
    (by change (a : A) ^ 0 * 1 = 1; simp)
    (by
      intro i j x y
      change (a : A) ^ (i + j) * ((x : A) * (y : A)) =
        ((a : A) ^ i * (x : A)) * ((a : A) ^ j * (y : A))
      simp [pow_add, mul_assoc, mul_left_comm, mul_comm])).comp
    (DirectSum.decomposeRingEquiv 𝒜).toRingHom

/-- Degreewise scaling has its prescribed literal value on every homogeneous element. -/
theorem scaleRingHom_apply_of_mem (a : 𝒜 0) {d : ℕ} {x : A} (hx : x ∈ 𝒜 d) :
    scaleRingHom 𝒜 a x = (a : A) ^ d * x := by
  unfold scaleRingHom
  dsimp only [RingHom.comp_apply]
  erw [DirectSum.decompose_of_mem 𝒜 hx, DirectSum.toSemiring_of]
  rfl

/-- The actual graded automorphism underlying degreewise scaling by a degree-zero unit. -/
def scaleAut (u : (𝒜 0)ˣ) : 𝒜 →+*ᵍ 𝒜 where
  __ := scaleRingHom 𝒜 (u : 𝒜 0)
  map_mem {i x} hx := by
    rw [scaleRingHom_apply_of_mem 𝒜 _ hx]
    simpa only [smul_zero, zero_add] using
      (SetLike.mul_mem_graded (SetLike.pow_mem_graded i (u : 𝒜 0).property) hx)

/-- Unit scaling multiplies a homogeneous element by the corresponding unit power. -/
theorem scaleAut_apply_of_mem (u : (𝒜 0)ˣ) {d : ℕ} {x : A} (hx : x ∈ 𝒜 d) :
    scaleAut 𝒜 u x = ((u : 𝒜 0) : A) ^ d * x :=
  scaleRingHom_apply_of_mem 𝒜 _ hx

/-- A unit in the actual degree-zero ring is an actual unit in the entire graded ring. -/
def ambientUnit (u : (𝒜 0)ˣ) : Aˣ where
  val := (u : 𝒜 0)
  inv := (u⁻¹ : (𝒜 0)ˣ)
  val_inv := congrArg (fun x : 𝒜 0 ↦ (x : A)) u.val_inv
  inv_val := congrArg (fun x : 𝒜 0 ↦ (x : A)) u.inv_val

@[simp]
theorem ambientUnit_coe (u : (𝒜 0)ˣ) : (ambientUnit 𝒜 u : A) = (u : 𝒜 0) := rfl

/-- Scaling by the inverse unit is an actual inverse graded ring map. -/
theorem scaleAut_inv_comp (u : (𝒜 0)ˣ) :
    (scaleAut 𝒜 u⁻¹).comp (scaleAut 𝒜 u) = GradedRingHom.id 𝒜 := by
  apply GradedRingHom.ext
  refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_
  · simp
  · intro d x
    change scaleAut 𝒜 u⁻¹ (scaleAut 𝒜 u (x : A)) = (x : A)
    erw [scaleAut_apply_of_mem 𝒜 _ ((scaleAut 𝒜 u).map_mem x.property),
      scaleAut_apply_of_mem 𝒜 _ x.property]
    have hunit : (((u⁻¹ : (𝒜 0)ˣ) : 𝒜 0) : A) * ((u : 𝒜 0) : A) = 1 :=
      congrArg (fun z : 𝒜 0 ↦ (z : A)) u.inv_val
    rw [← mul_assoc, ← mul_pow, hunit, one_pow, one_mul]
  · intro x y hx hy
    simp only [GradedRingHom.comp_apply, map_add, GradedRingHom.id_apply] at hx hy ⊢
    rw [hx, hy]

/-- The actual ring equivalence with the prescribed degreewise-unit scaling. -/
def scaleRingEquiv (u : (𝒜 0)ˣ) : A ≃+* A where
  __ := (scaleAut 𝒜 u).toRingHom
  invFun := scaleAut 𝒜 u⁻¹
  left_inv x := GradedRingHom.congr_fun (scaleAut_inv_comp 𝒜 u) x
  right_inv x := by
    change scaleAut 𝒜 u (scaleAut 𝒜 u⁻¹ x) = x
    simpa only [inv_inv, GradedRingHom.comp_apply, GradedRingHom.id_apply] using
      GradedRingHom.congr_fun (scaleAut_inv_comp 𝒜 u⁻¹) x

/-- The actual graded scaling homomorphism is surjective. -/
theorem scaleAut_surjective (u : (𝒜 0)ˣ) : Function.Surjective (scaleAut 𝒜 u) :=
  (scaleRingEquiv 𝒜 u).surjective

/-- The actual native Proj map is defined without a supplied irrelevant-ideal certificate. -/
theorem irrelevant_le_map (u : (𝒜 0)ˣ) : 𝒜₊ ≤ 𝒜₊.map (scaleAut 𝒜 u) :=
  ProjClosedImmersion.irrelevant_le_map_of_surjective _ (scaleAut_surjective 𝒜 u)

/-- Degree-zero scaling is the actual identity on the coefficient ring. -/
theorem scaleAut_gradedZeroRingHom (u : (𝒜 0)ˣ) :
    (scaleAut 𝒜 u).gradedZeroRingHom = RingHom.id (𝒜 0) := by
  ext x
  change scaleAut 𝒜 u (x : A) = (x : A)
  rw [scaleAut_apply_of_mem 𝒜 u x.property]
  simp

/-- Every actual homogeneous ideal is unchanged under inverse image by unit scaling. -/
theorem homogeneousIdeal_comap (u : (𝒜 0)ˣ) (P : HomogeneousIdeal 𝒜) :
    P.comap (scaleAut 𝒜 u) = P := by
  apply HomogeneousIdeal.ext'
  intro d x hx
  change scaleAut 𝒜 u x ∈ P ↔ x ∈ P
  rw [scaleAut_apply_of_mem 𝒜 u hx]
  constructor
  · intro h
    have h' := P.toIdeal.mul_mem_left
      ((((u⁻¹ : (𝒜 0)ˣ) : 𝒜 0) : A) ^ d) h
    have hunit : (((u⁻¹ : (𝒜 0)ˣ) : 𝒜 0) : A) * ((u : 𝒜 0) : A) = 1 :=
      congrArg (fun z : 𝒜 0 ↦ (z : A)) u.inv_val
    change x ∈ P.toIdeal
    simpa only [← mul_assoc, ← mul_pow, hunit, one_pow, one_mul] using h'
  · exact P.toIdeal.mul_mem_left _

/-- The actual native projective-spectrum map fixes every homogeneous prime. -/
theorem comapFun_eq (u : (𝒜 0)ˣ) (p : ProjectiveSpectrum 𝒜) :
    ProjectiveSpectrum.comapFun (scaleAut 𝒜 u) (irrelevant_le_map 𝒜 u) p = p := by
  apply ProjectiveSpectrum.ext
  exact homogeneousIdeal_comap 𝒜 u p.asHomogeneousIdeal

/-- Unit powers cancel on every actual degree-zero homogeneous localization. -/
theorem localizationMap_eq_id (u : (𝒜 0)ˣ) (M : Submonoid A)
    (hM : M ≤ M.comap (scaleAut 𝒜 u)) :
    HomogeneousLocalization.map (scaleAut 𝒜 u) hM = RingHom.id (HomogeneousLocalization 𝒜 M) := by
  ext x
  obtain ⟨c, rfl⟩ := x.mk_surjective
  rw [HomogeneousLocalization.map_mk]
  simp only [HomogeneousLocalization.val_mk, RingHom.id_apply]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  change (1 : A) * ((c.den : A) * scaleAut 𝒜 u c.num) =
    1 * (scaleAut 𝒜 u c.den * (c.num : A))
  rw [scaleAut_apply_of_mem 𝒜 u c.num.property, scaleAut_apply_of_mem 𝒜 u c.den.property]
  ring

private theorem localRingHom_apply_eq (u : (𝒜 0)ˣ)
    (P Q : Ideal A) [P.IsPrime] [Q.IsPrime] (hPQ : P = Q)
    (hf : P = Q.comap (scaleAut 𝒜 u))
    (x : AtPrime 𝒜 P) (y : AtPrime 𝒜 Q) (hxy : HEq x y) :
    localRingHom (scaleAut 𝒜 u) P Q hf x = y := by
  subst Q
  have hmap : localRingHom (scaleAut 𝒜 u) P P hf = RingHom.id (AtPrime 𝒜 P) :=
    localizationMap_eq_id 𝒜 u P.primeCompl _
  rw [hmap]
  exact eq_of_heq hxy

private theorem dependent_apply_heq {ι : Type*} {D : ι → Type*}
    (s : ∀ i, D i) {i j : ι} (h : i = j) : HEq (s i) (s j) := by
  cases h
  rfl

/-- Degreewise scaling is literally the identity morphism on the native projective scheme. -/
theorem map_eq_id (u : (𝒜 0)ˣ) :
    Proj.map (scaleAut 𝒜 u) (irrelevant_le_map 𝒜 u) = 𝟙 (Proj 𝒜) := by
  have hbase : (Proj.map (scaleAut 𝒜 u) (irrelevant_le_map 𝒜 u)).base =
      (𝟙 (Proj 𝒜) : Proj 𝒜 ⟶ Proj 𝒜).base := by
    ext p
    exact comapFun_eq 𝒜 u p
  apply Scheme.Hom.ext hbase
  intro U
  ext s
  apply Subtype.ext
  funext p
  change localRingHom (scaleAut 𝒜 u)
      (ProjectiveSpectrum.comapFun (scaleAut 𝒜 u) (irrelevant_le_map 𝒜 u) p.val).1.toIdeal
      p.val.1.toIdeal rfl
      (s.val ⟨ProjectiveSpectrum.comapFun (scaleAut 𝒜 u) (irrelevant_le_map 𝒜 u) p.val,
        by simp [comapFun_eq]⟩) = s.val p
  apply localRingHom_apply_eq 𝒜 u _ _
    (congrArg HomogeneousIdeal.toIdeal (homogeneousIdeal_comap 𝒜 u p.val.1)) rfl
  exact dependent_apply_heq s.val (Subtype.ext (comapFun_eq 𝒜 u p.val))

/-- The identity induced by unit scaling preserves the actual degree-zero structure morphism. -/
@[reassoc]
theorem map_toSpecZero (u : (𝒜 0)ˣ) :
    Proj.map (scaleAut 𝒜 u) (irrelevant_le_map 𝒜 u) ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero 𝒜 := by
  rw [map_eq_id, Category.id_comp]

/-- For a graded algebra, the genuine unit scaling automorphism preserves its original base. -/
def scaleAlgEquiv {R : Type*} [CommRing R] [Algebra R A]
    (ℬ : ℕ → Submodule R A) [GradedAlgebra ℬ] (u : (ℬ 0)ˣ) : A ≃ₐ[R] A where
  __ := scaleRingEquiv ℬ u
  commutes' r := by
    change scaleAut ℬ u (algebraMap R A r) = algebraMap R A r
    rw [scaleAut_apply_of_mem ℬ u (SetLike.algebraMap_mem_graded ℬ r)]
    simp

/-- The actual unit scaling also has the native bundled graded algebra-homomorphism type. -/
def scaleGradedAlgHom {R : Type*} [CommRing R] [Algebra R A]
    (ℬ : ℕ → Submodule R A) [GradedAlgebra ℬ] (u : (ℬ 0)ˣ) : ℬ →ₐᵍ[R] ℬ where
  __ := (scaleAlgEquiv ℬ u).toAlgHom
  __ := scaleAut ℬ u

/-- The graded algebra scaling uses exactly the same actual graded ring map. -/
@[simp]
theorem scaleGradedAlgHom_toGradedRingHom {R : Type*} [CommRing R] [Algebra R A]
    (ℬ : ℕ → Submodule R A) [GradedAlgebra ℬ] (u : (ℬ 0)ˣ) :
    (scaleGradedAlgHom ℬ u).toGradedRingHom = scaleAut ℬ u := rfl

end

end DeJongAlterations.Geometry.ProjUnitScaling
