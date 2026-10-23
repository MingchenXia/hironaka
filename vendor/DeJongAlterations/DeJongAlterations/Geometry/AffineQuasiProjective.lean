import DeJongAlterations.Geometry.SegreChart
import DeJongAlterations.Geometry.QuasiProjectiveCompactification
import Mathlib.RingTheory.FiniteType
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Actual projective immersions of finite-type affine schemes

A finite polynomial presentation gives a closed immersion into a genuine
native projective coordinate chart. Finite generation supplies the presentation
internally. Transport along the native affine spectrum isomorphism then gives
a projective immersion of the original affine scheme, preserving its literal
structure morphism. No presentation or immersion certificate is assumed by
the final existence theorems.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

universe u

namespace DeJongAlterations.Geometry.AffineQuasiProjective

open ProjectiveIdeal

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- Rename a finite polynomial presentation into the actual zero coordinate chart. -/
def coordinatePresentation {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] A) :
    CoordinateRing R (0 : Fin (n + 1)) →ₐ[R] A :=
  f.comp (MvPolynomial.renameEquiv R (finSuccAboveEquiv (0 : Fin (n + 1))).symm).toAlgHom

/-- The actual native projective map supplied by a finite polynomial presentation. -/
def polynomialProjectiveImmersion {n : ℕ} (f : MvPolynomial (Fin n) R →ₐ[R] A) :
    Spec (CommRingCat.of A) ⟶ projectiveSpace R n :=
  Spec.map (CommRingCat.ofHom (coordinatePresentation f).toRingHom) ≫
    Segre.coordinateChartInclusion (R := R) (0 : Fin (n + 1))

/-- A surjective presentation gives a genuine closed chart immersion, hence an immersion. -/
theorem polynomialProjectiveImmersion_isImmersion {n : ℕ}
    (f : MvPolynomial (Fin n) R →ₐ[R] A) (hf : Function.Surjective f) :
    IsImmersion (polynomialProjectiveImmersion f) := by
  have hs : Function.Surjective (coordinatePresentation f) :=
    hf.comp (MvPolynomial.renameEquiv R
      (finSuccAboveEquiv (0 : Fin (n + 1))).symm).surjective
  have : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (coordinatePresentation f).toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hs
  unfold polynomialProjectiveImmersion
  infer_instance

/-- The actual projective immersion preserves the original coefficient morphism. -/
@[reassoc]
theorem polynomialProjectiveImmersion_structure {n : ℕ}
    (f : MvPolynomial (Fin n) R →ₐ[R] A) :
    polynomialProjectiveImmersion f ≫ projectiveSpaceStructure R n =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [polynomialProjectiveImmersion, Category.assoc,
    Segre.coordinateChartInclusion_structure, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext r
  exact (coordinatePresentation f).commutes r

/-- Finite generation internally constructs a native projective immersion with its original base map. -/
theorem exists_projective_immersion_spec_algebraMap [Algebra.FiniteType R A] :
    ∃ (n : ℕ) (e : Spec (CommRingCat.of A) ⟶ projectiveSpace R n),
      IsImmersion e ∧ e ≫ projectiveSpaceStructure R n =
        Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R A)
  exact ⟨n, polynomialProjectiveImmersion f,
    polynomialProjectiveImmersion_isImmersion f hf,
    polynomialProjectiveImmersion_structure f⟩

omit [Algebra R A] in
/-- Recover the canonical algebra from the given spectrum morphism, then construct its immersion. -/
theorem exists_projective_immersion_of_locallyOfFiniteType
    (p : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType p] :
    ∃ (n : ℕ) (e : Spec (CommRingCat.of A) ⟶ projectiveSpace R n),
      IsImmersion e ∧ e ≫ projectiveSpaceStructure R n = p := by
  obtain ⟨φ, rfl : Spec.map φ = p⟩ := Spec.homEquiv.symm.surjective p
  let : Algebra R A := φ.hom.toAlgebra
  have : RingHom.FiniteType φ.hom :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  let : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp this
  exact exists_projective_immersion_spec_algebraMap

/-- Every affine locally finite-type morphism has an actual native projective immersion. -/
theorem exists_projective_immersion_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType p] :
    ∃ (n : ℕ) (e : X ⟶ projectiveSpace R n),
      IsImmersion e ∧ e ≫ projectiveSpaceStructure R n = p := by
  obtain ⟨n, e, he, hbase⟩ :=
    exists_projective_immersion_of_locallyOfFiniteType (X.isoSpec.inv ≫ p)
  have := he
  refine ⟨n, X.isoSpec.hom ≫ e, inferInstance, ?_⟩
  rw [Category.assoc, hbase]
  simp

/-- Native quasi-projectivity of the original affine finite-type morphism. -/
theorem isQuasiProjectiveOver_of_isAffine {X : Scheme.{u}} [IsAffine X]
    (p : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType p] : IsQuasiProjectiveOver p :=
  exists_projective_immersion_of_isAffine p

/-- An affine variety has an actual dense open projective compactification over its original field. -/
theorem exists_affine_variety_compactification {k : Type u} [Field k]
    {X : Scheme.{u}} [IsAffine X] (p : X ⟶ Spec (CommRingCat.of k)) [IsVariety p] :
    ∃ (Xbar : Scheme.{u}) (pbar : Xbar ⟶ Spec (CommRingCat.of k)) (j : X ⟶ Xbar),
      IsVariety pbar ∧ IsProjectiveOver pbar ∧ IsOpenImmersion j ∧ IsDominant j ∧ j ≫ pbar = p :=
  QuasiProjectiveCompactification.exists_compactification p (isQuasiProjectiveOver_of_isAffine p)

end DeJongAlterations.Geometry.AffineQuasiProjective
