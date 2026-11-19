import Hironaka.Geometry.QuotGrassmannPivotAffineTensorBaseChange

/-!
# SAME actual quotient gives a native natural Grassmannian classifier

Every affine point is produced from SAME original global quotient. Native
Grassmannian base change preserves the actual original point, with source
coordinates and both target maps internally constructed and compared.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem originalActualPointNaturality
    {R A B V M N : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [AddCommGroup V] [Module R V]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [Module.Projective A M]
    [AddCommGroup N] [Module B N] [Module.Finite B N] [Module.Projective B N]
    (φ : A →ₐ[R] B) (qA : A ⊗[R] V →ₗ[A] M) (hqA : Function.Surjective qA)
    (qB : B ⊗[R] V →ₗ[B] N) (hqB : Function.Surjective qB) (r : ℕ)
    (hrA : ∀ p, Module.rankAtStalk (R := A) M p = r)
    (hrB : ∀ p, Module.rankAtStalk (R := B) N p = r)
    (e : letI : Algebra A B := φ.toAlgebra; B ⊗[A] M ≃ₗ[B] N)
    (he : letI : Algebra A B := φ.toAlgebra
      letI : IsScalarTower R A B :=
        IsScalarTower.of_algebraMap_eq' (by ext x; exact (φ.commutes x).symm)
      qB = e.toLinearMap.comp (Algebra.GrassmannQuotientKernel.changedQuotient qA)) :
    Module.Grassmannian.map φ (Algebra.GrassmannQuotientKernel.point qA hqA r hrA) =
      Algebra.GrassmannQuotientKernel.point qB hqB r hrB := by
  let : Algebra A B := φ.toAlgebra
  let : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (φ.commutes x).symm)
  exact (Algebra.GrassmannQuotientKernel.point_map φ qA hqA r hrA).trans
    (Algebra.GrassmannQuotientKernel.point_eq_of_targetEquiv
      (Algebra.GrassmannQuotientKernel.changedQuotient qA)
      (Algebra.GrassmannQuotientKernel.changedQuotient_surjective qA hqA)
      qB hqB r (Algebra.GrassmannQuotientKernel.changedRank r hrA) hrB e he)

variable (R : Type u) [CommRing R] (ι ν : Type u)
  [Fintype ι] [Fintype ν] [DecidableEq ι]

/-- Native Grassmannian base change maps the actual ORIGINAL quotient point to SAME original composed affine-test point. -/
theorem originalGlobalAffineGrassmannianTensorPoint_map
    {A B : CommRingCat.{u}} [Algebra R A] [Algebra R B]
    (φ : A →ₐ[R] B) (f : Spec A ⟶ projectiveModel R ι ν) :
    Module.Grassmannian.map φ (originalGlobalAffineGrassmannianTensorPoint R ι ν f) =
      originalGlobalAffineGrassmannianTensorPoint R ι ν
        (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f) := by
  let : Algebra A B := φ.toAlgebra
  let : IsScalarTower R A B :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (φ.commutes x).symm)
  have hA := originalGlobalAffinePullbackSections_finitePresentation_projective R ι ν f
  let := hA.1
  let := hA.2
  have hB := originalGlobalAffinePullbackSections_finitePresentation_projective R ι ν
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f)
  let := hB.1
  let := hB.2
  let qA := originalGlobalAffineTensorQuotient R ι ν f
  let qB := originalGlobalAffineTensorQuotient R ι ν
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f)
  let hqA := originalGlobalAffineTensorQuotient_surjective R ι ν f
  let hqB := originalGlobalAffineTensorQuotient_surjective R ι ν
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f)
  let hrA := originalGlobalAffinePullbackSections_rankAtStalk R ι ν f
  let hrB := originalGlobalAffinePullbackSections_rankAtStalk R ι ν
    (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f)
  have h := originalActualPointNaturality φ qA hqA qB hqB (Fintype.card ι) hrA hrB
    (originalGlobalAffineImageSectionsBaseChangeIso R ι ν
      (CommRingCat.ofHom φ.toRingHom) f).toLinearEquiv
    (originalGlobalAffineTensorQuotient_baseChange R ι ν φ f)
  have hpA : originalGlobalAffineGrassmannianTensorPoint R ι ν f =
      Algebra.GrassmannQuotientKernel.point qA hqA (Fintype.card ι) hrA := by
    apply Module.Grassmannian.ext
    rfl
  have hpB : originalGlobalAffineGrassmannianTensorPoint R ι ν
      (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ f) =
        Algebra.GrassmannQuotientKernel.point qB hqB (Fintype.card ι) hrB := by
    apply Module.Grassmannian.ext
    rfl
  exact (congrArg (Module.Grassmannian.map φ) hpA).trans (h.trans hpB.symm)

/-- The genuine native affine-test functor of SAME original projective Plucker model. -/
def originalGlobalAffineTestFunctor : CommAlgCat.{u} R ⥤ Type u :=
  forget₂ (CommAlgCat.{u} R) CommRingCat ⋙ Scheme.Spec.rightOp ⋙
    yoneda.obj (projectiveModel R ι ν)

/-- Actual original quotient points give a natural transformation to the native Grassmannian functor, with no classifier comparison supplied. -/
def originalGlobalAffineGrassmannianClassifier :
    originalGlobalAffineTestFunctor R ι ν ⟶
      Module.Grassmannian.functor (R := R) (M := (ι ⊕ ν) → R) (Fintype.card ι) where
  app A := ↾fun f => originalGlobalAffineGrassmannianTensorPoint R ι ν
    (A := CommRingCat.of A) f
  naturality A B φ := by
    ext f
    exact (originalGlobalAffineGrassmannianTensorPoint_map R ι ν
      (A := CommRingCat.of A) (B := CommRingCat.of B) φ.hom f).symm

end Hironaka.Geometry.QuotGrassmann
