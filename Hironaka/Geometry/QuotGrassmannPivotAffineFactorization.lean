import Hironaka.Geometry.QuotGrassmannPivotEvaluatedInjectivity
import Mathlib.AlgebraicGeometry.Gluing

/-! Original affine chart morphisms internally produce their whole polynomial evaluations. -/

noncomputable section

open scoped Classical
open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

open Algebra.PluckerQuot Algebra.PluckerQuotTransition

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {A ι ν : Type u} [CommRing A] [Algebra R A]
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

omit [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν] in
/-- An actual original over-R polynomial-chart morphism produces its SAME whole original evaluation. -/
theorem originalChartMap_eq_evaluation
    (a : Spec (.of A) ⟶ affineChart R ι ν)
    (ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R ι ν))) =
      Spec.map (CommRingCat.ofHom (algebraMap R A))) :
    ∃ C : Matrix ι ν A, a = Spec.map (CommRingCat.ofHom
      (originalMatrixCoefficientEvaluation R C).toRingHom) := by
  let ψ := Spec.preimage a
  have hψ : ψ.hom.comp (algebraMap R (ChartRing R ι ν)) = algebraMap R A := by
    have hcat : CommRingCat.ofHom (algebraMap R (ChartRing R ι ν)) ≫ ψ =
        CommRingCat.ofHom (algebraMap R A) := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_preimage]
      exact ha
    exact congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of A => f.hom) hcat
  let φ : ChartRing R ι ν →ₐ[R] A :=
    { ψ.hom with commutes' := fun r => RingHom.congr_fun hψ r }
  let C : Matrix ι ν A := fun i j => φ (MvPolynomial.X (i, j))
  have heval : φ = originalMatrixCoefficientEvaluation R C := by
    ext ij
    rcases ij with ⟨i, j⟩
    rw [originalMatrixCoefficientEvaluation_X]
  refine ⟨C, ?_⟩
  calc
    a = Spec.map ψ := (Spec.map_preimage a).symm
    _ = Spec.map (CommRingCat.ofHom φ.toRingHom) := rfl
    _ = _ := congrArg (fun f : ChartRing R ι ν →ₐ[R] A =>
      Spec.map (CommRingCat.ofHom f.toRingHom)) heval

/-- The actual original open-immersion lift constructs the matrix and entire original morphism. -/
theorem originalAffineMorphism_eq_evaluatedPivot_of_range
    (f : Spec (.of A) ⟶ projectiveModel R ι ν)
    (hf : f ≫ projectiveStructure R ι ν = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (p : (ι ⊕ ν) ≃ (ι ⊕ ν))
    (hp : Set.range f ⊆ Set.range (originalPivotModelMorphism R p)) :
    ∃ C : Matrix ι ν A, f = originalMatrixEvaluatedPivotMorphism R p C := by
  let a := IsOpenImmersion.lift (originalPivotModelMorphism R p) f hp
  have haf : a ≫ originalPivotModelMorphism R p = f := IsOpenImmersion.lift_fac _ _ hp
  have ha : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (ChartRing R ι ν))) =
      Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [← originalPivotModelMorphism_structure R p, ← Category.assoc, haf]
    exact hf
  obtain ⟨C, hC⟩ := originalChartMap_eq_evaluation R a ha
  refine ⟨C, haf.symm.trans ?_⟩
  rw [hC]
  rfl

/-- Native classifier equality determines arbitrary actual original morphisms lying in original charts. -/
theorem originalAffineMorphism_eq_of_classifier_eq_of_ranges
    (f g : Spec (.of A) ⟶ projectiveModel R ι ν)
    (hf : f ≫ projectiveStructure R ι ν = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hg : g ≫ projectiveStructure R ι ν = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (p t : (ι ⊕ ν) ≃ (ι ⊕ ν))
    (hp : Set.range f ⊆ Set.range (originalPivotModelMorphism R p))
    (ht : Set.range g ⊆ Set.range (originalPivotModelMorphism R t))
    (h : originalGlobalAffineGrassmannianTensorPoint R ι ν f =
      originalGlobalAffineGrassmannianTensorPoint R ι ν g) : f = g := by
  obtain ⟨C, rfl⟩ := originalAffineMorphism_eq_evaluatedPivot_of_range R f hf p hp
  obtain ⟨D, rfl⟩ := originalAffineMorphism_eq_evaluatedPivot_of_range R g hg t ht
  exact originalMatrixEvaluatedPivotMorphism_eq_of_classifier_eq R p t C D h

end Hironaka.Geometry.QuotGrassmann
