import Hironaka.Geometry.CurveFibrationGenericSmoothMarksCommonField
import Hironaka.Geometry.CurveFibrationMarkedOpenSmooth

/-! Actual finite Galois generic smooth marks for the ORIGINAL curve fibration. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
noncomputable section
universe u

namespace Hironaka.Geometry.CurveFibrationGenericSmoothMarks

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- ORIGINAL fibration geometry produces the three generic smooth maps over
ONE actual finite Galois extension of the ORIGINAL function field. -/
theorem exists_original_generic_smooth_marks {X S : Scheme.{u}}
    [IsIntegral X] [IsIntegral S] (f : X ⟶ S) [IsDominant f] [IsProper f]
    [LocallyOfFinitePresentation f] [Smooth (f.fiberToSpecResidueField (genericPoint S))]
    (hdim : 0 < topologicalKrullDim (f.fiber (genericPoint S))) :
    ∃ L : IntermediateField S.functionField (SeparableClosure S.functionField),
      FiniteDimensional S.functionField L ∧ IsGalois S.functionField L ∧
      ∃ φ : Fin 3 → (Spec (.of L) ⟶ X),
        (∀ i, φ i ≫ f = Spec.map (CommRingCat.ofHom (algebraMap S.functionField L)) ≫
          S.fromSpecStalk (genericPoint S)) ∧
        Function.Injective (fun i => φ i (⊥ : PrimeSpectrum L)) ∧
        ∀ i, φ i (⊥ : PrimeSpectrum L) ∈ f.smoothLocus := by
  let η := genericPoint S
  let C := f.fiber η
  let := GenericFiberIntegral.genericFiber_isIntegral f
  let ρ := S.residue η
  let : IsIso ρ := (ConcreteCategory.isIso_iff_bijective ρ).mpr
    ⟨ρ.hom.injective, IsLocalRing.residue_surjective⟩
  let p : C ⟶ Spec S.functionField := f.fiberToSpecResidueField η ≫ Spec.map ρ
  let : IsProper (f.fiberToSpecResidueField η) := by
    dsimp only [Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  let : IsProper p := by dsimp only [p]; infer_instance
  let : Smooth p := inferInstance
  have hη (x : C) : f (f.fiberι η x) = η := (f.fiberHomeo η x).property
  let U : C.Opens := (f.fiberι η) ⁻¹ᵁ f.smoothLocus
  have hU : (U : Set C).Nonempty :=
    ⟨genericPoint C, CurveFibrationMarkedOpen.genericFiber_le_smoothLocus f _ (hη _)⟩
  obtain ⟨L, hfin, hgal, q, hq, hmem, hinj, _⟩ :=
    exists_three_common_field_points p hdim U hU
  let φ (i : Fin 3) : Spec (.of L) ⟶ X := q i ≫ f.fiberι η
  have hp : f.fiberι η ≫ f = p ≫ S.fromSpecStalk η := by
    rw [Scheme.Hom.fiber_fac]
    simp only [p, ρ, Scheme.fromSpecResidueField, Category.assoc]
  refine ⟨L, hfin, hgal, φ, ?_, ?_, ?_⟩
  · intro i
    dsimp only [φ]
    rw [Category.assoc, hp, ← Category.assoc, hq i]
  · intro i j hij
    apply hinj
    exact (f.fiberι η).isEmbedding.injective hij
  · intro i
    exact hmem i

end Hironaka.Geometry.CurveFibrationGenericSmoothMarks
