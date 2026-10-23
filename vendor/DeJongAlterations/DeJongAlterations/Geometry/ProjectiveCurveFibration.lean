import DeJongAlterations.Geometry.ProjectiveCurveFibrationModel
import DeJongAlterations.Geometry.ProjectiveCurveFibrationFiberMaps
import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiber
import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberOpenDimension
import DeJongAlterations.Geometry.GenericFiberIntegral
import DeJongAlterations.Geometry.FiberDimension

/-!
# Actual projective models of the rational curve projection

The original projective variety and its canonical separating function field
construct all coordinates, opens, graph maps, projective embeddings and
generic-fibre comparisons internally. Only the actual generic fibre is
asserted to have dimension one; no all-fibre, boundary, geometric connectedness
or Bertini conclusion is claimed here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.ProjectiveCurveFibration

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open RationalCoordinateMap

section Integral

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}

/-- The actual target affine chart carries the known generic curve fibre to projective space. -/
theorem projectiveCoordinateMap_genericFiber_dimension_one
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (r : Fin (n + 1) → X.functionField)
    (hb : letI := SeparableGenericSmoothness.functionFieldAlgebra p; IsTranscendenceBasis k r) :
    topologicalKrullDim ((projectiveCoordinateMap p (fun i : Fin n ↦ r i.castSucc)).fiber
      (genericPoint (projectiveSpace k n))) = 1 := by
  let := projectiveSpace_isIntegral k n
  let r' := fun i : Fin n ↦ r i.castSucc
  let e := fiberCompOpenImmersionIso (coordinateMap p r') (affineChart k n)
    (genericPoint (Spec (.of (MvPolynomial (Fin n) k))))
  have heq := e.schemeIsoToHomeo.isHomeomorph.topologicalKrullDim_eq
  rw [genericPoint_eq_of_isOpenImmersion (affineChart k n)] at heq
  change topologicalKrullDim ((coordinateMap p r' ≫ affineChart k n).fiber
    (genericPoint (projectiveSpace k n))) = 1
  rw [← heq]
  exact RationalCoordinateMapGenericFiber.genericFiber_dimension_one p r hb

end Integral

section Variety

variable {k : Type u} [Field k] {X : Scheme.{u}} {n : ℕ}

/-- The actual graph source open retains its actual dimension-one generic fibre. -/
theorem graphOpenGenericFiber_dimension_one (p : X ⟶ Spec (.of k)) [IsVariety p]
    (r : Fin (n + 1) → X.functionField)
    (hb : letI := SeparableGenericSmoothness.functionFieldAlgebra p; IsTranscendenceBasis k r) :
    topologicalKrullDim (((graphOpenInclusion p (fun i : Fin n ↦ r i.castSucc)) ≫
      graphFibration p (fun i : Fin n ↦ r i.castSucc)).fiber
      (genericPoint (projectiveSpace k n))) = 1 := by
  rw [graphOpenInclusion_fibration]
  exact projectiveCoordinateMap_genericFiber_dimension_one p r hb

/-- Nonemptiness comes from the actual affine-coordinate fibre computation. -/
theorem graphOpenGenericFiber_nonempty (p : X ⟶ Spec (.of k)) [IsVariety p]
    (r : Fin (n + 1) → X.functionField)
    (hb : letI := SeparableGenericSmoothness.functionFieldAlgebra p; IsTranscendenceBasis k r) :
    Nonempty (((graphOpenInclusion p (fun i : Fin n ↦ r i.castSucc)) ≫
      graphFibration p (fun i : Fin n ↦ r i.castSucc)).fiber
      (genericPoint (projectiveSpace k n))) := by
  apply (FiberDimension.topologicalKrullDim_nonneg_iff _).mp
  rw [graphOpenGenericFiber_dimension_one p r hb]
  exact zero_le_one

/-- The actual graph model's generic fibre is integral by the proved general native theorem. -/
theorem graphGenericFiber_isIntegral (p : X ⟶ Spec (.of k)) [IsVariety p]
    (r : Fin n → X.functionField)
    (hr : letI := SeparableGenericSmoothness.functionFieldAlgebra p; AlgebraicIndependent k r) :
    IsIntegral ((graphFibration p r).fiber (genericPoint (projectiveSpace k n))) := by
  let := projectiveSpace_isIntegral k n
  let := graphFibration_isDominant p r hr
  exact GenericFiberIntegral.genericFiber_isIntegral (graphFibration p r)

/-- The actual generic fibre of the original dense open is a dominant open in the model fibre. -/
theorem graphOpenGenericFiber_isDominant (p : X ⟶ Spec (.of k)) [IsVariety p]
    (r : Fin (n + 1) → X.functionField)
    (hb : letI := SeparableGenericSmoothness.functionFieldAlgebra p; IsTranscendenceBasis k r) :
    IsDominant (sourceFiberMap (graphOpenInclusion p (fun i : Fin n ↦ r i.castSucc))
      (graphFibration p (fun i : Fin n ↦ r i.castSucc)) (genericPoint (projectiveSpace k n))) := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let : IsIntegral ((graphFibration p (fun i : Fin n ↦ r i.castSucc)).fiber
      (genericPoint (projectiveSpace k n))) :=
    graphGenericFiber_isIntegral p (fun i : Fin n ↦ r i.castSucc)
      (hb.1.comp Fin.castSucc (Fin.castSucc_injective n))
  let := graphOpenGenericFiber_nonempty p r hb
  constructor
  exact (sourceFiberMap _ _ _).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)

/-- The full actual projective-model generic fibre has dimension exactly one. -/
theorem graphFibration_genericFiber_dimension_one (p : X ⟶ Spec (.of k)) [IsVariety p]
    (hp : IsProjectiveOver p) (r : Fin (n + 1) → X.functionField)
    (hb : letI := SeparableGenericSmoothness.functionFieldAlgebra p; IsTranscendenceBasis k r) :
    topologicalKrullDim ((graphFibration p (fun i : Fin n ↦ r i.castSucc)).fiber
      (genericPoint (projectiveSpace k n))) = 1 := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  let r' := fun i : Fin n ↦ r i.castSucc
  let f := graphFibration p r'
  let j := graphOpenInclusion p r'
  let y := genericPoint (projectiveSpace k n)
  let := graphGenericFiber_isIntegral p r' (hb.1.comp Fin.castSucc (Fin.castSucc_injective n))
  let := graphOpenGenericFiber_nonempty p r hb
  let : IsProper f := graphFibration_isProper p hp r'
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have heq := FunctionFieldDimension.topologicalKrullDim_eq_of_openImmersion
    (f.fiberToSpecResidueField y) (sourceFiberMap j f y)
  exact heq.symm.trans (graphOpenGenericFiber_dimension_one p r hb)

/-- Canonical separating coordinates produce an actual projective modification with generic curve fibre. -/
theorem exists_projective_curve_fibration_model
    (p : X ⟶ Spec (.of k)) [IsVariety p] (hp : IsProjectiveOver p)
    (h : SeparableGenericSmoothness.FunctionFieldSeparablyGenerated p)
    (htr : letI := SeparableGenericSmoothness.functionFieldAlgebra p
      Algebra.Transcendental k X.functionField) :
    ∃ (n : ℕ) (Y : Scheme.{u}) (π : Y ⟶ X) (F : Y ⟶ projectiveSpace k n),
      IsModification π ∧ IsVariety (π ≫ p) ∧ IsProjectiveOver (π ≫ p) ∧
      IsProper F ∧ IsDominant F ∧ F ≫ projectiveSpaceStructure k n = π ≫ p ∧
      topologicalKrullDim (F.fiber (genericPoint (projectiveSpace k n))) = 1 ∧
      (∃ e : Y ⟶ pullback p (projectiveSpaceStructure k n),
        IsClosedImmersion e ∧ e ≫ pullback.fst _ _ = π ∧ e ≫ pullback.snd _ _ = F) ∧
      ∃ U : X.affineOpens, Nonempty U.1 ∧ Dense (U.1 : Set X) ∧ IsIso (π ∣_ U.1) ∧
        ∃ j : U.1.toScheme ⟶ Y, IsOpenImmersion j ∧ IsDominant j ∧ j ≫ π = U.1.ι := by
  let := SeparableGenericSmoothness.functionFieldAlgebra p
  obtain ⟨n, r, hb, -, -, -, -⟩ := exists_separating_projection p h htr
  let r' := fun i : Fin n ↦ r i.castSucc
  refine ⟨n, graphModel p r', graphProjection p r', graphFibration p r', inferInstance,
    graphModel_isVariety p r', graphModel_isProjective p hp r', graphFibration_isProper p hp r',
    graphFibration_isDominant p r' (hb.1.comp Fin.castSucc (Fin.castSucc_injective n)),
    graphFibration_structure p r', graphFibration_genericFiber_dimension_one p hp r hb,
    ⟨graphEmbedding p r', inferInstance, graphEmbedding_fst p r', graphEmbedding_snd p r'⟩,
    coordinateOpen r', inferInstance, coordinateOpen_dense r', graphProjection_restrict_isIso p r',
    graphOpenInclusion p r', inferInstance, inferInstance, graphOpenInclusion_projection p r'⟩

end Variety

end DeJongAlterations.Geometry.ProjectiveCurveFibration
