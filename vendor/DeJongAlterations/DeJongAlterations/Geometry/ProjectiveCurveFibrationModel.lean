import DeJongAlterations.Geometry.ProjectiveCurveFibrationCharts
import DeJongAlterations.Geometry.ProjectiveGraphModification
import DeJongAlterations.Geometry.BlowupProjective

/-!
# The actual projective graph model of the rational projection

All morphisms are the native schematic-image graph maps. Projectivity uses
the actual original closed embedding, its actual product base change, and
the native Segre closed immersion.
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

/-- The actual schematic graph closure in the native product of the original X with projective space. -/
def graphModel (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) : Scheme.{u} :=
  ProjectiveGraphModification.modification p (coordinateOpen r).1
    (projectiveCoordinateMap p r) (projectiveCoordinateMap_structure p r)

/-- The actual closed graph embedding into the actual product. -/
def graphEmbedding (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    graphModel p r ⟶ pullback p (projectiveSpaceStructure k n) :=
  ProjectiveGraphModification.embedding p (coordinateOpen r).1
    (projectiveCoordinateMap p r) (projectiveCoordinateMap_structure p r)

/-- The actual projection back to the original variety. -/
def graphProjection (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) : graphModel p r ⟶ X :=
  ProjectiveGraphModification.projection p (coordinateOpen r).1
    (projectiveCoordinateMap p r) (projectiveCoordinateMap_structure p r)

/-- The actual extension to projective coordinate space. -/
def graphFibration (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    graphModel p r ⟶ projectiveSpace k n :=
  ProjectiveGraphModification.projectiveMap p (coordinateOpen r).1
    (projectiveCoordinateMap p r) (projectiveCoordinateMap_structure p r)

/-- The actual source open inclusion into the graph closure. -/
def graphOpenInclusion (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    (coordinateOpen r).1.toScheme ⟶ graphModel p r :=
  ProjectiveGraphModification.inclusion p (coordinateOpen r).1
    (projectiveCoordinateMap p r) (projectiveCoordinateMap_structure p r)

instance graphEmbedding_isClosedImmersion (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    IsClosedImmersion (graphEmbedding p r) := by
  unfold graphEmbedding
  infer_instance

@[reassoc (attr := simp)]
theorem graphEmbedding_fst (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    graphEmbedding p r ≫ pullback.fst _ _ = graphProjection p r := rfl

@[reassoc (attr := simp)]
theorem graphEmbedding_snd (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    graphEmbedding p r ≫ pullback.snd _ _ = graphFibration p r := rfl

@[reassoc (attr := simp)]
theorem graphOpenInclusion_projection (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    graphOpenInclusion p r ≫ graphProjection p r = (coordinateOpen r).1.ι :=
  ProjectiveGraphModification.inclusion_projection _ _ _ _

@[reassoc (attr := simp)]
theorem graphOpenInclusion_fibration (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    graphOpenInclusion p r ≫ graphFibration p r = projectiveCoordinateMap p r :=
  ProjectiveGraphModification.inclusion_projectiveMap _ _ _ _

@[reassoc]
theorem graphFibration_structure (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    graphFibration p r ≫ projectiveSpaceStructure k n = graphProjection p r ≫ p :=
  ProjectiveGraphModification.structure_triangle _ _ _ _

end Integral

section Variety

variable {k : Type u} [Field k] {X : Scheme.{u}} {n : ℕ}

theorem variety_isNoetherian (p : X ⟶ Spec (.of k)) [IsVariety p] :
    AlgebraicGeometry.IsNoetherian X := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  exact ⟨⟩

instance graphOpenInclusion_isOpenImmersion (p : X ⟶ Spec (.of k)) [IsVariety p]
    (r : Fin n → X.functionField) : IsOpenImmersion (graphOpenInclusion p r) := by
  let := variety_isNoetherian p
  unfold graphOpenInclusion
  infer_instance

instance graphOpenInclusion_isDominant (p : X ⟶ Spec (.of k)) [IsVariety p]
    (r : Fin n → X.functionField) : IsDominant (graphOpenInclusion p r) := by
  let := variety_isNoetherian p
  unfold graphOpenInclusion
  infer_instance

instance graphProjection_isModification (p : X ⟶ Spec (.of k)) [IsVariety p]
    (r : Fin n → X.functionField) : IsModification (graphProjection p r) :=
  ProjectiveGraphModification.projection_isModification_of_variety _ _ _ _

instance graphModel_isIntegral (p : X ⟶ Spec (.of k)) [IsVariety p]
    (r : Fin n → X.functionField) : IsIntegral (graphModel p r) :=
  (inferInstance : IsModification (graphProjection p r)).sourceIntegral

theorem graphProjection_restrict_isIso (p : X ⟶ Spec (.of k)) [IsVariety p]
    (r : Fin n → X.functionField) : IsIso (graphProjection p r ∣_ (coordinateOpen r).1) := by
  let := variety_isNoetherian p
  exact ProjectiveGraphModification.projection_restrict_isIso _ _ _ _

theorem graphModel_isVariety (p : X ⟶ Spec (.of k)) [IsVariety p]
    (r : Fin n → X.functionField) : IsVariety (graphProjection p r ≫ p) :=
  ProjectiveGraphModification.modification_isVariety _ _ _ _

end Variety

section Integral

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}

/-- A closed projective product embedding and actual Segre give projectivity of the model. -/
theorem graphModel_isProjective (p : X ⟶ Spec (.of k)) (hp : IsProjectiveOver p)
    (r : Fin n → X.functionField) : IsProjectiveOver (graphProjection p r ≫ p) := by
  obtain ⟨m, i, hi, hbase⟩ := hp
  let := hi
  subst p
  refine ⟨Algebra.Segre.dimension m n,
    graphEmbedding (i ≫ projectiveSpaceStructure k m) r ≫
      BlowupProjective.productClosedEmbedding i n ≫ Segre.segre k m n, inferInstance, ?_⟩
  simp only [Category.assoc, Segre.segre_structure,
    BlowupProjective.productClosedEmbedding_fst_assoc]
  rfl

theorem graphFibration_isProper (p : X ⟶ Spec (.of k)) (hp : IsProjectiveOver p)
    (r : Fin n → X.functionField) : IsProper (graphFibration p r) := by
  let := hp.isProper
  unfold graphFibration ProjectiveGraphModification.projectiveMap
  infer_instance

theorem graphFibration_isDominant (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField)
    (hr : letI := SeparableGenericSmoothness.functionFieldAlgebra p; AlgebraicIndependent k r) :
    IsDominant (graphFibration p r) := by
  have : IsDominant (graphOpenInclusion p r ≫ graphFibration p r) := by
    rw [graphOpenInclusion_fibration]
    exact projectiveCoordinateMap_isDominant p r hr
  exact IsDominant.of_comp (graphOpenInclusion p r) (graphFibration p r)

end Integral

end DeJongAlterations.Geometry.ProjectiveCurveFibration
