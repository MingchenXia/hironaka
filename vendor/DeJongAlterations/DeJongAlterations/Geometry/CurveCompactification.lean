import DeJongAlterations.Geometry.CurveCompactificationLift
import DeJongAlterations.Geometry.NormalCurveModificationProjective
import DeJongAlterations.Geometry.NormalizationFiniteArbitraryField
import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberOpenDimension
import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberNormalizationDimension

/-!
# Actual regular projective compactifications of normal curves

The original normal curve is embedded into its actual schematic projective
closure, which is then normalized. The whole original normal open lifts
through that finite modification. Projectivity of the normalized proper
curve follows from the genuine Chow and normal-modification theorems.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.CurveCompactification

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- A normal curve over any field has an internally constructed normal regular
projective compactification, with the actual original open inclusion and coefficient map. -/
theorem exists_regular_projective_compactification
    (p : X ⟶ Spec (.of k)) [IsVariety p] (hn : IsNormalScheme X)
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ (C : Scheme.{u}) (pC : C ⟶ Spec (.of k)) (i : X ⟶ C),
      IsVariety pC ∧ IsProjectiveOver pC ∧ IsOpenImmersion i ∧ IsDominant i ∧
      i ≫ pC = p ∧ IsNormalScheme C ∧ IsRegularScheme C ∧ topologicalKrullDim C ≤ 1 := by
  have hqp := NormalCurveModification.isQuasiProjectiveOver_of_normal_curve p hn hdim
  obtain ⟨Y, pY, j, hvY, hpY, hj, hdj, hbase⟩ :=
    QuasiProjectiveCompactification.exists_compactification p hqp
  let := hvY
  let := hj
  let := hdj
  have hdimY : topologicalKrullDim Y ≤ 1 :=
    FunctionFieldDimension.topologicalKrullDim_le_one_of_dense_open pY j hdim
  let C := NormalizationGluing.normalization Y
  let π := NormalizationGluing.normalizationStructure Y
  let pC := π ≫ pY
  let : IsIntegral C := NormalizationFinite.isIntegral_normalization
  let : IsModification π := NormalizationFiniteArbitraryField.normalizationStructure_isModification pY
  let : IsFinite π := NormalizationFiniteArbitraryField.normalizationStructure_isFinite pY
  let : IsVariety pC := NormalizationFiniteArbitraryField.normalization_isVariety pY
  let : IsProper pY := hpY.isProper
  let : IsProper pC := by dsimp only [pC]; infer_instance
  have hnC : IsNormalScheme C := NormalizationGluing.normalization_isNormalScheme Y
  have hrC : IsRegularScheme C := NormalizationFiniteArbitraryField.normalization_isRegular pY hdimY
  have hdimC : topologicalKrullDim C ≤ 1 :=
    FunctionFieldDimension.topologicalKrullDim_normalization_le_one Y hdimY
  have hpC : IsProjectiveOver pC :=
    NormalCurveModification.isProjectiveOver_of_isProper_normal_curve pC hnC hdimC
  obtain ⟨i, hi, hdi, heq⟩ := exists_open_lift_of_finite_modification π j hn
  refine ⟨C, pC, i, inferInstance, hpC, hi, hdi, ?_, hnC, hrC, hdimC⟩
  change i ≫ π ≫ pY = p
  rw [← Category.assoc, heq, hbase]

end DeJongAlterations.Geometry.CurveCompactification
