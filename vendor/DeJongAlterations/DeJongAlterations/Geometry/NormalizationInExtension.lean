import DeJongAlterations.Geometry.NormalizationInExtensionFunctionField
import DeJongAlterations.Geometry.NormalizationInExtensionEtale

/-!
# Actual finite normal alterations in specified function-field extensions

The comparison chart is chosen internally from the actual nonempty affine
cover. All geometry and the actual compatible function-field isomorphism
refer to the same native glued normalization and its actual structure map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.NormalizationInExtension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An actual nonempty affine chart chosen from the canonical cover at the generic point. -/
def comparisonChart (X : Scheme.{u}) [IsIntegral X] : NonemptyAffineOpen X :=
  (NormalizationFinite.nonemptyAffineCoordinateOpenCover X).idx (genericPoint X)

section Integral

variable {X : Scheme.{u}} [IsIntegral X] (L : Type u) [Field L]
  [Algebra X.functionField L] [FiniteDimensional X.functionField L]

/-- The prescribed field is the actual function field; no comparison chart is supplied. -/
def normalizationFunctionFieldEquiv : (normalization X L).functionField ≃+* L :=
  functionFieldEquiv L (comparisonChart X)

/-- The actual generic-stalk map agrees with the originally specified field embedding. -/
theorem normalizationFunctionFieldEquiv_comp :
    (normalizationFunctionFieldEquiv (X := X) L).toRingHom.comp
      (functionFieldMap (normalizationStructure X L)).hom = algebraMap X.functionField L :=
  functionFieldEquiv_comp L (comparisonChart X)

/-- The same actual field comparison, as an isomorphism over the actual original generic stalk. -/
def normalizationFunctionFieldAlgEquiv :
    letI := normalizationFunctionFieldAlgebra (X := X) L
    (normalization X L).functionField ≃ₐ[X.functionField] L :=
  functionFieldAlgEquiv L (comparisonChart X)

/-- The complete constructed geometric object has a normal integral source and the prescribed
actual function-field embedding, without a supplied gluing or comparison certificate. -/
theorem normalization_normal_integral_functionField :
    IsIntegral (normalization X L) ∧ IsNormalScheme (normalization X L) ∧
      IsDominant (normalizationStructure X L) ∧
      ∃ e : (normalization X L).functionField ≃+* L,
        e.toRingHom.comp (functionFieldMap (normalizationStructure X L)).hom =
          algebraMap X.functionField L :=
  ⟨inferInstance, normalization_isNormalScheme L, inferInstance,
    normalizationFunctionFieldEquiv L, normalizationFunctionFieldEquiv_comp L⟩

end Integral

section Variety

variable {k : Type u} [Field k] {X : Scheme.{u}}
  (p : X ⟶ Spec (.of k)) [IsVariety p]
  (L : Type u) [Field L] [Algebra X.functionField L] [FiniteDimensional X.functionField L]

/-- The actual normalization in the extension is a variety over the original arbitrary field. -/
theorem normalization_isVariety : IsVariety (normalizationStructure X L ≫ p) := by
  let : IsFinite (normalizationStructure X L) := normalizationStructure_isFinite L p
  exact .mk

/-- The actual constructed normal variety is a finite dominant alteration with exactly the
specified extension of the original canonical function field. -/
theorem finite_normal_alteration_in_extension :
    IsVariety (normalizationStructure X L ≫ p) ∧
      IsNormalScheme (normalization X L) ∧ IsFinite (normalizationStructure X L) ∧
      IsAlteration (normalizationStructure X L) ∧
      ∃ e : (normalization X L).functionField ≃+* L,
        e.toRingHom.comp (functionFieldMap (normalizationStructure X L)).hom =
          algebraMap X.functionField L :=
  ⟨normalization_isVariety p L, normalization_isNormalScheme L,
    normalizationStructure_isFinite L p, normalizationStructure_isAlteration L p,
    normalizationFunctionFieldEquiv L, normalizationFunctionFieldEquiv_comp L⟩

/-- Actual separability gives the generic-etale refinement of the same finite alteration. -/
theorem finite_normal_genericallyEtale_alteration_in_extension
    [Algebra.IsSeparable X.functionField L] :
    IsVariety (normalizationStructure X L ≫ p) ∧
      IsNormalScheme (normalization X L) ∧ IsFinite (normalizationStructure X L) ∧
      IsAlteration (normalizationStructure X L) ∧
      IsGenericallyEtale (normalizationStructure X L) :=
  ⟨normalization_isVariety p L, normalization_isNormalScheme L,
    normalizationStructure_isFinite L p, normalizationStructure_isAlteration L p,
    normalizationStructure_isGenericallyEtale L p⟩

end Variety

end DeJongAlterations.Geometry.NormalizationInExtension
