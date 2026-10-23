import DeJongAlterations.Geometry.FiniteProjectivePreservation
import DeJongAlterations.Geometry.NormalizationFiniteArbitraryField

/-!
# Projectivity of the actual normalization over an arbitrary ground field

The genuine arbitrary-field finiteness theorem applies to the literal global
normalization structure map. Finite projectivity preservation retains this
same normalization scheme and its original map to the ground field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Geometry.NormalizationProjective

open NormalizationGluing

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- The actual normalization of a projective finite-type integral scheme is projective
over the same arbitrary field, with its original normalization structure map. -/
theorem normalization_isProjectiveOver (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hp : IsProjectiveOver p) : IsProjectiveOver (normalizationStructure X ≫ p) := by
  let : IsFinite (normalizationStructure X) :=
    NormalizationFiniteArbitraryField.normalizationStructure_isFinite p
  exact FiniteProjective.isProjectiveOver_comp_of_isFinite p hp (normalizationStructure X)

end DeJongAlterations.Geometry.NormalizationProjective
