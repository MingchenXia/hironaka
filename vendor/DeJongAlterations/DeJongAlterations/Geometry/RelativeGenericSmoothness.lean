import DeJongAlterations.Geometry.NormalizationInExtensionFunctionField
import DeJongAlterations.Geometry.SeparableGenericSmoothness

/-!
# Generic smoothness of a dominant morphism over an integral base

The field algebra is the actual canonical generic-stalk map. Separable
generation implies smoothness at the source generic point and constructs
the actual nonempty dense source smooth locus. Fibrewise density is separate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.RelativeGenericSmoothness

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
  (f : X ⟶ S) [IsDominant f]

/-- The actual generic-stalk map defines the relative function-field algebra. -/
abbrev functionFieldAlgebra : Algebra S.functionField X.functionField :=
  (NormalizationInExtension.functionFieldMap f).hom.toAlgebra

/-- Finite separable generation of the actual relative function-field extension. -/
def FunctionFieldSeparablyGenerated : Prop :=
  letI : Algebra S.functionField X.functionField := functionFieldAlgebra f
  ∃ s : Finset X.functionField,
    IsTranscendenceBasis S.functionField ((↑) : s → X.functionField) ∧
      Algebra.IsSeparable (IntermediateField.adjoin S.functionField (s : Set X.functionField))
        X.functionField

/-- A separating basis makes the actual relative function-field map formally smooth. -/
theorem formallySmooth_functionField (h : FunctionFieldSeparablyGenerated f) :
    (NormalizationInExtension.functionFieldMap f).hom.FormallySmooth := by
  let : Algebra S.functionField X.functionField := functionFieldAlgebra f
  obtain ⟨s, hs, hsep⟩ := h
  let : Algebra.IsSeparable
      (IntermediateField.adjoin S.functionField (Set.range ((↑) : s → X.functionField)))
      X.functionField := by
    convert! hsep <;> simp
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

/-- The source generic point lies in the actual relative smooth locus. -/
theorem genericPoint_mem_smoothLocus [LocallyOfFinitePresentation f]
    (h : FunctionFieldSeparablyGenerated f) : genericPoint X ∈ f.smoothLocus := by
  rw [Scheme.Hom.mem_smoothLocus]
  let e := S.presheaf.stalkCongr (.of_eq (genericPoint_map_of_isDominant f).symm)
  apply (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    e.hom (f.stalkMap (genericPoint X))).mp
  exact formallySmooth_functionField f h

/-- The actual smooth locus is dense in the integral source. -/
theorem dense_smoothLocus [LocallyOfFinitePresentation f]
    (h : FunctionFieldSeparablyGenerated f) : Dense (f.smoothLocus : Set X) :=
  f.smoothLocus.isOpen.dense ⟨genericPoint X, genericPoint_mem_smoothLocus f h⟩

/-- The original morphism is smooth on a constructed nonempty dense source open. -/
theorem exists_dense_smooth_open [LocallyOfFinitePresentation f]
    (h : FunctionFieldSeparablyGenerated f) :
    ∃ U : X.Opens, Nonempty U ∧ Dense (U : Set X) ∧ Smooth (U.ι ≫ f) :=
  ⟨f.smoothLocus, ⟨⟨genericPoint X, genericPoint_mem_smoothLocus f h⟩⟩,
    dense_smoothLocus f h, GenericSmoothness.smooth_smoothLocus f⟩

end DeJongAlterations.Geometry.RelativeGenericSmoothness
