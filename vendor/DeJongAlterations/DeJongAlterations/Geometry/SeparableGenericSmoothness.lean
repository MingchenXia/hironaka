import DeJongAlterations.Geometry.GenericSmoothness
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.Smooth.Field

/-!
# Generic smoothness for a separably generated function field

The base-field algebra structure on the function field is defined from the specified
structure morphism, through its actual generic-point stalk map. A separating transcendence
basis for this extension produces a nonempty dense source open on which that morphism is
smooth, over an arbitrary field.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.SeparableGenericSmoothness

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]

/-- The canonical field extension induced by the actual generic-point stalk map of `p`. -/
abbrev functionFieldAlgebra (p : X ⟶ Spec (CommRingCat.of k)) : Algebra k X.functionField :=
  ((p.stalkMap (genericPoint X)).hom.comp
    (algebraMap k ((Spec.structureSheaf k).presheaf.stalk (p (genericPoint X))))).toAlgebra

/-- The scalar map is exactly the structural stalk map composed with the base localization. -/
theorem functionFieldAlgebra_algebraMap (p : X ⟶ Spec (CommRingCat.of k)) :
    @algebraMap k X.functionField _ _ (functionFieldAlgebra p) =
      (p.stalkMap (genericPoint X)).hom.comp
        (algebraMap k ((Spec.structureSheaf k).presheaf.stalk (p (genericPoint X)))) := rfl

/-- A separating transcendence basis for the canonical extension, with no caller algebra choice. -/
def FunctionFieldSeparablyGenerated (p : X ⟶ Spec (CommRingCat.of k)) : Prop :=
  letI : Algebra k X.functionField := functionFieldAlgebra p
  ∃ s : Finset X.functionField,
    IsTranscendenceBasis k ((↑) : s → X.functionField) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set X.functionField)) X.functionField

/-- The canonical function-field extension is formally smooth when separably generated. -/
theorem formallySmooth_functionField (p : X ⟶ Spec (CommRingCat.of k))
    (h : FunctionFieldSeparablyGenerated p) :
    @Algebra.FormallySmooth k X.functionField _ _ (functionFieldAlgebra p) := by
  let : Algebra k X.functionField := functionFieldAlgebra p
  obtain ⟨s, hs, hsep⟩ := h
  let : Algebra.IsSeparable
      (IntermediateField.adjoin k (Set.range ((↑) : s → X.functionField))) X.functionField := by
    convert! hsep <;> simp
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

/-- The canonical localization of the base field at the image of the generic point is an iso. -/
def baseStalkAlgEquiv (p : X ⟶ Spec (CommRingCat.of k)) :
    k ≃ₐ[k] ((Spec.structureSheaf k).presheaf.stalk (p (genericPoint X))) :=
  IsLocalization.atUnits _ (p (genericPoint X)).asIdeal.primeCompl
    (fun x hx => by aesop (add simp IsUnit.mem_submonoid_iff))

/-- Separable generation of the actual function field puts the generic point in the smooth locus. -/
theorem genericPoint_mem_smoothLocus (p : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFinitePresentation p] (h : FunctionFieldSeparablyGenerated p) :
    genericPoint X ∈ p.smoothLocus := by
  rw [Scheme.Hom.mem_smoothLocus]
  let e := baseStalkAlgEquiv p
  have he : e.toRingHom =
      algebraMap k ((Spec.structureSheaf k).presheaf.stalk (p (genericPoint X))) := by
    ext x
    exact e.commutes x
  apply (RingHom.FormallySmooth.respectsIso.cancel_left_isIso
    e.toRingEquiv.toCommRingCatIso.hom (p.stalkMap (genericPoint X))).mp
  change ((p.stalkMap (genericPoint X)).hom.comp e.toRingHom).FormallySmooth
  rw [he]
  exact formallySmooth_functionField p h

/-- The actual smooth locus is dense under separable generation of the canonical function field. -/
theorem dense_smoothLocus (p : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFinitePresentation p] (h : FunctionFieldSeparablyGenerated p) :
    Dense (p.smoothLocus : Set X) :=
  p.smoothLocus.isOpen.dense ⟨genericPoint X, genericPoint_mem_smoothLocus p h⟩

/-- The arbitrary-field generic-smoothness assertion, with an actual nonempty dense source open. -/
theorem exists_dense_smooth_open (p : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] (h : FunctionFieldSeparablyGenerated p) :
    ∃ U : X.Opens, Nonempty U ∧ Dense (U : Set X) ∧ Smooth (U.ι ≫ p) := by
  exact ⟨p.smoothLocus, ⟨⟨genericPoint X, genericPoint_mem_smoothLocus p h⟩⟩,
    dense_smoothLocus p h, GenericSmoothness.smooth_smoothLocus p⟩

end DeJongAlterations.Geometry.SeparableGenericSmoothness
