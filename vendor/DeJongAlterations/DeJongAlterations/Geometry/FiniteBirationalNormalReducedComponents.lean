import DeJongAlterations.Geometry.AlterationDominatingBaseChangeComponentEtale
import DeJongAlterations.Geometry.ReducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# The intrinsic reduced components of a finite flat boundary

All components are the actual native irreducible components, endowed
with their genuine vanishing-ideal closed subscheme structures. Only
the whole boundary morphism is assumed flat.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.FiniteBirationalNormal

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {S Z : Scheme.{u}}

/-- The genuine reduced closed subscheme of a native irreducible component. -/
def reducedComponent (Z : Scheme.{u}) (C : irreducibleComponents Z) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val, isClosed_of_mem_irreducibleComponents _ C.property⟩ : Closeds Z)).subscheme

/-- The original closed immersion of the actual reduced component. -/
def reducedComponentInclusion (Z : Scheme.{u}) (C : irreducibleComponents Z) :
    reducedComponent Z C ⟶ Z :=
  (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val, isClosed_of_mem_irreducibleComponents _ C.property⟩ : Closeds Z)).subschemeι

instance reducedComponent_isIntegral (C : irreducibleComponents Z) :
    IsIntegral (reducedComponent Z C) := by
  let : IsReduced (reducedComponent Z C) :=
    ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme _
  let : IrreducibleSpace (reducedComponent Z C) := Subtype.irreducibleSpace C.property.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

instance reducedComponentInclusion_isClosedImmersion (C : irreducibleComponents Z) :
    IsClosedImmersion (reducedComponentInclusion Z C) := by
  delta reducedComponentInclusion
  infer_instance

/-- The component map has exactly its original native component as image. -/
theorem reducedComponentInclusion_range (C : irreducibleComponents Z) :
    Set.range (reducedComponentInclusion Z C) = C.val := by
  change Set.range (Scheme.IdealSheafData.vanishingIdeal
    (⟨C.val, isClosed_of_mem_irreducibleComponents _ C.property⟩ : Closeds Z)).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- Every point belongs to an actual intrinsic reduced component. -/
theorem reducedComponents_cover :
    ⋃ C : irreducibleComponents Z, Set.range (reducedComponentInclusion Z C) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  refine Set.mem_iUnion.mpr ⟨⟨irreducibleComponent z,
    irreducibleComponent_mem_irreducibleComponents z⟩, ?_⟩
  rw [reducedComponentInclusion_range]
  exact mem_irreducibleComponent

/-- A component of a flat morphism to an integral scheme dominates the target. -/
instance reducedComponent_dominant (f : Z ⟶ S) [Flat f] [IsIntegral S]
    (C : irreducibleComponents Z) : IsDominant (reducedComponentInclusion Z C ≫ f) := by
  let x := (genericPoints.ofComponent C).val
  have hx : IsGenericPoint x C.val := genericPoints.isGenericPoint_ofComponent C
  obtain ⟨z, hzx, hz⟩ := Flat.generalizingMap f (genericPoint_specializes (f x))
  have hCz : C.val ⊆ closure ({z} : Set Z) := by
    rw [← hx.def]
    exact (specializes_iff_closure_subset.mp hzx)
  have hzC : z ∈ C.val :=
    C.property.2 isIrreducible_singleton.closure hCz (subset_closure (Set.mem_singleton z))
  rw [← reducedComponentInclusion_range C] at hzC
  obtain ⟨w, hw⟩ := hzC
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← genericPoint_closure S]
  apply closure_mono
  exact Set.singleton_subset_iff.mpr ⟨w, by
    change f (reducedComponentInclusion Z C w) = _
    rw [hw]
    exact hz⟩

/-- Reduced Noetherian components retain the genuine generic etaleness of the boundary map. -/
theorem reducedComponent_genericallyEtale (f : Z ⟶ S)
    [IsReduced Z] [AlgebraicGeometry.IsNoetherian Z]
    (hf : IsGenericallyEtale f) (C : irreducibleComponents Z) :
    IsGenericallyEtale (reducedComponentInclusion Z C ≫ f) := by
  apply IsGenericallyEtale.comp _ hf
  apply AlterationDominatingBaseChange.genericallyEtale_component
  rw [reducedComponentInclusion_range]
  exact C.property

end DeJongAlterations.Geometry.FiniteBirationalNormal
