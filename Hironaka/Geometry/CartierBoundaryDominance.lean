import Hironaka.Geometry.CartierBoundaryComponentDimension
import Hironaka.Geometry.FiniteVarietyDominance
import Hironaka.Geometry.VarietyFunctionFieldDimension

/-!
# Actual nonflat Cartier boundary components dominate the curve base

The original Cartier boundary and its whole reduced-support finite map
internally imply dominance of every genuine support component. Neither
flatness nor desired component dominance is a hypothesis.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.CartierBoundaryDominance

open Scheme.IdealSheafData CartierBoundaryComponentDimension SNCSubdivisorComponent

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X S : Scheme.{u}}

/-- The literal whole reduced boundary, with the original actual support. -/
def reducedBoundary (D : X.IdealSheafData) : Scheme.{u} := (vanishingIdeal D.support).subscheme

/-- The original closed immersion of the whole reduced boundary. -/
def reducedBoundaryInclusion (D : X.IdealSheafData) : reducedBoundary D ⟶ X :=
  (vanishingIdeal D.support).subschemeι

instance reducedBoundaryInclusion_isClosedImmersion (D : X.IdealSheafData) :
    IsClosedImmersion (reducedBoundaryInclusion D) := by
  delta reducedBoundaryInclusion
  infer_instance

/-- The genuine native inclusion of each reduced component in the whole reduced boundary. -/
def componentBoundaryInclusion (D : X.IdealSheafData) (C : DivisorComponent D) :
    componentScheme D C ⟶ reducedBoundary D :=
  Scheme.IdealSheafData.inclusion (vanishingIdeal_antimono (component_le_support D C))

@[reassoc (attr := simp)]
theorem componentBoundaryInclusion_structure (D : X.IdealSheafData) (C : DivisorComponent D) :
    componentBoundaryInclusion D C ≫ reducedBoundaryInclusion D = componentInclusion D C :=
  Scheme.IdealSheafData.inclusion_subschemeι _

instance componentBoundaryInclusion_isClosedImmersion (D : X.IdealSheafData)
    (C : DivisorComponent D) : IsClosedImmersion (componentBoundaryInclusion D C) := by
  let : IsClosedImmersion (componentBoundaryInclusion D C ≫ reducedBoundaryInclusion D) := by
    rw [componentBoundaryInclusion_structure]
    infer_instance
  exact IsClosedImmersion.of_comp (componentBoundaryInclusion D C) (reducedBoundaryInclusion D)

/-- Finiteness is derived from the original whole boundary map, not assumed for components. -/
instance component_isFinite (f : X ⟶ S) (D : X.IdealSheafData)
    [IsFinite (reducedBoundaryInclusion D ≫ f)] (C : DivisorComponent D) :
    IsFinite (componentInclusion D C ≫ f) := by
  rw [← componentBoundaryInclusion_structure D C, Category.assoc]
  infer_instance

variable {k : Type u} [Field k]

/-- The original Cartier ideal and ambient dimension relation internally force component dominance. -/
theorem component_isDominant_of_dimension
    (p : S ⟶ Spec (.of k)) [IsVariety p] (f : X ⟶ S) [IsVariety (f ≫ p)]
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    [IsFinite (reducedBoundaryInclusion D ≫ f)]
    (hdim : topologicalKrullDim X = topologicalKrullDim S + 1) (C : DivisorComponent D) :
    IsDominant (componentInclusion D C ≫ f) := by
  apply FiniteVarietyDominance.isDominant_of_dimension_le p
  let pC := (componentInclusion D C ≫ f) ≫ p
  let : IsVariety pC := by
    change IsVariety (componentInclusion D C ≫ (f ≫ p))
    exact .mk
  obtain ⟨d, hd, _⟩ := FunctionFieldDimension.exists_dimension_and_trdeg p
  obtain ⟨e, he, _⟩ := FunctionFieldDimension.exists_dimension_and_trdeg pC
  have hC := (component_dimension_add_one (f ≫ p) D hD C).trans hdim
  rw [hd, he] at hC
  have hnat : e + 1 = d + 1 := by exact_mod_cast hC
  have hed : e = d := Nat.add_right_cancel hnat
  rw [hd, he, hed]

/-- The natural actual generic-curve hypothesis gives nonflat boundary-component dominance. -/
theorem component_isDominant
    (p : S ⟶ Spec (.of k)) [IsVariety p] (f : X ⟶ S) [IsVariety (f ≫ p)] [IsDominant f]
    (hgen : topologicalKrullDim (f.fiber (genericPoint S)) = 1)
    (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D)
    [IsFinite (reducedBoundaryInclusion D ≫ f)] (C : DivisorComponent D) :
    IsDominant (componentInclusion D C ≫ f) := by
  let : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f p
  exact component_isDominant_of_dimension p f D hD
    (VarietyFunctionFieldDimension.dimension_eq_base_add_one p f hgen) C

end Hironaka.Geometry.CartierBoundaryDominance
