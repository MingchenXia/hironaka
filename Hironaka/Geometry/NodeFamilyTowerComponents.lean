import Hironaka.Geometry.NodeFamilyTowerDimension
import Hironaka.Geometry.FiberDimensionCurveComponents

/-! Pure dimension one of every actual fibre of the global finite node tower. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.NodeFamilyTowerComponents

open NodeFamilyTower NodeFamilyTowerDimension NodeFamilyFlat
open MonomialBlowupTower MonomialBlowupTowerRegular
open FiberDimension FiberDimensionCurveComponents

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] [IsDomain A]

/-- Actual dimension-one fibres force surjectivity of the original family morphism. -/
theorem prefix_family_surjective (l : List A) (hl : (0 : A) ∉ l)
    (a b : List A) (hab : l = a ++ b) : Surjective (familyMorphism l a.length) := by
  constructor
  intro p
  apply (fiberDimension_nonneg_iff_mem_range (familyMorphism l a.length) p).mp
  rw [prefix_fiber_dimension l hl a b hab p]
  exact zero_le_one

variable [IsNoetherianRing A]

/-- Every actual irreducible component of every actual processed-stage fibre has dimension one. -/
theorem prefix_fiber_component_dimension (l : List A) (hl : (0 : A) ∉ l)
    (a b : List A) (hab : l = a ++ b) (p : PrimeSpectrum A)
    (Z : Set ((familyMorphism l a.length).fiber p))
    (hZ : Z ∈ irreducibleComponents ((familyMorphism l a.length).fiber p)) :
    topologicalKrullDim Z = 1 := by
  let : IsIntegral (tower l a.length).left := (tower_isAlteration l hl a.length).sourceIntegral
  let : LocallyOfFinitePresentation (familyMorphism l a.length) :=
    (prefix_family_properties l hl a b hab).2.1
  let : QuasiCompact (familyMorphism l a.length) := familyMorphism_quasiCompact l hl a.length
  let : Surjective (familyMorphism l a.length) := prefix_family_surjective l hl a b hab
  apply le_antisymm
  · exact (topologicalKrullDim_subspace_le _ Z).trans
      (prefix_fiber_dimension l hl a b hab p).le
  · apply one_le_fiberComponentDimension_of_one_le_genericFiberDimension
      (familyMorphism l a.length) _ p Z hZ
    exact (prefix_fiber_dimension l hl a b hab (genericPoint (Spec (CommRingCat.of A)))).ge

/-- Every actual component of every final-stage fibre has dimension exactly one. -/
theorem final_fiber_component_dimension (l : List A) (hl : (0 : A) ∉ l)
    (p : PrimeSpectrum A) (Z : Set ((resolutionMorphism l ≫ nodeMorphism l.prod).fiber p))
    (hZ : Z ∈ irreducibleComponents ((resolutionMorphism l ≫ nodeMorphism l.prod).fiber p)) :
    topologicalKrullDim Z = 1 :=
  prefix_fiber_component_dimension l hl l [] (by simp) p Z hZ

end Hironaka.Geometry.NodeFamilyTowerComponents
