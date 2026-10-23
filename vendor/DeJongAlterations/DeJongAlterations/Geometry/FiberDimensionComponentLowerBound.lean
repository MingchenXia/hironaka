import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundLocality

/-!
# Every actual fiber component has at least the actual generic fiber dimension

The full source 2.7(c) inequality follows from the internally constructed
quasi-finite coordinate projection, actual generic tensor dimension, and
native affine source and target neighborhoods. All dimensions concern the
literal original scheme-theoretic fibers and all of their components.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.FiberDimensionComponentLowerBound

open FiberDimension FiberDimensionGenericRestriction FiberDimensionComponentLowerBoundLocality

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Source 2.7(c) in every relative dimension: every component of every actual
fiber of a dominant locally finite-type morphism of integral schemes has at
least the actual generic fiber dimension. All affine neighborhoods and
quasi-finite projections are internally constructed. -/
theorem everyFiberComponentDimensionGEGeneric
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    EveryFiberComponentDimensionGEGeneric f := by
  intro s Z hZ
  obtain ⟨U, hU, hsU, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := s) (U := (⊤ : Y.Opens)) (by trivial)
  let : Nonempty U.toScheme := ⟨⟨s, hsU⟩⟩
  let : IsAffine U.toScheme := hU
  let : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have hηU : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr ⟨s, Set.mem_univ _, hsU⟩
  let : Nonempty (f ⁻¹ᵁ U).toScheme := ⟨⟨genericPoint X, by
    change f (genericPoint X) ∈ U
    rw [genericPoint_map_of_isDominant f]
    exact hηU⟩⟩
  let : IsIntegral (f ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  let : IsDominant (f ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (inferInstance : IsDominant f) U
  have hbound := everyFiberComponentDimensionGEGeneric_of_isAffine_target (f ∣_ U)
  have hgen := fiberDimension_morphismRestrict f U (genericPoint U.toScheme)
  rw [genericPoint_eq_of_isOpenImmersion U.ι] at hgen
  rw [← hgen]
  let t : U.toScheme := ⟨s, hsU⟩
  exact componentDimension_lowerBound_of_homeomorph
    (restrictionFiberIso f U t).hom.homeomorph _ (hbound t) Z hZ

end DeJongAlterations.Geometry.FiberDimensionComponentLowerBound
