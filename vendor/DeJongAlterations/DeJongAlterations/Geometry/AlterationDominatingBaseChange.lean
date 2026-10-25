import DeJongAlterations.Geometry.AlterationCommonRefinement

/-!
# Genuine dominating components of alteration base changes

An actual point over both generic points determines an actual native
irreducible component with its genuine reduced closed subscheme structure.
The alteration projection is produced without generic finiteness of the
original dominant morphism. The component and both projections are built
internally, not supplied by the caller.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace DeJongAlterations.Geometry.AlterationDominatingBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y S T : Scheme.{u}}

private theorem dominant_of_generic_mem_range
    (a : T ⟶ X) [IsIntegral X]
    (h : genericPoint X ∈ Set.range a) : IsDominant a := by
  refine ⟨?_⟩
  rw [denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← (genericPoint_spec X).def]
  exact closure_mono (Set.singleton_subset_iff.mpr h)

/-- The actual reduced component meeting both generic points, for any
two dominant morphisms of integral schemes. Its actual range is a native
irreducible component, and both actual projections are dominant. -/
theorem exists_dominating_reduced_component
    (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral X] [IsIntegral Y] [IsIntegral S]
    [IsDominant f] [IsDominant g] :
    ∃ (T : Scheme.{u}) (j : T ⟶ pullback f g),
      IsIntegral T ∧ IsClosedImmersion j ∧
      Set.range j ∈ irreducibleComponents (pullback f g : Scheme.{u}) ∧
      IsDominant (j ≫ pullback.fst f g) ∧ IsDominant (j ≫ pullback.snd f g) := by
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := g) (genericPoint X) (genericPoint Y)
    ((genericPoint_map_of_isDominant f).trans (genericPoint_map_of_isDominant g).symm)
  let C : Closeds (pullback f g : Scheme.{u}) :=
    ⟨irreducibleComponent z, isClosed_irreducibleComponent⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  let T := I.subscheme
  let j : T ⟶ pullback f g := I.subschemeι
  let : IsReduced T := ReducedClosedSubscheme.isReduced_vanishingIdeal_subscheme C
  let : IrreducibleSpace T :=
    Subtype.irreducibleSpace isIrreducible_irreducibleComponent
  let : IsIntegral T := isIntegral_of_irreducibleSpace_of_isReduced T
  let w : T := ⟨z, mem_irreducibleComponent⟩
  have ha : (j ≫ pullback.fst f g) w = genericPoint X := hz₁
  have hb : (j ≫ pullback.snd f g) w = genericPoint Y := hz₂
  have hj : Set.range j = irreducibleComponent z := by
    change Set.range I.subschemeι = _
    rw [I.range_subschemeι]
    rfl
  refine ⟨T, j, inferInstance, inferInstance, ?_,
    dominant_of_generic_mem_range _ ⟨w, ha⟩, dominant_of_generic_mem_range _ ⟨w, hb⟩⟩
  rw [hj]
  exact irreducibleComponent_mem_irreducibleComponents z

/-- The first projection of an actual dominating component is an alteration.
Only the opposite morphism is required to be an alteration. -/
theorem first_isAlteration
    (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral X] [hg : IsAlteration g]
    (j : T ⟶ pullback f g) [IsIntegral T] [IsClosedImmersion j]
    [IsDominant (j ≫ pullback.fst f g)] [IsDominant (j ≫ pullback.snd f g)] :
    IsAlteration (j ≫ pullback.fst f g) := by
  let := hg.sourceIntegral
  let := hg.targetIntegral
  have hx : g.QuasiFiniteAt ((j ≫ pullback.snd f g) (genericPoint T)) := by
    rw [genericPoint_map_of_isDominant (j ≫ pullback.snd f g)]
    exact hg.genericallyFinite.quasiFiniteAt_genericPoint g
  exact {
    sourceIntegral := inferInstance
    targetIntegral := inferInstance
    genericallyFinite := isGenericallyFinite_of_quasiFiniteAt_genericPoint _
      (AlterationCommonRefinement.quasiFiniteAt_fst f g j (genericPoint T) hx) }

/-- The actual asymmetric dominating base-change component, including the
alteration over the original source and the dominant map to the altered base. -/
theorem exists_alteration_component
    (f : X ⟶ S) (g : Y ⟶ S) [IsIntegral X] [IsDominant f] [hg : IsAlteration g] :
    ∃ (T : Scheme.{u}) (j : T ⟶ pullback f g),
      IsIntegral T ∧ IsClosedImmersion j ∧
      Set.range j ∈ irreducibleComponents (pullback f g : Scheme.{u}) ∧
      IsAlteration (j ≫ pullback.fst f g) ∧ IsDominant (j ≫ pullback.snd f g) := by
  let := hg.sourceIntegral
  let := hg.targetIntegral
  obtain ⟨T, j, hT, hj, hcomponent, hfirst, hsecond⟩ := exists_dominating_reduced_component f g
  let := hT
  let := hj
  let := hfirst
  let := hsecond
  exact ⟨T, j, hT, hj, hcomponent, first_isAlteration f g j, hsecond⟩

/-- The altered-base projection is genuinely proper when the original map is proper. -/
theorem second_isProper
    (f : X ⟶ S) (g : Y ⟶ S) [IsProper f]
    (j : T ⟶ pullback f g) [IsClosedImmersion j] :
    IsProper (j ≫ pullback.snd f g) := inferInstance

/-- Both actual component projections retain the original native Cartesian triangle. -/
@[reassoc]
theorem triangle (f : X ⟶ S) (g : Y ⟶ S) (j : T ⟶ pullback f g) :
    (j ≫ pullback.fst f g) ≫ f = (j ≫ pullback.snd f g) ≫ g := by
  rw [Category.assoc, pullback.condition, Category.assoc]

end DeJongAlterations.Geometry.AlterationDominatingBaseChange
