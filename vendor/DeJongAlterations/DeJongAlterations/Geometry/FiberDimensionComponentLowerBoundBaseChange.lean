import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundDescent

/-!
# Quasi-finite points descend through actual preimmersion base change

Actual residue-field maps are isomorphisms because the original stalk maps
are surjective. The native Cartesian fiber comparison is then an actual
fiber isomorphism, preserving its original isolated point and inclusion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundBaseChange

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual stalk surjections of a preimmersion give actual residue-field isomorphisms. -/
theorem residueFieldMap_isIso_of_preimmersion {Y' Y : Scheme.{u}}
    (i : Y' ⟶ Y) [IsPreimmersion i] (y : Y') : IsIso (i.residueFieldMap y) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨RingHom.injective _, ?_⟩
  intro a
  obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
  obtain ⟨c, hc⟩ := i.stalkMap_surjective y b
  refine ⟨IsLocalRing.residue _ c, ?_⟩
  change IsLocalRing.ResidueField.map (i.stalkMap y).hom (IsLocalRing.residue _ c) =
    IsLocalRing.residue _ b
  rw [IsLocalRing.ResidueField.map_residue]
  exact congrArg (IsLocalRing.residue _) hc

/-- Native quasi-finite points descend through the actual fiber isomorphisms of preimmersion base change. -/
theorem quasiFiniteAt_of_isPullback_of_preimmersion
    {X' Y' X Y : Scheme.{u}} {iX : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {iY : Y' ⟶ Y}
    (h : IsPullback iX f' f iY) [IsPreimmersion iY]
    [LocallyOfFiniteType f] [LocallyOfFiniteType f'] (x : X') (hq : f'.QuasiFiniteAt x) :
    f.QuasiFiniteAt (iX x) := by
  let y := f' x
  let ψ : f'.fiber y ⟶ f.fiber (iY y) :=
    pullback.map _ _ _ _ iX (Spec.map (iY.residueFieldMap y)) iY h.w.symm (by simp)
  have hψ : IsPullback ψ (f'.fiberToSpecResidueField y)
      (f.fiberToSpecResidueField (iY y)) (Spec.map (iY.residueFieldMap y)) :=
    isPullback_fiberToSpecResidueField_of_isPullback h y
  let : IsIso (iY.residueFieldMap y) := residueFieldMap_isIso_of_preimmersion iY y
  let : IsIso ψ := hψ.isIso_fst_of_isIso
  have hι : ψ ≫ f.fiberι (iY y) = f'.fiberι y ≫ iX := by
    dsimp only [ψ, Scheme.Hom.fiber, Scheme.Hom.fiberι, pullback.map]
    simp only [pullback.lift_fst]
  have hpoint : f.fiberι (iY y) (ψ (f'.asFiber x)) = iX x := by
    rw [← Scheme.Hom.comp_apply, hι, Scheme.Hom.comp_apply]
    exact congrArg iX (f'.fiberι_asFiber x)
  have hopen := ψ.isOpenEmbedding.isOpenMap _
    (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hq)
  have hsingle : IsOpen ({ψ (f'.asFiber x)} : Set (f.fiber (iY y))) := by
    simpa only [Set.image_singleton] using hopen
  have hqfull := FiberDimensionCurveComponents.quasiFiniteAt_of_isOpen_singleton_fiber
    f (iY y) (ψ (f'.asFiber x)) hsingle
  simpa only [hpoint] using hqfull

end DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundBaseChange
