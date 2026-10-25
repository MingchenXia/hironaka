import DeJongAlterations.Geometry.FiberDimensionGenericFinite

/-!
# Actual fiber invariance under restriction of the target

The native fiber comparison of the actual restriction pullback is a
pullback over an actual residue-field isomorphism. It constructs an
isomorphism of the original scheme-theoretic fibers, preserving dimension.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace DeJongAlterations.Geometry.FiberDimensionGenericRestriction

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (s : U)

/-- The actual fiber map from the original restriction to the original scheme fiber. -/
def restrictionFiberMap : (f ∣_ U).fiber s ⟶ f.fiber (U.ι s) :=
  pullback.map _ _ _ _ (f ⁻¹ᵁ U).ι (Spec.map (U.ι.residueFieldMap s)) U.ι
    (morphismRestrict_ι f U) (U.ι.SpecMap_residueFieldMap_fromSpecResidueField s).symm

/-- The actual fiber comparison square is Cartesian over the actual residue-field map. -/
theorem restrictionFiberMap_isPullback :
    IsPullback (restrictionFiberMap f U s) ((f ∣_ U).fiberToSpecResidueField s)
      (f.fiberToSpecResidueField (U.ι s)) (Spec.map (U.ι.residueFieldMap s)) :=
  isPullback_fiberToSpecResidueField_of_isPullback (isPullback_morphismRestrict f U).flip s

/-- The open target immersion gives a residue-field isomorphism, hence an actual fiber isomorphism. -/
instance restrictionFiberMap_isIso : IsIso (restrictionFiberMap f U s) :=
  (restrictionFiberMap_isPullback f U s).isIso_fst_of_isIso

/-- The native fiber isomorphism uses the actual restriction comparison morphism. -/
def restrictionFiberIso : (f ∣_ U).fiber s ≅ f.fiber (U.ι s) :=
  asIso (restrictionFiberMap f U s)

/-- The actual original fiber dimension is unchanged by restricting its target to an open neighborhood. -/
theorem fiberDimension_morphismRestrict :
    FiberDimension.fiberDimension (f ∣_ U) s = FiberDimension.fiberDimension f (U.ι s) :=
  IsHomeomorph.topologicalKrullDim_eq _ (restrictionFiberIso f U s).hom.homeomorph.isHomeomorph

end DeJongAlterations.Geometry.FiberDimensionGenericRestriction
