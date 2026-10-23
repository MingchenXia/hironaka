import DeJongAlterations.Geometry.AffineBlowupModification
import DeJongAlterations.Geometry.AffineBlowupAlteration
import Mathlib.AlgebraicGeometry.Birational.Birational

/-!
# Native birationality of affine blowups

The actual open restriction gives a Mathlib partial isomorphism over the
original base. Thus a nonzero finitely generated ideal in a domain yields
a proper birational modification in de Jong's sense, using intrinsic
scheme birationality rather than a separate certificate predicate.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

namespace DeJongAlterations

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A dominant map of integral schemes which is an isomorphism over a nonempty
open is birational over its target, via its actual restricted morphism. -/
theorem birationalOver_id_of_isIso_morphismRestrict {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (U : Y.Opens) (hU : (U : Set Y).Nonempty) [IsIso (f ∣_ U)] :
    Scheme.BirationalOver f (𝟙 Y) := by
  have hηY : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using hU)
  have hηX : genericPoint X ∈ f ⁻¹ᵁ U := by
    change f (genericPoint X) ∈ U
    rw [genericPoint_map_of_isDominant f]
    exact hηY
  let e : X.PartialIso Y := {
    source := f ⁻¹ᵁ U
    dense_source := (f ⁻¹ᵁ U).isOpen.dense ⟨genericPoint X, hηX⟩
    target := U
    dense_target := U.isOpen.dense hU
    iso := asIso (f ∣_ U) }
  refine ⟨e, ?_⟩
  change (f ∣_ U) ≫ U.ι ≫ 𝟙 Y = (f ⁻¹ᵁ U).ι ≫ f
  rw [Category.comp_id, morphismRestrict_ι]

variable {R : Type u} [CommRing R] [IsDomain R]

/-- The actual native blowup map of a nonzero ideal is birational over its base.
No finite-generation hypothesis is needed for this partial isomorphism. -/
theorem affineBlowupStructure_birationalOver (I : Ideal R) (hI : I ≠ ⊥) :
    Scheme.BirationalOver (affineBlowupStructure I) (𝟙 (Spec (CommRingCat.of R))) := by
  let : IsIntegral (affineBlowup I) := Geometry.ProjIntegral.isIntegral_affineBlowup I hI
  let : IsDominant (affineBlowupStructure I) := affineBlowupStructure_isDominant I hI
  let := affineBlowupStructure_centerComplement_isIso I
  exact birationalOver_id_of_isIso_morphismRestrict _ (affineBlowupCenterComplement I)
    (affineBlowupCenterComplement_nonempty I hI)

/-- A genuine affine blowup in a nonzero finitely generated ideal is a proper
birational modification over its original spectrum. -/
theorem affineBlowupStructure_proper_birational (I : Ideal R) (hI : I ≠ ⊥) (hfg : I.FG) :
    IsProper (affineBlowupStructure I) ∧
      Scheme.BirationalOver (affineBlowupStructure I) (𝟙 (Spec (CommRingCat.of R))) :=
  ⟨affineBlowupStructure_isProper I hfg, affineBlowupStructure_birationalOver I hI⟩

end DeJongAlterations
