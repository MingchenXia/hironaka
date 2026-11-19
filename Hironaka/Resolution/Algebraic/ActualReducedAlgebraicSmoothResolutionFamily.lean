import Hironaka.Resolution.Algebraic.ActualGlobalStrongResolutionSmoothNaturality

/-!
# One actual smooth-compatible strong family on ALL reduced algebraic schemes

Source-first proof: `actual-reduced-algebraic-smooth-resolution-family-20261102.tex`.
The actual full original category has no affine/equidimensional restriction.
This packages the SAME proved construction; field compatibility stays open.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
universe u

namespace Hironaka.Resolution.Algebraic.ActualReducedAlgebraicSmoothResolutionFamily

noncomputable section
open ActualGlobalStrongResolutionSmoothNaturality

abbrev ReducedAlgebraicScheme (k : Type u) [Field k] : Type (u + 1) :=
  ObjectProperty.FullSubcategory fun X : AlgScheme k => IsReduced X.left

instance hasUnderlyingScheme (k : Type u) [Field k] : HasUnderlyingScheme (ReducedAlgebraicScheme k) k where
  forget := ObjectProperty.ι _

private instance input_reduced {k : Type u} [Field k] (X : ReducedAlgebraicScheme k) : IsReduced X.obj.left :=
  X.property

private instance input_finiteType {k : Type u} [Field k] (X : ReducedAlgebraicScheme k) : FiniteType X.obj.hom :=
  X.obj.prop.1

private instance input_separated {k : Type u} [Field k] (X : ReducedAlgebraicScheme k) : IsSeparated X.obj.hom :=
  X.obj.prop.2

private instance input_noetherian {k : Type u} [Field k] (X : ReducedAlgebraicScheme k) : IsNoetherian X.obj.left :=
  X.obj.hom.isNoetherian_of_field

def resolutionFamily : ∀ (k : Type u) [Field k] [CharZero k], BlowUpSequenceFunctor (ReducedAlgebraicScheme k) :=
  fun _ _ _ X => resolutionHistory (X := X.obj.left) X.obj.hom

theorem resolutionFamily_isStrongResolution (k : Type u) [Field k] [CharZero k] (X : ReducedAlgebraicScheme k) :
    @Scheme.BlowUpSequence.IsStrongResolution k _ X.obj (resolutionFamily k X) := by
  exact resolutionHistory_isStrongResolution (X := X.obj.left) X.obj.hom

private theorem resolutionHistory_congr {Z : Scheme.{u}} [IsNoetherian Z] [IsReduced Z]
    {k : Type u} [Field k] [CharZero k] {q q' : Z ⟶ Spec (.of k)}
    [LocallyOfFiniteType q] [IsSeparated q] [LocallyOfFiniteType q'] [IsSeparated q'] (h : q = q') :
    resolutionHistory q = resolutionHistory q' := by
  subst q'
  rfl

theorem resolutionFamily_commutesWithSmoothMorphisms (k : Type u) [Field k] [CharZero k] :
    CommutesWithSmoothMorphisms (resolutionFamily k) := by
  constructor
  · intro X Y h hs hsurj
    have : Smooth h.hom.left := hs
    have : Surjective h.hom.left := ⟨hsurj⟩
    have hfield : h.hom.left ≫ X.obj.hom = Y.obj.hom := h.hom.w
    have : IsSeparated (h.hom.left ≫ X.obj.hom) := by rw [hfield]; infer_instance
    have he := resolutionHistory_smooth_surjective (X := X.obj.left) (Y := Y.obj.left) X.obj.hom h.hom.left
    exact (resolutionHistory_congr hfield).symm.trans he
  · intro X Y h hs
    have : Smooth h.hom.left := hs
    have hfield : h.hom.left ≫ X.obj.hom = Y.obj.hom := h.hom.w
    have : IsSeparated (h.hom.left ≫ X.obj.hom) := by rw [hfield]; infer_instance
    have he := resolutionHistory_smooth (X := X.obj.left) (Y := Y.obj.left) X.obj.hom h.hom.left
    exact (resolutionHistory_congr hfield).symm.trans he

theorem exists_functorial_strong_resolution_smooth :
    ∃ F : ∀ (k : Type u) [Field k] [CharZero k], BlowUpSequenceFunctor (ReducedAlgebraicScheme k),
      (∀ (k : Type u) [Field k] [CharZero k] (X : ReducedAlgebraicScheme k),
        @Scheme.BlowUpSequence.IsStrongResolution k _ X.obj (F k X)) ∧
      (∀ (k : Type u) [Field k] [CharZero k], CommutesWithSmoothMorphisms (F k)) :=
  ⟨resolutionFamily, resolutionFamily_isStrongResolution, resolutionFamily_commutesWithSmoothMorphisms⟩

end
end Hironaka.Resolution.Algebraic.ActualReducedAlgebraicSmoothResolutionFamily
