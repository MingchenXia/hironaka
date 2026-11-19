import Hironaka.Resolution.Algebraic.ActualGlobalSeparationSmoothNaturality

/-!
# Genuine smooth functoriality of the actual global original separation step

Source-first proof: `actual-global-separation-blowup-functoriality-20261102.tex`.
Actual intrinsic centre naturality constructs a real smooth cartesian map;
genuine original blowup universality proves its identity/composition laws.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.IdealSheafData
universe u

namespace Hironaka.Resolution.Algebraic.ActualGlobalSeparationBlowupFunctoriality

noncomputable section
open ActualGlobalDimensionSeparationIdeal ActualGlobalDimensionClopenPartition
  ActualGlobalSeparationSmoothNaturality

private theorem idealEq_isPullback {A B : Scheme.{u}} (f : A ⟶ B) [Flat f]
    (I : B.IdealSheafData) (J : A.IdealSheafData) (h : I.comap f = J) :
    IsPullback (eqToHom (congrArg Scheme.IdealSheafData.blowUp h.symm) ≫ Scheme.Hom.blowUpMap f I)
      J.blowUpπ I.blowUpπ f := by
  subst J
  simpa only [eqToHom_refl, Category.id_comp] using isPullback_blowUpMap f I

variable {X Y : Scheme.{u}} [IsNoetherian X] [IsReduced X] [IsNoetherian Y] [IsReduced Y]
    {k : Type u} [Field k] [CharZero k] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (f : Y ⟶ X) [Smooth f]

def separationMap : separationSpace Y ⟶ separationSpace X :=
  eqToHom (congrArg Scheme.IdealSheafData.blowUp (separationIdeal_smooth p f).symm) ≫
    Scheme.Hom.blowUpMap f (separationIdeal X)

theorem separationMap_isPullback : IsPullback (separationMap p f) (separationProjection Y)
    (separationProjection X) f := idealEq_isPullback f _ _ (separationIdeal_smooth p f)

theorem separationMap_over : separationMap p f ≫ separationProjection X = separationProjection Y ≫ f :=
  (separationMap_isPullback p f).w

theorem separationMap_smooth : Smooth (separationMap p f) :=
  property_of_isPullback _ (separationMap_isPullback p f) (inferInstance : Smooth f)

theorem separationMap_surjective [Surjective f] : Surjective (separationMap p f) :=
  property_of_isPullback _ (separationMap_isPullback p f) (inferInstance : Surjective f)

theorem separationMap_id : separationMap p (𝟙 X) = 𝟙 (separationSpace X) := by
  apply (blowUp.isBlowUp (separationIdeal X)).hom_ext (separationProjection X)
    (blowUp.isBlowUp (separationIdeal X)).admissible
  · simpa only [Category.comp_id] using separationMap_over p (𝟙 X)
  · exact Category.id_comp _

theorem separationMap_comp {Z : Scheme.{u}} [IsNoetherian Z] [IsReduced Z]
    (g : Z ⟶ Y) [Smooth g] :
    separationMap (f ≫ p) g ≫ separationMap p f = separationMap p (g ≫ f) := by
  have hI : ((separationIdeal X).comap (separationProjection Z ≫ g ≫ f)).IsInvertible := by
    rw [comap_comp, separationIdeal_smooth p (g ≫ f)]
    exact (blowUp.isBlowUp (separationIdeal Z)).admissible
  apply (blowUp.isBlowUp (separationIdeal X)).hom_ext (separationProjection Z ≫ g ≫ f) hI
  · rw [Category.assoc, separationMap_over, ← Category.assoc, separationMap_over, Category.assoc]
  · exact separationMap_over p (g ≫ f)

end
end Hironaka.Resolution.Algebraic.ActualGlobalSeparationBlowupFunctoriality
