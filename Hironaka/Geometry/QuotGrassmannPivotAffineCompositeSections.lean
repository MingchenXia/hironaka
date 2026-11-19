import Hironaka.Geometry.QuotGrassmannPivotAffinePullbackSections

/-!
# SAME native module sections under actual original affine composition

The actual affine section base-change isomorphism is followed by SAME native
pullback-composition isomorphism. Its whole original-map naturality is literal
native naturality of the internally constructed composite transformation.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Genuine native affine-section comparison under original scheme-map composition, for ALL original module sheaves. -/
def originalCompositeSpecPullbackSectionsNatTrans {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {X : Scheme.{u}} (f : Spec A ⟶ X) :
    (pullback f ⋙ moduleSpecΓFunctor) ⋙ ModuleCat.extendScalars φ.hom ⟶
      pullback (Spec.map φ ≫ f) ⋙ moduleSpecΓFunctor :=
  Functor.whiskerLeft (pullback f) (originalSpecPullbackSectionsNatTrans φ) ≫
    Functor.whiskerRight (pullbackComp (Spec.map φ) f).hom moduleSpecΓFunctor

/-- Actual native affine-section base change has the SAME actual native composed-pullback target. -/
def originalCompositeSpecPullbackSectionsIso {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {X : Scheme.{u}} (f : Spec A ⟶ X) (M : X.Modules)
    [((pullback f).obj M).IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj ((pullback f).obj M)) ≅
      moduleSpecΓFunctor.obj ((pullback (Spec.map φ ≫ f)).obj M) :=
  originalSpecPullbackSectionsIso φ ((pullback f).obj M) ≪≫
    moduleSpecΓFunctor.mapIso ((pullbackComp (Spec.map φ) f).app M)

/-- The actual whole composite-section isomorphism is the SAME internally produced natural comparison. -/
theorem originalCompositeSpecPullbackSectionsIso_hom {A B : CommRingCat.{u}} (φ : A ⟶ B)
    {X : Scheme.{u}} (f : Spec A ⟶ X) (M : X.Modules)
    [((pullback f).obj M).IsQuasicoherent] :
    (originalCompositeSpecPullbackSectionsIso φ f M).hom =
      (originalCompositeSpecPullbackSectionsNatTrans φ f).app M := rfl

/-- EVERY original whole module map satisfies actual native section scalar-extension/composite-pullback naturality. -/
theorem originalCompositeSpecPullbackSectionsIso_naturality {A B : CommRingCat.{u}}
    (φ : A ⟶ B) {X : Scheme.{u}} (f : Spec A ⟶ X) {M N : X.Modules}
    [((pullback f).obj M).IsQuasicoherent] [((pullback f).obj N).IsQuasicoherent] (q : M ⟶ N) :
    (ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map ((pullback f).map q)) ≫
        (originalCompositeSpecPullbackSectionsIso φ f N).hom =
      (originalCompositeSpecPullbackSectionsIso φ f M).hom ≫
        moduleSpecΓFunctor.map ((pullback (Spec.map φ ≫ f)).map q) := by
  rw [originalCompositeSpecPullbackSectionsIso_hom, originalCompositeSpecPullbackSectionsIso_hom]
  exact (originalCompositeSpecPullbackSectionsNatTrans φ f).naturality q

end Hironaka.Geometry.QuotGrassmann
