import DeJongAlterations.Geometry.QuotGrassmannPivotAffinePushforwardSections

/-!
# Genuine native affine pullback is original scalar extension on actual sections

The native tilde/pullback adjunction mate constructs the actual comparison.
All units, counits and structural ring maps are original. Native affine
quasicoherence gives its actual inverse. The WHOLE actual map comparison
is native naturality of an internally constructed natural transformation.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace DeJongAlterations.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The actual original native tilde-pullback/scalar-extension comparison is the adjunction mate of original pushforward sections. -/
def originalSpecTildePullbackIsoExtendScalars
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde.functor R ⋙ pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S := by
  let adj₁ := (tilde.adjunction (R := R)).comp
    (pullbackPushforwardAdjunction (Spec.map φ))
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
    (tilde.adjunction (R := S))
  exact ((conjugateIsoEquiv adj₁ adj₂).symm
    (originalSpecPushforwardSectionsIso φ)).symm

/-- The native actual affine pullback-section comparison exists naturally for ALL original sheaves as a morphism. -/
def originalSpecPullbackSectionsNatTrans {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    moduleSpecΓFunctor ⋙ ModuleCat.extendScalars φ.hom ⟶
      pullback (Spec.map φ) ⋙ moduleSpecΓFunctor :=
  (Functor.isoWhiskerLeft (moduleSpecΓFunctor ⋙ ModuleCat.extendScalars φ.hom)
      (tilde.toTildeΓNatIso (R := S))).hom ≫
    (Functor.isoWhiskerLeft moduleSpecΓFunctor
      (Functor.isoWhiskerRight (originalSpecTildePullbackIsoExtendScalars φ).symm
        moduleSpecΓFunctor)).hom ≫
    Functor.whiskerRight (fromTildeΓNatTrans (R := R))
      (pullback (Spec.map φ) ⋙ moduleSpecΓFunctor)

/-- Actual affine quasicoherence produces BOTH whole native maps of the original affine pullback-section isomorphism. -/
def originalSpecPullbackSectionsIso {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars φ.hom).obj (moduleSpecΓFunctor.obj M) ≅
      moduleSpecΓFunctor.obj ((pullback (Spec.map φ)).obj M) := by
  let : IsIso M.fromTildeΓ := inferInstance
  let A := moduleSpecΓFunctor.obj M
  exact tilde.isoTop _ ≪≫
    moduleSpecΓFunctor.mapIso ((originalSpecTildePullbackIsoExtendScalars φ).app A).symm ≪≫
    moduleSpecΓFunctor.mapIso ((pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ))

/-- The actual whole isomorphism is the SAME internally produced original native natural comparison. -/
theorem originalSpecPullbackSectionsIso_hom {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (originalSpecPullbackSectionsIso φ M).hom =
      (originalSpecPullbackSectionsNatTrans φ).app M := rfl

/-- EVERY original native map satisfies the WHOLE original affine-section scalar-extension/pullback triangle. -/
theorem originalSpecPullbackSectionsIso_naturality {R S : CommRingCat.{u}} (φ : R ⟶ S)
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (q : M ⟶ N) :
    (ModuleCat.extendScalars φ.hom).map (moduleSpecΓFunctor.map q) ≫
        (originalSpecPullbackSectionsIso φ N).hom =
      (originalSpecPullbackSectionsIso φ M).hom ≫
        moduleSpecΓFunctor.map ((pullback (Spec.map φ)).map q) := by
  rw [originalSpecPullbackSectionsIso_hom, originalSpecPullbackSectionsIso_hom]
  exact (originalSpecPullbackSectionsNatTrans φ).naturality q

end DeJongAlterations.Geometry.QuotGrassmann
