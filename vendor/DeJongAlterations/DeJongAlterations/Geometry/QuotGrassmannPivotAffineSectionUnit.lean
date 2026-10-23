import DeJongAlterations.Geometry.QuotGrassmannPivotAffinePullbackSections
import DeJongAlterations.Geometry.QuotGrassmannPivotAdjunctionSectionBaseChange

/-!
# WHOLE original native affine-section base-change and adjunction-unit square

Native unit-conjugation for the SAME original adjunction mate, actual native
right-adjoint comparison naturality, and original adjunction triangles prove
the exact unit square. The square is a conclusion for EVERY original module.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

namespace DeJongAlterations.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- EVERY original sheaf has the WHOLE native extension-unit/pullback-unit square for SAME original affine-section comparison. -/
theorem originalSpecPullbackSectionsNatTrans_unit {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (M : (Spec A).Modules) :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (moduleSpecΓFunctor.obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map ((originalSpecPullbackSectionsNatTrans φ).app M) =
      moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
        (originalSpecPushforwardSectionsIso φ).hom.app ((pullback (Spec.map φ)).obj M) := by
  let T := originalAdjunctionSectionBaseChange (tilde.adjunction (R := A))
    (pullbackPushforwardAdjunction (Spec.map φ)) (ModuleCat.extendRestrictScalarsAdj φ.hom)
    (tilde.adjunction (R := B)) (originalSpecPushforwardSectionsIso φ)
  have hT : originalSpecPullbackSectionsNatTrans φ = T := rfl
  let H (t : moduleSpecΓFunctor ⋙ ModuleCat.extendScalars φ.hom ⟶
      pullback (Spec.map φ) ⋙ moduleSpecΓFunctor) : Prop :=
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (moduleSpecΓFunctor.obj M) ≫
      (ModuleCat.restrictScalars φ.hom).map (t.app M) =
    moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
      (originalSpecPushforwardSectionsIso φ).hom.app ((pullback (Spec.map φ)).obj M)
  have h : H T := originalAdjunctionSectionBaseChange_unit (tilde.adjunction (R := A))
    (pullbackPushforwardAdjunction (Spec.map φ)) (ModuleCat.extendRestrictScalarsAdj φ.hom)
    (tilde.adjunction (R := B)) (originalSpecPushforwardSectionsIso φ) M
  exact (congrArg H hT).mpr h

/-- For actual quasicoherent modules the SAME produced native isomorphism satisfies the WHOLE original unit square. -/
theorem originalSpecPullbackSectionsIso_unit {A B : CommRingCat.{u}}
    (φ : A ⟶ B) (M : (Spec A).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app (moduleSpecΓFunctor.obj M) ≫
        (ModuleCat.restrictScalars φ.hom).map (originalSpecPullbackSectionsIso φ M).hom =
      moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M) ≫
        (originalSpecPushforwardSectionsIso φ).hom.app ((pullback (Spec.map φ)).obj M) := by
  rw [originalSpecPullbackSectionsIso_hom]
  exact originalSpecPullbackSectionsNatTrans_unit φ M

end DeJongAlterations.Geometry.QuotGrassmann
