import Hironaka.Geometry.QuotGrassmannPivotOverSchemePullback
import Hironaka.Geometry.QuotGrassmannPivotOverFree
import Hironaka.Geometry.QuotGrassmannPivotPullbackCoefficients

/-!
# Actual original coefficients through the native over-site/open-scheme equivalence

The terminal coefficient is transported by the actual original open-section
isomorphism and then by the genuine native scheme pullback structural map.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original whole unit endomorphism in the actual native open-scheme unit frame. -/
def originalOverEquivUnitEnd (X : Scheme.{u}) (U : X.Opens)
    (b : End (SheafOfModules.unit (X.ringCatSheaf.over U))) :
    End (SheafOfModules.unit U.toScheme.ringCatSheaf) :=
  (originalOverEquivUnitIso X U).inv ≫ (Scheme.Modules.overEquiv U).functor.map b ≫
    (originalOverEquivUnitIso X U).hom

/-- The actual original terminal coefficient is transported by the SAME original open top-section isomorphism. -/
theorem originalOverEquivUnitEnd_one_top (X : Scheme.{u}) (U : X.Opens)
    (b : End (SheafOfModules.unit (X.ringCatSheaf.over U))) :
    (originalOverEquivUnitEnd X U b).val.app (.op ⊤) (1 : Γ(U.toScheme, ⊤)) =
      U.topIso.inv (originalOverUnitCoefficient X U b) := by
  let V := U.overEquivalence.symm.functor.obj ⊤
  change b.val.app (.op V) (1 : Γ(X, V.left)) = _
  exact (originalOverUnitEnd_one_restrict X U b V).symm

/-- Genuine native pullback sends the SAME entire original over-site coefficient to its actual structural image. -/
theorem originalOverSchemePullbackUnitEnd_one_top {X Y : Scheme.{u}} (U : X.Opens)
    (h : Y ⟶ U.toScheme) (b : End (SheafOfModules.unit (X.ringCatSheaf.over U))) :
    (originalPullbackUnitEnd h (originalOverEquivUnitEnd X U b)).val.app (.op ⊤)
        (1 : Γ(Y, ⊤)) =
      h.appTop (U.topIso.inv (originalOverUnitCoefficient X U b)) :=
  (originalPullbackUnitEnd_one h (originalOverEquivUnitEnd X U b) ⊤).trans
    (congrArg (fun x => h.appTop x) (originalOverEquivUnitEnd_one_top X U b))

end Hironaka.Geometry.QuotGrassmann
