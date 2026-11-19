import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.CategoryTheory.Limits.Final

/-!
# Actual native pullback of the original free quotient frames

The unit isomorphism is the genuine adjoint of the original structure-ring
morphism. The free-frame comparison is the native coproduct comparison,
with its actual original basis-inclusion triangle.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Functor

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}}

/- The first two constructions adapt the native Mathlib-only proof in
BingWangEntropy/NativeLinePullbackFrames.lean, with its source hash recorded
in the associated blueprint: bc8833ac017958913b75ed024f5d27fca0a7affce371985666b9e4167f1938ca. -/

/-- The actual native inverse-image functor preserves the terminal open and is final. -/
theorem originalInverseImageOpens_final (f : X ⟶ Y) : (Opens.map f.base).Final := by
  have : (fromPUnit.{0} (⊤ : Y.Opens)).Final := final_fromPUnit_of_isTerminal isTerminalTop
  have : (fromPUnit.{0} (⊤ : X.Opens)).Final := final_fromPUnit_of_isTerminal isTerminalTop
  have : (fromPUnit.{0} (⊤ : Y.Opens) ⋙ Opens.map f.base).Final :=
    Functor.final_of_natIso (F := fromPUnit.{0} (⊤ : X.Opens))
      (Discrete.natIso (fun _ ↦ eqToIso (by rfl)))
  exact Functor.final_of_final_comp (fromPUnit.{0} (⊤ : Y.Opens)) (Opens.map f.base)

/-- The native unit frame pulls back by the actual original structural-ring adjoint. -/
def originalPullbackUnitIso (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  have := originalInverseImageOpens_final f
  let e := asIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
  exact { hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }

/-- Its actual adjunction mate is precisely the original structure-ring sheaf morphism. -/
theorem originalPullbackUnitIso_mate (f : X ⟶ Y) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (originalPullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  change (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) = _
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

/-- The original free frame pulls back to the native free sheaf on its same original index. -/
def originalPullbackFreeIso (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I := by
  have := originalInverseImageOpens_final f
  let e := SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I
  exact { hom := e.hom, inv := e.inv, hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }

/-- The original native free basis inclusions commute with this actual pullback comparison. -/
theorem originalPullbackFreeIso_inclusion (f : X ⟶ Y) {I : Type u} (i : I) :
    (Scheme.Modules.pullback f).map (SheafOfModules.ιFree i) ≫
      (originalPullbackFreeIso f I).hom =
    (originalPullbackUnitIso f).hom ≫ SheafOfModules.ιFree i := by
  have := originalInverseImageOpens_final f
  exact SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom f.toRingCatSheafHom i

end Hironaka.Geometry.QuotGrassmann
