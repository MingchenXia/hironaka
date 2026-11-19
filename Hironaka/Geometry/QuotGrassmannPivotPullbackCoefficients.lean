import Hironaka.Geometry.QuotGrassmannPivotPullbackFree

/-!
# True original structural coefficients under native sheaf pullback

The endomorphism is pulled back through the actual native functor and its
actual native unit frame. Its structural-ring square and coefficient at one
are proved for every original open of every original scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The actual original unit endomorphism, transported by true native pullback and its true frame. -/
def originalPullbackUnitEnd (b : End (SheafOfModules.unit Y.ringCatSheaf)) :
    End (SheafOfModules.unit X.ringCatSheaf) :=
  (originalPullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map b ≫
    (originalPullbackUnitIso f).hom

/-- True native pullback retains the exact original structural-ring square. -/
theorem originalPullbackUnitEnd_square (b : End (SheafOfModules.unit Y.ringCatSheaf)) :
    b ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map (originalPullbackUnitEnd f b) := by
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  rw [← originalPullbackUnitIso_mate f,
    ← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right]
  apply congrArg (adj.homEquiv _ _)
  simp only [originalPullbackUnitEnd, Iso.hom_inv_id_assoc]

/-- On every original open the pulled-back coefficient is exactly the original structural image. -/
theorem originalPullbackUnitEnd_one (b : End (SheafOfModules.unit Y.ringCatSheaf)) (U : Y.Opens) :
    (originalPullbackUnitEnd f b).val.app (.op (f ⁻¹ᵁ U)) (1 : Γ(X, f ⁻¹ᵁ U)) =
      f.app U (b.val.app (.op U) (1 : Γ(Y, U))) := by
  have h := congrArg (fun m ↦ m.val.app (.op U) (1 : Γ(Y, U)))
    (originalPullbackUnitEnd_square f b)
  change f.app U (b.val.app (.op U) (1 : Γ(Y, U))) =
    (originalPullbackUnitEnd f b).val.app (.op (f ⁻¹ᵁ U)) (f.app U (1 : Γ(Y, U))) at h
  have hone : f.app U (1 : Γ(Y, U)) = (1 : Γ(X, f ⁻¹ᵁ U)) := map_one _
  rw [hone] at h
  exact h.symm

end Hironaka.Geometry.QuotGrassmann
