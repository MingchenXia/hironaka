import DeJongAlterations.Geometry.CompletedLocalRing

/-! Exact WHOLE original affine-section germs under actual scheme maps through the
original affine-open spectrum. There is no residue, Noetherianity, node or model input. -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace DeJongAlterations.Geometry.NodeCompletedLocalAffineGerm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Z : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

/-- The ENTIRE original affine section germ followed by its actual affine-open stalk
map is the SAME canonical native coefficient map from the original section ring. -/
theorem fromSpec_germ_stalkMap (q : Spec Γ(X, U)) (hq : hU.fromSpec q ∈ U) :
    X.presheaf.germ U (hU.fromSpec q) hq ≫ hU.fromSpec.stalkMap q =
      Scheme.baseToStalk (𝟙 (Spec Γ(X, U))) q := by
  rw [Scheme.Hom.germ_stalkMap, hU.fromSpec_app_self, Category.assoc,
    TopCat.Presheaf.germ_res]
  simp only [Scheme.baseToStalk, Scheme.Modules.baseRingHom, Scheme.Hom.id_appTop,
    Category.comp_id]

/-- Pulling the ORIGINAL affine sections along ANY actual map to their spectrum keeps
EVERY original germ, with no supplied coefficient-compatibility certificate. -/
theorem affine_germ_stalkMap (p : Z ⟶ Spec Γ(X, U)) (z : Z)
    (hz : (p ≫ hU.fromSpec) z ∈ U) :
    X.presheaf.germ U ((p ≫ hU.fromSpec) z) hz ≫ (p ≫ hU.fromSpec).stalkMap z =
      Scheme.baseToStalk p z := by
  rw [Scheme.Hom.stalkMap_comp, ← Category.assoc]
  change (X.presheaf.germ U (hU.fromSpec (p z)) hz ≫ hU.fromSpec.stalkMap (p z)) ≫
    p.stalkMap z = _
  rw [fromSpec_germ_stalkMap]
  simpa only [Category.comp_id] using
    Scheme.baseToStalk_comp_stalkMap p (𝟙 (Spec Γ(X, U))) z

/-- The separately named ACTUAL geometric projection retains its WHOLE original section
germs when the original affine factorization is proved as an equality of scheme maps. -/
theorem affine_germ_stalkMap_over (p : Z ⟶ Spec Γ(X, U)) (t : Z ⟶ X)
    (h : t = p ≫ hU.fromSpec) (z : Z) (hz : t z ∈ U) :
    X.presheaf.germ U (t z) hz ≫ t.stalkMap z = Scheme.baseToStalk p z := by
  subst t
  exact affine_germ_stalkMap hU p z hz

end DeJongAlterations.Geometry.NodeCompletedLocalAffineGerm
