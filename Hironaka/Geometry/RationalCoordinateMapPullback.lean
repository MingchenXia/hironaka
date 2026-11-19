import Hironaka.Geometry.RationalCoordinateMap

/-!
# The actual pullback of rational coordinates

The native scheme morphism's map on global sections is exactly the
constructed polynomial evaluation map, through the canonical spectrum and
open-section isomorphisms. Thus the realization concerns the actual sheaf map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

namespace Hironaka.Geometry.RationalCoordinateMap

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] {n : ℕ}

/-- The constructed spectrum morphism is the native adjoint of actual polynomial evaluation. -/
theorem coordinateMap_eq_adjunction (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    coordinateMap p r =
      (ΓSpec.adjunction.homEquiv (coordinateOpen r).1.toScheme
        (op (CommRingCat.of (MvPolynomial (Fin n) k))))
        (CommRingCat.ofHom (coordinateRingMap p r) ≫ (coordinateOpen r).1.topIso.inv).op := by
  rw [Adjunction.homEquiv_apply]
  change (coordinateOpen r).1.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (coordinateRingMap p r)) =
    (coordinateOpen r).1.toScheme.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (coordinateRingMap p r) ≫ (coordinateOpen r).1.topIso.inv)
  rw [Scheme.Opens.toSpecΓ, Category.assoc, ← Spec.map_comp]

/-- The actual global-section pullback is exactly the constructed coordinate-ring homomorphism. -/
theorem coordinateMap_appTop (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField) :
    (Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv ≫
      (coordinateMap p r).appTop ≫ (coordinateOpen r).1.topIso.hom =
      CommRingCat.ofHom (coordinateRingMap p r) := by
  rw [coordinateMap_eq_adjunction, ← Category.assoc, ΓSpecIso_inv_ΓSpec_adjunction_homEquiv]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- Every variable pulled back by the actual sheaf morphism has its prescribed canonical germ. -/
theorem coordinateMap_pullback_X (p : X ⟶ Spec (.of k)) (r : Fin n → X.functionField)
    (i : Fin n) :
    X.germToFunctionField (coordinateOpen r).1
      ((coordinateOpen r).1.topIso.hom ((coordinateMap p r).appTop
        ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv (MvPolynomial.X i)))) = r i := by
  have h := congrArg (fun f : CommRingCat.of (MvPolynomial (Fin n) k) ⟶
      Γ(X, (coordinateOpen r).1) ↦ f (MvPolynomial.X i)) (coordinateMap_appTop p r)
  change (coordinateOpen r).1.topIso.hom ((coordinateMap p r).appTop
    ((Scheme.ΓSpecIso (.of (MvPolynomial (Fin n) k))).inv (MvPolynomial.X i))) =
      coordinateRingMap p r (MvPolynomial.X i) at h
  rw [h, coordinateRingMap_X, coordinateSection_germ]

end Hironaka.Geometry.RationalCoordinateMap
