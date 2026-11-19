import Hironaka.Geometry.ProperGeometricGlobalFunctionsBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Native properness derives finiteness of the ORIGINAL coefficient and global-section algebra. -/

noncomputable section
open AlgebraicGeometry CategoryTheory
namespace Hironaka.Geometry.ProperGeometricGlobalFunctions
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- ORIGINAL universal closedness makes the ORIGINAL coefficient homomorphism integral. -/
theorem coefficientMap_isIntegral {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [UniversallyClosed p] : (coefficientMap p).IsIntegral := by
  apply RingHom.isIntegral_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv)
  exact isIntegral_appTop_of_universallyClosed p

/-- ORIGINAL universal closedness and finite type derive finiteness of the ORIGINAL whole coefficient map. -/
theorem coefficientMap_finite {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [UniversallyClosed p] [LocallyOfFiniteType p] :
    (coefficientMap p).Finite := by
  apply RingHom.finite_respectsIso.2
    (e := (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv)
  exact finite_appTop_of_universallyClosed k p

/-- The ACTUAL whole original section ring is a field, derived from original universal closedness. -/
theorem sections_isField {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [UniversallyClosed p] : IsField Γ(X, ⊤) :=
  isField_of_universallyClosed k p

/-- The ORIGINAL section algebra is finite, without an assumed finite-section certificate. -/
theorem sections_finite {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (.of k)) [UniversallyClosed p] [LocallyOfFiniteType p] :
    letI : Algebra k Γ(X, ⊤) := sectionsAlgebra p
    Module.Finite k Γ(X, ⊤) := by
  change (coefficientMap p).Finite
  exact coefficientMap_finite p

end Hironaka.Geometry.ProperGeometricGlobalFunctions
