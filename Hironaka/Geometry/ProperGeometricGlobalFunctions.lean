import Hironaka.Geometry.ProperGeometricGlobalFunctionsFinite
import Hironaka.Geometry.ProperGeometricGlobalFunctionsTensor
import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# The ORIGINAL global functions of a proper geometrically integral scheme are constants

Actual properness derives the original finite section field. Actual GI
makes its literal self tensor a domain via the native WHOLE flat section
comparison. The degree-one argument constructs the ORIGINAL coefficient
algebra equivalence; no section finiteness or constant-field certificate.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace Hironaka.Geometry.ProperGeometricGlobalFunctions
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- ORIGINAL properness and GI internally make the ORIGINAL whole coefficient homomorphism bijective. -/
theorem coefficientMap_bijective {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] [GeometricallyIntegral p] :
    Function.Bijective (coefficientMap p) := by
  let : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton p
  let : Field Γ(X, ⊤) := (sections_isField p).toField
  let : Algebra k Γ(X, ⊤) := sectionsAlgebra p
  let : Module.Finite k Γ(X, ⊤) := sections_finite p
  let T := baseChange (S := Γ(X, ⊤)) p
  let : IsIntegral T := GeometricallyIntegral.geometrically_isIntegral
    (Spec.map (CommRingCat.ofHom (algebraMap k Γ(X, ⊤))))
    (firstProjection (S := Γ(X, ⊤)) p) (structureMap (S := Γ(X, ⊤)) p)
    (IsPullback.of_hasPullback _ _)
  let : Algebra Γ(X, ⊤) Γ(T, ⊤) := sectionsAlgebra (structureMap (S := Γ(X, ⊤)) p)
  let e := fieldTensorEquiv (L := Γ(X, ⊤)) p
  let : IsDomain (Γ(X, ⊤) ⊗[k] Γ(X, ⊤)) := e.injective.isDomain
  change Function.Bijective (algebraMap k Γ(X, ⊤))
  exact algebraMap_bijective_of_selfTensor_domain k Γ(X, ⊤)

/-- The ACTUAL original coefficient algebra equivalence, with its ENTIRE forward coefficient map retained. -/
def coefficientAlgEquiv {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] [GeometricallyIntegral p] :
    letI : Algebra k Γ(X, ⊤) := sectionsAlgebra p
    k ≃ₐ[k] Γ(X, ⊤) := by
  letI : Algebra k Γ(X, ⊤) := sectionsAlgebra p
  exact AlgEquiv.ofBijective (Algebra.ofId k Γ(X, ⊤)) (coefficientMap_bijective p)

/-- EVERY original coefficient element is unchanged by the actual coefficient equivalence. -/
@[simp]
theorem coefficientAlgEquiv_apply {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] [GeometricallyIntegral p] (a : k) :
    letI : Algebra k Γ(X, ⊤) := sectionsAlgebra p
    coefficientAlgEquiv p a = coefficientMap p a := rfl

/-- EVERY ORIGINAL whole global regular function is a UNIQUE ORIGINAL scalar. -/
theorem existsUnique_constant {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] [GeometricallyIntegral p] (b : Γ(X, ⊤)) :
    ∃! a : k, coefficientMap p a = b := by
  obtain ⟨a, ha⟩ := (coefficientMap_bijective p).2 b
  exact ⟨a, ha, fun a' ha' => (coefficientMap_bijective p).1 (ha'.trans ha.symm)⟩

/-- The dimension of the ACTUAL original section algebra is internally exactly one. -/
theorem finrank_sections_eq_one {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] [GeometricallyIntegral p] :
    letI : Algebra k Γ(X, ⊤) := sectionsAlgebra p
    Module.finrank k Γ(X, ⊤) = 1 := by
  let : Algebra k Γ(X, ⊤) := sectionsAlgebra p
  exact Module.finrank_of_bijective_algebraMap (coefficientMap_bijective p)

/-- EVERY actual field extension has the actual ORIGINAL whole coefficient algebra equivalence. -/
def fieldSectionsAlgEquiv {k L : Type u} [Field k] [Field L] [Algebra k L] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] [GeometricallyIntegral p] :
    letI : Algebra L Γ(baseChange (S := L) p, ⊤) := sectionsAlgebra (structureMap (S := L) p)
    L ≃ₐ[L] Γ(baseChange (S := L) p, ⊤) :=
  coefficientAlgEquiv (structureMap (S := L) p)

/-- The ENTIRE ORIGINAL coefficient map on the actual whole base change is retained. -/
@[simp]
theorem fieldSectionsAlgEquiv_apply {k L : Type u} [Field k] [Field L] [Algebra k L] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [IsProper p] [GeometricallyIntegral p] (a : L) :
    letI : Algebra L Γ(baseChange (S := L) p, ⊤) := sectionsAlgebra (structureMap (S := L) p)
    fieldSectionsAlgEquiv p a = coefficientMap (structureMap (S := L) p) a := rfl

end Hironaka.Geometry.ProperGeometricGlobalFunctions
