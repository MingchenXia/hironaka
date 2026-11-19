import Hironaka.Geometry.ProperGeometricGlobalFunctionsBaseChange

/-! # The ORIGINAL coefficient equivalence survives actual WHOLE genuinely flat coefficient base changes. -/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
namespace Hironaka.Geometry.ProperSteinFlatSections
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open ProperGeometricGlobalFunctions

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {T : Scheme.{u}} (q : T ⟶ Spec (.of A))

/-- The ORIGINAL coefficient algebra equivalence is built from the ENTIRE original now-bijective coefficient map. -/
def coefficientAlgEquivOfBijective (hq : Function.Bijective (coefficientMap q)) :
    letI : Algebra A Γ(T, ⊤) := sectionsAlgebra q
    A ≃ₐ[A] Γ(T, ⊤) := by
  let : Algebra A Γ(T, ⊤) := sectionsAlgebra q
  exact AlgEquiv.ofBijective (Algebra.ofId A Γ(T, ⊤)) hq

/-- Genuinely flat coefficient base change gives the SAME ORIGINAL whole section algebra and its ORIGINAL coefficient equivalence. -/
def flatSectionsAlgEquiv (hq : Function.Bijective (coefficientMap q))
    [QuasiCompact q] [QuasiSeparated q] [Module.Flat A B] :
    letI : Algebra B Γ(baseChange (S := B) q, ⊤) := sectionsAlgebra (structureMap (S := B) q)
    B ≃ₐ[B] Γ(baseChange (S := B) q, ⊤) := by
  let : Algebra A Γ(T, ⊤) := sectionsAlgebra q
  let : Algebra B Γ(baseChange (S := B) q, ⊤) := sectionsAlgebra (structureMap (S := B) q)
  exact (Algebra.TensorProduct.rid A B B).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B)
      (coefficientAlgEquivOfBijective q hq)).trans (tensorEquiv (S := B) q))

/-- The ENTIRE actual flat-base-change coefficient map remains the ORIGINAL coefficient map. -/
theorem flatSectionsAlgEquiv_apply (hq : Function.Bijective (coefficientMap q))
    [QuasiCompact q] [QuasiSeparated q] [Module.Flat A B] (b : B) :
    letI : Algebra B Γ(baseChange (S := B) q, ⊤) := sectionsAlgebra (structureMap (S := B) q)
    flatSectionsAlgEquiv q hq b = coefficientMap (structureMap (S := B) q) b := by
  let : Algebra B Γ(baseChange (S := B) q, ⊤) := sectionsAlgebra (structureMap (S := B) q)
  exact (flatSectionsAlgEquiv q hq).commutes b

end Hironaka.Geometry.ProperSteinFlatSections
