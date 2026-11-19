import Hironaka.Algebra.NodeFittingOmegaGluing
import Hironaka.Algebra.NodeFittingIdealSheafQuotient

/-! # The actual intrinsic Fitting closed-subscheme stalk over the SAME original local base -/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Hironaka.Algebra.NodeFittingOmegaStalkQuotient

open NodeFittingOmegaGluing

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFinitePresentation f]

/-- The SAME original intrinsic whole local differential ideal has the ACTUAL native subscheme stalk quotient. -/
def stalkQuotientRingEquiv (i : ℕ) (z : (idealSheaf f i).subscheme) :
    (X.presheaf.stalk ((idealSheaf f i).subschemeι z) ⧸
      NodeFittingOmegaStalk.ideal f i ((idealSheaf f i).subschemeι z)) ≃+*
      (idealSheaf f i).subscheme.presheaf.stalk z :=
  (Ideal.quotEquivOfEq (idealSheaf_stalk f i ((idealSheaf f i).subschemeι z)).symm).trans
    (NodeFittingIdealSheaf.stalkQuotientEquiv (idealSheaf f i) z)

/-- Every actual original quotient representative follows the SAME original inclusion stalk map. -/
@[simp]
theorem stalkQuotientRingEquiv_mk (i : ℕ) (z : (idealSheaf f i).subscheme)
    (a : X.presheaf.stalk ((idealSheaf f i).subschemeι z)) :
    stalkQuotientRingEquiv f i z (Ideal.Quotient.mk _ a) =
      (idealSheaf f i).subschemeι.stalkMap z a := rfl

/-- The ACTUAL composite's native stalk map, with its SAME original base point made explicit. -/
@[instance_reducible]
def structuralStalkAlgebra (i : ℕ) (z : (idealSheaf f i).subscheme) :
    Algebra (Y.presheaf.stalk (f ((idealSheaf f i).subschemeι z)))
      ((idealSheaf f i).subscheme.presheaf.stalk z) :=
  (show Y.presheaf.stalk (f ((idealSheaf f i).subschemeι z)) →+*
      (idealSheaf f i).subscheme.presheaf.stalk z from
    ((fittingMorphism f i).stalkMap z).hom).toAlgebra

/-- Actual quotient equivalence over the SAME original base local ring, with the ACTUAL composite's native coefficients. -/
def actualStalkQuotientEquiv (i : ℕ) (z : (idealSheaf f i).subscheme) :
    letI := NodeFittingOmegaStalk.stalkAlgebra f ((idealSheaf f i).subschemeι z)
    letI := structuralStalkAlgebra f i z
    (X.presheaf.stalk ((idealSheaf f i).subschemeι z) ⧸
      NodeFittingOmegaStalk.ideal f i ((idealSheaf f i).subschemeι z)) ≃ₐ[
        Y.presheaf.stalk (f ((idealSheaf f i).subschemeι z))]
      (idealSheaf f i).subscheme.presheaf.stalk z := by
  letI := NodeFittingOmegaStalk.stalkAlgebra f ((idealSheaf f i).subschemeι z)
  letI := structuralStalkAlgebra f i z
  refine { toRingEquiv := stalkQuotientRingEquiv f i z, commutes' := ?_ }
  intro r
  change stalkQuotientRingEquiv f i z
      (Ideal.Quotient.mk _ (f.stalkMap ((idealSheaf f i).subschemeι z) r)) =
    (fittingMorphism f i).stalkMap z r
  rw [stalkQuotientRingEquiv_mk]
  change (idealSheaf f i).subschemeι.stalkMap z
      (f.stalkMap ((idealSheaf f i).subschemeι z) r) =
    ((idealSheaf f i).subschemeι ≫ f).stalkMap z r
  rw [Scheme.Hom.stalkMap_comp]
  rfl

/-- The algebra isomorphism preserves the WHOLE original quotient-map triangle. -/
@[simp]
theorem actualStalkQuotientEquiv_mk (i : ℕ) (z : (idealSheaf f i).subscheme)
    (a : X.presheaf.stalk ((idealSheaf f i).subschemeι z)) :
    actualStalkQuotientEquiv f i z (Ideal.Quotient.mk _ a) =
      (idealSheaf f i).subschemeι.stalkMap z a := rfl

end Hironaka.Algebra.NodeFittingOmegaStalkQuotient
