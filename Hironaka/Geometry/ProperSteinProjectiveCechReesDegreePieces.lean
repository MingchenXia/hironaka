/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.AffineBlowup
import Mathlib.RingTheory.Noetherian.Basic

/-! # The SAME native actual Rees grading and its original ideal-power coefficients

No new grading is introduced. The ALREADY native AffineBlowup.reesGrading
is identified with the literal original ideal powers through actual polynomial
coefficients and monomials. Original degree finiteness is derived from R itself.
-/
open scoped Polynomial
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.ReesDegreePieces
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The actual native ORIGINAL Rees degree is linearly the SAME actual original ideal power. -/
def powerEquiv (n : ℕ) : Hironaka.reesGrading I n ≃ₗ[R] ↥(I^n) where
  toFun p := ⟨((p.val : reesAlgebra I) : R[X]).coeff n, p.val.property n⟩
  invFun a := ⟨⟨Polynomial.monomial n a.val, reesAlgebra.monomial_mem.mpr a.property⟩,
    ⟨a.val, rfl⟩⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact (Hironaka.mem_reesGrading_iff I n p.val).mp p.property |>.symm
  right_inv a := by
    apply Subtype.ext
    simp only [Polynomial.coeff_monomial, ↓reduceIte]
  map_add' p q := Subtype.ext (Polynomial.coeff_add _ _ _)
  map_smul' r p := Subtype.ext (Polynomial.coeff_smul _ _ _)

/-- EVERY native homogeneous section is sent to its literal original polynomial coefficient. -/
theorem powerEquiv_apply (n : ℕ) (p : Hironaka.reesGrading I n) :
    (powerEquiv I n p).val = ((p.val : reesAlgebra I) : R[X]).coeff n := rfl

/-- EVERY original ideal-power coefficient is inserted as its literal original Rees monomial. -/
theorem powerEquiv_symm_apply (n : ℕ) (a : ↥(I^n)) :
    (((powerEquiv I n).symm a).val : R[X]) = Polynomial.monomial n a.val := rfl

/-- Original Noetherianity internally proves finite EVERY SAME native Rees coefficient degree piece. -/
theorem nativePiece_finite [IsNoetherianRing R] (n : ℕ) :
    Module.Finite R (Hironaka.reesGrading I n) :=
  Module.Finite.equiv (powerEquiv I n).symm

end Hironaka.Geometry.ProperSteinProjectiveCech.ReesDegreePieces
