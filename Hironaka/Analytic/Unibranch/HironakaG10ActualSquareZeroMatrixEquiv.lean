import Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroColumns

/-! A finite matrix cokernel as the square-zero summand of an actual analytic quotient. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalAlgebraEquiv
  Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroColumns
  Hironaka.Analytic.Unibranch.HironakaG10SquareZeroMatrixQuotient
  Hironaka.Analytic.Unibranch.HironakaG10SquareZeroMatrixAlgebraEquiv
namespace Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroMatrixEquiv
noncomputable section

/-- The whole explicit ideal: normal square plus the original normal-linear matrix columns. -/
def actualSquareZeroMatrixIdeal (d a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel d))) :
    Ideal (HolGerm (ComplexModel (d+a))) :=
  normalIdeal d a ^ 2 ⊔ Ideal.span (Set.range (actualMatrixColumn d a F))

/-- The abstract matrix-column ideal maps to the literal actual normal-linear columns. -/
theorem map_matrixColumnIdeal (d a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel d))) :
    letI := tangentAlgebra d a
    Ideal.map (firstOrderNormalAlgEquiv d a).toRingHom (matrixColumnIdeal F) =
      Ideal.map (Ideal.Quotient.mk (normalIdeal d a ^ 2))
        (Ideal.span (Set.range (actualMatrixColumn d a F))) := by
  letI := tangentAlgebra d a
  simp only [matrixColumnIdeal, Ideal.map_span]
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨_,⟨j,rfl⟩,rfl⟩
    exact ⟨_,⟨j,rfl⟩,(firstOrderNormalAlgEquiv_matrixColumn d a F j).symm⟩
  · rintro ⟨_,⟨j,rfl⟩,rfl⟩
    exact ⟨_,⟨j,rfl⟩,firstOrderNormalAlgEquiv_matrixColumn d a F j⟩

/-- The actual explicit analytic quotient is the square-zero extension of
the actual finite matrix cokernel, with the original tangent scalar action. -/
def actualSquareZeroMatrixAlgEquiv (d a : ℕ) {b : ℕ}
    (F : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel d))) :
    letI := tangentAlgebra d a
    (HolGerm (ComplexModel (d+a)) ⧸ actualSquareZeroMatrixIdeal d a F) ≃ₐ[HolGerm (ComplexModel d)]
      TrivSqZeroExt (HolGerm (ComplexModel d))
        ((Fin a → HolGerm (ComplexModel d)) ⧸ LinearMap.range F.mulVecLin) := by
  letI := tangentAlgebra d a
  let B := HolGerm (ComplexModel d)
  let J := normalIdeal d a ^ 2
  let P := Ideal.span (Set.range (actualMatrixColumn d a F))
  let I := matrixColumnIdeal F
  let e := firstOrderNormalAlgEquiv d a
  have hmap : P.map (Ideal.Quotient.mk J) = I.map e.toRingHom := (map_matrixColumnIdeal d a F).symm
  let q := DoubleQuot.quotQuotEquivQuotSupₐ B J P
  let eq := Ideal.quotientEquivAlg I (P.map (Ideal.Quotient.mk J)) e hmap
  exact q.symm.trans (eq.symm.trans (matrixColumnQuotientAlgEquiv F))
end
end Hironaka.Analytic.Unibranch.HironakaG10ActualSquareZeroMatrixEquiv
