import DeJongAlterations.Algebra.FunctionFieldDimension
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# A genuine algebra bound for the componentwise generic-dimension argument

A field quasi-finite over an actual compatible polynomial coefficient
algebra has base-field transcendence degree bounded by the number of
variables. The proof constructs the actual residue-field tower internally.
The full componentwise specialization theorem is not asserted here.
-/

noncomputable section

namespace DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundAlgebra

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual quasi-finiteness over a polynomial coefficient algebra bounds field transcendence degree. -/
theorem trdeg_le_of_quasiFinite_polynomial_algebra
    (k F : Type u) [Field k] [Field F] [Algebra k F] (d : ℕ)
    [Algebra (MvPolynomial (Fin d) k) F]
    [IsScalarTower k (MvPolynomial (Fin d) k) F]
    [Algebra.QuasiFinite (MvPolynomial (Fin d) k) F] : Algebra.trdeg k F ≤ d := by
  let P := MvPolynomial (Fin d) k
  let q : Ideal F := ⊥
  let p : Ideal P := q.under P
  have : p.IsPrime := inferInstance
  have : q.LiesOver p := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Module.Finite p.ResidueField q.ResidueField := inferInstance
  have : Algebra.IsIntegral p.ResidueField q.ResidueField :=
    Algebra.IsIntegral.of_finite _ _
  have hres : Algebra.trdeg k F = Algebra.trdeg k q.ResidueField :=
    ((Ideal.algEquivResidueFieldOfField q).restrictScalars k).trdeg_eq
  have hfinite : Algebra.trdeg k p.ResidueField = Algebra.trdeg k q.ResidueField :=
    Algebra.FunctionFieldDimension.trdeg_eq_of_isAlgebraic k p.ResidueField q.ResidueField
  have : Algebra.IsAlgebraic (P ⧸ p) p.ResidueField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (P ⧸ p))
  have hfrac : Algebra.trdeg k (P ⧸ p) = Algebra.trdeg k p.ResidueField :=
    Algebra.FunctionFieldDimension.trdeg_eq_of_isAlgebraic k (P ⧸ p) p.ResidueField
  calc
    Algebra.trdeg k F = Algebra.trdeg k q.ResidueField := hres
    _ = Algebra.trdeg k p.ResidueField := hfinite.symm
    _ = Algebra.trdeg k (P ⧸ p) := hfrac.symm
    _ ≤ Algebra.trdeg k P :=
      trdeg_le_of_surjective (Ideal.Quotient.mkₐ k p) Ideal.Quotient.mk_surjective
    _ = d := by simp [P]

end DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundAlgebra
