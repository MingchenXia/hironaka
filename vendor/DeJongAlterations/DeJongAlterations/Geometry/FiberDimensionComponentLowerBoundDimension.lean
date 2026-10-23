import DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundAlgebra

/-! # Actual affine dimension bounded by a quasi-finite polynomial projection -/

noncomputable section

namespace DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundDimension

universe u

/-- Native quasi-finiteness of the actual fraction field over a polynomial coefficient
algebra bounds the dimension of the original finite-type domain, with no dimension premise. -/
theorem ringKrullDim_le_of_quasiFinite_polynomial_fractionField
    (k A F : Type u) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] [Field F] [Algebra k F] [Algebra A F]
    [IsScalarTower k A F] [IsFractionRing A F] (d : ℕ)
    [Algebra (MvPolynomial (Fin d) k) F]
    [IsScalarTower k (MvPolynomial (Fin d) k) F]
    [Algebra.QuasiFinite (MvPolynomial (Fin d) k) F] : ringKrullDim A ≤ d := by
  obtain ⟨n, hdim, htr⟩ := Algebra.FunctionFieldDimension.exists_dimension_and_trdeg k A F
  have hle := FiberDimensionComponentLowerBoundAlgebra.trdeg_le_of_quasiFinite_polynomial_algebra k F d
  rw [htr] at hle
  have hnd : n ≤ d := by exact_mod_cast hle
  rw [hdim]
  exact_mod_cast hnd

end DeJongAlterations.Geometry.FiberDimensionComponentLowerBoundDimension
