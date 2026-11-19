import Hironaka.Algebra.ModuleFlatteningMinors

/-!
# The original homogeneous replacement-minor identities

The actual matrix of original replacement-column minors is an adjugate product.
Taking determinants gives the integral Plücker chart relation over every
commutative coefficient ring, without a domain or invertibility hypothesis.
-/

noncomputable section

open scoped Matrix

namespace Hironaka.Algebra.PluckerQuot

open ModuleFlatteningMinors

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w}
  [Fintype ι] [DecidableEq ι]

/-- The original replacement-minor matrix is the actual adjugate product. -/
theorem replacementMinorMatrix_eq_adjugate_mul (M : Matrix ι κ R) (s t : ι → κ) :
    (fun i j ↦ columnMinor M (Function.update s i (t j))) =
      (selectedMatrix M s).adjugate * selectedMatrix M t := by
  ext i j
  calc
    _ = (selectedMatrix M s).cramer (fun k ↦ M k (t j)) i := by
      rw [Matrix.cramer_apply, updateCol_selectedMatrix]
      rfl
    _ = _ := by
      rw [Matrix.cramer_eq_adjugate_mulVec]
      rfl

/-- The actual replacement-minor Plücker identity over every commutative ring. -/
theorem det_replacementMinorMatrix (M : Matrix ι κ R) (s t : ι → κ) :
    Matrix.det (fun i j ↦ columnMinor M (Function.update s i (t j))) =
      columnMinor M s ^ (Fintype.card ι - 1) * columnMinor M t := by
  rw [replacementMinorMatrix_eq_adjugate_mul, Matrix.det_mul, Matrix.det_adjugate]
  rfl

/-- Original selectors with a repeated column have exactly zero maximal minor. -/
theorem columnMinor_eq_zero_of_not_injective (M : Matrix ι κ R) (s : ι → κ)
    (hs : ¬ Function.Injective s) : columnMinor M s = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hs
  apply Matrix.det_zero_of_column_eq hne
  intro k
  exact congrArg (M k) hij

end Hironaka.Algebra.PluckerQuot
