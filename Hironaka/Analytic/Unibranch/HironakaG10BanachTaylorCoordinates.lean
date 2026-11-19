import Hironaka.Analytic.Unibranch.HironakaG10BanachMultilinearCoordinates

/-! # Actual Banach Taylor polynomials as finite-rank holomorphic sums -/
set_option autoImplicit false
namespace Hironaka.Analytic.Unibranch.HironakaG10BanachTaylorCoordinates
open Hironaka
  Hironaka.Analytic.Unibranch.HironakaG10BanachTaylorRemainder
  Hironaka.Analytic.Unibranch.HironakaG10BanachMultilinearCoordinates

/-- A coordinate word of length strictly less than the truncation degree. -/
def TaylorWord (d N : ℕ) := Σ k : Fin N, Fin k.val → Fin d

noncomputable instance (d N : ℕ) : Fintype (TaylorWord d N) := inferInstanceAs
  (Fintype (Σ k : Fin N, Fin k.val → Fin d))

/-- Scalar monomial associated with one actual Taylor word. -/
def wordScalar {d N : ℕ} (w : TaylorWord d N) (z : ComplexModel d) : ℂ :=
  ∏ i, z (w.2 i)

/-- Actual normalized Banach Taylor coefficient associated with the word. -/
noncomputable def wordCoefficient {d N : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] (f : ComplexModel d → E)
    (w : TaylorWord d N) : E :=
  (Nat.factorial w.1.val : ℂ)⁻¹ • (iteratedFDeriv ℂ w.1.val f 0)
    (fun i => EuclideanSpace.single (w.2 i) (1 : ℂ))

/-- The actual finite Taylor polynomial is a finite-rank holomorphic sum
with exactly its own normalized derivative coefficients. -/
theorem taylorPartial_eq_word_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (d N : ℕ) (f : ComplexModel d → E) (z : ComplexModel d) :
    taylorPartial f N z = ∑ w : TaylorWord d N, wordScalar w z • wordCoefficient f w := by
  classical
  rw [taylorPartial, ← Fin.sum_univ_eq_sum_range]
  change _ = ∑ w : (Σ k : Fin N, Fin k.val → Fin d), wordScalar w z • wordCoefficient f w
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro k hk
  rw [diagonal_eq_coordinate_words]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [wordScalar, wordCoefficient]
  exact smul_comm _ _ _

end Hironaka.Analytic.Unibranch.HironakaG10BanachTaylorCoordinates
