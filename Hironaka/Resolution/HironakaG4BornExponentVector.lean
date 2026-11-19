import Hironaka.Resolution.HironakaG4WeightedBinomialStraightening

/-! Reindex the actual born-coordinate product by ambient coordinates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
namespace Hironaka.HironakaG4BornExponentVector
noncomputable section
open Hironaka.BlowupSequences

variable {n : ℕ} {ι : Type*}

/-- Record the sum of the exponents of all tracked members in each slot. -/
def coordinateExponent (T : Finset ι) (σ : ι → Fin n) (e : ι → ℕ) (b : Fin n) : ℕ :=
  ∑ i ∈ T, if σ i = b then e i else 0

/-- The indexed product equals the full-coordinate weighted monomial. -/
theorem indexed_product_eq_coordinate_monomial (T : Finset ι) (σ : ι → Fin n)
    (e : ι → ℕ) (z : ComplexModel n) :
    (∏ i ∈ T, z (σ i) ^ e i) = ∏ b : Fin n, z b ^ coordinateExponent T σ e b := by
  classical
  simp only [coordinateExponent, ← Finset.prod_pow_eq_pow_sum]
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Finset.prod_eq_single (σ i)]
  · simp
  · intro b hb hbne
    simp [Ne.symm hbne]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- A coordinate avoided by all tracked members has exponent zero. -/
theorem coordinateExponent_eq_zero_of_avoided (T : Finset ι) (σ : ι → Fin n)
    (e : ι → ℕ) (s : Fin n) (hs : ∀ i ∈ T, σ i ≠ s) :
    coordinateExponent T σ e s = 0 := by
  classical
  simp only [coordinateExponent]
  apply Finset.sum_eq_zero
  intro i hi
  simp [hs i hi]

end
end Hironaka.HironakaG4BornExponentVector
