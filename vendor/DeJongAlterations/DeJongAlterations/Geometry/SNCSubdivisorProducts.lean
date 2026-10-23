import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Associated

/-!
# Products of actual distinct prime component equations

Only divisibility by the actual prime equations is used. No UFD or
decomposition-monoid structure on the ambient local domain is required.
-/

noncomputable section

namespace DeJongAlterations.Geometry.SNCSubdivisorProducts

variable {R ι : Type*} [CommRing R]

/-- Distinct actual prime factors divide simultaneously precisely by their product. -/
theorem prod_dvd_of_prime
    (F : Finset ι) (a : ι → R)
    (hprime : ∀ i ∈ F, Prime (a i))
    (hdist : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ¬ a i ∣ a j)
    (x : R) (hx : ∀ i ∈ F, a i ∣ x) : (∏ i ∈ F, a i) ∣ x := by
  classical
  induction F using Finset.induction_on generalizing x with
  | empty => simp
  | @insert i F hi ih =>
    obtain ⟨y, hy⟩ := hx i (Finset.mem_insert_self _ _)
    rw [Finset.prod_insert hi, hy]
    apply mul_dvd_mul_left
    apply ih
    · exact fun j hj ↦ hprime j (Finset.mem_insert_of_mem hj)
    · exact fun j hj k hk hjk ↦
        hdist j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk
    · intro j hj
      have hjx : a j ∣ a i * y := hy ▸ hx j (Finset.mem_insert_of_mem hj)
      apply ((hprime j (Finset.mem_insert_of_mem hj)).dvd_mul.mp hjx).resolve_left
      apply hdist j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self _ _)
      intro hji
      exact hi (hji ▸ hj)

/-- The actual intersection of distinct principal prime component ideals is their product equation. -/
theorem finset_inf_span_singleton_of_prime
    (F : Finset ι) (a : ι → R)
    (hprime : ∀ i ∈ F, Prime (a i))
    (hdist : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → ¬ a i ∣ a j) :
    (F.inf fun i ↦ Ideal.span {a i}) = Ideal.span {∏ i ∈ F, a i} := by
  classical
  ext x
  simp only [Submodule.mem_finsetInf, Ideal.mem_span_singleton]
  exact ⟨prod_dvd_of_prime F a hprime hdist x,
    fun h i hi ↦ (Finset.dvd_prod_of_mem a hi).trans h⟩

end DeJongAlterations.Geometry.SNCSubdivisorProducts
