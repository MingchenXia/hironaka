import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Regular.Basic

/-! An actual non-zero-divisor generator descends from a faithfully flat local extension. -/

noncomputable section

namespace DeJongAlterations.Algebra.FaithfullyFlatCartierEquation

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Module.FaithfullyFlat A B] [IsLocalRing B]

/-- An actual principal regular extended ideal INTERNALLY produces an original regular generator. -/
theorem exists_regular_generator (I : Ideal A) (b : B) (hb : IsRegular b)
    (hI : I.map (algebraMap A B) = Ideal.span {b}) :
    ∃ a ∈ I, IsRegular a ∧ I = Ideal.span {a} := by
  classical
  have hbmem : b ∈ Submodule.span B (Set.range fun a : I => algebraMap A B a) := by
    have himage : (algebraMap A B) '' (I : Set A) =
        Set.range (fun a : I => algebraMap A B a) := by
      ext z
      constructor
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, a.property, rfl⟩
    change b ∈ Ideal.span (Set.range fun a : I => algebraMap A B a)
    rw [← himage, ← Ideal.map, hI]
    exact Ideal.mem_span_singleton_self b
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp.mp hbmem)
  have hdiv (a : I) : ∃ d : B, algebraMap A B a = b * d := by
    have ha : algebraMap A B a ∈ Ideal.span {b} := by
      rw [← hI]
      exact Ideal.mem_map_of_mem _ a.property
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp ha
    exact ⟨d, hd⟩
  choose d hd using hdiv
  have hsum : (∑ a ∈ c.support, c a * d a) = 1 := by
    apply hb.left
    change b * (∑ a ∈ c.support, c a * d a) = b * 1
    rw [mul_one, Finset.mul_sum]
    calc
      (∑ a ∈ c.support, b * (c a * d a)) =
          ∑ a ∈ c.support, c a * algebraMap A B a := by
        apply Finset.sum_congr rfl
        intro a _
        rw [hd a]
        ring
      _ = b := by simpa only [Finsupp.sum, smul_eq_mul] using hc
  obtain ⟨a, _, haunit⟩ := IsLocalRing.exists_of_isUnit_sum (hsum ▸ isUnit_one)
  have hdunit : IsUnit (d a) := by
    obtain ⟨e, he⟩ := haunit.exists_right_inv
    exact IsUnit.of_mul_eq_one (c a * e) (by simpa only [mul_comm, mul_left_comm,
      mul_assoc] using he)
  have hmapreg : IsRegular (algebraMap A B a) := by
    rw [hd a]
    exact hb.mul hdunit.isRegular
  have hinj := FaithfulSMul.algebraMap_injective A B
  have hareg : IsRegular (a : A) := by
    constructor
    · intro x y hxy
      apply hinj
      apply hmapreg.left
      simpa only [← map_mul] using congrArg (algebraMap A B) hxy
    · intro x y hxy
      apply hinj
      apply hmapreg.right
      simpa only [← map_mul] using congrArg (algebraMap A B) hxy
  refine ⟨a, a.property, hareg, ?_⟩
  apply Ideal.map_injective_of_faithfullyFlat (A := A) (B := B)
  rw [hI, Ideal.map_span, Set.image_singleton, hd a,
    Ideal.span_singleton_mul_right_unit hdunit]

end DeJongAlterations.Algebra.FaithfullyFlatCartierEquation
