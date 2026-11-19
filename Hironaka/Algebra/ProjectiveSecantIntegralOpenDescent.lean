import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Actual integral principal-ideal contraction produces a nonzero original base element
-/

noncomputable section

namespace Hironaka.Algebra.ProjectiveSecant

universe u v

/-- The actual original principal ideal internally supplies a nonzero original base element in that same ideal. -/
theorem exists_nonzero_base_multiple_of_integral
    (R : Type u) [CommRing R] [Nontrivial R] (S : Type v) [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S] (b : S) (hb : b ≠ 0) :
    ∃ a : R, a ≠ 0 ∧ algebraMap R S a ∈ Ideal.span ({b} : Set S) := by
  have hI : Ideal.span ({b} : Set S) ≠ ⊥ := by
    intro h
    have hm : b ∈ Ideal.span ({b} : Set S) := Ideal.subset_span (Set.mem_singleton b)
    rw [h, Ideal.mem_bot] at hm
    exact hb hm
  obtain ⟨a, ha, hne⟩ :=
    ((Ideal.span ({b} : Set S)).comap (algebraMap R S)).ne_bot_iff.mp
      (Ideal.IsIntegral.comap_ne_bot R hI)
  exact ⟨a, hne, ha⟩

end Hironaka.Algebra.ProjectiveSecant
