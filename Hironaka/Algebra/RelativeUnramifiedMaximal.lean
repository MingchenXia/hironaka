import Mathlib.RingTheory.Unramified.Locus

/-! # Formal unramifiedness detected at all original maximal ideals -/

noncomputable section

namespace Hironaka.Algebra.RelativeUnramified

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The whole original differential module vanishes if it vanishes at every maximal ideal. -/
theorem formallyUnramified_of_maximal
    (h : ∀ (m : Ideal A) [m.IsMaximal], Algebra.IsUnramifiedAt R m) :
    Algebra.FormallyUnramified R A := by
  rw [← Algebra.unramifiedLocus_eq_univ_iff, Algebra.unramifiedLocus_eq_compl_support]
  apply Set.eq_univ_iff_forall.mpr
  intro p hp
  obtain ⟨m, hm, hpm⟩ := p.asIdeal.exists_le_maximal p.isPrime.ne_top
  let : m.IsMaximal := hm
  have hmU : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∈ Algebra.unramifiedLocus R A := h m
  rw [Algebra.unramifiedLocus_eq_compl_support] at hmU
  exact hmU (Module.mem_support_mono hpm hp)

end Hironaka.Algebra.RelativeUnramified
