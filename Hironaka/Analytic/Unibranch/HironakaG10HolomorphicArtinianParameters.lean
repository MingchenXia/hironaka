import Hironaka.Analytic.Unibranch.HironakaG10FiniteLocalAlgebra
import Hironaka.Resolution.HironakaHolomorphicPointJets
import Mathlib.RingTheory.LocalRing.Quotient

/-! # Actual holomorphic point truncations are finite local parameter rings -/
set_option autoImplicit false
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10HolomorphicArtinianParameters
open Hironaka Hironaka
  HironakaHolomorphicPointJets
open Hironaka.Analytic.Unibranch.HironakaG10FiniteLocalAlgebra

/-- A proper actual holomorphic-germ truncation has a finite complex basis,
  is local, and has a nilpotent maximal ideal. -/
theorem truncated_germ_finite_local_nilpotent (n q : ℕ)
    (I : Ideal (HolGerm (ComplexModel n)))
    (hproper : I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ≠ ⊤) :
    let Q := HolGerm (ComplexModel n) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)
    ∃ (hlocal : IsLocalRing Q),
      letI := hlocal
      ∃ r : ℕ, Nonempty (Module.Basis (Fin r) ℂ Q) ∧
        ∃ k : ℕ, IsLocalRing.maximalIdeal Q ^ k = ⊥ := by
  let J := I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q
  let Q := HolGerm (ComplexModel n) ⧸ J
  letI : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hproper
  letI : IsLocalRing Q := IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  letI : FiniteDimensional ℂ Q := finiteDimensional_quotient_sup_maximalIdeal_pow n q I
  exact ⟨inferInstance,Module.finrank ℂ Q,⟨Module.finBasis ℂ Q⟩,maximalIdeal_nilpotent⟩

end Hironaka.Analytic.Unibranch.HironakaG10HolomorphicArtinianParameters
