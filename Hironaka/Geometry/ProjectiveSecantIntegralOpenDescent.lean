import Hironaka.Algebra.ProjectiveSecantIntegralOpenDescent
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Actual original nonempty principal parameter open below a specified integral scalar open
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace Hironaka.Geometry.ProjectiveSecant

universe u

/-- Integral contraction internally produces an actual nonempty original base principal open whose literal inverse image lies in the specified actual scalar open. -/
theorem exists_nonempty_base_principal_open_of_integral
    (R S : Type u) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [Algebra.IsIntegral R S]
    (O : (Spec (.of S)).Opens) (hO : (O : Set (Spec (.of S))).Nonempty) :
    ∃ a : R, a ≠ 0 ∧ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)).Nonempty ∧
      (Spec.map (CommRingCat.ofHom (algebraMap R S)) ⁻¹ᵁ PrimeSpectrum.basicOpen a) ≤ O := by
  obtain ⟨q, hq⟩ := hO
  obtain ⟨_, ⟨b, rfl⟩, hqb, hbO⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp O.isOpen q hq
  have hb : b ≠ 0 := by
    intro h
    exact hqb (h ▸ q.asIdeal.zero_mem)
  obtain ⟨a, ha, ham⟩ := Algebra.ProjectiveSecant.exists_nonzero_base_multiple_of_integral R S b hb
  refine ⟨a, ha, ⟨⊥, ?_⟩, ?_⟩
  · change a ∉ (⊥ : Ideal R)
    simpa only [Ideal.mem_bot] using ha
  · intro P hP
    apply hbO
    intro hbP
    change algebraMap R S a ∉ P.asIdeal at hP
    exact hP ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hbP)) ham)

end Hironaka.Geometry.ProjectiveSecant
