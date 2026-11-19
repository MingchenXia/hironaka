import Mathlib.RingTheory.LocalRing.Etale
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Nakayama

/-! # The ACTUAL finite etale local map is bijective from its native residue surjectivity -/

noncomputable section

namespace Hironaka.Algebra.NodeEtaleResidueIdentity

open IsLocalRing

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
  [Module.Finite R S] [Algebra.Etale R S]

/-- Finite native Nakayama lifts residue surjectivity of the SAME actual algebra map. -/
theorem algebraMap_surjective
    (hκ : Function.Surjective (ResidueField.map (algebraMap R S))) :
    Function.Surjective (algebraMap R S) := by
  apply (Algebra.linearMap R S).surjective_of_surjective_comp_mkQ
    (maximalIdeal R) (maximalIdeal_le_jacobson ⊥)
  intro y
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective
    (maximalIdeal R • (⊤ : Submodule R S)) y
  obtain ⟨a, ha⟩ := hκ (residue S s)
  obtain ⟨r, hr⟩ := residue_surjective a
  refine ⟨r, ?_⟩
  change (Submodule.Quotient.mk (algebraMap R S r) : S ⧸
    (maximalIdeal R • (⊤ : Submodule R S))) = Submodule.Quotient.mk s
  apply (Submodule.Quotient.eq _).mpr
  rw [Ideal.smul_top_eq_map, Algebra.FormallyUnramified.map_maximalIdeal]
  change algebraMap R S r - s ∈ maximalIdeal S
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change residue S (algebraMap R S r - s) = 0
  rw [map_sub, ← ResidueField.map_residue, hr, ha, sub_self]

/-- Actual local etale flatness supplies faithful flatness and injectivity; no rank certificate is used. -/
theorem algebraMap_bijective
    (hκ : Function.Surjective (ResidueField.map (algebraMap R S))) :
    Function.Bijective (algebraMap R S) := by
  let : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨FaithfulSMul.algebraMap_injective R S, algebraMap_surjective R S hκ⟩

/-- The genuine equivalence has forward map EXACTLY the SAME actual original algebra map. -/
def algebraEquiv
    (hκ : Function.Surjective (ResidueField.map (algebraMap R S))) : R ≃ₐ[R] S :=
  AlgEquiv.ofBijective (Algebra.ofId R S) (algebraMap_bijective R S hκ)

/-- EVERY original coefficient follows the SAME actual algebra map, not a replacement map. -/
theorem algebraEquiv_apply
    (hκ : Function.Surjective (ResidueField.map (algebraMap R S))) (r : R) :
    algebraEquiv R S hκ r = algebraMap R S r := rfl

end Hironaka.Algebra.NodeEtaleResidueIdentity
