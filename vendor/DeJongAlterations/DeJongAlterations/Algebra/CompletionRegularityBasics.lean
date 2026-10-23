import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! Faithfulness and the exact original residue/ideal maps of literal local completion. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.CompletionRegularityBasics

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The literal maximal-adic completion of the original local ring. -/
abbrev Completion := AdicCompletion (maximalIdeal R) R

/-- The actual original coefficient algebra of local completion is faithfully flat. -/
theorem faithfullyFlat : Module.FaithfullyFlat R (Completion R) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The literal original completion map is injective. -/
theorem algebraMap_injective : Function.Injective (algebraMap R (Completion R)) := by
  let : Module.FaithfullyFlat R (Completion R) := faithfullyFlat R
  exact FaithfulSMul.algebraMap_injective R (Completion R)

/-- The actual local completion map preserves and reflects every original ideal after extension. -/
theorem comap_map (I : Ideal R) :
    (I.map (algebraMap R (Completion R))).comap (algebraMap R (Completion R)) = I := by
  let : Module.FaithfullyFlat R (Completion R) := faithfullyFlat R
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I

/-- The original coefficient lies in the completed maximal square exactly when it lay in the original square. -/
theorem mem_maximalIdeal_sq_iff (t : R) :
    algebraMap R (Completion R) t ∈ maximalIdeal (Completion R) ^ 2 ↔ t ∈ maximalIdeal R ^ 2 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow]
  change t ∈ ((maximalIdeal R ^ 2).map (algebraMap R (Completion R))).comap
    (algebraMap R (Completion R)) ↔ _
  rw [comap_map R]

/-- The actual induced residue-field map of original local completion is bijective. -/
theorem residueField_map_bijective :
    Function.Bijective (ResidueField.map (algebraMap R (Completion R))) :=
  AdicCompletion.residueField_map_bijective R

/-- The canonical original residue-field isomorphism, with forward map the literal induced map. -/
def residueFieldEquiv : ResidueField R ≃+* ResidueField (Completion R) :=
  RingEquiv.ofBijective (ResidueField.map (algebraMap R (Completion R))) (residueField_map_bijective R)

/-- Its forward map is the actual residue-field map of the original completion algebra. -/
theorem residueFieldEquiv_apply (x : ResidueField R) :
    residueFieldEquiv R x = ResidueField.map (algebraMap R (Completion R)) x := rfl

end DeJongAlterations.Algebra.CompletionRegularityBasics
