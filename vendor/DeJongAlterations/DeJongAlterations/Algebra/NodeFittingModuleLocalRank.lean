import DeJongAlterations.Algebra.NodeFittingModuleCyclic
import DeJongAlterations.Algebra.NodeFittingModuleBaseChange
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! # Actual local cotensor rank bounds force the entire original Fitting ideal to be the unit ideal -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFittingModule

open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

/-- A genuine local coefficient map reflects the ENTIRE unit ideal. -/
theorem ideal_eq_top_of_local_map_eq_top {R : Type u} {S : Type w}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (ρ : R →+* S) [IsLocalHom ρ] (J : Ideal R) (hJ : J.map ρ = ⊤) : J = ⊤ := by
  by_contra hn
  have hle := Ideal.map_mono (f := ρ) (IsLocalRing.le_maximalIdeal hn)
  rw [hJ] at hle
  exact (not_le_of_gt (IsLocalRing.map_maximalIdeal_lt_top ρ)) hle

/-- The actual native finite field basis gives the full unit ideal in every sufficient original degree. -/
theorem fittingIdeal_eq_top_of_field_finrank_le {K : Type w} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] [Module.FinitePresentation K V]
    (i : ℕ) (h : Module.finrank K V ≤ i) :
    fittingIdeal (R := K) (M := V) i = ⊤ :=
  fittingIdeal_eq_top_of_surjective (Module.finBasis K V).equivFun.symm.toLinearMap
    (Module.finBasis K V).equivFun.symm.surjective i h

/-- The actual local-field cotensor rank controls the ENTIRE original local Fitting ideal. -/
theorem fittingIdeal_eq_top_of_local_field_finrank_le
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (K : Type w) [Field K] [Algebra R K] [IsLocalHom (algebraMap R K)]
    (i : ℕ) (h : Module.finrank K (K ⊗[R] M) ≤ i) :
    fittingIdeal (R := R) (M := M) i = ⊤ := by
  apply ideal_eq_top_of_local_map_eq_top (algebraMap R K)
  rw [fittingIdeal_baseChange (R := R) (M := M) K i]
  exact fittingIdeal_eq_top_of_field_finrank_le i h

/-- In particular, the SAME actual native residue cotensor of rank at most one excludes the first Fitting locus. -/
theorem fittingIdeal_one_eq_top_of_residue_finrank_le_one
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]
    (h : Module.finrank (IsLocalRing.ResidueField R)
      ((IsLocalRing.ResidueField R) ⊗[R] M) ≤ 1) :
    fittingIdeal (R := R) (M := M) 1 = ⊤ := by
  let : IsLocalHom (algebraMap R (IsLocalRing.ResidueField R)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    infer_instance
  exact fittingIdeal_eq_top_of_local_field_finrank_le (IsLocalRing.ResidueField R) 1 h

end DeJongAlterations.Algebra.NodeFittingModule
