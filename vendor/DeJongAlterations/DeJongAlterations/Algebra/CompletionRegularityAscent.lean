import DeJongAlterations.Algebra.NoetherianCompletion
import DeJongAlterations.Algebra.CompletionRegularity

/-! Regularity ascends to the literal maximal-adic completion of the original ring. -/

noncomputable section

open IsLocalRing

namespace DeJongAlterations.Algebra.CompletionRegularityAscent

open CompletionRegularityBasics

universe u

/-- The actual flat local completion map cannot decrease the original Krull dimension. -/
theorem ringKrullDim_le_completion (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim R ≤ ringKrullDim (Completion R) := by
  let P : Ideal (Completion R) := maximalIdeal (Completion R)
  have hheight : (P.under R).height ≤ P.height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under R) P]
    exact le_self_add
  have hunder : P.under R = maximalIdeal R :=
    IsLocalRing.maximalIdeal_comap (algebraMap R (Completion R))
  rw [hunder] at hheight
  rw [← maximalIdeal_height_eq_ringKrullDim (R := R),
    ← maximalIdeal_height_eq_ringKrullDim (R := Completion R)]
  exact_mod_cast hheight

/-- Regularity of the original ring implies regularity of its literal native completion.
No completed Noetherianity or regularity is assumed: both are derived internally. -/
theorem isRegularLocalRing_completion (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing (Completion R) := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [AdicCompletion.spanFinrank_maximalIdeal_eq,
    (isRegularLocalRing_iff R).mp inferInstance]
  exact ringKrullDim_le_completion R

/-- Regularity of an original Noetherian local ring is equivalent to regularity of its
literal maximal-adic completion, with the original completion algebra retained. -/
theorem isRegularLocalRing_iff_completion (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsRegularLocalRing R ↔ IsRegularLocalRing (Completion R) := by
  constructor
  · intro h
    let : IsRegularLocalRing R := h
    exact isRegularLocalRing_completion R
  · intro h
    let : IsRegularLocalRing (Completion R) := h
    exact CompletionRegularity.isRegularLocalRing_of_completion R

end DeJongAlterations.Algebra.CompletionRegularityAscent
