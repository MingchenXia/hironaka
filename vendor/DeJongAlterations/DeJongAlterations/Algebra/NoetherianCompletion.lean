import DeJongAlterations.Algebra.NoetherianCompletionEvaluation
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-! Noetherianity of the literal maximal-adic completion, from actual complete evaluation. -/

noncomputable section

namespace DeJongAlterations.Algebra.NoetherianCompletion

open IsLocalRing CompletionRegularityBasics NoetherianCompletionEvaluation

universe u

/-- The literal completion of an original Noetherian local ring is Noetherian.
The proof constructs its actual formal-series presentation internally. -/
instance isNoetherianRing_completion (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    IsNoetherianRing (AdicCompletion (maximalIdeal R) R) :=
  isNoetherianRing_of_surjective (MvPowerSeries (generatorSet R) R) (Completion R)
    (completionEvaluation R).toRingHom (completionEvaluation_surjective R)

end DeJongAlterations.Algebra.NoetherianCompletion
