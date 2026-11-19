import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ClosedFormPullback
import Hironaka.Blowup.ExceptionalMetricProof

set_option autoImplicit false

/-!
# Exceptional correction of a pulled-back Kähler form

Source: Copy-4, `lem:exceptional-metric` (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:exceptional-metric`.

Let `(X, ω)` be a compact Kähler manifold and `π : Y → X` a composition of
blowups with smooth centers.  There is an effective `π`-exceptional
`ℚ`-divisor `E` on `Y` with a smooth Hermitian metric on `𝒪_Y(E)` such that
`π^* ω - Θ_E` is a Kähler form.  If `π` is an isomorphism, one may take `E = 0`.

Encoding notes.  `E` with its metric is a `MeteredEffectiveQDivisor`; exceptional
means `supp E ⊆ Exc π`; `E = 0` means `supp E = ∅`.  The single statement
`∃ E, … ∧ (π iso → supp E = ∅)` is equivalent to the manuscript's two
assertions: when `π` is an isomorphism use the `E = 0` witness, otherwise the
general one.

PROVED (sorry-free) in `Hironaka.ExceptionalMetricProof`: induction over the sequence, adding at
each blowup a small rational multiple of the Blanchard divisor of its exceptional centre.
-/

open Set

universe u

namespace Hironaka.ExceptionalMetric

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **Exceptional correction of a pulled-back Kähler form**
(Copy-4, `lem:exceptional-metric`). -/
theorem exists_exceptionalMetric [CompactSpace X] (omega : KahlerBackground n X)
    (π : Y → X) (hπ : IsBlowupSequence n X Y π) :
    ∃ E : MeteredEffectiveQDivisor n Y,
      E.support ⊆ exceptionalLocus n π ∧
      (ClosedRealOneOneForm.pullback hπ.contMDiff omega.form - E.curvature).val.IsKahler ∧
      (IsIsomorphismOver n π univ → E.support = ∅) :=
  ExceptionalMetricProof.exists_exceptionalMetric omega π hπ

end

end Hironaka.ExceptionalMetric
