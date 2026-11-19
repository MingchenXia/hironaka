import Hironaka.Analytic.SingularLocus
import Hironaka.Analytic.BoucksomMinimalMultiplicityProof

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Boucksom's minimal multiplicities

Source: S. Boucksom, *Divisorial Zariski decompositions on compact complex manifolds*,
Ann. Sci. ÉNS 37 (2004), Section 3 (the minimal multiplicity `ν(α, x)` of a pseudoeffective
class and its relation to the non-nef locus); quoted by CT22 in Section 2 and used in the proof
of Lemma 4.2.

For a pseudoeffective class `α` on a compact Kähler manifold `(Y, ω)` Boucksom sets
`ν(α, x) = lim_{t ↓ 0} inf { ν(T, x) : T ≥ 0 closed in α + t{ω} }`, and
`E_nn(α) = { x : ν(α, x) > 0 }`.  The content recorded here is the direction that the
`⋃_{t>0} E_nK(α + t{ω})` definition used in this development does not give for free:
membership of `E_nn(α)` yields a lower bound on the Lelong number at `x` that is **uniform in
the current**, for all sufficiently small perturbation parameters at once.  It is exactly this
uniformity that beats the loss of Lelong number incurred when a Kähler current upstairs is
corrected back into a pullback class across an exceptional divisor.

Human decision I-0154 allowed this as a named interface (TN-CLASSICAL).  It is no
longer one: the statement is **PROVED** in
`Hironaka.BoucksomMinimalMultiplicityProof.exists_uniform_lelongNumber_lowerBound_of_mem_nonNefLocus`
and the theorem below is a one-line appeal to it.  The uniform constant is the
Lelong number at `x` of the minimal-singularity potential `V_Θ` of one Kähler
current's representative `Θ` in `α + (2ε/3){ω}`: every Kähler current in
`α + t{ω}` with `t ≤ ε/3` is, after a Kähler shift and a smooth change of
representative, a competitor for that envelope, and `V_Θ` itself is a Kähler
current potential in `α + ε{ω}`, where membership of `E_nK` makes its Lelong
number positive.

No module in the root import closure imports this file.
-/

open Set
open scoped ENNReal

namespace Hironaka.BoucksomMinimalMultiplicity

open Hironaka.PositiveClasses Hironaka.NonKahlerLocus

noncomputable section

variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- **PROVED** (Boucksom, minimal multiplicities).  A point of the non-nef
locus admits a positive lower bound for the Lelong number at that point, uniform over all
Kähler currents in all sufficiently small perturbations of the class. -/
theorem exists_uniform_lelongNumber_lowerBound_of_mem_nonNefLocus [CompactSpace Y]
    (omega : KahlerBackground n Y) (alpha : RealBottChern n Y) {y : Y}
    (hy : y ∈ nonNefLocus omega alpha) :
    ∃ c : ℝ≥0∞, 0 < c ∧ ∃ t₀ : ℝ, 0 < t₀ ∧
      ∀ t : ℝ, 0 < t → t ≤ t₀ →
        ∀ T : KahlerCurrent (alpha + t • RealBottChern.ofRepresentative omega.form),
          c ≤ lelongNumber (n := n) T.potential y :=
  BoucksomMinimalMultiplicityProof.exists_uniform_lelongNumber_lowerBound_of_mem_nonNefLocus
    omega alpha hy

end

end Hironaka.BoucksomMinimalMultiplicity
