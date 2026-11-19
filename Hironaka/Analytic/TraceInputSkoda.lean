import Hironaka.Analytic.Copy4FixedDataFromInputs
import Hironaka.Analytic.SkodaIntegrability

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 input (I2): the Skoda clause from one point of `V` with zero Lelong number

Source: Copy-4, `sec:setup`, "The trace of `V_θ`"
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1405-1425`):

> Since `V ⊄ E_nn(α)`, choose `x_* ∈ V \ E_nn(α)`.  Then `ν(V_θ, x_*) = 0` by `sec:nK`. [...]
> By Skoda's theorem and `ν(V_θ, x_*) = 0`, `𝔅_q` and `𝔅̄_q` are unit ideals near `x_*`.

`Copy4FixedDataFromInputs.TraceInput` asks, for its potential `φ` (Copy-4: `V_θ`), the clause
`∀ q ≥ 1, V ⊄ Z(𝓘(qφ))`.  `SkodaIntegrability` proves Skoda's theorem, so that clause follows
from the existence of ONE point `x_* ∈ V` with `ν(φ, x_*) = 0`, which is exactly what Copy-4
uses.

* `TraceInputAtPoint` — `TraceInput` with the Skoda clause replaced by
  `∃ x_* ∈ V, ν(φ, x_*) = 0`; the subadditivity clause and `sec:positive-current` are unchanged.
* `traceInput_of_atPoint` — `TraceInputAtPoint → TraceInput` (Skoda).
* `exists_copy4StepOneData_of_inputs_atPoint` — `hRP` + (I1) + `TraceInputAtPoint` give the
  conclusion of `ct22Copy4_exists_stepOneData`.

Sorry-free.  No existing statement is changed.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.TraceInputSkoda

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  PrincipalizationCopy4StepFiveCoreReduction SubmanifoldChartedSpace IdealWeightPowers
  RestrictedIdealWeight PrincipalizationStepOneInterface Copy4FixedDataAssembly
  Copy4FixedDataFromInputs SkodaIntegrability

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **(I2) + (I3) with Copy-4's Skoda hypothesis**: `TraceInput` in which the clause
`∀ q ≥ 1, V ⊄ Z(𝓘(qφ))` is replaced by its source, a point `x_* ∈ V` with `ν(φ, x_*) = 0`
(Copy-4: `x_* ∈ V \ E_nn(α)`, `φ = V_θ`). -/
def TraceInputAtPoint [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) : Prop :=
  ∃ φ : X → EReal, IsThetaPshPotential θ.val φ ∧
    (∃ x ∈ V.carrier, lelongNumber (n := n) φ x = 0) ∧
    (∀ q k : ℕ, 1 ≤ q → (multiplierIdeal (n := n) ((q * k : ℕ) : ℝ) φ).Le
        (idealPow (multiplierIdeal (n := n) (q : ℝ) φ) k)) ∧
    ∀ C : ℕ, 2 ≤ C → ∃ m : ℕ, 1 ≤ m ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧ 1 ≤ r ∧
        ∃ (idealB : GermIdeal n X) (ψB : X → EReal) (φK : V.carrier → EReal),
          idealB.IsCoherent ∧ ¬ V.carrier ⊆ idealB.zeroLocus ∧
          HasAnalyticSingularitiesOfType (n := n) ψB 1 idealB ∧
          RestrictLe V.carrier
            (idealB.mul (idealPow (multiplierIdeal (n := n) (m : ℝ) φ) ((C - 1) * r)))
            (multiplierIdeal (n := n) ((C * m * r : ℕ) : ℝ) φ) ∧
          IsLevelPotential omega θ V hV δ₀ φK ∧
          SameSingularityTypeOn φK
            (fun v => ((1 / ((m * r : ℕ) : ℝ) : ℝ) : EReal) * ψB v.1) univ

/-- **Skoda's theorem supplies the Skoda clause of (I2).** -/
theorem traceInput_of_atPoint [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (h : TraceInputAtPoint omega θ V hV) : TraceInput omega θ V hV := by
  obtain ⟨φ, hφ, ⟨x, hxV, hν⟩, hsub, hqea⟩ := h
  exact ⟨φ, hφ, not_subset_zeroLocus_multiplierIdeal_of_lelongNumber_eq_zero hφ.1 hxV hν,
    hsub, hqea⟩

/-- **The conclusion of `ct22Copy4_exists_stepOneData` from `lem:relative-principalization`,
(I1) and (I2)+(I3) with Copy-4's Skoda hypothesis** (one point of `V` where `ν(φ, ·) = 0`). -/
theorem exists_copy4StepOneData_of_inputs_atPoint (hRP : RelativePrincipalizationHolds.{u} n)
    [CompactSpace X] [ConnectedSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n) (hI1 : AmbientFixedInput omega θ V)
    (hI2 : TraceInputAtPoint omega θ V hV) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π)
      (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim),
      Nonempty (Copy4StepOneData omega θ hπ.isBlowupSequence V hW) :=
  exists_copy4StepOneData_of_inputs hRP omega θ V hV hdim_pos hdim_lt hI1
    (traceInput_of_atPoint omega θ V hV hI2)

end

end Hironaka.TraceInputSkoda
