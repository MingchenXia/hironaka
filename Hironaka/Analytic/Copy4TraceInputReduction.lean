import Hironaka.Analytic.MultiplierSubadditivity
import Hironaka.Analytic.MinimalSingularityLelongVanishing
import Hironaka.Analytic.AmbientFixedInputProducer

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Copy-4 input (I2): only `sec:positive-current` remains

Source: Copy-4, `sec:setup`, "The trace of `V_θ`", and `sec:positive-current`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1398-1425`).

`Copy4FixedDataFromInputs.TraceInput` (input (I2)+(I3) of `ct22Copy4_exists_stepOneData`) asks for
a `θ`-psh potential `φ` (Copy-4: `V_θ`) with three properties.  Two of them are now theorems:

* the Skoda clause `∀ q ≥ 1, V ⊄ Z(𝓘(qφ))`: from `x_* ∈ V \ E_nn(α)`,
  `ν(V_θ, x_*) = 0` (`MinimalSingularityLelongVanishing.lelongNumber_thetaPshSupremum_eq_zero`) and
  Skoda's theorem (`SkodaIntegrability`, via `TraceInputSkoda.traceInput_of_atPoint`);
* the subadditivity clause `𝓘(qkφ) ⊆ 𝓘(qφ)^k` (`MultiplierSubadditivity`, DEL00).

What remains is the third clause, `sec:positive-current` for `φ = V_θ` (the quasi-equisingular
approximation of `V_θ`, which waits): `PositiveCurrentInput`.

* `traceInputAtPointNoSub_of_positiveCurrentInput` — bigness, `V ⊄ E_nn(α)` and
  `PositiveCurrentInput` give `MultiplierSubadditivity.TraceInputAtPointNoSub` with `φ = V_θ`.
* `exists_copy4StepOneData_of_positiveCurrentInput` — the conclusion of
  `ct22Copy4_exists_stepOneData` from `lem:relative-principalization` (`hRP`), (I1), bigness,
  `V ⊄ E_nn(α)` and `PositiveCurrentInput`.
* `exists_copy4StepOneData_of_cover_positiveCurrentInput` — the same with (I1) replaced by its
  proved producer `AmbientFixedInputProducer.ambientFixedInput_of_cover`: the inputs are `hRP`
  (Hironaka; on the route `RelativePrincipalization.exists_factorizationData`, proved in place from the canonical resolution invariant),
  a coherent `𝔧` with `E_nK(α) ⊆ V ∪ Z(𝔧)` and `V ⊄ Z(𝔧)` (Cartan coherence of `𝓘_{Z'}`), and
  `PositiveCurrentInput` (QEA; `PositiveCurrentInputInterface.ct22Copy4_positiveCurrentInput`, since proved).  Every other hypothesis is one
  of `ct22Copy4_exists_stepOneData`'s own.

Sorry-free.  No existing statement is changed.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.Copy4TraceInputReduction

noncomputable section

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  PrincipalizationCopy4StepFiveCoreReduction SubmanifoldChartedSpace IdealWeightPowers
  RestrictedIdealWeight PrincipalizationStepOneInterface Copy4FixedDataAssembly
  Copy4FixedDataFromInputs TraceInputSkoda MultiplierSubadditivity
  MinimalSingularityLelongVanishing AmbientFixedInputProducer

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **(I3), Copy-4 `sec:positive-current`, for `φ = V_θ`**: the last clause of
`Copy4FixedDataFromInputs.TraceInput` with its potential fixed to the minimal-singularity potential
`V_θ = thetaPshSupremum θ` (Copy-4: the quasi-equisingular approximation `φ_{K,ℓ}` of `V_θ` and the
ideals `𝔅_q = 𝓘(qV_θ)`). -/
def PositiveCurrentInput [CompactSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) : Prop :=
  ∀ C : ℕ, 2 ≤ C → ∃ m : ℕ, 1 ≤ m ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ N : ℕ, ∃ r : ℕ, N ≤ r ∧ 1 ≤ r ∧
      ∃ (idealB : GermIdeal n X) (ψB : X → EReal) (φK : V.carrier → EReal),
        idealB.IsCoherent ∧ ¬ V.carrier ⊆ idealB.zeroLocus ∧
        HasAnalyticSingularitiesOfType (n := n) ψB 1 idealB ∧
        RestrictLe V.carrier
          (idealB.mul (idealPow (multiplierIdeal (n := n) (m : ℝ) (thetaPshSupremum θ.val))
            ((C - 1) * r)))
          (multiplierIdeal (n := n) ((C * m * r : ℕ) : ℝ) (thetaPshSupremum θ.val)) ∧
        IsLevelPotential omega θ V hV δ₀ φK ∧
        SameSingularityTypeOn φK
          (fun v => ((1 / ((m * r : ℕ) : ℝ) : ℝ) : EReal) * ψB v.1) univ

/-- **The Skoda clause and the subadditivity clause of (I2) are theorems**: bigness and
`V ⊄ E_nn(α)` turn `PositiveCurrentInput` into `TraceInputAtPointNoSub` with `φ = V_θ`. -/
theorem traceInputAtPointNoSub_of_positiveCurrentInput [CompactSpace X] (hn : 0 < n)
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hI3 : PositiveCurrentInput omega θ V hV) : TraceInputAtPointNoSub omega θ V hV := by
  obtain ⟨x, hxV, hxnn⟩ := not_subset.mp hnonNef
  have : Nonempty X := ⟨x⟩
  exact ⟨thetaPshSupremum θ.val, isThetaPshPotential_thetaPshSupremum θ hbig,
    ⟨x, hxV, lelongNumber_thetaPshSupremum_eq_zero hn omega θ hbig hxnn⟩, hI3⟩

/-- **(I2)+(I3) from `sec:positive-current` alone.** -/
theorem traceInput_of_positiveCurrentInput [CompactSpace X] (hn : 0 < n)
    (omega : KahlerBackground n X) (θ : ClosedRealOneOneForm n X)
    (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim)
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hI3 : PositiveCurrentInput omega θ V hV) : TraceInput omega θ V hV :=
  traceInput_of_atPoint omega θ V hV (traceInputAtPoint_of_noSub hn omega θ V hV
    (traceInputAtPointNoSub_of_positiveCurrentInput hn omega θ hbig V hV hnonNef hI3))

/-- **The conclusion of `ct22Copy4_exists_stepOneData` from `hRP`, (I1), bigness,
`V ⊄ E_nn(α)` and `sec:positive-current`.** -/
theorem exists_copy4StepOneData_of_positiveCurrentInput
    (hRP : RelativePrincipalizationHolds.{u} n)
    [CompactSpace X] [ConnectedSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n)
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hI1 : AmbientFixedInput omega θ V) (hI3 : PositiveCurrentInput omega θ V hV) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π)
      (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim),
      Nonempty (Copy4StepOneData omega θ hπ.isBlowupSequence V hW) :=
  exists_copy4StepOneData_of_inputs hRP omega θ V hV hdim_pos hdim_lt hI1
    (traceInput_of_positiveCurrentInput (hdim_pos.trans hdim_lt) omega θ hbig V hV hnonNef hI3)

/-- **The conclusion of `ct22Copy4_exists_stepOneData` from `hRP`, Cartan's `𝔧` and
`sec:positive-current`**; every other hypothesis is one of `ct22Copy4_exists_stepOneData`'s own
(bigness, `0 < dim V < n`, `V ⊄ E_nn(α)`). -/
theorem exists_copy4StepOneData_of_cover_positiveCurrentInput
    (hRP : RelativePrincipalizationHolds.{u} n)
    [CompactSpace X] [ConnectedSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n)
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    {𝔧 : GermIdeal n X} (h𝔧 : 𝔧.IsCoherent)
    (hcover : nonKahlerLocus (RealBottChern.ofRepresentative θ) ⊆ V.carrier ∪ 𝔧.zeroLocus)
    (hV𝔧 : ¬ V.carrier ⊆ 𝔧.zeroLocus) (hI3 : PositiveCurrentInput omega θ V hV) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π)
      (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim),
      Nonempty (Copy4StepOneData omega θ hπ.isBlowupSequence V hW) :=
  exists_copy4StepOneData_of_cover hRP omega θ hbig V hV hdim_pos hdim_lt h𝔧 hcover hV𝔧
    (traceInput_of_positiveCurrentInput (hdim_pos.trans hdim_lt) omega θ hbig V hV hnonNef hI3)

end

end Hironaka.Copy4TraceInputReduction
