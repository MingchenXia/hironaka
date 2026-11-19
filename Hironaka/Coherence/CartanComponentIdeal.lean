import Hironaka.Analytic.Copy4TraceInputReduction
import Hironaka.Analytic.IrreducibleComponentFilling
import Hironaka.Analytic.ClosureDifferenceAnalytic
import Hironaka.Analytic.NonKahlerLocusPoleSet
import Hironaka.Coherence.CartanCoherenceDef

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The ideal `𝔧 = 𝓘_{Z'}` of the other components, from Cartan's coherence theorem

Source: Copy-4, `sec:fixed-data` (`references/transcendental-nakamaye-copy4-20260911/source/
main-Nulllocus.tex:1503-1515`): "Let `Z'` be the union of the irreducible components of `E_nK(α)`
other than `V`, and put `𝔧 := 𝓘_{Z'}`".

`AmbientFixedInputProducer.ambientFixedInput_of_cover` takes a coherent `𝔧` with
`E_nK(α) ⊆ V ∪ Z(𝔧)` and `V ⊄ Z(𝔧)`.  Here `Z' = closure (E_nK(α) \ V)` (analytic:
`ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff`) and `𝔧 = vanishingIdeal Z'`:

* `subset_union_zeroLocus_vanishingIdeal_closure_diff` — `A ⊆ V ∪ Z(𝓘_{closure (A \ V)})`, for
  any sets;
* `not_subset_zeroLocus_vanishingIdeal_closure_diff` — `V ⊄ Z(𝓘_{closure (A \ V)})` when `V` is an
  irreducible component of the analytic set `A`: some open `U` meets `V` with `A ∩ U ⊆ V`
  (`IrreducibleComponentFilling.exists_isOpen_inter_subset`), so `1 ∈ 𝓘_{Z'}` at a point of
  `V ∩ U`;
* `exists_copy4StepOneData_of_cartan_positiveCurrentInput` — the conclusion of
  `ct22Copy4_exists_stepOneData` from its own hypotheses, `hRP` (relative principalization,
  proved as `PrincipalizationStepOneInterface.relativePrincipalizationHolds`), the
  coherence of `𝓘_{Z'}` for the one analytic set `Z' = closure (E_nK(α) \ V)` (Cartan's theorem,
  H. Cartan 1950; Grauert--Remmert, *Coherent analytic sheaves*, Ch. 4 §2), and
  `PositiveCurrentInput` (`sec:positive-current`, proved as
  `PositiveCurrentInputInterface.ct22Copy4_positiveCurrentInput`);
* `CartanCoherence`, `exists_copy4StepOneData_of_cartanCoherence` — the same with Cartan's
  theorem for all analytic subsets as the hypothesis (Cartan's theorem is proved as
  `CartanIrreducible.cartanCoherence`).

`CartanCoherence` itself lives in `Hironaka.CartanCoherenceDef`, which this module imports and so
re-exports: same namespace, name and body.  It was moved there so that the proof of Cartan's theorem
does not import this module's closure.

Sorry-free.  No existing statement is changed.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.CartanComponentIdeal

noncomputable section

open Hironaka.PositiveClasses Hironaka.HolomorphicIdealSheaves
  Hironaka.GlobalAnalyticSingularities Hironaka.NonKahlerLocus Hironaka.BlowupSequences
  PrincipalizationCopy4StepFiveCoreReduction SubmanifoldChartedSpace
  PrincipalizationStepOneInterface Copy4FixedDataAssembly Copy4TraceInputReduction

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Points of `Z` lie in the zero locus of `𝓘_Z`. -/
theorem subset_zeroLocus_vanishingIdeal (Z : Set X) :
    Z ⊆ (vanishingIdeal (n := n) Z).zeroLocus := fun _ hx _ hg =>
  hg.2.self_of_nhds hx

/-- `A ⊆ V ∪ Z(𝓘_{closure (A \ V)})`. -/
theorem subset_union_zeroLocus_vanishingIdeal_closure_diff (A V : Set X) :
    A ⊆ V ∪ (vanishingIdeal (n := n) (closure (A \ V))).zeroLocus := by
  intro x hx
  by_cases hxV : x ∈ V
  · exact Or.inl hxV
  · exact Or.inr (subset_zeroLocus_vanishingIdeal _ (subset_closure ⟨hx, hxV⟩))

/-- **An irreducible component is not contained in the other components**:
`V ⊄ Z(𝓘_{closure (A \ V)})` for an irreducible component `V` of an analytic set `A`. -/
theorem not_subset_zeroLocus_vanishingIdeal_closure_diff {A : Set X}
    (hA : IsComplexAnalyticSubset (n := n) A) {V : ClosedIrreducibleAnalyticSubvariety n X}
    (hV : IsIrreducibleComponent V A) :
    ¬ V.carrier ⊆ (vanishingIdeal (n := n) (closure (A \ V.carrier))).zeroLocus := by
  obtain ⟨U, hU, ⟨v, hvV, hvU⟩, hAU⟩ :=
    IrreducibleComponentFilling.exists_isOpen_inter_subset hA hV
  have hdisj : ∀ y ∈ U, y ∉ closure (A \ V.carrier) := by
    intro y hyU hy
    obtain ⟨z, hzU, hzA, hzV⟩ := mem_closure_iff.mp hy U hU hyU
    exact hzV (hAU ⟨hzA, hzU⟩)
  intro hsub
  have h1 : (vanishingIdeal (n := n) (closure (A \ V.carrier))).mem v (fun _ => (1 : ℂ)) :=
    ⟨holomorphicAt_const 1, Filter.eventually_of_mem (hU.mem_nhds hvU) fun y hyU hy =>
      absurd hy (hdisj y hyU)⟩
  exact one_ne_zero (hsub hvV _ h1)

/-- **The conclusion of `ct22Copy4_exists_stepOneData` from its own hypotheses, `hRP`, Cartan's
coherence of `𝓘_{Z'}` for `Z' = closure (E_nK(α) \ V)`, and `sec:positive-current`.** -/
theorem exists_copy4StepOneData_of_cartan_positiveCurrentInput
    (hRP : RelativePrincipalizationHolds.{u} n)
    [CompactSpace X] [ConnectedSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n)
    (hcomponent :
      IsIrreducibleComponent V (nonKahlerLocus (RealBottChern.ofRepresentative θ)))
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hCartan : (vanishingIdeal (n := n)
      (closure (nonKahlerLocus (RealBottChern.ofRepresentative θ) \ V.carrier))).IsCoherent)
    (hI3 : PositiveCurrentInput omega θ V hV) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π)
      (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim),
      Nonempty (Copy4StepOneData omega θ hπ.isBlowupSequence V hW) := by
  have hA : IsComplexAnalyticSubset (n := n) (nonKahlerLocus (RealBottChern.ofRepresentative θ)) :=
    NonKahlerLocusPoleSet.isComplexAnalyticSubset_nonKahlerLocus (hdim_pos.trans hdim_lt) _ hbig
  exact exists_copy4StepOneData_of_cover_positiveCurrentInput hRP omega θ hbig V hV hdim_pos
    hdim_lt hnonNef hCartan (subset_union_zeroLocus_vanishingIdeal_closure_diff _ _)
    (not_subset_zeroLocus_vanishingIdeal_closure_diff hA hcomponent) hI3

/-- **The same from Cartan's theorem for all analytic subsets.** -/
theorem exists_copy4StepOneData_of_cartanCoherence
    (hRP : RelativePrincipalizationHolds.{u} n) (hCartan : CartanCoherence n X)
    [CompactSpace X] [ConnectedSpace X] (omega : KahlerBackground n X)
    (θ : ClosedRealOneOneForm n X) (hbig : IsBigClass (RealBottChern.ofRepresentative θ))
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : IsClosedConnectedSubmanifold n V.carrier V.dim) (hdim_pos : 0 < V.dim)
    (hdim_lt : V.dim < n)
    (hcomponent :
      IsIrreducibleComponent V (nonKahlerLocus (RealBottChern.ofRepresentative θ)))
    (hnonNef : ¬ V.carrier ⊆ nonNefLocus omega (RealBottChern.ofRepresentative θ))
    (hI3 : PositiveCurrentInput omega θ V hV) :
    ∃ (Y : Type u) (_ : TopologicalSpace Y) (_ : ChartedSpace (ComplexModel n) Y)
      (_ : IsComplexManifold n Y) (π : Y → X)
      (hπ : IsAdaptedBlowupSequence n X V.carrier Y π)
      (hW : IsClosedConnectedSubmanifold n (strictTransform n π V.carrier) V.dim),
      Nonempty (Copy4StepOneData omega θ hπ.isBlowupSequence V hW) := by
  have hA : IsComplexAnalyticSubset (n := n) (nonKahlerLocus (RealBottChern.ofRepresentative θ)) :=
    NonKahlerLocusPoleSet.isComplexAnalyticSubset_nonKahlerLocus (hdim_pos.trans hdim_lt) _ hbig
  exact exists_copy4StepOneData_of_cartan_positiveCurrentInput hRP omega θ hbig V hV hdim_pos
    hdim_lt hcomponent hnonNef
    (hCartan _ (ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff hA V.analytic)) hI3

end

end Hironaka.CartanComponentIdeal
