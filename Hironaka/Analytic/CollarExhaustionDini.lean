import Hironaka.Analytic.CompactCollarCutoff
import Hironaka.Analytic.ThetaCapacityDecreasingConvergence
import Hironaka.Analytic.SmoothOffPole

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The exhaustion and the Dini step of the collar construction

Two ingredients of CT22 Lemma 4.3, Step 3 (node `695c24b3e585`, comment-3,
items 4 and 5) that are independent of the current-theoretic content.

## The exhaustion

The collar construction glues on an increasing family of compacta exhausting the
open set `U` where `ψ` is finite and chart-smooth, and each compactum comes with
two open collars around it.  What the construction actually consumes is weaker
than a `CompactExhaustion`: since the family is monotone with union `U`, every
point of `U` lies in `K m` for all large `m`, and `K m ⊆ N m` where the cut-off
vanishes.  So `K m ⊆ interior (K (m+1))` is never needed.

## The Dini step

To choose the index `k_m` of the regularization the construction needs
`sup_{closure V_m} (ψ_k - ψ) < s_m/4` for large `k`, which is Dini's theorem
(`Hironaka.ThetaCapacityDecreasingConvergence.exists_forall_lt_add_of_antitone_of_continuousOn`)
applied on the compact set `closure V_m`.  Dini needs the functions to be
*continuous real* functions there, and what the regularization supplies is
analytic singularities in the `I-0489` convention.  The bridge is below: a
function with analytic singularities smooth off its poles is continuous, as a
real function, at every point where it is finite.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.CollarExhaustionDini

open Hironaka.AdmissibleCurrentFormPositivity
open Hironaka.NumericalRestrictedVolumeScaffold

noncomputable section

/-! ## The exhaustion of an open set by compacta -/

section Exhaustion

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [SecondCountableTopology X]

/-- **An open subset of a compact, Hausdorff, second-countable space is exhausted
by an increasing sequence of compacta.**  This is the form the collar
construction consumes: monotone, contained in `U`, with union `U`.  The stronger
`K m ⊆ interior (K (m+1))` of `CompactExhaustion` is not needed, because the
cut-off of `Hironaka.CompactCollarCutoff.exists_chartSmooth_collar` already
vanishes on an open neighbourhood of `K m`. -/
theorem _root_.IsOpen.exists_monotone_isCompact_iUnion {U : Set X} (hU : IsOpen U) :
    ∃ K : ℕ → Set X, (∀ m, IsCompact (K m)) ∧ Monotone K ∧ (∀ m, K m ⊆ U) ∧
      ⋃ m, K m = U := by
  have : LocallyCompactSpace X := inferInstance
  have : LocallyCompactSpace (U : Set X) := hU.locallyCompactSpace
  have : SigmaCompactSpace (U : Set X) := inferInstance
  set E : CompactExhaustion (U : Set X) := CompactExhaustion.choice (U : Set X) with hE
  refine ⟨fun m => Subtype.val '' E m, fun m => (E.isCompact m).image continuous_subtype_val,
    fun m l hml => image_mono (E.subset hml), fun m => by
      rintro _ ⟨y, -, rfl⟩; exact y.2, ?_⟩
  apply Subset.antisymm
  · exact iUnion_subset fun m => by rintro _ ⟨y, -, rfl⟩; exact y.2
  · intro x hx
    obtain ⟨m, hm⟩ := E.exists_mem (⟨x, hx⟩ : (U : Set X))
    exact mem_iUnion.2 ⟨m, ⟨⟨x, hx⟩, hm, rfl⟩⟩

/-- **The nested triple the collar construction needs.**  Around each compactum
of the exhaustion, two open collars with compact closures inside `U`. -/
theorem _root_.IsOpen.exists_nested_collar_exhaustion {U : Set X} (hU : IsOpen U) :
    ∃ (K : ℕ → Set X) (W V : ℕ → Set X),
      (∀ m, IsCompact (K m)) ∧ Monotone K ∧ (⋃ m, K m = U) ∧
      (∀ m, IsOpen (W m)) ∧ (∀ m, IsOpen (V m)) ∧
      (∀ m, K m ⊆ W m) ∧ (∀ m, closure (W m) ⊆ V m) ∧
      (∀ m, closure (V m) ⊆ U) ∧ ∀ m, IsCompact (closure (V m)) := by
  obtain ⟨K, hKc, hKmono, hKU, hKunion⟩ := hU.exists_monotone_isCompact_iUnion
  have : LocallyCompactSpace X := inferInstance
  choose V hVopen hKV hVcl hVcomp using fun m =>
    exists_open_between_and_isCompact_closure (hKc m) hU (hKU m)
  -- the inner collar, inside `V m`
  choose W hWopen hKW hWcl hWcomp
    using fun m => exists_open_between_and_isCompact_closure (hKc m) (hVopen m) (hKV m)
  exact ⟨K, W, V, hKc, hKmono, hKunion, hWopen, hVopen, hKW,
    hWcl, hVcl, hVcomp⟩

end Exhaustion

/-! ## Continuity off the poles -/

section Continuity

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **A function with analytic singularities smooth off its poles is a continuous
real function near every point where it is finite.**  In the chart around such a
point its coordinate representative agrees with a smooth real function, by
`SmoothOffPoleSet`; transporting that germ back to the manifold gives continuity
of `toReal`. -/
theorem continuousAt_toReal_of_smoothOffPoleSet {u : M → EReal}
    (hu : SmoothOffPoleSet (n := n) u) {x : M} (hx : u x ≠ ⊥) :
    ContinuousAt (fun y => (u y).toReal) x := by
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source (n := n) x
  have hz : e.val x ∈ e.val.target := e.val.map_source hxs
  have hsymm : e.val.symm (e.val x) = x := e.val.left_inv hxs
  have hpole : chartFunction u e (e.val x) ≠ ⊥ := by
    show u (e.val.symm (e.val x)) ≠ ⊥
    rw [hsymm]; exact hx
  obtain ⟨g, hg, hug⟩ := hu e (e.val x) hz hpole
  have hcont : ContinuousAt e.val x :=
    e.val.continuousOn.continuousAt (e.val.open_source.mem_nhds hxs)
  have hlocal : (fun y => (u y).toReal) =ᶠ[𝓝 x] fun y => g (e.val y) := by
    filter_upwards [hcont.eventually hug, e.val.open_source.mem_nhds hxs] with y hy hys
    have : u y = ((g (e.val y) : ℝ) : EReal) := by
      have h := hy
      show u y = _
      rw [show u y = chartFunction u e (e.val y) by
        show u y = u (e.val.symm (e.val y)); rw [e.val.left_inv hys]]
      exact h
    rw [this, EReal.toReal_coe]
  refine ContinuousAt.congr ?_ hlocal.symm
  exact (hg.self_of_nhds.continuousAt).comp hcont

/-- The same statement for the `I-0489` convention. -/
theorem continuousAt_toReal_of_hasManifoldAnalyticSingularitiesSmoothOffPole
    {u : M → EReal} (hu : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u)
    {x : M} (hx : u x ≠ ⊥) : ContinuousAt (fun y => (u y).toReal) x :=
  continuousAt_toReal_of_smoothOffPoleSet
    (SmoothOffPoleSet.of_hasManifoldAnalyticSingularitiesSmoothOffPole hu) hx

/-- **Continuity on a set of finiteness.**  This is the hypothesis Dini's theorem
asks for on the compact set `closure V_m`. -/
theorem continuousOn_toReal_of_hasManifoldAnalyticSingularitiesSmoothOffPole
    {u : M → EReal} (hu : HasManifoldAnalyticSingularitiesSmoothOffPole (n := n) u)
    {S : Set M} (hS : ∀ x ∈ S, u x ≠ ⊥) :
    ContinuousOn (fun y => (u y).toReal) S := fun x hx =>
  (continuousAt_toReal_of_hasManifoldAnalyticSingularitiesSmoothOffPole hu
    (hS x hx)).continuousWithinAt

end Continuity

end

end Hironaka.CollarExhaustionDini
