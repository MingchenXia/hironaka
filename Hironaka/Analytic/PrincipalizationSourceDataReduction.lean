import Hironaka.Analytic.PrincipalizationGluingLocalAssembly

set_option autoImplicit false

/-!
# Normal forms for the local source data of principalization

This file gives the exact normal form of the raw existential Step-3--5 source
presentation.  The CT22/Copy-4 interface exposes the anchored normal form.
In particular, the correction form `η` and the equation `θ = β + η` are
redundant: after fixing the strictly positive part `β`, the correction is
canonically `θ - β`.

The core record contains exactly the data consumed by the source-free Step-6
assembly.  The facts that the chosen point lies on the strict transform and
that its neighbourhood contains the transform are kept in a separate anchoring
record, since Step 6 itself does not use them.  Both conversions are proved, so
this is a change of normal form rather than an additional analytic assumption.
-/

open Set
open scoped Topology Manifold ContDiff

namespace Hironaka.PrincipalizationSourceDataReduction

open Hironaka.AnalyticGluingData Hironaka.NonKahlerLocus
  PrincipalizationGluingLocalAssembly

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The pre-normalization existential presentation of the Step-3--5 source
data.  It is retained here only to prove the exact normal-form equivalence. -/
def PrincipalizationStepSixSourceData
    (θ : ClosedRealOneOneForm n M) (W : Set M) (φG : M → EReal) : Prop :=
  ∃ y ∈ W, ∃ U : Set M, IsOpen U ∧ W ⊆ U ∧
    ∃ β η : ClosedRealOneOneForm n M, ∃ σ : M → ℝ, ∃ ρ : M → EReal,
      θ = β + η ∧ ChartSmooth (n := n) σ ∧
      DominatesKahlerFormOn β (fun x => (σ x : EReal)) U ∧
      IsThetaPshPotentialOn η.val ρ U ∧ IsSmoothNear (n := n) ρ y ∧
      ∀ Λ : Set M, IsCompact Λ → Λ ⊆ U \ W →
        ∃ C : ℝ, ∀ z ∈ Λ, ρ z ≤ φG z + (C : EReal)

/-- The fields of the CT22/Copy-4 local construction which are actually
consumed by Step 6.  The correction form is normalized to `θ - β`; hence no
separate `η` or decomposition equality is stored. -/
structure PrincipalizationStepSixCoreData
    (θ : ClosedRealOneOneForm n M) (W : Set M) (φG : M → EReal) where
  y : M
  U : Set M
  β : ClosedRealOneOneForm n M
  σ : M → ℝ
  ρ : M → EReal
  smooth_σ : ChartSmooth (n := n) σ
  dominates_β : DominatesKahlerFormOn β (fun x => (σ x : EReal)) U
  positive_correction : IsThetaPshPotentialOn (θ - β).val ρ U
  smooth_ρ_at_y : IsSmoothNear (n := n) ρ y
  collar : ∀ Λ : Set M, IsCompact Λ → Λ ⊆ U \ W →
    ∃ C : ℝ, ∀ z ∈ Λ, ρ z ≤ φG z + (C : EReal)

/-- The geometric anchoring fields carried by the public principalization
interface but unused by the Step-6 current assembly. -/
structure PrincipalizationStepSixAnchoredData
    (θ : ClosedRealOneOneForm n M) (W : Set M) (φG : M → EReal) where
  core : PrincipalizationStepSixCoreData θ W φG
  point_mem : core.y ∈ W
  open_neighbourhood : IsOpen core.U
  transform_subset : W ⊆ core.U

/-- The normalized core data feed directly into the existing source-free Step
6 theorem.  No membership, openness, or neighbourhood-containment hypothesis
is used here. -/
theorem PrincipalizationStepSixCoreData.gluingConclusions
    {θ : ClosedRealOneOneForm n M} {W : Set M} {φG : M → EReal}
    (d : PrincipalizationStepSixCoreData θ W φG)
    (hφG : IsKahlerCurrentPotential θ φG) (hpole : ∀ w ∈ W, φG w = ⊥) :
    PrincipalizationGluingConclusions θ W d.y d.U φG
      (fun x => (d.σ x : EReal) + d.ρ x) := by
  exact principalizationGluingConclusions_coe_add
    (θ := θ) (β := d.β) (η := θ - d.β) (W := W) (U := d.U) (y := d.y)
    (σ := d.σ) (ρ := d.ρ) (φG := φG) (by
      rw [add_comm]
      exact (sub_add_cancel θ d.β).symm)
    d.smooth_σ d.dominates_β d.positive_correction hφG hpole
    d.smooth_ρ_at_y d.collar

/-- An anchored normal form supplies the existential local-branch statement
used by `PrincipalizationData`. -/
theorem PrincipalizationStepSixAnchoredData.exists_localBranch
    {θ : ClosedRealOneOneForm n M} {W : Set M} {φG : M → EReal}
    (d : PrincipalizationStepSixAnchoredData θ W φG)
    (hφG : IsKahlerCurrentPotential θ φG) (hpole : ∀ w ∈ W, φG w = ⊥) :
    ∃ y ∈ W, ∃ U : Set M, IsOpen U ∧ W ⊆ U ∧ ∃ φU : M → EReal,
      (DominatesKahlerFormOn θ φU U ∧ IsSmoothNear (n := n) φU y) ∧
        ∀ Λ : Set M, IsCompact Λ → Λ ⊆ U \ W →
          ∃ C : ℝ, ∀ z ∈ Λ, φU z ≤ φG z + (C : EReal) := by
  refine ⟨d.core.y, d.point_mem, d.core.U, d.open_neighbourhood, d.transform_subset,
    fun x => (d.core.σ x : EReal) + d.core.ρ x, ?_⟩
  exact d.core.gluingConclusions hφG hpole |>.2

/-- Convert the original existential source-data presentation to the anchored
normal form.  The equality `θ = β + η` identifies `η` with `θ - β`. -/
theorem nonempty_anchoredData_of_sourceData
    {θ : ClosedRealOneOneForm n M} {W : Set M} {φG : M → EReal}
    (h : PrincipalizationStepSixSourceData θ W φG) :
    Nonempty (PrincipalizationStepSixAnchoredData θ W φG) := by
  rcases h with ⟨y, hy, U, hU, hWU, β, η, σ, ρ, hθ, hσ, hdom, hρ, hsmooth, hcollar⟩
  have hη : θ - β = η := by
    rw [hθ]
    exact add_sub_cancel_left β η
  refine ⟨⟨⟨y, U, β, σ, ρ, hσ, hdom, ?_, hsmooth, hcollar⟩, hy, hU, hWU⟩⟩
  rwa [hη]

/-- Convert the normal form back to the original Step-3--5 interface
presentation.  Thus normalization discards no source data. -/
theorem sourceData_of_anchoredData
    {θ : ClosedRealOneOneForm n M} {W : Set M} {φG : M → EReal}
    (d : PrincipalizationStepSixAnchoredData θ W φG) :
    PrincipalizationStepSixSourceData θ W φG := by
  refine ⟨d.core.y, d.point_mem, d.core.U, d.open_neighbourhood, d.transform_subset,
    d.core.β, θ - d.core.β, d.core.σ, d.core.ρ, ?_, d.core.smooth_σ,
    d.core.dominates_β, d.core.positive_correction, d.core.smooth_ρ_at_y, d.core.collar⟩
  rw [add_comm]
  exact (sub_add_cancel θ d.core.β).symm

/-- Exact equivalence between the public CT22/Copy-4 Step-3--5 source data and
the anchored minimal normal form. -/
theorem principalizationStepSixSourceData_iff_anchoredData
    {θ : ClosedRealOneOneForm n M} {W : Set M} {φG : M → EReal} :
    PrincipalizationStepSixSourceData θ W φG ↔
      Nonempty (PrincipalizationStepSixAnchoredData θ W φG) :=
  ⟨nonempty_anchoredData_of_sourceData, fun h => by
    obtain ⟨d⟩ := h
    exact sourceData_of_anchoredData d⟩

/-- The unanchored core is the precise reduction needed whenever only the Step
6 current conclusions are consumed. -/
theorem exists_coreData_of_sourceData
    {θ : ClosedRealOneOneForm n M} {W : Set M} {φG : M → EReal}
    (h : PrincipalizationStepSixSourceData θ W φG) :
    ∃ d : PrincipalizationStepSixCoreData θ W φG,
      d.y ∈ W ∧ IsOpen d.U ∧ W ⊆ d.U := by
  obtain ⟨d⟩ := nonempty_anchoredData_of_sourceData h
  exact ⟨d.core, d.point_mem, d.open_neighbourhood, d.transform_subset⟩

/-- Consumer form of the reduction: the original Step-3--5 source input,
together with the separately supplied polar branch, yields exactly the local
branch statement without repeating any Step-6 analytic argument. -/
theorem exists_localBranch_of_sourceData
    {θ : ClosedRealOneOneForm n M} {W : Set M} {φG : M → EReal}
    (h : PrincipalizationStepSixSourceData θ W φG)
    (hφG : IsKahlerCurrentPotential θ φG) (hpole : ∀ w ∈ W, φG w = ⊥) :
    ∃ y ∈ W, ∃ U : Set M, IsOpen U ∧ W ⊆ U ∧ ∃ φU : M → EReal,
      (DominatesKahlerFormOn θ φU U ∧ IsSmoothNear (n := n) φU y) ∧
        ∀ Λ : Set M, IsCompact Λ → Λ ⊆ U \ W →
          ∃ C : ℝ, ∀ z ∈ Λ, φU z ≤ φG z + (C : EReal) := by
  obtain ⟨d⟩ := nonempty_anchoredData_of_sourceData h
  exact d.exists_localBranch hφG hpole

end

end Hironaka.PrincipalizationSourceDataReduction
