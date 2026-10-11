/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.OrderTaylor
import Hironaka.Invariant.IteratedChartDerivativeAppend
import Hironaka.Invariant.CoherentZeroLocus
import Hironaka.MarkedIdeal.DerivativeIdealCoherence

set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.OrderTaylor
open Hironaka HolomorphicIdealSheaves
noncomputable section
open GermIdealOrder DerivativeIdeal IdealWeightPowers
variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
variable {𝔞 : GermIdeal n M}

/-- **Giraud--Villamayor, the second inclusion**: for `μ ≥ 1`, `cosupp(𝓓𝔞, μ) ⊆ cosupp(𝔞, μ + 1)`
(for `N = M`, `𝔞` an ideal of holomorphic germs). -/
theorem cosupport_derivIdeal_subset_cosupport_succ
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {μ : ℕ} (hμ : 1 ≤ μ) :
    cosupport n univ (derivIdeal 𝔞) μ ⊆ cosupport n univ 𝔞 (μ + 1) := by
  rintro x ⟨-, hx⟩
  refine ⟨mem_univ x, fun f hf => ?_⟩
  set e := complexChartAt (n := n) x
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  have hfD : (idealPow (pointIdeal n x) μ).mem x f :=
    mem_idealPow_of_vanishesToOrderOn_univ (hx f (le_derivIdeal h𝔞 x f hf))
  have hdf : ∀ v, (idealPow (pointIdeal n x) μ).mem x (chartDeriv e v f) := fun v =>
    mem_idealPow_of_vanishesToOrderOn_univ (hx _ (chartDeriv_mem_derivIdeal h𝔞 hxe hf))
  refine ⟨f, mem_idealPow_of_iterChartDeriv_eq_zero hxe (h𝔞 x f hf) (μ + 1) fun L hL => ?_,
    Eventually.of_forall fun _ _ => rfl⟩
  rcases List.eq_nil_or_concat L with rfl | ⟨L', v, rfl⟩
  · exact apply_eq_zero_of_mem_idealPow_pointIdeal hμ hfD
  · rw [List.concat_eq_append, iterChartDeriv_append]
    have hL' : L'.length < μ := by simp at hL; omega
    exact iterChartDeriv_eq_zero_of_mem_idealPow hxe (hdf v) L' hL'

/-- **Giraud--Villamayor** (`N = M`): for `μ ≥ 1`, `cosupp(𝔞, μ + 1) = cosupp(𝓓𝔞, μ)`. -/
theorem cosupport_succ_eq_cosupport_derivIdeal
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {μ : ℕ} (hμ : 1 ≤ μ) :
    cosupport n univ 𝔞 (μ + 1) = cosupport n univ (derivIdeal 𝔞) μ :=
  Subset.antisymm (cosupport_succ_subset_cosupport_derivIdeal μ)
    (cosupport_derivIdeal_subset_cosupport_succ h𝔞 hμ)

/-- **Giraud--Villamayor, iterated** (`N = M`): for `μ ≥ 1` and every `i`,
`cosupp(𝔞, μ + i) = cosupp(𝓓^i 𝔞, μ)`. -/
theorem cosupport_add_eq_cosupport_iterDerivIdeal
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) :
    ∀ (i : ℕ) {μ : ℕ}, 1 ≤ μ → cosupport n univ 𝔞 (μ + i) = cosupport n univ (iterDerivIdeal 𝔞 i) μ
  | 0, μ, _ => rfl
  | i + 1, μ, hμ => by
    rw [show μ + (i + 1) = (μ + 1) + i by omega,
      cosupport_add_eq_cosupport_iterDerivIdeal h𝔞 i (by omega : 1 ≤ μ + 1),
      cosupport_succ_eq_cosupport_derivIdeal (holomorphicAt_of_mem_iterDerivIdeal h𝔞 i) hμ]
    rfl

/-- **The cosupport is the zero locus of a derivative ideal** (`N = M`):
`cosupp(𝔞, j + 1) = V(𝓓^j 𝔞)`. -/
theorem cosupport_succ_eq_zeroLocus_iterDerivIdeal
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (j : ℕ) :
    cosupport n univ 𝔞 (j + 1) = (iterDerivIdeal 𝔞 j).zeroLocus := by
  rw [show j + 1 = 1 + j by omega, cosupport_add_eq_cosupport_iterDerivIdeal h𝔞 j le_rfl,
    cosupport_one (holomorphicAt_of_mem_iterDerivIdeal h𝔞 j), univ_inter]


/-- **The cosupport of a coherent ideal is closed** (`N = M`). -/
theorem isClosed_cosupport (h𝔞 : 𝔞.IsCoherent) (μ : ℕ) : IsClosed (cosupport n univ 𝔞 μ) := by
  have hhol : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x := fun x g hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg
  rcases μ with _ | j
  · rw [cosupport_zero hhol]
    exact isClosed_univ
  · rw [cosupport_succ_eq_zeroLocus_iterDerivIdeal hhol j]
    exact isClosed_zeroLocus_of_isCoherent (isCoherent_iterDerivIdeal h𝔞 j)


end
end Hironaka.OrderTaylor
