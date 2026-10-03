/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.RegularLocusComponent
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.AnalyticGermDecomposition
set_option autoImplicit false

/-!
# Descending chains of analytic subsets are stationary on compact manifolds

Source: Grauert--Remmert, *Coherent analytic sheaves*, Ch. 5, §6 and Ch. 9, §1; Gunning--Rossi, *Analytic functions
of several complex variables*, II.E; Boucksom, *Divisorial Zariski decompositions*, proof of Theorem 3.17 ("by the
strong Noetherian property of analytic sets").

Let `A₀ ⊇ A₁ ⊇ ⋯` be analytic subsets of a complex manifold and `p` a point.

* In the chart at `p` the vanishing ideals of the translated germs form an ascending chain in the Noetherian ring of
  holomorphic germs, and analytic germs are determined by their vanishing ideals
  (`AnalyticGermDecomposition.le_of_vanishingIdeal_le`). So there is `N` such that for `i ≥ N`, `A_N ∩ U_i ⊆ A_i` on
  some neighbourhood `U_i` of `p`, which depends on `i`.
* Each `Gⱼ` accumulates at `p`, hence meets `U_i`; the connected component of the regular locus of `A_N` through
  such a point contains `Gⱼ` and has a nonempty relatively open part inside `A_i`, so by the identity theorem
  (`RegularLocusComponent.component_subset_of_isOpen`) it lies in `A_i`. Since `A_N` is covered near `p` by the
  closures of the `Gⱼ`, `A_N = A_i` near `p` for all `i ≥ N` on a neighbourhood independent of `i`.
-/

open Set Filter
open scoped Topology

namespace Hironaka.AnalyticDescendingChain

open AnalyticGermDecomposition RegularLocusComponent LocalStatementConnected

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The germ at `0` of `A`, read in the preferred chart at `p` and translated so that `p`
sits at the origin. -/
def chartGerm (A : Set M) (p : M) : Set (ComplexModel n) :=
  {w | w + (complexChartAt (n := n) p).val p ∈ (complexChartAt (n := n) p).val.target ∩
    (complexChartAt (n := n) p).val.symm ⁻¹' A}

omit [IsComplexManifold n M] in
theorem chartGerm_mono {A B : Set M} (hAB : A ⊆ B) (p : M) :
    chartGerm (n := n) A p ⊆ chartGerm (n := n) B p :=
  fun _ hw => ⟨hw.1, hAB hw.2⟩

theorem isAnalyticGerm_chartGerm {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (p : M) : IsAnalyticGerm (chartGerm (n := n) A p) := by
  obtain ⟨P⟩ := hA p
  let e := (complexChartAt (n := n) p).val
  let q := e p
  have hN : ∀ᶠ w in 𝓝 (0 : ComplexModel n), w + q ∈ P.coordinateNeighborhood := by
    have ht : Tendsto (fun w : ComplexModel n => w + q) (𝓝 0) (𝓝 q) := by
      exact (continuous_add_const q).tendsto' 0 q (zero_add q)
    exact ht (P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood)
  refine ⟨P.generatorCount, fun j w => P.generator j (w + q), fun j => ?_, ?_⟩
  · filter_upwards [hN] with w hw
    exact ((P.generator_holomorphic j).differentiableAt
      (P.isOpen_coordinateNeighborhood.mem_nhds hw)).comp w (differentiableAt_id.add_const q)
  · filter_upwards [hN] with w hw
    have ht : w + q ∈ e.target := P.coordinateNeighborhood_subset_target hw
    have hy : e.symm (w + q) ∈ e.source := e.map_target ht
    have hz := P.zeroLocus hy (by rwa [e.right_inv ht])
    rw [e.right_inv ht] at hz
    change (w + q ∈ e.target ∧ e.symm (w + q) ∈ A) ↔ _
    exact ⟨fun h => hz.mp h.2, fun h => ⟨ht, hz.mpr h⟩⟩

end

end Hironaka.AnalyticDescendingChain
