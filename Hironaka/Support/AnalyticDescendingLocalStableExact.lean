/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Analytic.AnalyticDescendingChain
import Hironaka.Analytic.RegularLocusComponent

set_option autoImplicit false

/-!
# Descending chains of analytic subsets are stationary on compact manifolds

Source: Grauert--Remmert, *Coherent analytic sheaves*, Ch. 5, §6 and Ch. 9, §1;
Gunning--Rossi, *Analytic functions of several complex variables*, II.E; Boucksom,
*Divisorial Zariski decompositions*, proof of Theorem 3.17 ("by the strong Noetherian
property of analytic sets"); blueprint `ana:analytic-noether`.

Let `A₀ ⊇ A₁ ⊇ ⋯` be analytic subsets of a complex manifold and `p` a point.

* `exists_germ_stable`: the germs at `p` stabilize.  In the chart at `p` the vanishing
  ideals of the translated germs form an ascending chain in the Noetherian ring of
  holomorphic germs, and analytic germs are determined by their vanishing ideals
  (`AnalyticGermDecomposition.le_of_vanishingIdeal_le`).  So there is `N` such that for
  `i ≥ N`, `A_N ∩ U_i ⊆ A_i` on some neighbourhood `U_i` of `p`, which depends on `i`.
* `exists_local_stable`: the chain is stationary on ONE neighbourhood of `p`.  Take local
  decomposition data of `A_N` at `p` with connected regular parts `Gⱼ`
  (`LocalStatementConnected.exists_connectedParts`).  Each `Gⱼ` accumulates at `p`, hence
  meets `U_i`; the connected component of the regular locus of `A_N` through such a point
  contains `Gⱼ` and has a nonempty relatively open part inside `A_i`, so by the identity
  theorem (`RegularLocusComponent.component_subset_of_isOpen`) it lies in `A_i`.  Since
  `A_N` is covered near `p` by the closures of the `Gⱼ`, `A_N = A_i` near `p` for all
  `i ≥ N` on a neighbourhood independent of `i`.
* `exists_stable`: on a compact manifold, finitely many such neighbourhoods cover.
* `exists_minimal_of_isComplexAnalyticSubset`: a nonempty family of analytic subsets of a
  compact complex manifold has a minimal member (otherwise dependent choice produces a
  strictly descending chain).
-/

open Set Filter
open scoped Topology

namespace Hironaka.AnalyticDescendingChain

open AnalyticGermDecomposition RegularLocusComponent LocalStatementConnected

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]


omit [IsComplexManifold n M] in
/-- A germ inclusion in the chart at `p` is an inclusion on a neighbourhood of `p`. -/
theorem exists_isOpen_inter_subset_of_chartGerm_le {A B : Set M} {p : M}
    (h : chartGerm (n := n) A p ≤ᶠ[𝓝 0] chartGerm (n := n) B p) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ A ∩ U ⊆ B := by
  let e := (complexChartAt (n := n) p).val
  have hsrc : e.source ∈ 𝓝 p := e.open_source.mem_nhds (mem_complexChartAt_source p)
  have ht : Tendsto (fun y => e y - e p) (𝓝 p) (𝓝 0) := by
    have hc : ContinuousAt (fun y => e y - e p) p :=
      (e.continuousAt (mem_complexChartAt_source p)).sub continuousAt_const
    simpa using hc.tendsto
  have hev : ∀ᶠ y in 𝓝 p, y ∈ e.source ∧
      (e y - e p ∈ chartGerm (n := n) A p → e y - e p ∈ chartGerm (n := n) B p) :=
    (Filter.eventually_of_mem hsrc fun _ hy => hy).and (ht.eventually h)
  obtain ⟨U, hUsub, hU, hpU⟩ := mem_nhds_iff.mp hev
  refine ⟨U, hU, hpU, fun y hy => ?_⟩
  obtain ⟨hys, himp⟩ := hUsub hy.2
  have hy' : e y - e p + e p = e y := sub_add_cancel _ _
  have hmem : e y - e p ∈ chartGerm (n := n) A p := by
    change e y - e p + e p ∈ e.target ∩ e.symm ⁻¹' A
    rw [hy']
    exact ⟨e.map_source hys, by simpa [mem_preimage, e.left_inv hys] using hy.1⟩
  have hB := himp hmem
  change e y - e p + e p ∈ e.target ∩ e.symm ⁻¹' B at hB
  rw [hy'] at hB
  simpa [mem_preimage, e.left_inv hys] using hB.2

/-- **Germ stabilization.**  A descending chain of analytic subsets has stationary germs at
every point. -/
theorem exists_germ_stable {A : ℕ → Set M} (hA : ∀ i, IsComplexAnalyticSubset (n := n) (A i))
    (hanti : Antitone A) (p : M) :
    ∃ N, ∀ i, N ≤ i → ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ A N ∩ U ⊆ A i := by
  have := isNoetherianRing_holGerm_euclidean n
  let I : ℕ →o Ideal (HolGerm (ComplexModel n)) :=
    ⟨fun i => vanishingIdeal (chartGerm (n := n) (A i) p), fun i j hij =>
      vanishingIdeal_anti (Eventually.of_forall (chartGerm_mono (hanti hij) p))⟩
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) I
  refine ⟨N, fun i hi => exists_isOpen_inter_subset_of_chartGerm_le (n := n) ?_⟩
  exact le_of_vanishingIdeal_le (isAnalyticGerm_chartGerm (hA i) p) (hN i hi).ge

/-- **Local stationarity.**  A descending chain of analytic subsets is stationary on a
neighbourhood of every point. -/
theorem exists_local_stable {A : ℕ → Set M} (hA : ∀ i, IsComplexAnalyticSubset (n := n) (A i))
    (hanti : Antitone A) (p : M) :
    ∃ N, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ i, N ≤ i → A i ∩ U = A N ∩ U := by
  obtain ⟨N, hN⟩ := exists_germ_stable hA hanti p
  by_cases hp : p ∈ A N
  swap
  · refine ⟨N, (A N)ᶜ, (hA N).isClosed.isOpen_compl, hp, fun i hi => ?_⟩
    have h1 : A i ∩ (A N)ᶜ = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun x hx => hx.2 (hanti hi hx.1)
    rw [h1, inter_compl_self]
  obtain ⟨D, ⟨G⟩⟩ := exists_connectedParts (hA N) hp
  refine ⟨N, D.nbhd ∩ ⋂ j, G.core j, D.isOpen_nbhd.inter (isOpen_iInter_of_finite G.isOpen_core),
    ⟨D.mem_nbhd, mem_iInter.mpr G.mem_core⟩, fun i hi => ?_⟩
  refine Subset.antisymm (fun x hx => ⟨hanti hi hx.1, hx.2⟩) ?_
  rintro x ⟨hxN, hxD, hxcore⟩
  obtain ⟨U, hU, hpU, hUsub⟩ := hN i hi
  have hxpiece : x ∈ ⋃ j, D.piece j := D.inter_nbhd_eq ▸ ⟨hxN, hxD⟩
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hxpiece
  obtain ⟨g, hgU, hgj⟩ :=
    mem_closure_iff.mp (G.subset_closure_good j ⟨G.mem_piece j, G.mem_core j⟩) U hU hpU
  have hg := G.regularAtDim_of_mem_good j g hgj
  have hgood : G.good j ⊆ component (n := n) (A N) g :=
    subset_component_of_isPreconnected (G.isPreconnected_good j)
      (fun z hz => ⟨D.dim j, G.regularAtDim_of_mem_good j z hz⟩)
      ⟨g, hgj, mem_component_self hg⟩
  have hcomp : component (n := n) (A N) g ⊆ A i :=
    component_subset_of_isOpen (hA i) hU ⟨g, hgU, mem_component_self hg⟩
      fun z hz => hUsub ⟨component_subset (n := n) (A N) g hz.2, hz.1⟩
  have hcl : closure (G.good j) ⊆ A i :=
    closure_minimal (hgood.trans hcomp) (hA i).isClosed
  exact ⟨hcl (G.subset_closure_good j ⟨hxj, mem_iInter.mp hxcore j⟩), hxD, hxcore⟩

end
end Hironaka.AnalyticDescendingChain
