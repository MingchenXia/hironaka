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

/-- **Descending chain condition.**  On a compact complex manifold every descending chain of
analytic subsets is stationary. -/
theorem exists_stable [CompactSpace M] {A : ℕ → Set M}
    (hA : ∀ i, IsComplexAnalyticSubset (n := n) (A i)) (hanti : Antitone A) :
    ∃ N, ∀ i, N ≤ i → A i = A N := by
  choose N U hU hpU hstab using exists_local_stable hA hanti
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU
    fun p _ => mem_iUnion.mpr ⟨p, hpU p⟩
  refine ⟨t.sup N, fun i hi => ?_⟩
  ext x
  obtain ⟨p, hpt, hxp⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  have hle : N p ≤ t.sup N := Finset.le_sup hpt
  have h1 := hstab p i (hle.trans hi)
  have h2 := hstab p (t.sup N) hle
  constructor
  · intro hx
    have : x ∈ A (N p) ∩ U p := h1 ▸ ⟨hx, hxp⟩
    exact (h2 ▸ this : x ∈ A (t.sup N) ∩ U p).1
  · intro hx
    have : x ∈ A (N p) ∩ U p := h2 ▸ ⟨hx, hxp⟩
    exact (h1 ▸ this : x ∈ A i ∩ U p).1

/-- **Noether property of analytic sets.**  A nonempty family of analytic subsets of a
compact complex manifold has a minimal member. -/
theorem exists_minimal_of_isComplexAnalyticSubset [CompactSpace M]
    (𝒜 : Set (Set M)) (h𝒜 : ∀ A ∈ 𝒜, IsComplexAnalyticSubset (n := n) A)
    (hne : 𝒜.Nonempty) :
    ∃ A ∈ 𝒜, ∀ B ∈ 𝒜, B ⊆ A → B = A := by
  by_contra hcon
  push Not at hcon
  choose f hf𝒜 hfsub hfne using hcon
  let s : ℕ → 𝒜 := fun k => Nat.rec ⟨hne.some, hne.some_mem⟩
    (fun _ S => ⟨f S.1 S.2, hf𝒜 S.1 S.2⟩) k
  have hsucc : ∀ k, (s (k + 1)).1 = f (s k).1 (s k).2 := fun _ => rfl
  have hanti : Antitone fun k => (s k).1 :=
    antitone_nat_of_succ_le fun k => by
      rw [hsucc]
      exact hfsub _ _
  obtain ⟨N, hN⟩ := exists_stable (fun k => h𝒜 _ (s k).2) hanti
  exact hfne _ _ (by rw [← hsucc]; exact hN (N + 1) (Nat.le_succ N))

end

end Hironaka.AnalyticDescendingChain
