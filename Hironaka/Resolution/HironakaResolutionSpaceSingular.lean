import Hironaka.Resolution.HironakaResolutionSpace
import Hironaka.Resolution.HironakaDimensionGlobalComponents
import Hironaka.Resolution.HironakaHilbertSamuelTangentValue
import Hironaka.Analytic.ConstantRankImage
import Hironaka.Coherence.CartanIrreducible

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The singular set of an analytic set is analytic

Blueprint: `blueprint/src/hironaka-g11-resolution.tex` (goal G11, milestone G11a), node
`g11:singular-set-analytic`.

For an analytic subset `W` of a complex manifold whose irreducible components may have different
dimensions, the singular set `W_sing` (the points at which `W` is not a submanifold of any
dimension, `HironakaResolutionSpace.singularSet`) is analytic.  With the dimension parts
`W⁽ᵏ⁾ = closure (Reg_k W)` (`k ≤ n`, each analytic of pure dimension `k`):

  `W_sing = ⋃ₖ (W⁽ᵏ⁾ \ Reg_k W⁽ᵏ⁾) ∪ ⋃_{j ≠ k} (W⁽ʲ⁾ ∩ W⁽ᵏ⁾)`   (`singularSet_eq`),

and the singular set of the pure-dimensional analytic set `W⁽ᵏ⁾` is analytic (it is a superlevel
set of the first Hilbert--Samuel function of the coherent ideal of `W⁽ᵏ⁾`;
`HironakaHilbertSamuelTangentValue.singularLocus_eq_first_hilbertSamuel_superlevel`, Cartan's
coherence theorem `CartanIrreducible.cartanCoherence`).  Main result:
`isComplexAnalyticSubset_singularSet`.  Sorry-free.
-/

open Set Filter
open scoped Topology

namespace Hironaka.HironakaResolutionSpaceSingular

open HironakaResolutionSpace HironakaEmbeddedDimensionParts AnalyticDimensionBasics
open HironakaEmbeddedAnalytic (singularSet isClosed_singularSet)

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The singular set of a pure-dimensional analytic set is analytic. -/
theorem isComplexAnalyticSubset_diff_regularLocus_of_isPureDim {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {d : ℕ} (hd : d ≤ n)
    (hpure : IsPureDim (n := n) A d) :
    IsComplexAnalyticSubset (n := n) (A \ regularLocus (n := n) A d) := by
  rw [HironakaHilbertSamuelTangentValue.singularLocus_eq_first_hilbertSamuel_superlevel hA hd hpure]
  exact hA.inter (HironakaHolomorphicJetChartInvariance.isComplexAnalyticSubset_hilbertSamuelAt_superlevel
    (HolomorphicIdealSheaves.vanishingIdeal (n := n) A) (CartanIrreducible.cartanCoherence A hA) 1 (d + 2))

/-- A regular point of `W` of dimension `i` lying on `W⁽ᵏ⁾` has `i = k`. -/
theorem eq_of_regularAtDim_of_mem_dimensionPart {W : Set M} {x : M} {i k : ℕ}
    (hx : RegularAtDim (n := n) W x i) (hxk : x ∈ dimensionPart (n := n) W k) : i = k := by
  obtain ⟨z, hz, hzk⟩ := mem_closure_iff_nhds.mp hxk _
    (RegularPatchNeighborhood.eventually_regularAtDim hx)
  exact RegularPointDimension.eq_of_regularAtDim (hz hzk.2.1) hzk

/-- The part of `W_sing` coming from the singular sets of the dimension parts. -/
def partSingular (W : Set M) : Set M :=
  ⋃ k : Fin (n + 1), (dimensionPart (n := n) W k \
    regularLocus (n := n) (dimensionPart (n := n) W k) k)

/-- The part of `W_sing` where two dimension parts meet. -/
def partCrossing (W : Set M) : Set M :=
  ⋃ p ∈ (Finset.univ.filter fun p : Fin (n + 1) × Fin (n + 1) => p.1 ≠ p.2),
    (dimensionPart (n := n) W p.1 ∩ dimensionPart (n := n) W p.2)

/-- **The singular set through the dimension parts.** -/
theorem singularSet_eq {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W) :
    singularSet (n := n) W = partSingular (n := n) W ∪ partCrossing (n := n) W := by
  have hWc : IsClosed W := hWa.isClosed
  ext x
  constructor
  · rintro ⟨hxW, hxreg⟩
    have hx' := hxW
    rw [eq_iUnion_dimensionPart hWa] at hx'
    obtain ⟨k, hxk⟩ := mem_iUnion.mp hx'
    by_cases hcross : ∃ j : Fin (n + 1), j ≠ k ∧ x ∈ dimensionPart (n := n) W j
    · obtain ⟨j, hjk, hxj⟩ := hcross
      refine Or.inr (mem_iUnion₂.mpr ⟨(j, k), ?_, hxj, hxk⟩)
      simpa using hjk
    · push Not at hcross
      refine Or.inl (mem_iUnion.mpr ⟨k, hxk, fun hreg => hxreg ?_⟩)
      -- near `x`, `W` agrees with `W⁽ᵏ⁾`
      let O : Set M := (⋃ j ∈ (Finset.univ.filter fun j : Fin (n + 1) => j ≠ k),
        dimensionPart (n := n) W j)ᶜ
      have hOo : IsOpen O := by
        refine (isClosed_biUnion_finset fun j _ => isClosed_closure).isOpen_compl
      have hxO : x ∈ O := by
        simp only [O, mem_compl_iff, mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and,
          not_exists]
        exact fun j hj hxj => hcross j hj hxj
      have hAB : dimensionPart (n := n) W k ∩ O = W ∩ O := by
        ext y
        constructor
        · rintro ⟨hy, hyO⟩
          exact ⟨dimensionPart_subset hWc k hy, hyO⟩
        · rintro ⟨hyW, hyO⟩
          refine ⟨?_, hyO⟩
          have hy' := hyW
          rw [eq_iUnion_dimensionPart hWa] at hy'
          obtain ⟨j, hyj⟩ := mem_iUnion.mp hy'
          by_cases hjk : j = k
          · rwa [hjk] at hyj
          · exact absurd (mem_iUnion₂.mpr ⟨j, by simpa using hjk, hyj⟩) hyO
      exact mem_iUnion.mpr ⟨k, RegularPointDimension.regularAtDim_of_inter_eq hOo hxO hAB hreg⟩
  · rintro (hx | hx)
    · obtain ⟨k, hxk, hxnreg⟩ := mem_iUnion.mp hx
      refine ⟨dimensionPart_subset hWc k hxk, fun hreg => ?_⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hreg
      have hik := eq_of_regularAtDim_of_mem_dimensionPart hi hxk
      subst hik
      exact hxnreg (regularAtDim_dimensionPart_of_regularAtDim hWc hi)
    · obtain ⟨p, hp, hxj, hxk⟩ := mem_iUnion₂.mp hx
      refine ⟨dimensionPart_subset hWc p.2 hxk, fun hreg => ?_⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hreg
      have h1 := eq_of_regularAtDim_of_mem_dimensionPart hi hxj
      have h2 := eq_of_regularAtDim_of_mem_dimensionPart hi hxk
      have hne : p.1 ≠ p.2 := by simpa using hp
      exact hne (Fin.ext (h1.symm.trans h2))

/-- **The singular set of an analytic set is analytic** (the irreducible components may have
different dimensions). -/
theorem isComplexAnalyticSubset_singularSet {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W) :
    IsComplexAnalyticSubset (n := n) (singularSet (n := n) W) := by
  rw [singularSet_eq hWa]
  refine ConstantRankImage.IsComplexAnalyticSubset.union ?_ ?_
  · have h := ConstantRankImage.isComplexAnalyticSubset_biUnion (n := n) (Finset.univ : Finset (Fin (n + 1)))
      (S := fun k : Fin (n + 1) => dimensionPart (n := n) W k \
        regularLocus (n := n) (dimensionPart (n := n) W k) k)
      (fun k _ => isComplexAnalyticSubset_diff_regularLocus_of_isPureDim
        (isComplexAnalyticSubset_dimensionPart hWa k) (Nat.lt_succ_iff.mp k.2)
        (HironakaDimensionGlobalComponents.isPureDim_dimensionPart hWa k))
    simpa [partSingular] using h
  · exact ConstantRankImage.isComplexAnalyticSubset_biUnion _ fun p _ =>
      (isComplexAnalyticSubset_dimensionPart hWa p.1).inter (isComplexAnalyticSubset_dimensionPart hWa p.2)

end

end Hironaka.HironakaResolutionSpaceSingular
