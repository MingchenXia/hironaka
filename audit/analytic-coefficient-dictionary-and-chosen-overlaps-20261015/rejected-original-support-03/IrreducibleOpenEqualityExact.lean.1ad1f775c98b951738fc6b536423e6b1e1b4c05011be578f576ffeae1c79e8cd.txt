/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Analytic.ClosureDifferenceAnalytic
import Hironaka.Analytic.PureDimension

set_option autoImplicit false

/-!
# Closures of differences of analytic sets

Blueprint `ana:closure-difference-analytic`, `ana:component-maximal` (Demailly, *Complex
analytic and differential geometry*, II.5.3).

* `isComplexAnalyticSubset_closure_diff`: for analytic `X`, `Y`, the set
  `closure (X \ Y)` is analytic.  Near `p ∈ X`, in a chart, `X` is a finite union of
  irreducible germs `Xᵢ`; those contained in `Y` near `p` contribute nothing, and for the
  others `Xᵢ ∩ Y` is thin in `Xᵢ` (`IrreducibleGermLocal.exists_thin_nhds`), so near `p`
  the closure is the union of the `Xᵢ ⊄ Y`.
* `eq_of_subset_of_inter_open_subset`: an analytic `V` inside an irreducible `Z` which
  contains a nonempty relatively open piece of `Z` is all of `Z`, since
  `Z = V ∪ closure (Z \ V)`.
-/

open Set Filter
open scoped Topology

namespace Hironaka.ClosureDifferenceAnalytic

open AnalyticGermDecomposition IrreducibleGermLocal AnalyticLocalStatement

variable {n : ℕ}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Maximality from an open piece.** -/
theorem eq_of_subset_of_inter_open_subset {V Z : Set M}
    (hV : IsComplexAnalyticSubset (n := n) V)
    (hZ : IsComplexAnalyticallyIrreducible (n := n) Z) (hVZ : V ⊆ Z) {O : Set M}
    (hO : IsOpen O) (hne : (Z ∩ O).Nonempty) (hsub : Z ∩ O ⊆ V) : V = Z := by
  have hC := isComplexAnalyticSubset_closure_diff hZ.analytic hV
  have hCZ : closure (Z \ V) ⊆ Z := closure_minimal sdiff_subset hZ.analytic.isClosed
  have hZVC : Z = V ∪ closure (Z \ V) := by
    refine Subset.antisymm (fun z hz => ?_) (union_subset hVZ hCZ)
    by_cases hzV : z ∈ V
    · exact Or.inl hzV
    · exact Or.inr (subset_closure ⟨hz, hzV⟩)
  rcases hZ.eq_left_or_eq_right hV hC hVZ hCZ hZVC with h | h
  · exact h.symm
  · exfalso
    obtain ⟨y, hyZ, hyO⟩ := hne
    obtain ⟨z, hzO, hzZ, hzV⟩ := mem_closure_iff.mp (h.subset hyZ) O hO hyO
    exact hzV (hsub ⟨hzZ, hzO⟩)

end Hironaka.ClosureDifferenceAnalytic
