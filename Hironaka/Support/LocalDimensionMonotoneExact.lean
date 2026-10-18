/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Analytic.DimensionMonotone
import Hironaka.Analytic.FiniteFibrePiece
import Hironaka.Analytic.GermComponentDimension
import Hironaka.Analytic.GermParametrizationProof
import Hironaka.Analytic.AnalyticDimensionBasics

set_option autoImplicit false

/-!
# Monotonicity of dimension

Blueprint `rem:dimension-monotone` (Demailly, *Complex analytic and differential geometry*, II.5,
used throughout II.8).  Let `T` be an analytic subset of a complex manifold.

* `exists_parametrization`: an irreducible germ carries, after a linear change of coordinates,
  parametrization data and parametrizing sets.
* `exists_isOpen_subset_inter_of_cover`: a nonempty open set covered by finitely many relatively
  closed sets has a nonempty open subset inside one of them.
* `exists_regularAtDim_ge_germ` (germ level): if an injective holomorphic `k`-parameter piece of an
  analytic germ `T` at `0 ∈ ℂⁿ` passes through `0`, every neighbourhood of `0` contains a regular point
  of `T` of dimension `≥ k`.  The germ of `T` is a finite irredundant union of irreducible germs
  `A_i`; the piece has an open part inside one `A_i`, which in Noether coordinates bounds `k` by the
  dimension `d_i` of `A_i` (`FiniteFibrePiece.le_dim_of_injOn`); near `0`, off the other components,
  `A_i` has regular points of dimension `d_i`, and there `T = A_i`.
* `locDimGE_of_regularAtDim_subset` (manifold level): if `B ⊆ T` and `z` is a regular point of `B`
  of dimension `k`, then `dim_z T ≥ k` — read in the chart at `z`.
* Consequences: `LocDimGE.mono` (`dim_x B ≥ q ⇒ dim_x T ≥ q`) and `DimLE.anti`
  (`dim T ≤ a ⇒ dim B ≤ a`).
-/

open Set Filter Topology Metric

noncomputable section

namespace Hironaka.DimensionMonotone

open Hironaka.RegularLocusDense AnalyticGermDecomposition HolGerm
  GermAlgebraicParametrization GermParametrization GermParametrizationData GermComponentDimension
  RegularPointDimension RegularAtDimChart AnalyticLocalStatement AnalyticDescendingChain
  AnalyticDimensionBasics FiniteFibrePiece

variable {n : ℕ}

/-! ### Parametrizations of irreducible germs -/

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- `dim_x B ≥ q` and `B ⊆ T` give `dim_x T ≥ q`. -/
theorem LocDimGE.mono {T B : Set M} (hT : IsComplexAnalyticSubset (n := n) T) (hBT : B ⊆ T)
    {x : M} {q : ℕ} (h : LocDimGE (n := n) B x q) : LocDimGE (n := n) T x q := by
  intro N hN
  obtain ⟨y, hyN, j, hqj, hy⟩ := h (interior N) (interior_mem_nhds.2 hN)
  obtain ⟨y', hy'N, j', hjj', hy'⟩ :=
    locDimGE_of_regularAtDim_subset hT hBT hy (interior N) (isOpen_interior.mem_nhds hyN)
  exact ⟨y', interior_subset hy'N, j', hqj.trans hjj', hy'⟩

end Hironaka.DimensionMonotone
end
