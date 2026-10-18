/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Analytic.RegularLocusComponent
import Hironaka.Analytic.LocalStatementConnected
import Hironaka.Analytic.ClosureDifferenceAnalytic

set_option autoImplicit false

/-!
# Closures of connected components of the regular locus

Blueprint `ana:regular-component` (Demailly, *Complex analytic and differential geometry*,
II.5.3).

Let `R` be the set of regular points (of any dimension) of an analytic subset `A` of a
complex manifold, and `C` the connected component of `R` through a regular point `c` of
dimension `k`.

* `exists_open_inter_subset_component`, `regularAtDim_of_mem_component`: near each point of
  `C` the set `A` lies in `C`, and all points of `C` are regular of dimension `k`;
* `isComplexAnalyticSubset_closure_component`: `closure C` is analytic (near `p`, it is the
  union of the pieces of (LS) whose connected regular part lies in `C`);
* `isComplexAnalyticallyIrreducible_closure_component`: `closure C` is irreducible
  (identity theorem in flattening coordinates on the connected manifold `C`);
* `regularAtDim_closure_component`: points of `C` are regular points of `closure C` of
  dimension `k`.

The local tool is a `FlatBall`: a flattening `Φ` of `A` at `y` together with a ball in the
target of `Φ`.  On its neighbourhood `W = e_y⁻¹ (Φ⁻¹ ball)`, the set `A ∩ W` is the continuous
image of the convex set `ball ∩ ℂ^j`, consists of `j`-regular points, is relatively closed in
`W`, and local equations vanishing on a nonempty open part of `A ∩ W` vanish on all of it.
-/

open Set Filter
open scoped Topology

namespace Hironaka.RegularLocusComponent

open RegularLocusDense

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]


theorem regularAtDim_closure_component {A : Set M} {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) {y : M} (hy : y ∈ component (n := n) A c) :
    RegularAtDim (n := n) (closure (component (n := n) A c)) y k := by
  have hyk := regularAtDim_of_mem_component hc hy
  obtain ⟨W, hW, hyW, hWC, -, hWcl⟩ := exists_isOpen_inter_subset hy hyk
  refine RegularPointDimension.regularAtDim_of_inter_eq hW hyW ?_ hyk
  apply Subset.antisymm
  · exact fun x hx => ⟨subset_closure (hWC hx), hx.2⟩
  · rintro x ⟨hxcl, hxW⟩
    have h1 : x ∈ closure (W ∩ component (n := n) A c) := hW.inter_closure ⟨hxW, hxcl⟩
    have h2 : W ∩ component (n := n) A c ⊆ A ∩ W :=
      fun z hz => ⟨component_subset (n := n) A c hz.2, hz.1⟩
    exact ⟨hWcl ⟨hxW, closure_mono h2 h1⟩, hxW⟩

end Hironaka.RegularLocusComponent
