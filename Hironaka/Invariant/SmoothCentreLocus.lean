/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.Coherence.VanishingIdealCoherent
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.MarkedIdeals
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The ideal of a smooth centre inside a submanifold: cosupport, codimension-one part, domain

Source: Włodarczyk 2005 (`wlodarczyk05-hironaka`), subsection "Weak embedded desingularization" (`supp(𝓘_Y, 1) = Y`;
at a smooth point of `Y` Steps 2a and 1b pass to a hypersurface until the algorithm ends in Step 1ba).

`hir:smooth-centre` resolves the marked ideal `(U, U, ∅, 𝓘_Z, 1)` of a closed submanifold `Z` of pure codimension `c`:
if `c = 1` then `Z = Z₁` and the invariant is constant; if `c ≥ 2` one passes to `(U, V(u), ∅, 𝓘_Z, 1)` with `Z` of
codimension `c - 1` in `V(u)`, by induction on `c`.  So the statements are made for `(M, N, [], 𝓘_Z, 1)` with `Z ⊆ N`
closed submanifolds: the cosupport is `Z`, the codimension-one part `Z₁` of the cosupport along `N` is `Z` when `Z` has
codimension one in `N` and empty when it has codimension at least two, `Z` is an admissible centre, `𝓘_Z` is nonzero
along `N` when `Z` has positive codimension in `N` at each of its points, and the marked ideal lies in the domain of a
resolution invariant (`ResolutionInvariantSpec.IsInvDomain`).

## Main results

* `zeroLocus_vanishingIdeal`, `cosupport_vanishingIdeal_one`, `cosupp_vanishingIdeal`: `cosupp(𝓘_Z|_N, 1) = N ∩ Z`;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.SmoothCentreLocus

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.CodimOneSupportAlong Hironaka.DivisorExponentAlong Hironaka.ResolutionInvariantSpec Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings Hironaka.RegularPointDimension

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N Z : Set M}

/-! ### The cosupport -/

/-- The germs of a vanishing ideal are holomorphic. -/
theorem holomorphicAt_of_mem_vanishingIdeal :
    ∀ x g, (vanishingIdeal (n := n) Z).mem x g → HolomorphicAt n g x :=
  fun _ _ hg => hg.1

/-- **The zero locus of the ideal of a closed set is the set**: off `Z` the constant `1` is a germ of `𝓘_Z`. -/
theorem zeroLocus_vanishingIdeal (hZ : IsClosed Z) : (vanishingIdeal (n := n) Z).zeroLocus = Z := by
  ext x
  constructor
  · intro hx
    by_contra hxZ
    have h1 : (vanishingIdeal (n := n) Z).mem x (fun _ => (1 : ℂ)) :=
      ⟨holomorphicAt_const 1, by
        filter_upwards [hZ.isOpen_compl.mem_nhds hxZ] with y hy hyZ
        exact absurd hyZ hy⟩
    exact one_ne_zero (hx _ h1)
  · intro hx g hg
    exact hg.2.self_of_nhds hx

/-- **The cosupport of `(𝓘_Z|_N, 1)` is `N ∩ Z`** (`Z` closed). -/
theorem cosupport_vanishingIdeal_one (hZ : IsClosed Z) :
    cosupport n N (vanishingIdeal (n := n) Z) 1 = N ∩ Z := by
  rw [cosupport_one holomorphicAt_of_mem_vanishingIdeal, zeroLocus_vanishingIdeal hZ]

/-- **The cosupport of `(M, N, [], 𝓘_Z, 1)` is `Z`** (`Z ⊆ N` closed). -/
theorem cosupp_vanishingIdeal (hZ : IsClosed Z) (hZN : Z ⊆ N) :
    (⟨N, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n M).cosupp = Z := by
  show cosupport n N (vanishingIdeal (n := n) Z) 1 = Z
  rw [cosupport_vanishingIdeal_one hZ, inter_eq_right.mpr hZN]

end

end Hironaka.SmoothCentreLocus
