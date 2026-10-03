/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.CodimOnePartTowerAlong
import Hironaka.MarkedIdeal.CodimOneSupport
import Hironaka.Analytic.RegularLocusComponent
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.MarkedIdeal.SubmanifoldRestrictLe
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.AnalyticIrreducibleComponents
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Invariant.DivisorExponentAlong
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The domain condition of relative principalization

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), the marked ideals to which the resolution applies.

Let `N` be a closed connected submanifold of dimension `k` of a complex manifold `M` and `𝔞` a coherent ideal with
`𝔞 ⊄ 𝓘_N`.  Then at every point of `N` some germ of `𝔞` does not vanish identically on `N` near the point.  The set of points
of `N` at which every germ of `𝔞` vanishes on `N` nearby is open (coherence); if it were nonempty, the zero locus of `𝔞`, an
analytic set, would contain a nonempty open part of the connected manifold `N`, hence all of `N` (identity theorem along a
component of a regular locus), and then every germ of `𝔞` would vanish on `N`, i.e. `𝔞 ⊆ 𝓘_N`.

So the marked ideal `(M, N, ∅, 𝔞, 1)` lies in the domain of the invariants in every dimension `≥ k`; for `N = M` connected this
is the domain condition of the second application in the proof of relative principalization, `(Y_t, Y_t, ∅, 𝔞_t, 1)`.

## Main results

* `isNonzeroAlongAt_of_not_le`: `𝔞 ⊄ 𝓘_N` with `N` a closed connected submanifold and `𝔞` coherent gives
  `IsNonzeroAlongAt N 𝔞 y` at every `y ∈ N`;
-/

open Set Filter
open scoped Topology Manifold

universe u

namespace Hironaka.FactorizationDomain

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.DivisorExponentAlong Hironaka.MarkedIdeals Hironaka.NormalCrossings Hironaka.RegularLocusComponent
open Hironaka.ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- On a set all of whose points are regular of one dimension, the component of the regular locus through a point is the
connected component of the set through it. -/
theorem component_eq_connectedComponentIn {N : Set M} {k : ℕ} (hreg : ∀ x ∈ N, RegularAtDim (n := n) N x k) (c : M) :
    component (n := n) N c = connectedComponentIn N c := by
  have hR : regularPoints (n := n) N = N :=
    Subset.antisymm (regularPoints_subset (n := n) N) fun x hx => ⟨k, hreg x hx⟩
  rw [component, hR]

/-- **A coherent ideal not contained in the ideal of a closed connected submanifold is nonzero along it at every point**
(`mc:factorization-domain`). -/
theorem isNonzeroAlongAt_of_not_le {N : Set M} {k : ℕ} (hN : IsClosedConnectedSubmanifold n N k)
    {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (hres : ¬ 𝔞.Le (vanishingIdeal (n := n) N)) :
    ∀ y ∈ N, IsNonzeroAlongAt N 𝔞 y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y₀, hy₀N, hy₀⟩ := hcon
  apply hres
  obtain ⟨O, hOsub, hO, hy₀O⟩ :=
    mem_nhds_iff.mp (CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt h𝔞 hy₀)
  have hcomp : component (n := n) N y₀ = N := by
    rw [component_eq_connectedComponentIn hN.2.2 y₀]
    exact hN.2.1.isPreconnected.connectedComponentIn hy₀N
  have hsub : N ⊆ 𝔞.zeroLocus := by
    rw [← hcomp]
    refine component_subset_of_isOpen (CodimOneSupport.isComplexAnalyticSubset_zeroLocus h𝔞) hO
      ⟨y₀, hy₀O, mem_component_self (hN.2.2 y₀ hy₀N)⟩ ?_
    rintro z ⟨hzO, hzN⟩ g hg
    exact (hOsub hzO g hg).self_of_nhds (component_subset (n := n) N y₀ hzN)
  intro x g hg
  refine ⟨SubmanifoldRestrictLe.holomorphicAt_of_mem_of_isCoherent h𝔞 hg, ?_⟩
  filter_upwards [HadamardBridge.eventually_mem_of_isCoherent h𝔞 hg] with z hz hzN
  exact hsub hzN g hz

/-- A closed connected submanifold of dimension `k` is a closed submanifold. -/
theorem isClosedSubmanifold_of_isClosedConnectedSubmanifold {N : Set M} {k : ℕ}
    (hN : IsClosedConnectedSubmanifold n N k) : IsClosedSubmanifold n N :=
  ⟨hN.1, fun x hx => ⟨k, hN.2.2 x hx⟩⟩

/-- A connected complex manifold of dimension `n` is a closed connected submanifold of itself, of dimension `n`. -/
theorem isClosedConnectedSubmanifold_univ [ConnectedSpace M] : IsClosedConnectedSubmanifold n (univ : Set M) n :=
  ⟨isClosed_univ, isConnected_univ, fun x _ => AnalyticIrreducibleComponents.regularAtDim_univ x⟩

end Hironaka.FactorizationDomain
