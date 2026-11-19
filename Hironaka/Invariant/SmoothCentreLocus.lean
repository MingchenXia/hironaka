import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.Coherence.VanishingIdealCoherent

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The ideal of a smooth centre inside a submanifold: cosupport, codimension-one part, domain

Hironaka phase H2 (TN3), the blowup-calculus half of TN-CLASSICAL's `hir:smooth-centre` (claim I-0977 C-0116).
Blueprint `bcalc:smooth-centre-locus` (chapter `blowup-calculus.tex`).  Source: Włodarczyk 2005
(`wlodarczyk05-hironaka`), subsection "Weak embedded desingularization" (`supp(𝓘_Y, 1) = Y`; at a smooth point of `Y`
Steps 2a and 1b pass to a hypersurface until the algorithm ends in Step 1ba).

`hir:smooth-centre` resolves the marked ideal `(U, U, ∅, 𝓘_Z, 1)` of a closed submanifold `Z` of pure codimension `c`:
if `c = 1` then `Z = Z₁` and the invariant is constant; if `c ≥ 2` one passes to `(U, V(u), ∅, 𝓘_Z, 1)` with `Z` of
codimension `c - 1` in `V(u)`, by induction on `c`.  So the statements are made for `(M, N, [], 𝓘_Z, 1)` with `Z ⊆ N`
closed submanifolds: the cosupport is `Z`, the codimension-one part `Z₁` of the cosupport along `N` is `Z` when `Z` has
codimension one in `N` and empty when it has codimension at least two, `Z` is an admissible centre, `𝓘_Z` is nonzero
along `N` when `Z` has positive codimension in `N` at each of its points, and the marked ideal lies in the domain of a
resolution invariant (`ResolutionInvariantSpec.IsInvDomain`).

## Main results

* `zeroLocus_vanishingIdeal`, `cosupport_vanishingIdeal_one`, `cosupp_vanishingIdeal`: `cosupp(𝓘_Z|_N, 1) = N ∩ Z`;
* `mem_codimOnePartAlong_vanishingIdeal_iff`: `x ∈ Z₁` iff `dim_x N = dim_x Z + 1`;
  `codimOnePartAlong_vanishingIdeal_eq_self` (codimension one), `codimOnePartAlong_vanishingIdeal_eq_empty`
  (codimension `≥ 2`), `codimOnePartAlong_vanishingIdeal_subset`;
* `isAdmissibleCentre_vanishingIdeal`: `Z` is an admissible centre of `(M, N, [], 𝓘_Z, 1)`;
* `frequently_mem_diff`, `isNonzeroAlongAt_vanishingIdeal`: `𝓘_Z` is nonzero along `N` at every point of `N` when
  `dim_x Z < dim_x N` on `Z` (off `Z` the constant `1`; on `Z` coherence and the points of `N \ Z` accumulating there);
* `isInvDomain_vanishingIdeal`: `(M, N, [], 𝓘_Z, 1)` lies in `IsInvDomain k` when `dim N ≤ k`.

Import discipline (Hironaka phase): this module does not import, even transitively,
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.  Sorry-free.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.SmoothCentreLocus

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.CodimOneSupportAlong
  Hironaka.DivisorExponentAlong Hironaka.ResolutionInvariantSpec
  Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal
  Hironaka.NormalCrossings Hironaka.RegularPointDimension

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

/-- **`Z` is an admissible centre of `(M, N, [], 𝓘_Z, 1)`** (`Z ⊆ N` a closed submanifold). -/
theorem isAdmissibleCentre_vanishingIdeal (hZ : IsClosedSubmanifold n Z) (hZN : Z ⊆ N) :
    (⟨N, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n M).IsAdmissibleCentre Z :=
  ⟨hZ, (cosupp_vanishingIdeal hZ.1 hZN).symm.subset, hasNormalCrossings_nil_of_isClosedSubmanifold hZ⟩

/-! ### The codimension-one part -/

/-- **The codimension-one part of `cosupp(𝓘_Z|_N, 1)` lies in `Z`.** -/
theorem codimOnePartAlong_vanishingIdeal_subset (hZ : IsClosed Z) :
    codimOnePartAlong N (vanishingIdeal (n := n) Z) 1 ⊆ Z := fun x hx => by
  have h := codimOnePartAlong_subset hx
  rw [cosupport_vanishingIdeal_one hZ] at h
  exact h.2

/-- **A point of `Z` is in `Z₁` iff `Z` has codimension one in `N` there**: for `Z ⊆ N`, `Z` closed, regular of
dimension `j` at `x`, and `N` regular of dimension `j'` at `x`, `x ∈ Z₁(𝓘_Z|_N, 1)` iff `j' = j + 1`. -/
theorem mem_codimOnePartAlong_vanishingIdeal_iff (hZ : IsClosed Z) (hZN : Z ⊆ N) {x : M} {j j' : ℕ}
    (hZx : RegularAtDim (n := n) Z x j) (hNx : RegularAtDim (n := n) N x j') :
    x ∈ codimOnePartAlong N (vanishingIdeal (n := n) Z) 1 ↔ j' = j + 1 := by
  show (∃ k, RegularAtDim (n := n) N x (k + 1) ∧
      RegularAtDim (n := n) (cosupport n N (vanishingIdeal (n := n) Z) 1) x k) ↔ j' = j + 1
  rw [cosupport_vanishingIdeal_one hZ, inter_eq_right.mpr hZN]
  constructor
  · rintro ⟨k, hN', hZ'⟩
    rw [eq_of_regularAtDim hNx hN', eq_of_regularAtDim hZx hZ']
  · rintro rfl
    exact ⟨j, hNx, hZx⟩

/-- **In codimension one, `Z₁ = Z`** (`hir:smooth-centre`, `c = 1`): if at every point of `Z` the submanifold `N` has
dimension one more than `Z`, the codimension-one part of `cosupp(𝓘_Z|_N, 1)` is `Z`. -/
theorem codimOnePartAlong_vanishingIdeal_eq_self (hZ : IsClosed Z) (hZN : Z ⊆ N)
    (h : ∀ x ∈ Z, ∃ j, RegularAtDim (n := n) Z x j ∧ RegularAtDim (n := n) N x (j + 1)) :
    codimOnePartAlong N (vanishingIdeal (n := n) Z) 1 = Z := by
  refine Subset.antisymm (codimOnePartAlong_vanishingIdeal_subset hZ) fun x hx => ?_
  obtain ⟨j, hZx, hNx⟩ := h x hx
  exact (mem_codimOnePartAlong_vanishingIdeal_iff hZ hZN hZx hNx).mpr rfl

/-- **In codimension at least two, `Z₁ = ∅`** (`hir:smooth-centre`, `c ≥ 2`). -/
theorem codimOnePartAlong_vanishingIdeal_eq_empty (hZ : IsClosed Z) (hZN : Z ⊆ N)
    (h : ∀ x ∈ Z, ∃ j j', RegularAtDim (n := n) Z x j ∧ RegularAtDim (n := n) N x j' ∧ j + 2 ≤ j') :
    codimOnePartAlong N (vanishingIdeal (n := n) Z) 1 = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨j, j', hZx, hNx, hjj⟩ := h x (codimOnePartAlong_vanishingIdeal_subset hZ hx)
  have := (mem_codimOnePartAlong_vanishingIdeal_iff hZ hZN hZx hNx).mp hx
  omega

/-! ### Nonzero along `N` and the domain of a resolution invariant -/

/-- **Points of `N` off `Z` accumulate where `Z` has smaller dimension**: for `Z ⊆ N` regular at `x` of dimensions
`j < j'`, points of `N \ Z` lie in every neighbourhood of `x`. -/
theorem frequently_mem_diff (hZN : Z ⊆ N) {x : M} {j j' : ℕ} (hZx : RegularAtDim (n := n) Z x j)
    (hNx : RegularAtDim (n := n) N x j') (hjj : j < j') : ∃ᶠ y in 𝓝 x, y ∈ N ∧ y ∉ Z := by
  by_contra hcon
  rw [not_frequently] at hcon
  have hiff : ∀ᶠ y in 𝓝 x, y ∈ Z ↔ y ∈ N := hcon.mono fun y hy =>
    ⟨fun h => hZN h, fun h => by by_contra h'; exact hy ⟨h, h'⟩⟩
  have := eq_of_regularAtDim (CodimOneSupport.regularAtDim_of_eventually_mem_iff hiff hZx) hNx
  omega

/-- **`𝓘_Z` is nonzero along `N`** at every point of `N`, for a closed submanifold `Z ⊆ N` of smaller dimension than `N`
at each of its points: off `Z` the constant `1` is a germ of `𝓘_Z`; at a point of `Z`, if every germ of the coherent
`𝓘_Z` vanished on `N` nearby, so would every germ at the nearby points of `N \ Z`, among them `1`. -/
theorem isNonzeroAlongAt_vanishingIdeal (hZ : IsClosedSubmanifold n Z) (hZN : Z ⊆ N)
    (hdim : ∀ x ∈ Z, ∃ j j', RegularAtDim (n := n) Z x j ∧ RegularAtDim (n := n) N x j' ∧ j < j') {x : M}
    (hx : x ∈ N) : IsNonzeroAlongAt N (vanishingIdeal (n := n) Z) x := by
  have hone : ∀ y ∈ N, y ∉ Z → IsNonzeroAlongAt N (vanishingIdeal (n := n) Z) y := fun y hyN hyZ =>
    ⟨fun _ => (1 : ℂ), ⟨holomorphicAt_const 1, by
        filter_upwards [hZ.1.isOpen_compl.mem_nhds hyZ] with w hw hwZ
        exact absurd hwZ hw⟩,
      (mem_closure_iff_frequently.mp (subset_closure hyN)).mono fun _ hw => ⟨hw, one_ne_zero⟩⟩
  by_cases hxZ : x ∈ Z
  · obtain ⟨j, j', hZx, hNx, hjj⟩ := hdim x hxZ
    by_contra hcon
    have hev := CodimOnePartTowerAlong.eventually_forall_eq_zero_of_not_isNonzeroAlongAt
      (VanishingIdealCoherent.isCoherent_vanishingIdeal hZ) hcon
    obtain ⟨z, ⟨hzN, hzZ⟩, hzev⟩ := ((frequently_mem_diff hZN hZx hNx hjj).and_eventually hev).exists
    obtain ⟨g, hg, hgfreq⟩ := hone z hzN hzZ
    obtain ⟨w, ⟨hwN, hgw⟩, hw⟩ := (hgfreq.and_eventually (hzev g hg)).exists
    exact hgw (hw hwN)
  · exact hone x hx hxZ

/-- **`(M, N, [], 𝓘_Z, 1)` lies in the domain of a resolution invariant in dimension `≤ k`** (`hir:centre-function`,
`hir:smooth-centre`): for closed submanifolds `Z ⊆ N` with `dim N ≤ k` and `dim_x Z < dim_x N` at each point of `Z`. -/
theorem isInvDomain_vanishingIdeal {k : ℕ} (hN : IsClosedSubmanifold n N) (hNk : DimLE n N k)
    (hZ : IsClosedSubmanifold n Z) (hZN : Z ⊆ N)
    (hdim : ∀ x ∈ Z, ∃ j j', RegularAtDim (n := n) Z x j ∧ RegularAtDim (n := n) N x j' ∧ j < j') :
    IsInvDomain k (⟨N, [], vanishingIdeal (n := n) Z, 1⟩ : MarkedIdeal n M) where
  isWellFormed := ⟨hN, VanishingIdealCoherent.isCoherent_vanishingIdeal hZ, isSNCDivisor_nil,
    isTransverse_nil_of_isClosedSubmanifold hN⟩
  dimLE := hNk
  one_le_d := le_rfl
  isNonzeroAlongAt := fun _ hx => isNonzeroAlongAt_vanishingIdeal hZ hZN hdim hx

end

end Hironaka.SmoothCentreLocus
