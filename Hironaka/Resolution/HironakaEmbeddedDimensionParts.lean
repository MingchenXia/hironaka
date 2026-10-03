/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedBoundary
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Analytic.RegularPatchNeighborhood
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaEmbeddedReducible
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.PureDimension
import Hironaka.Analytic.RegularPointDimension
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Embedded resolution of the dimension parts of an analytic set (Hironaka)

Sources: Bierstone--Milman 1997 (`bierstone-milman97-invent-math`), Theorem 1.6; Włodarczyk 2005
(`wlodarczyk05-hironaka`); Demailly, *Complex analytic and differential geometry*, II.5 (dimension strata).

For a closed analytic set `W` of a complex manifold `X` and `k ∈ ℕ`, the **`k`-dimensional part** of `W` is
`W⁽ᵏ⁾ = closure (Reg_k W)`, the closure of the set of points at which `W` is a submanifold of dimension `k` (classically, the
union of the irreducible components of `W` of dimension `k`; this description is not used).  It is analytic
(`PureDimension.isComplexAnalyticSubset_closure_regularStratum`, from the local decomposition of analytic sets), of pure dimension
`k` (`subset_closure_regularLocus_dimensionPart`: a regular point of `W` of dimension `k` is a regular point of `W⁽ᵏ⁾` of
dimension `k`), contained in `W`, and `W = ⋃_{k ≤ n} W⁽ᵏ⁾` (`eq_iUnion_dimensionPart`: the regular points of `W` are dense in `W`).
For `W` of pure dimension `d`, `W⁽ᵈ⁾ = W`.

So the embedded resolution of analytic sets of pure dimension (`HironakaEmbeddedReducible`, and `HironakaEmbeddedBoundary` relative
to a boundary) applies to every dimension part of every analytic set: **each dimension part of `W` has an embedded resolution**
(`exists_embeddedResolution_dimensionPart_of_isCompact`, `exists_embeddedResolution_dimensionPart`,
`exists_embeddedResolution_dimensionPart_boundary_of_isCompact`), with centres over the points of `W⁽ᵏ⁾` at which it is not a
submanifold of dimension `k`, which lie among the points of `W⁽ᵏ⁾` at which `W` itself is not a submanifold of dimension `k`
(`diff_regularLocus_dimensionPart_subset`).

**What is not covered.**  One blowup sequence resolving all dimension parts at once, with smooth and pairwise disjoint strict
transforms (the standard form of embedded resolution of a non-equidimensional set).  The canonical resolution of `(𝓘_W, 1)`
stops being usable at the first centre meeting the smooth part of the parts of largest invariant, which contains their strict
transform, while the other parts may still be singular; and resolving the parts one after the other needs their strict
transforms to be separated first (for instance by principalizing `𝓘_A + 𝓘_B`; the library has no sum of ideal sheaves), since
a later centre meeting an earlier, already smooth strict transform may make it singular again.

## Main results

* `dimensionPart`, `regularStratum_eq_regularLocus`, `isComplexAnalyticSubset_dimensionPart`,
  `dimensionPart_subset`, `regularAtDim_dimensionPart_of_regularAtDim`, `subset_closure_regularLocus_dimensionPart`,
  `eq_iUnion_dimensionPart`, `diff_regularLocus_dimensionPart_subset`;
* **`exists_embeddedResolution_dimensionPart_of_isCompact`** (`W` compact, `k < n`), **`exists_embeddedResolution_dimensionPart`**
  (`X` compact) and **`exists_embeddedResolution_dimensionPart_boundary_of_isCompact`** (relative to a simple normal crossings
  boundary).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaEmbeddedDimensionParts

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.HironakaAdmissibleSequence

noncomputable section

variable {n : ℕ}

/-! ### The dimension parts of an analytic set -/

section Parts

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The `k`-dimensional part of `W`**: the closure of the points at which `W` is a submanifold of dimension `k`. -/
def dimensionPart (W : Set M) (k : ℕ) : Set M :=
  closure (regularLocus (n := n) W k)

/-- The dimension stratum `{j = k}` is the regular locus of dimension `k`. -/
theorem regularStratum_eq_regularLocus (W : Set M) (k : ℕ) :
    PureDimension.regularStratum (n := n) W (· = k) = regularLocus (n := n) W k := by
  ext x
  rw [PureDimension.mem_regularStratum, mem_regularLocus]
  constructor
  · rintro ⟨j, rfl, hj⟩
    exact hj
  · intro h
    exact ⟨k, rfl, h⟩

/-- **The dimension parts of an analytic set are analytic.** -/
theorem isComplexAnalyticSubset_dimensionPart {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W) (k : ℕ) :
    IsComplexAnalyticSubset (n := n) (dimensionPart (n := n) W k) := by
  have h := PureDimension.isComplexAnalyticSubset_closure_regularStratum hWa (· = k)
  rwa [regularStratum_eq_regularLocus] at h

/-- The dimension parts of a closed set lie in it. -/
theorem dimensionPart_subset {W : Set M} (hW : IsClosed W) (k : ℕ) : dimensionPart (n := n) W k ⊆ W :=
  closure_minimal (regularLocus_subset W k) hW

/-- **A regular point of `W` of dimension `k` is a regular point of `W⁽ᵏ⁾` of dimension `k`**: near it every point of `W` is
regular of dimension `k`, so `W` and `W⁽ᵏ⁾` agree there. -/
theorem regularAtDim_dimensionPart_of_regularAtDim {W : Set M} (hW : IsClosed W) {x : M} {k : ℕ}
    (hx : RegularAtDim (n := n) W x k) : RegularAtDim (n := n) (dimensionPart (n := n) W k) x k := by
  obtain ⟨U, hUev, hUo, hxU⟩ := mem_nhds_iff.mp (RegularPatchNeighborhood.eventually_regularAtDim hx)
  refine RegularPointDimension.regularAtDim_of_inter_eq hUo hxU ?_ hx
  ext y
  refine ⟨fun h => ⟨subset_closure (hUev h.2 h.1), h.2⟩, fun h => ⟨dimensionPart_subset hW k h.1, h.2⟩⟩

/-- **The `k`-dimensional part is of pure dimension `k`.** -/
theorem subset_closure_regularLocus_dimensionPart {W : Set M} (hW : IsClosed W) (k : ℕ) :
    dimensionPart (n := n) W k ⊆ closure (regularLocus (n := n) (dimensionPart (n := n) W k) k) :=
  closure_mono fun _ hx => regularAtDim_dimensionPart_of_regularAtDim hW hx

/-- **An analytic set is the union of its dimension parts** (`k ≤ n`): its regular points are dense in it. -/
theorem eq_iUnion_dimensionPart {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W) :
    W = ⋃ k : Fin (n + 1), dimensionPart (n := n) W k := by
  refine Subset.antisymm (fun x hx => ?_) (iUnion_subset fun k => dimensionPart_subset hWa.isClosed k)
  have hcl : x ∈ closure (⋃ k : Fin (n + 1), regularLocus (n := n) W k) := by
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨y, hyU, k, hk⟩ := Hironaka.RegularLocusDense.exists_regularAtDim_mem_nhds hWa hx hU
    exact ⟨y, hyU, mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_of_le hk.1⟩, hk⟩⟩
  rw [closure_iUnion_of_finite] at hcl
  exact hcl

/-- **The singular points of `W⁽ᵏ⁾` are points where `W` is not a submanifold of dimension `k`.** -/
theorem diff_regularLocus_dimensionPart_subset {W : Set M} (hW : IsClosed W) (k : ℕ) :
    dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k ⊆
      dimensionPart (n := n) W k \ regularLocus (n := n) W k :=
  fun _ hx => ⟨hx.1, fun h => hx.2 (regularAtDim_dimensionPart_of_regularAtDim hW h)⟩

end Parts

/-! ### Embedded resolution of the dimension parts -/

section Resolution

/-- **Embedded resolution of a dimension part** (Hironaka; `hir:embedded-resolution-dimension-parts`): let `X` be any
complex manifold, `W ⊆ X` a compact analytic set (its components may have different dimensions) and `k < n`. Write
`W⁽ᵏ⁾` for the `k`-dimensional part and `W⁽ᵏ⁾_sing` for the points of `W⁽ᵏ⁾` at which it is not a submanifold of
dimension `k`. There are an admissible blowup sequence `f: X' → X` (from the empty divisor, centres over
`W⁽ᵏ⁾_sing`) and its divisor `E` such that `E` has simple normal crossings, `Exc f = ⋃ E = f⁻¹(W⁽ᵏ⁾_sing)`, `f` is
an isomorphism over `X \ W⁽ᵏ⁾_sing`, and the strict transform of `W⁽ᵏ⁾` is a closed submanifold of `X'`, of
dimension `k` at each of its points, with only normal crossings with `E`. -/
theorem exists_embeddedResolution_dimensionPart_of_isCompact {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) {k : ℕ} (hk : k < n) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X []
        (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k) ∧
      IsIsomorphismOver n f (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f (dimensionPart (n := n) W k)) ∧
      (∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f (dimensionPart (n := n) W k)) x k) ∧
      HasNormalCrossings n (strictTransform n f (dimensionPart (n := n) W k)) E :=
  HironakaEmbeddedReducible.exists_embeddedResolution_pure_of_isCompact (isComplexAnalyticSubset_dimensionPart hWa k)
    (hK.of_isClosed_subset isClosed_closure (dimensionPart_subset hWa.isClosed k)) hk
    (subset_closure_regularLocus_dimensionPart hWa.isClosed k)

/-- **Embedded resolution of a dimension part in a compact manifold** (`X` compact). -/
theorem exists_embeddedResolution_dimensionPart {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {k : ℕ}
    (hk : k < n) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X []
        (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k) ∧
      IsIsomorphismOver n f (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f (dimensionPart (n := n) W k)) ∧
      (∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f (dimensionPart (n := n) W k)) x k) ∧
      HasNormalCrossings n (strictTransform n f (dimensionPart (n := n) W k)) E :=
  exists_embeddedResolution_dimensionPart_of_isCompact hWa hWa.isClosed.isCompact hk

/-- **Embedded resolution of a dimension part relative to a simple normal crossings boundary** (`W` compact): the
conclusions of `HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_isCompact` for `W⁽ᵏ⁾`, when no member
of `E₀` contains a nonempty relatively open subset of `W⁽ᵏ⁾`. -/
theorem exists_embeddedResolution_dimensionPart_boundary_of_isCompact {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) {k : ℕ} (hk : k < n) {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀)
    (hE₀W : dimensionPart (n := n) W k ⊆ closure (dimensionPart (n := n) W k \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀
        (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k ∪
          dimensionPart (n := n) W k ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' (dimensionPart (n := n) W k \
        regularLocus (n := n) (dimensionPart (n := n) W k) k ∪ dimensionPart (n := n) W k ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k) ⊆
        exceptionalLocus n f ∧
      IsIsomorphismOver n f (dimensionPart (n := n) W k \ regularLocus (n := n) (dimensionPart (n := n) W k) k ∪
        dimensionPart (n := n) W k ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f (dimensionPart (n := n) W k)) ∧
      (∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f (dimensionPart (n := n) W k)) x k) ∧
      HasNormalCrossings n (strictTransform n f (dimensionPart (n := n) W k)) E :=
  HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_isCompact (isComplexAnalyticSubset_dimensionPart hWa k)
    (hK.of_isClosed_subset isClosed_closure (dimensionPart_subset hWa.isClosed k)) hk
    (subset_closure_regularLocus_dimensionPart hWa.isClosed k) hE₀ hE₀W

end Resolution

end

end Hironaka.HironakaEmbeddedDimensionParts
