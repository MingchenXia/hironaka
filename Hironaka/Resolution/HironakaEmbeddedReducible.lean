/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaRelativelyCompact
import Hironaka.Analytic.AnalyticSubsetTopology
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.RegularPatchNeighborhood
import Hironaka.Analytic.AnalyticIrreducibleComponents
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CanonicalCentres
import Hironaka.Coherence.CartanIrreducible
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.Resolution.EmbeddedFromResolution
import Hironaka.Resolution.HironakaAdmissibleSequence
import Hironaka.Resolution.HironakaEmbeddedExceptional
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
import Hironaka.Resolution.HironakaFromSeqInvariant
import Hironaka.Resolution.HironakaLocalPrincipalization
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.MarkedIdeal.HomogenizedGlueingTower
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.RegularPointDimension
import Hironaka.Invariant.ResolutionInvariantSeq
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Invariant.SmoothCentreInvariant
import Hironaka.Invariant.SmoothCentreLocus
import Hironaka.Resolution.StrictTransformComposition
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Embedded resolution of a reducible analytic set of pure dimension (Hironaka)

Sources: Bierstone--Milman 1997 (`bierstone-milman97-invent-math`), Theorem 1.6 (embedded desingularization of a
closed subspace, not necessarily irreducible; the strict transform smooth, the centres over the singular locus);
Włodarczyk 2005 (`wlodarczyk05-hironaka`).

Let `W` be a closed analytic subset of a complex manifold `X` which is **of pure dimension `d < n`**: the points at
which `W` is a submanifold of dimension `d` are dense in `W` (`W ⊆ closure (regularLocus W d)`). `W` may be
reducible, and its strict transform need not be connected. Its singular set `W \ regularLocus W d` is then exactly
the set of points at which `W` is not a submanifold of any dimension, and it is closed.

The first-centre argument `HironakaAdmissibleSequence.exists_tower_embedded_of_isCanonical` already applies to such a `W`
(analytic, regular of dimension `d` on a dense open set): its proof never uses irreducibility.  The only new inputs are the
domain condition for `(X, X, ∅, 𝓘_W, 1)` (Cartan's coherence for any analytic set; `𝓘_W` nonzero at every point because `W`
has empty interior) and the sharpening `f⁻¹(W_sing) ⊆ Exc f` for a set in place of an irreducible subvariety.

## Main results

* `interior_eq_empty_of_pure`, `isInvDomain_vanishingIdeal_of_pure`;
* `isClosed_diff_regularLocus`;
* `preimage_diff_regularLocus_subset_exceptionalLocus`;
* `exists_embeddedResolution_pure_of_isCanonical` (the assembly from any canonical resolution of `(X, X, ∅, 𝓘_W, 1)`);
* **`exists_embeddedResolution_pure_of_isCompact`** (`W` compact, `X` any complex manifold),
  **`exists_embeddedResolution_pure`** (`X` compact) and **`exists_embeddedResolution_pure_of_subset_isCompact`** (any `W`,
  over every open set contained in a compact set);

In each, the blowup sequence is admissible (from the empty divisor) with centres over `W_sing`, its divisor `E` has simple
normal crossings, `Exc f = ⋃ E = f⁻¹(W_sing)`, `f` is an isomorphism over `X \ W_sing`, and the strict transform of `W` is a
closed submanifold, of dimension `d` at each of its points, with only normal crossings with `E`.

Not covered: an analytic set whose components have different dimensions (the canonical resolution of `(𝓘_W, 1)` would blow up
some components before the others are smooth).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaEmbeddedReducible

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.NormalCrossings Hironaka.RestrictEmptyTower Hironaka.DivisorExponentAlong Hironaka.BlowupTowerTransforms Hironaka.HironakaAdmissibleSequence
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.HironakaEmbeddedResolutionLocal (exceptionalDivisor_facts_of_centresAvoid)

noncomputable section

variable {n : ℕ}

/-! ### Sets of pure dimension -/

section Pure

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The non-regular set is closed**: for a closed `W`, the points of `W` at which `W` is not a submanifold of dimension `d`
form a closed set (regularity of dimension `d` propagates to nearby points of `W`). -/
theorem isClosed_diff_regularLocus {W : Set M} (hW : IsClosed W) (d : ℕ) :
    IsClosed (W \ regularLocus (n := n) W d) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro y hy
  by_cases hyW : y ∈ W
  · have hreg : RegularAtDim (n := n) W y d := by
      by_contra h
      exact hy ⟨hyW, h⟩
    filter_upwards [RegularPatchNeighborhood.eventually_regularAtDim hreg] with z hz hzS
    exact hzS.2 (hz hzS.1)
  · filter_upwards [hW.isOpen_compl.mem_nhds hyW] with z hz hzS
    exact hz hzS.1

/-- **A set of pure dimension `d < n` has empty interior**: an interior point would have nearby regular points of
dimension `d` which are interior points, hence regular of dimension `n`. -/
theorem interior_eq_empty_of_pure {W : Set M} {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) : interior W = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨z, hzI, hzd⟩ := mem_closure_iff.mp (hpure (interior_subset hx)) (interior W) isOpen_interior hx
  have hzn : RegularAtDim (n := n) W z n :=
    EmbeddedFromResolution.regularAtDim_of_mem_nhds (mem_interior_iff_mem_nhds.mp hzI)
  have := RegularPointDimension.eq_of_regularAtDim hzn hzd
  omega

/-- **The ideal of an analytic set with empty interior is nonzero at every point** (`IsNonzeroAlongAt univ`): off `W` the
constant `1` lies in it; at a point of `W`, some local equation of `W` does not vanish identically near the point, since
otherwise `W` would contain a neighbourhood of it. -/
theorem isNonzeroAlongAt_vanishingIdeal_of_interior_eq_empty {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hint : interior W = ∅) (x : M) :
    IsNonzeroAlongAt (univ : Set M) (vanishingIdeal (n := n) W) x := by
  by_cases hxW : x ∈ W
  · obtain ⟨P⟩ := hWa x
    set e := complexChartAt (n := n) x with he
    have hsrc : e.val.source ∈ 𝓝 x := e.val.open_source.mem_nhds (mem_complexChartAt_source x)
    have hnb : e.val ⁻¹' P.coordinateNeighborhood ∈ 𝓝 x :=
      (e.val.continuousAt (mem_complexChartAt_source x)).preimage_mem_nhds
        (P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood)
    by_cases hall : ∀ i, ∀ᶠ y in 𝓝 x, P.generator i (e.val y) = 0
    · exfalso
      have hWn : W ∈ 𝓝 x := by
        filter_upwards [eventually_all.mpr hall, hsrc, hnb] with y h1 h2 h3
        exact (P.zeroLocus h2 h3).mpr h1
      have hx' : x ∈ interior W := mem_interior_iff_mem_nhds.mpr hWn
      rw [hint] at hx'
      exact hx'
    · push Not at hall
      obtain ⟨i, hi⟩ := hall
      refine ⟨fun y => P.generator i (e.val y), ⟨?_, ?_⟩, hi.mono fun y hy => ⟨mem_univ y, hy⟩⟩
      · refine DerivativeIdeal.holomorphicAt_comp_chart e (mem_complexChartAt_source x) ?_
        filter_upwards [P.isOpen_coordinateNeighborhood.mem_nhds P.center_mem_coordinateNeighborhood] with z hz
        exact (P.generator_holomorphic i z hz).differentiableAt (P.isOpen_coordinateNeighborhood.mem_nhds hz)
      · filter_upwards [hsrc, hnb] with y h2 h3 hyW
        exact (P.zeroLocus h2 h3).mp hyW i
  · refine ⟨fun _ => (1 : ℂ), ⟨holomorphicAt_const 1, ?_⟩,
      Frequently.of_forall fun y => ⟨mem_univ y, one_ne_zero⟩⟩
    filter_upwards [hWa.isClosed.isOpen_compl.mem_nhds hxW] with y hy hyW
    exact absurd hyW hy

/-- **`(X, X, ∅, 𝓘_W, 1)` lies in the domain of the invariants in dimension `≤ k`** for `n ≤ k` and an analytic set `W` with
empty interior (Cartan's coherence of `𝓘_W`, `CartanIrreducible.cartanCoherence`, which holds for every analytic set). -/
theorem isInvDomain_vanishingIdeal_of_interior_eq_empty {k : ℕ} (hnk : n ≤ k) {W : Set M}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W = ∅) :
    IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n M) where
  isWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ, CartanIrreducible.cartanCoherence W hWa,
    NormalCrossings.isSNCDivisor_nil,
    NormalCrossings.isTransverse_nil_of_isClosedSubmanifold HomogenizedGlueingTower.isClosedSubmanifold_univ⟩
  dimLE := fun x _ => ⟨n, hnk, AnalyticIrreducibleComponents.regularAtDim_univ x⟩
  one_le_d := le_rfl
  isNonzeroAlongAt := fun x _ => isNonzeroAlongAt_vanishingIdeal_of_interior_eq_empty hWa hint x

/-- **`(X, X, ∅, 𝓘_W, 1)` lies in the domain of the invariants** for a set `W` of pure dimension `d < n`. -/
theorem isInvDomain_vanishingIdeal_of_pure {k : ℕ} (hnk : n ≤ k) {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W)
    {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    IsInvDomain k (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n M) :=
  isInvDomain_vanishingIdeal_of_interior_eq_empty hnk hWa (interior_eq_empty_of_pure hd hpure)

end Pure

/-! ### `f⁻¹(W_sing) ⊆ Exc f` -/

section Exceptional

variable {X X' : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace X'] [ChartedSpace (ComplexModel n) X'] [IsComplexManifold n X']

/-- **A smooth strict transform forces `f⁻¹(W_sing) ⊆ Exc f`** (`HironakaEmbeddedExceptional.preimage_singularLocus_subset_
exceptionalLocus` for a closed set in place of an irreducible subvariety): for any holomorphic `f : X' → X` between manifolds
of the same dimension and a closed `W`, if the strict transform of `W` is regular of dimension `d` at each of its points, then
every point over `W \ regularLocus W d` is exceptional. -/
theorem preimage_diff_regularLocus_subset_exceptionalLocus {f : X' → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {W : Set X} (hW : IsClosed W) {d : ℕ}
    (hreg : ∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) :
    f ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n f := by
  intro y hy
  by_contra hyE
  have hO : IsOpen (exceptionalLocus n f)ᶜ := StrictTransformComposition.isOpen_compl_exceptionalLocus hf
  have hAO : ∀ w ∈ (exceptionalLocus n f)ᶜ, w ∈ strictTransform n f W ↔ f w ∈ W := fun w hw =>
    ⟨fun h => closure_minimal sdiff_subset (hW.preimage hf.continuous) h, fun h => subset_closure ⟨h, hw⟩⟩
  have hyS : y ∈ strictTransform n f W := (hAO y hyE).mpr hy.1
  exact hy.2 (HironakaEmbeddedExceptional.regularAtDim_of_regularAtDim_preimage hf hyE hO hyE hAO (hreg y hyS))

end Exceptional

/-! ### Embedded resolution -/

section EmbeddedResolution

/-- **Embedded resolution of a set of pure dimension, from a canonical resolution** (the assembly): let `X` be any complex
manifold and `W ⊆ X` an analytic set of pure dimension `d < n`.  From a canonical resolution of `(X, X, ∅, 𝓘_W, 1)` (by the
canonical invariant) one gets an admissible blowup sequence `f : X' → X` (from the empty divisor, centres over
`W_sing = W \ regularLocus W d`) with divisor `E` such that `E` has simple normal crossings, `Exc f = ⋃ E = f⁻¹(W_sing)`, `f` is
an isomorphism over `X \ W_sing`, and the strict transform of `W` is a closed submanifold, regular of dimension `d` at each of
its points, with only normal crossings with `E`. -/
theorem exists_embeddedResolution_pure_of_isCanonical {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) {Y₀ : CMfd.{u} n}
    (T₀ : BlowupTower (CMfd.of (n := n) X) Y₀)
    (hcan₀ : IsCanonical (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X))
      ((CanonicalCentres.canonicalInvariant.{u} n).inv
        (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X))) T₀)
    (hres₀ : IsGeoResolution (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X)) T₀) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (W \ regularLocus (n := n) W d) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' (W \ regularLocus (n := n) W d) ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E := by
  have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X)) :=
    isInvDomain_vanishingIdeal_of_pure (M := CMfd.of (n := n) X) le_rfl hWa hd hpure
  let O : Opens (CMfd.of (n := n) X) :=
    ⟨(W \ regularLocus (n := n) W d)ᶜ, (isClosed_diff_regularLocus hWa.isClosed d).isOpen_compl⟩
  have hOc : ((O : Set (CMfd.of (n := n) X))ᶜ) = W \ regularLocus (n := n) W d := compl_compl _
  have hreg : ∀ x ∈ W, x ∈ O → RegularAtDim (n := n) W x d := fun x hxW hxO => by
    by_contra h
    exact hxO ⟨hxW, h⟩
  have hdense : W ⊆ closure (W ∩ O) := by
    refine hpure.trans (closure_mono fun x hx => ⟨hx.2.1, fun h => h.2 hx⟩)
  obtain ⟨Y, T, hTt, hT, -, hregS, hnc⟩ := exists_tower_embedded_of_isCanonical
    (HironakaFromSeqInvariant.embeddingFields_of_seq (CanonicalCentres.canonicalInvariant.{u} n))
    hWa O hreg hdense hdom T₀ hcan₀ hres₀
  obtain ⟨hsnc, hsupp, hexc, hsing⟩ := exceptionalDivisor_facts_of_centresAvoid hdom rfl O T hTt hT
  rw [hOc] at hsing
  have hsub := preimage_diff_regularLocus_subset_exceptionalLocus T.contMDiff_proj hWa.isClosed hregS
  have hadm := isAdmissibleBlowupSequence_proj _ ((O : Set (CMfd.of (n := n) X))ᶜ) T hTt
    (centresOver_compl_of_centresAvoid O T hT)
  rw [hOc] at hadm
  have hExcS : T.proj '' exceptionalLocus n T.proj ⊆ W \ regularLocus (n := n) W d := by
    rintro x ⟨z, hz, rfl⟩
    exact hsing (hexc hz)
  refine ⟨Y, inferInstance, inferInstance, inferInstance, T.proj, _, hadm, hsnc, ?_, ?_,
    HironakaLocalPrincipalization.isIsomorphismOver_compl_of_image_exceptionalLocus_subset T.isBlowupSequence hExcS,
    ⟨isClosed_closure, fun x hx => ⟨d, hregS x hx⟩⟩, hregS, hnc⟩
  · rw [← hsupp]
    exact Subset.antisymm hexc (hsing.trans hsub)
  · rw [← hsupp]
    exact Subset.antisymm hsing (hsub.trans hexc)

/-- **Embedded resolution of a compact analytic set of pure dimension** (Hironaka;
`hir:embedded-resolution-pure-dimensional`): let `X` be any complex manifold and `W ⊆ X` a compact analytic set of
pure dimension `d < n` (the points at which `W` is a submanifold of dimension `d` are dense in `W`; `W` may be
reducible). There are an admissible blowup sequence `f: X' → X` (from the empty divisor, centres over `W_sing = W \
regularLocus W d`) and its divisor `E` such that `E` has simple normal crossings, `Exc f = ⋃ E = f⁻¹(W_sing)`, `f`
is an isomorphism over `X \ W_sing`, and the strict transform of `W` is a closed submanifold of `X'`, of dimension
`d` at each of its points (possibly disconnected), with only normal crossings with `E`. -/
theorem exists_embeddedResolution_pure_of_isCompact {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    (hK : IsCompact W) {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (W \ regularLocus (n := n) W d) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' (W \ regularLocus (n := n) W d) ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E := by
  have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X)) :=
    isInvDomain_vanishingIdeal_of_pure (M := CMfd.of (n := n) X) le_rfl hWa hd hpure
  have hcos : (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X)).cosupp = W :=
    SmoothCentreLocus.cosupp_vanishingIdeal hWa.isClosed (subset_univ _)
  obtain ⟨Y₀, T₀, hcan₀, hres₀⟩ := exists_isGeoResolution_isCanonical_of_isCompact
    (CanonicalCentres.canonicalInvariant.{u} n) hdom (by rw [hcos]; exact hK)
  exact exists_embeddedResolution_pure_of_isCanonical hWa hd hpure T₀ hcan₀ hres₀

/-- **Embedded resolution of an analytic set of pure dimension in a compact manifold** (`X` compact). -/
theorem exists_embeddedResolution_pure {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [CompactSpace X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ}
    (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (W \ regularLocus (n := n) W d) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' (W \ regularLocus (n := n) W d) ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E :=
  exists_embeddedResolution_pure_of_isCompact hWa hWa.isClosed.isCompact hd hpure

/-- **Restriction of a set of pure dimension to an open set** (`regularLocus` commutes with `Subtype.val ⁻¹'`). -/
theorem preimage_val_diff_regularLocus {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] (U : Opens X) (W : Set X) (d : ℕ) :
    (Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d) =
      ((Subtype.val : U → X) ⁻¹' W) \ regularLocus (n := n) ((Subtype.val : U → X) ⁻¹' W) d := by
  ext x
  simp only [mem_preimage, Set.mem_sdiff, mem_regularLocus]
  rw [AnalyticSubsetOpens.regularAtDim_preimage_val_iff]

/-- **Embedded resolution of an analytic set of pure dimension over a relatively compact open set**: let `X` be any
complex manifold, `W ⊆ X` an analytic set of pure dimension `d < n` (no compactness) and `X₀ ⊆ X` an open set
contained in a compact set. The conclusions of `exists_embeddedResolution_pure_of_isCompact` hold for `W ∩ X₀` in
`X₀`, with centres over `W_sing ∩ X₀`. -/
theorem exists_embeddedResolution_pure_of_subset_isCompact {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X] {W : Set X} (hWa : IsComplexAnalyticSubset (n := n) W)
    {d : ℕ} (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    (X₀ : Opens X) {K : Set X} (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ [] ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d)) X₀' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d)) ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) x d) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) E := by
  have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) W, 1⟩ : MarkedIdeal n (CMfd.of (n := n) X)) :=
    isInvDomain_vanishingIdeal_of_pure (M := CMfd.of (n := n) X) le_rfl hWa hd hpure
  obtain ⟨Y₀, T₀, hcan₀, hres₀⟩ := HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (CanonicalCentres.canonicalInvariant.{u} n) hdom (X := CMfd.of (n := n) X) hK X₀ hX₀
  rw [SmoothCentreInvariant.pullback_val_smoothCentreMarked (X := CMfd.of (n := n) X) X₀ W] at hcan₀ hres₀
  set W₀ : Set X₀ := (Subtype.val : X₀ → X) ⁻¹' W with hW₀def
  have hWa₀ : IsComplexAnalyticSubset (n := n) W₀ :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hWa
  have hpure₀ : W₀ ⊆ closure (regularLocus (n := n) W₀ d) := by
    intro x hx
    have h1 : (x : X) ∈ closure (regularLocus (n := n) W d) := hpure hx
    have h2 := (X₀.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage continuous_subtype_val
      (regularLocus (n := n) W d)
    have h3 : x ∈ closure ((Subtype.val : X₀ → X) ⁻¹' regularLocus (n := n) W d) := (Set.ext_iff.mp h2 x).mp h1
    refine closure_mono (fun y hy => ?_) h3
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hy
  rw [preimage_val_diff_regularLocus X₀ W d]
  exact exists_embeddedResolution_pure_of_isCanonical (X := X₀) hWa₀ hd hpure₀ T₀ hcan₀ hres₀

end EmbeddedResolution

end

end Hironaka.HironakaEmbeddedReducible
