/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaEmbeddedBoundary
import Hironaka.Resolution.HironakaAdmissibleCalculus
import Hironaka.Resolution.HironakaEmbeddedAnalytic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Density produces transversality in embedded resolution

Blueprint `hir:nc-density-transverse`, `hir:strict-transform-density-transverse`,
`hir:embedded-resolution-transverse-boundary` in `hironaka-boundary-extension.tex`.
The new geometric ingredient excludes a coordinate hyperplane containing the
resolved submanifold locally, using density away from the whole boundary.
It applies to reducible sets without a connectedness assumption. The boundary
theorem retains the original centres over `W_sing ∪ (W ∩ |E₀|)`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaNormalCrossingsTransversality

open Hironaka.BlowupSequences
open NormalCrossings HironakaAdmissibleSequence HironakaAdmissibleCalculus

noncomputable section

variable {n : ℕ}

/-- Density off the boundary upgrades normal crossings to transversality:
none of the coordinate hyperplanes can contain the set locally. -/
theorem isTransverse_of_hasNormalCrossings_of_subset_closure_diff
    {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    {C : Set X} {E : List (Set X)} (hnc : HasNormalCrossings n C E)
    (hdense : C ⊆ closure (C \ ⋃ H ∈ E, H)) : IsTransverse n C E := by
  intro x hx
  obtain ⟨S₀, S, ⟨Φ, hΦt, hΦ0, hΦA⟩, hcard⟩ := hnc x hx
  refine ⟨S₀, S, ⟨Φ, hΦt, hΦ0, hΦA⟩, fun i hi => ⟨hcard i hi, ?_⟩⟩
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hcard i hi)
  rw [ha, Finset.disjoint_singleton_left]
  intro ha₀
  let e := (complexChartAt (n := n) x).val
  have hopen : IsOpen (e.source ∩ e ⁻¹' Φ.source) :=
    e.continuousOn.isOpen_inter_preimage e.open_source Φ.isOpen_source
  have hxU : x ∈ e.source ∩ e ⁻¹' Φ.source :=
    ⟨mem_complexChartAt_source x, Φ.center_mem_source⟩
  obtain ⟨y, hyU, hyC, hyE⟩ := mem_closure_iff.mp (hdense hx)
    (e.source ∩ e ⁻¹' Φ.source) hopen hxU
  have hy₀ : Φ.toFun (e y) ∈ coordSubspace S₀ :=
    (hΦA none hx hyU.1 hyU.2).mp hyC
  have hyH : y ∈ E.get i := (hΦA (some i) hi hyU.1 hyU.2).mpr (by
    change Φ.toFun (e y) ∈ coordSubspace (S i)
    rw [ha]
    intro j hj
    rw [Finset.mem_singleton.mp hj]
    exact hy₀ a ha₀)
  exact hyE (mem_iUnion₂.mpr ⟨E.get i, List.get_mem _ _, hyH⟩)

/-- Transversality of a strict transform when every boundary member lies either
in the exceptional locus or over a set avoided densely by the original set.
The proof produces nonexceptional approximating points via a local biholomorphism. -/
theorem isTransverse_strictTransform_of_support_subset
    {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {A B : Set X} {E : List (Set Y)} (hA : IsClosed A)
    (hdense : A ⊆ closure (A \ B))
    (hsupp : (⋃ H ∈ E, H) ⊆ exceptionalLocus n f ∪ f ⁻¹' B)
    (hnc : HasNormalCrossings n (strictTransform n f A) E) :
    IsTransverse n (strictTransform n f A) E := by
  apply isTransverse_of_hasNormalCrossings_of_subset_closure_diff hnc
  refine closure_minimal ?_ isClosed_closure
  rintro y ⟨hyA, hyE⟩
  rw [mem_closure_iff_nhds]
  intro t ht
  have ht' : t ∩ (exceptionalLocus n f)ᶜ ∈ 𝓝 y :=
    inter_mem ht ((StrictTransformComposition.isOpen_compl_exceptionalLocus hf).mem_nhds hyE)
  have himg : f '' (t ∩ (exceptionalLocus n f)ᶜ) ∈ 𝓝 (f y) := by
    rw [← StrictTransformComposition.map_nhds_eq_of_not_mem_exceptionalLocus hf hyE]
    exact image_mem_map ht'
  obtain ⟨_, ⟨w, ⟨hwt, hwE⟩, rfl⟩, hwA, hwB⟩ :=
    mem_closure_iff_nhds.mp (hdense hyA) _ himg
  refine ⟨w, hwt, (mem_strictTransform_iff_of_notMem hf.continuous hA hwE).mpr hwA, ?_⟩
  intro hw
  exact (hsupp hw).elim hwE hwB

/-- This form consumes the geometric conclusions of any embedded resolution
relative to an initial boundary, including nonequidimensional and local forms.
The set `G` is the original singular set; it need not be assumed dense or pure. -/
theorem isTransverse_strictTransform_of_admissible_of_preimage_subset_exceptional
    {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {f : Y → X} {E₀ : List (Set X)} {E : List (Set Y)} {G A : Set X}
    (hf : IsAdmissibleBlowupSequence n X E₀ (G ∪ A ∩ ⋃ H ∈ E₀, H) Y f E)
    (hE₀ : ∀ H ∈ E₀, IsClosed H) (hA : IsClosed A)
    (hdense : A ⊆ closure (A \ ⋃ H ∈ E₀, H))
    (hG : f ⁻¹' G ⊆ exceptionalLocus n f)
    (hnc : HasNormalCrossings n (strictTransform n f A) E) :
    IsTransverse n (strictTransform n f A) E := by
  apply isTransverse_strictTransform_of_support_subset hf.isBlowupSequence.contMDiff hA hdense
    (hnc := hnc)
  intro y hy
  have hy' := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.biUnion_subset hf hE₀ hy
  rcases hy' with hB | hF
  · exact Or.inr hB
  · rcases hF with hG' | hAB
    · exact Or.inl (hG hG')
    · exact Or.inr hAB.2

/-- A resolved set is transverse to the accumulated divisor when the original
set is dense off the initial boundary and the locus over which centres lie. -/
theorem isTransverse_strictTransform_of_admissible
    {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y] {f : Y → X} {E₀ : List (Set X)} {E : List (Set Y)} {F A : Set X}
    (hf : IsAdmissibleBlowupSequence n X E₀ F Y f E) (hE₀ : ∀ H ∈ E₀, IsClosed H)
    (hA : IsClosed A) (hdense : A ⊆ closure (A \ ((⋃ H ∈ E₀, H) ∪ F)))
    (hnc : HasNormalCrossings n (strictTransform n f A) E) :
    IsTransverse n (strictTransform n f A) E := by
  apply isTransverse_of_hasNormalCrossings_of_subset_closure_diff hnc
  have hsupp := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.biUnion_subset hf hE₀
  refine (strictTransform_subset_closure_diff hf.isBlowupSequence.contMDiff hA hdense).trans
    (closure_mono ?_)
  exact fun y hy => ⟨hy.1, fun h => hy.2 (hsupp h)⟩

section Embedded

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Pure-dimensional embedded resolution with transversality to the accumulated
divisor, retaining all conclusions of the original theorem. -/
theorem exists_embeddedResolution_pure_transverse_of_isCompact {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ}
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
      HasNormalCrossings n (strictTransform n f W) E ∧
      IsTransverse n (strictTransform n f W) E := by
  obtain ⟨X', tX', cX', mX', f, E, hf, hE, hexc, hsupp, hiso, hsub, hreg, hnc⟩ :=
    HironakaEmbeddedReducible.exists_embeddedResolution_pure_of_isCompact hWa hK hd hpure
  let := tX'
  let := cX'
  let := mX'
  have hdense : W ⊆ closure (W \ (W \ regularLocus (n := n) W d)) :=
    hpure.trans (closure_mono fun x hx => ⟨hx.2.1, fun h => h.2 hx⟩)
  have htr := isTransverse_strictTransform_of_admissible hf (by simp) hWa.isClosed
    (by simpa using hdense) hnc
  exact ⟨X', tX', cX', mX', f, E, hf, hE, hexc, hsupp, hiso, hsub, hreg, hnc, htr⟩

/-- The compact ambient-manifold form of pure-dimensional embedded resolution
with a transverse accumulated divisor. -/
theorem exists_embeddedResolution_pure_transverse [CompactSpace X] {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (W \ regularLocus (n := n) W d) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' (W \ regularLocus (n := n) W d) ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E ∧
      IsTransverse n (strictTransform n f W) E :=
  exists_embeddedResolution_pure_transverse_of_isCompact hWa hWa.isClosed.isCompact hd hpure

/-- Embedded resolution relative to an initial simple normal crossings boundary,
with the accumulated divisor transverse to the resolved pure-dimensional set.
The centres retain their original permitted image `W_sing ∪ (W ∩ |E₀|)`. -/
theorem exists_embeddedResolution_boundary_transverse_of_isCompact {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) {d : ℕ}
    (hd : d < n) (hpure : W ⊆ closure (regularLocus (n := n) W d))
    {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E ∧
      IsTransverse n (strictTransform n f W) E := by
  obtain ⟨X', tX', cX', mX', f, E, hf, hE, hexc, hsupp, hsing, hiso, hsub, hreg, hnc⟩ :=
    HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_isCompact hWa hK hd hpure hE₀ hE₀W
  let := tX'
  let := cX'
  let := mX'
  have hdense₀ := HironakaEmbeddedBoundary.subset_closure_inter_compl hpure
    (HironakaEmbeddedBoundary.isClosed_biUnion_of_forall_isClosed hE₀.1) hE₀W
  have hdense : W ⊆ closure (W \ ((⋃ H ∈ E₀, H) ∪
      (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H))) := by
    refine hdense₀.trans (closure_mono ?_)
    intro x hx
    refine ⟨hx.1, fun h => ?_⟩
    rcases h with hB | hF
    · exact hx.2 (Or.inr hB)
    · rcases hF with hs | hWB
      · exact hx.2 (Or.inl hs)
      · exact hx.2 (Or.inr hWB.2)
  have htr := isTransverse_strictTransform_of_admissible hf hE₀.1 hWa.isClosed hdense hnc
  exact ⟨X', tX', cX', mX', f, E, hf, hE, hexc, hsupp, hsing, hiso, hsub, hreg, hnc, htr⟩

/-- The compact ambient-manifold form of embedded resolution with a transverse
initial and accumulated boundary. -/
theorem exists_embeddedResolution_boundary_transverse [CompactSpace X] {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' (W \ regularLocus (n := n) W d) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      (∀ x ∈ strictTransform n f W, RegularAtDim (n := n) (strictTransform n f W) x d) ∧
      HasNormalCrossings n (strictTransform n f W) E ∧
      IsTransverse n (strictTransform n f W) E :=
  exists_embeddedResolution_boundary_transverse_of_isCompact hWa hWa.isClosed.isCompact hd hpure hE₀ hE₀W

end Embedded

section Analytic

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

open HironakaEmbeddedAnalytic HironakaEmbeddedDimensionParts

/-- Nonequidimensional compact analytic embedded resolution, retaining the
dimension-part decomposition and adding transversality to the accumulated divisor. -/
theorem exists_embeddedResolution_analytic_transverse_of_isCompact {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) (hint : interior W = ∅) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X [] (singularSet (n := n) W) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f = ⋃ H ∈ E, H ∧
      (⋃ H ∈ E, H) = f ⁻¹' singularSet (n := n) W ∧
      IsIsomorphismOver n f (singularSet (n := n) W)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      strictTransform n f W = ⋃ k : Fin n, strictTransform n f (dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f (dimensionPart (n := n) W k))
          (strictTransform n f (dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f W) E ∧
      IsTransverse n (strictTransform n f W) E := by
  obtain ⟨X', tX', cX', mX', f, E, hf, hE, hexc, hsupp, hiso, hsub, hparts, hreg, hdisj, hnc⟩ :=
    HironakaEmbeddedAnalytic.exists_embeddedResolution_analytic_of_isCompact hWa hK hint
  let := tX'
  let := cX'
  let := mX'
  have htr := isTransverse_strictTransform_of_support_subset hf.isBlowupSequence.contMDiff hWa.isClosed
    (B := ∅) (by simpa using (subset_closure : W ⊆ closure W))
    (by rw [← hexc]; exact subset_union_left) hnc
  exact ⟨X', tX', cX', mX', f, E, hf, hE, hexc, hsupp, hiso, hsub, hparts, hreg, hdisj, hnc, htr⟩

/-- Nonequidimensional compact analytic embedded resolution relative to an
initial boundary, preserving every dimension-part and support conclusion. -/
theorem exists_embeddedResolution_analytic_boundary_transverse_of_isCompact {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hK : IsCompact W) (hint : interior W = ∅)
    {E₀ : List (Set X)} (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H)) :
    ∃ (X' : Type u) (_ : TopologicalSpace X') (_ : ChartedSpace (ComplexModel n) X')
      (_ : IsComplexManifold n X') (f : X' → X) (E : List (Set X')),
      IsAdmissibleBlowupSequence n X E₀ (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H) X' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆ f ⁻¹' (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H) ∧
      f ⁻¹' singularSet (n := n) W ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f (singularSet (n := n) W ∪ W ∩ ⋃ H ∈ E₀, H)ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f W) ∧
      strictTransform n f W = ⋃ k : Fin n, strictTransform n f (dimensionPart (n := n) W k) ∧
      (∀ k : ℕ, ∀ x ∈ strictTransform n f (dimensionPart (n := n) W k),
        RegularAtDim (n := n) (strictTransform n f W) x k) ∧
      (∀ k j : ℕ, k ≠ j →
        Disjoint (strictTransform n f (dimensionPart (n := n) W k))
          (strictTransform n f (dimensionPart (n := n) W j))) ∧
      HasNormalCrossings n (strictTransform n f W) E ∧
      IsTransverse n (strictTransform n f W) E := by
  obtain ⟨X', tX', cX', mX', f, E, hf, hE, hexc, hsupp, hsing, hiso, hsub, hparts, hreg, hdisj, hnc⟩ :=
    HironakaEmbeddedAnalytic.exists_embeddedResolution_analytic_boundary_of_isCompact hWa hK hint hE₀ hE₀W
  let := tX'
  let := cX'
  let := mX'
  have htr := isTransverse_strictTransform_of_admissible_of_preimage_subset_exceptional
    hf hE₀.1 hWa.isClosed hE₀W hsing hnc
  exact ⟨X', tX', cX', mX', f, E, hf, hE, hexc, hsupp, hsing, hiso, hsub, hparts, hreg, hdisj, hnc, htr⟩

end Analytic

section Local

variable {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- Pure-dimensional embedded resolution on any open set contained in a
compact set, with the accumulated divisor transverse to the strict transform. -/
theorem exists_embeddedResolution_pure_transverse_of_subset_isCompact {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d))
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
      HasNormalCrossings n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) E ∧
      IsTransverse n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) E := by
  obtain ⟨X₀', tX₀', cX₀', mX₀', f, E, hf, hE, hexc, hsupp, hiso, hsub, hreg, hnc⟩ :=
    HironakaEmbeddedReducible.exists_embeddedResolution_pure_of_subset_isCompact hWa hd hpure X₀ hK hX₀
  let := tX₀'
  let := cX₀'
  let := mX₀'
  have htr := isTransverse_strictTransform_of_support_subset hf.isBlowupSequence.contMDiff
    (hWa.isClosed.preimage continuous_subtype_val)
    (B := ∅) (by simpa using (subset_closure :
      (Subtype.val : X₀ → X) ⁻¹' W ⊆ closure ((Subtype.val : X₀ → X) ⁻¹' W)))
    (by rw [← hexc]; exact subset_union_left) hnc
  exact ⟨X₀', tX₀', cX₀', mX₀', f, E, hf, hE, hexc, hsupp, hiso, hsub, hreg, hnc, htr⟩

/-- Embedded resolution relative to the restricted initial boundary on an
open set contained in a compact set, strengthened by actual transversality. -/
theorem exists_embeddedResolution_boundary_transverse_of_subset_isCompact {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    (X₀ : Opens X) {K : Set X} (hK : IsCompact K) (hX₀ : (X₀ : Set X) ⊆ K) :
    ∃ (X₀' : Type u) (_ : TopologicalSpace X₀') (_ : ChartedSpace (ComplexModel n) X₀')
      (_ : IsComplexManifold n X₀') (f : X₀' → X₀) (E : List (Set X₀')),
      IsAdmissibleBlowupSequence n X₀ (E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·))
        ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) X₀' f E ∧
      IsSNCDivisor n E ∧
      exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
      (⋃ H ∈ E.drop E₀.length, H) ⊆
        f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) ∧
      f ⁻¹' ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d)) ⊆ exceptionalLocus n f ∧
      IsIsomorphismOver n f ((Subtype.val : X₀ → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H))ᶜ ∧
      IsClosedSubmanifold n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) ∧
      (∀ x ∈ strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W),
        RegularAtDim (n := n) (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) x d) ∧
      HasNormalCrossings n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) E ∧
      IsTransverse n (strictTransform n f ((Subtype.val : X₀ → X) ⁻¹' W)) E := by
  obtain ⟨X₀', tX₀', cX₀', mX₀', f, E, hf, hE, hexc, hsupp, hsing, hiso, hsub, hreg, hnc⟩ :=
    HironakaEmbeddedBoundary.exists_embeddedResolution_boundary_of_subset_isCompact
      hWa hd hpure hE₀ hE₀W X₀ hK hX₀
  let := tX₀'
  let := cX₀'
  let := mX₀'
  have hf' := hf
  rw [preimage_union, preimage_inter, HironakaEmbeddedBoundary.preimage_biUnion_list] at hf'
  have hcl : ∀ H ∈ E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·), IsClosed H := by
    intro H hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact (hE₀.1 H₀ hH₀).preimage continuous_subtype_val
  have hdense : (Subtype.val : X₀ → X) ⁻¹' W ⊆
      closure ((Subtype.val : X₀ → X) ⁻¹' W \ ⋃ H ∈ E₀.map ((Subtype.val : X₀ → X) ⁻¹' ·), H) := by
    intro x hx
    have h1 : (x : X) ∈ closure (W \ ⋃ H ∈ E₀, H) := hE₀W hx
    have h3 : x ∈ closure ((Subtype.val : X₀ → X) ⁻¹' (W \ ⋃ H ∈ E₀, H)) :=
      (Set.ext_iff.mp ((X₀.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
        continuous_subtype_val _) x).mp h1
    rwa [preimage_sdiff, HironakaEmbeddedBoundary.preimage_biUnion_list] at h3
  have htr := isTransverse_strictTransform_of_admissible_of_preimage_subset_exceptional hf' hcl
    (hWa.isClosed.preimage continuous_subtype_val) hdense hsing hnc
  exact ⟨X₀', tX₀', cX₀', mX₀', f, E, hf, hE, hexc, hsupp, hsing, hiso, hsub, hreg, hnc, htr⟩

/-- A relatively compact neighbourhood of every compact set admits embedded
resolution with a transverse accumulated divisor, without compactness of `W`. -/
theorem exists_embeddedResolution_boundary_transverse_local {W : Set X}
    (hWa : IsComplexAnalyticSubset (n := n) W) {d : ℕ} (hd : d < n)
    (hpure : W ⊆ closure (regularLocus (n := n) W d)) {E₀ : List (Set X)}
    (hE₀ : IsSNCDivisor n E₀) (hE₀W : W ⊆ closure (W \ ⋃ H ∈ E₀, H))
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ IsCompact (closure (U : Set X)) ∧
      ∃ (U' : Type u) (_ : TopologicalSpace U') (_ : ChartedSpace (ComplexModel n) U')
        (_ : IsComplexManifold n U') (f : U' → U) (E : List (Set U')),
        IsAdmissibleBlowupSequence n U (E₀.map ((Subtype.val : U → X) ⁻¹' ·))
          ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) U' f E ∧
        IsSNCDivisor n E ∧
        exceptionalLocus n f ⊆ ⋃ H ∈ E.drop E₀.length, H ∧
        (⋃ H ∈ E.drop E₀.length, H) ⊆
          f ⁻¹' ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H)) ∧
        f ⁻¹' ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d)) ⊆ exceptionalLocus n f ∧
        IsIsomorphismOver n f ((Subtype.val : U → X) ⁻¹' (W \ regularLocus (n := n) W d ∪ W ∩ ⋃ H ∈ E₀, H))ᶜ ∧
        IsClosedSubmanifold n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) ∧
        (∀ x ∈ strictTransform n f ((Subtype.val : U → X) ⁻¹' W),
          RegularAtDim (n := n) (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) x d) ∧
        HasNormalCrossings n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) E ∧
        IsTransverse n (strictTransform n f ((Subtype.val : U → X) ⁻¹' W)) E := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨U, hUo, hKU, hUc⟩ := exists_isOpen_superset_and_isCompact_closure hK
  exact ⟨⟨U, hUo⟩, hKU, hUc,
    exists_embeddedResolution_boundary_transverse_of_subset_isCompact
      hWa hd hpure hE₀ hE₀W ⟨U, hUo⟩ hUc subset_closure⟩

end Local

end

end Hironaka.HironakaNormalCrossingsTransversality
