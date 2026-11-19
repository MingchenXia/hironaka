import Hironaka.API3
import Hironaka.Analytic.AnalyticRegularStratumTopology
import Hironaka.Resolution.StrictTransformComposition
import Hironaka.Analytic.AnalyticSubsetPreimage
import Hironaka.Analytic.AnalyticIrreducibleComponents
import Hironaka.Analytic.RegularPointDimension
import Hironaka.Resolution.HironakaLocalPrincipalization

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Resolution of a closed analytic subset of a compact complex manifold (goal G11a)

Blueprint: `blueprint/src/hironaka-g11-resolution.tex` (goal G11, milestone G11a; Hironaka `thm:res`).

Let `M` be a compact complex manifold and `W ⊆ M` a closed analytic subset with empty interior
(its irreducible components may have different dimensions).  Write `W_sing` for the set of points
at which `W` is not a submanifold of any dimension (`HironakaEmbeddedAnalytic.singularSet`) and
`W_reg = W \ W_sing`.
The embedded resolution of `W` (`Hironaka.exists_embeddedResolution_analytic`, Hironaka;
Bierstone--Milman 1997, Theorem 1.6) gives a finite sequence `σ : M' → M` of blowups with smooth
nowhere dense centres lying over `W_sing`.  This file shows that the strict transform
`W' = closure (σ⁻¹ W \ Exc σ)` together with the restriction of `σ` is a resolution of `W`:

* `W'` is a compact closed complex submanifold of `M'` (of possibly varying dimension);
* `σ` maps `W'` onto `W`;
* `σ` is an isomorphism over `M \ W_sing`, and `W'` meets `σ⁻¹ (M \ W_sing)` exactly in
  `σ⁻¹ W_reg`, so that `σ : W' ∩ σ⁻¹ W_reg → W_reg` is the restriction of a biholomorphism;
* `W' ∩ σ⁻¹ W_sing` is nowhere dense in `W'` (`W'` is the closure of `σ⁻¹ W_reg`) and is the
  trace on `W'` of the simple normal crossings exceptional divisor;
* `W_sing` is closed and nowhere dense in `W`.

The structure `IsStrictTransformResolution` packages these conclusions.  Main results:

* `isStrictTransformResolution_of_data`: the data of an embedded resolution together with
  closedness of `σ` give a resolution by the strict transform (no compactness);
* `exists_isStrictTransformResolution`: existence for `W` with empty interior in compact `M`
  (with normal crossings of `W'` and `E`);
* `isStrictTransformResolution_of_diff_interior`: the interior of `W` (open, closed, regular) is
  carried along, so a resolution of `W \ interior W` resolves `W`;
* `exists_isStrictTransformResolution_of_isAnalytic`: **G11a**, existence for an arbitrary closed
  analytic subset of a compact complex manifold.

What this file does **not** claim: that the restriction of `σ` to `W'` is a composition of
blowups of the (singular) intermediate strict transforms along smooth centres contained in them
(the centres of the embedded resolution are only known to lie over `W_sing`), and nothing about
compact complex spaces that do not embed into a compact manifold (that needs the embedding
independence of goal G1).  Sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaResolutionSpace

open Hironaka.BlowupSequences
open Hironaka.NormalCrossings Hironaka.HironakaAdmissibleSequence
open Hironaka.HironakaEmbeddedAnalytic (singularSet mem_singularSet_iff
  singularSet_subset isClosed_singularSet)

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### The singular set of an analytic set -/

/-- The regular part `W \ W_sing` is the union of the regular loci of all dimensions. -/
theorem diff_singularSet (W : Set M) :
    W \ singularSet (n := n) W = ⋃ k : ℕ, regularLocus (n := n) W k := by
  ext x
  constructor
  · rintro ⟨hxW, hx⟩
    by_contra hreg
    exact hx ⟨hxW, hreg⟩
  · intro hx
    refine ⟨(mem_iUnion.mp hx).elim fun k hk => regularLocus_subset W k hk, ?_⟩
    rintro ⟨-, hreg⟩
    exact hreg hx

/-- The regular part of an analytic set is dense in it. -/
theorem subset_closure_diff_singularSet {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W) :
    W ⊆ closure (W \ singularSet (n := n) W) := by
  rw [diff_singularSet]
  exact RegularLocusDense.subset_closure_iUnion_regularLocus hWa

/-! ### Resolutions by strict transforms -/

variable (n) in
/-- `σ : M' → M`, with divisor `E`, *resolves* `W ⊆ M` by its strict transform
`W' = strictTransform n σ W`:

* `σ` is an admissible finite sequence of blowups of `M` with smooth nowhere dense centres
  lying over `W_sing`, with exceptional divisor `E` with simple normal crossings;
* `W'` is a closed complex submanifold of `M'`;
* `σ (W') = W`;
* `σ` is an isomorphism over `M \ W_sing` and `W' ∩ σ⁻¹ (M \ W_sing) = σ⁻¹ (W \ W_sing)`;
* `W'` is the closure of `σ⁻¹ (W \ W_sing)`, and `W' ∩ σ⁻¹ W_sing` is the trace of `⋃ E`. -/
structure IsStrictTransformResolution (W : Set M) {M' : Type u} [TopologicalSpace M']
    [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M'] (σ : M' → M)
    (E : List (Set M')) : Prop where
  admissible : IsAdmissibleBlowupSequence n M [] (singularSet (n := n) W) M' σ E
  snc : IsSNCDivisor n E
  isClosedSubmanifold : IsClosedSubmanifold n (strictTransform n σ W)
  image_eq : σ '' strictTransform n σ W = W
  isIsomorphismOver : IsIsomorphismOver n σ (singularSet (n := n) W)ᶜ
  inter_preimage_compl : strictTransform n σ W ∩ σ ⁻¹' (singularSet (n := n) W)ᶜ =
    σ ⁻¹' (W \ singularSet (n := n) W)
  eq_closure : strictTransform n σ W = closure (σ ⁻¹' (W \ singularSet (n := n) W))
  inter_preimage_singular : strictTransform n σ W ∩ σ ⁻¹' singularSet (n := n) W =
    strictTransform n σ W ∩ ⋃ H ∈ E, H

namespace IsStrictTransformResolution

variable {W : Set M} {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M']
  [IsComplexManifold n M'] {σ : M' → M} {E : List (Set M')}

/-- `σ` is a finite composition of blowups with smooth nowhere dense centres. -/
theorem isBlowupSequence (h : IsStrictTransformResolution n W σ E) : IsBlowupSequence n M M' σ :=
  h.admissible.isBlowupSequence

theorem contMDiff (h : IsStrictTransformResolution n W σ E) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ σ :=
  h.isBlowupSequence.contMDiff

theorem isClosed_strictTransform (h : IsStrictTransformResolution n W σ E) :
    IsClosed (strictTransform n σ W) :=
  h.isClosedSubmanifold.1

/-- The strict transform lies over `W`. -/
theorem strictTransform_subset_preimage (h : IsStrictTransformResolution n W σ E) :
    strictTransform n σ W ⊆ σ ⁻¹' W := by
  intro y hy
  have hy' : σ y ∈ σ '' strictTransform n σ W := mem_image_of_mem σ hy
  rwa [h.image_eq] at hy'

/-- The part of the strict transform over the singular set is nowhere dense in the strict
transform: its complement in `W'` is dense. -/
theorem strictTransform_subset_closure (h : IsStrictTransformResolution n W σ E) :
    strictTransform n σ W ⊆ closure (strictTransform n σ W \ σ ⁻¹' singularSet (n := n) W) := by
  conv_lhs => rw [h.eq_closure]
  apply closure_mono
  intro y hy
  refine ⟨?_, fun hs => hy.2 hs⟩
  rw [h.eq_closure]
  exact subset_closure hy

/-- Over a compact base the resolving manifold is compact. -/
theorem compactSpace [CompactSpace M] (h : IsStrictTransformResolution n W σ E) :
    CompactSpace M' :=
  (StrictTransformComposition.IsBlowupSequence.compactSpace_surjective h.isBlowupSequence).1

/-- Over a compact base the strict transform is compact. -/
theorem isCompact_strictTransform [CompactSpace M] (h : IsStrictTransformResolution n W σ E) :
    IsCompact (strictTransform n σ W) := by
  have := h.compactSpace
  exact h.isClosed_strictTransform.isCompact

end IsStrictTransformResolution

/-! ### From the embedded resolution to a resolution -/

/-- **The data of an embedded resolution give a resolution by the strict transform.**  An
admissible blowup sequence with centres over `W_sing` whose exceptional locus is the SNC divisor
`E = σ⁻¹ W_sing`, which is an isomorphism over `M \ W_sing`, whose strict transform `W'` is a
closed submanifold, and which is a closed map, resolves `W` by its strict transform.  No
compactness is used. -/
theorem isStrictTransformResolution_of_data {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W)
    {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
    {σ : M' → M} {E : List (Set M')}
    (hadm : IsAdmissibleBlowupSequence n M [] (singularSet (n := n) W) M' σ E)
    (hsnc : IsSNCDivisor n E) (hexc : exceptionalLocus n σ = ⋃ H ∈ E, H)
    (hunion : (⋃ H ∈ E, H) = σ ⁻¹' singularSet (n := n) W)
    (hiso : IsIsomorphismOver n σ (singularSet (n := n) W)ᶜ)
    (hsub : IsClosedSubmanifold n (strictTransform n σ W)) (hclosed : IsClosedMap σ) :
    IsStrictTransformResolution n W σ E := by
  have hseq := hadm.isBlowupSequence
  have hsurj : Function.Surjective σ := HironakaLocalPrincipalization.IsBlowupSequence.surjective hseq
  have hcont : Continuous σ := hseq.contMDiff.continuous
  have hWc : IsClosed W := hWa.isClosed
  -- the strict transform is the closure of the preimage of the regular part
  have hpre : σ ⁻¹' W \ exceptionalLocus n σ = σ ⁻¹' (W \ singularSet (n := n) W) := by
    rw [hexc, hunion, preimage_sdiff]
  have heq : strictTransform n σ W = closure (σ ⁻¹' (W \ singularSet (n := n) W)) := by
    rw [strictTransform, hpre]
  have hsubW : strictTransform n σ W ⊆ σ ⁻¹' W := by
    rw [heq]
    exact closure_minimal (preimage_mono sdiff_subset) (hWc.preimage hcont)
  have hreg_sub : σ ⁻¹' (W \ singularSet (n := n) W) ⊆ strictTransform n σ W := by
    rw [heq]
    exact subset_closure
  refine ⟨hadm, hsnc, hsub, ?_, hiso, ?_, heq, ?_⟩
  · -- `σ (W') = W`
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hsubW hy
    · have hcl : IsClosed (σ '' strictTransform n σ W) := hclosed _ hsub.1
      refine (subset_closure_diff_singularSet hWa).trans (closure_minimal ?_ hcl)
      intro x hx
      obtain ⟨y, rfl⟩ := hsurj x
      exact ⟨y, hreg_sub hx, rfl⟩
  · -- `W' ∩ σ⁻¹ (M \ W_sing) = σ⁻¹ (W \ W_sing)`
    apply Subset.antisymm
    · rintro y ⟨hyW, hyS⟩
      exact ⟨hsubW hyW, hyS⟩
    · intro y hy
      exact ⟨hreg_sub hy, hy.2⟩
  · -- the trace of the exceptional divisor
    rw [hunion]

/-! ### Existence (G11a) -/

/-- **Resolution of a closed analytic subset of a compact complex manifold (goal G11a).**  For a
closed analytic subset `W` with empty interior of a compact complex manifold `M` there are a
compact complex manifold `M'` and a finite sequence of blowups `σ : M' → M` with smooth centres
over `W_sing` whose strict transform resolves `W` (`IsStrictTransformResolution`) and has only
normal crossings with the exceptional divisor. -/
theorem exists_isStrictTransformResolution [CompactSpace M] {W : Set M}
    (hWa : IsComplexAnalyticSubset (n := n) W) (hint : interior W = ∅) :
    ∃ (M' : Type u) (_ : TopologicalSpace M') (_ : ChartedSpace (ComplexModel n) M')
      (_ : IsComplexManifold n M') (σ : M' → M) (E : List (Set M')),
      CompactSpace M' ∧ IsStrictTransformResolution n W σ E ∧
        HasNormalCrossings n (strictTransform n σ W) E := by
  obtain ⟨M', _, _, _, σ, E, hadm, hsnc, hexc, hunion, hiso, hsub, -, -, -, hnc⟩ :=
    Hironaka.exists_embeddedResolution_analytic hWa hint
  change IsAdmissibleBlowupSequence n M [] (singularSet (n := n) W) M' σ E at hadm
  change (⋃ H ∈ E, H) = σ ⁻¹' singularSet (n := n) W at hunion
  change IsIsomorphismOver n σ (singularSet (n := n) W)ᶜ at hiso
  obtain ⟨hcpt, -⟩ :=
    StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hadm.isBlowupSequence
  have hclosed : IsClosedMap σ := hadm.isBlowupSequence.contMDiff.continuous.isClosedMap
  exact ⟨M', inferInstance, inferInstance, inferInstance, σ, E, hcpt,
    isStrictTransformResolution_of_data hWa hadm hsnc hexc hunion hiso hsub hclosed, hnc⟩


/-! ### Analytic sets with interior -/

section Interior

/-- A set containing a neighbourhood of `x` is regular of dimension `n` at `x`. -/
theorem regularAtDim_of_mem_nhds' {S : Set M} {x : M} (hS : S ∈ 𝓝 x) :
    RegularAtDim (n := n) S x n := by
  obtain ⟨O, hOS, hOo, hxO⟩ := mem_nhds_iff.mp hS
  refine RegularPointDimension.regularAtDim_of_inter_eq hOo hxO ?_
    (AnalyticIrreducibleComponents.regularAtDim_univ x)
  rw [univ_inter, inter_eq_right.mpr hOS]

/-- The part `W \ interior W` of `W` off its interior. -/
theorem isComplexAnalyticSubset_diff_interior {W : Set M}
    (hWa : IsComplexAnalyticSubset (n := n) W) :
    IsComplexAnalyticSubset (n := n) (W \ interior W) := by
  refine AnalyticSubsetPreimage.isComplexAnalyticSubset_of_locally_eq hWa
    (hWa.isClosed.sdiff isOpen_interior) fun y hy => ⟨(interior W)ᶜ,
      hWa.isClosed_interior.isOpen_compl, hy.2, ?_⟩
  ext z
  constructor
  · rintro ⟨hz, hzK⟩
    exact ⟨⟨hz, hzK⟩, hzK⟩
  · rintro ⟨⟨hz, -⟩, hzK⟩
    exact ⟨hz, hzK⟩

theorem interior_diff_interior (W : Set M) : interior (W \ interior W) = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  exact (interior_subset hx).2 (interior_mono sdiff_subset hx)

/-- Removing the (open and closed) interior does not change the singular set. -/
theorem singularSet_diff_interior {W : Set M} (hWa : IsComplexAnalyticSubset (n := n) W) :
    singularSet (n := n) (W \ interior W) = singularSet (n := n) W := by
  ext x
  by_cases hx : x ∈ interior W
  · constructor
    · rintro ⟨hx0, -⟩
      exact absurd hx hx0.2
    · rintro ⟨-, hreg⟩
      exact absurd (mem_iUnion.mpr ⟨n, regularAtDim_of_mem_nhds' (mem_interior_iff_mem_nhds.mp hx)⟩)
        hreg
  · have hN : IsOpen (interior W)ᶜ := hWa.isClosed_interior.isOpen_compl
    have heq : (W \ interior W) ∩ (interior W)ᶜ = W ∩ (interior W)ᶜ := by
      ext z
      constructor
      · rintro ⟨⟨hz, -⟩, hzK⟩
        exact ⟨hz, hzK⟩
      · rintro ⟨hz, hzK⟩
        exact ⟨⟨hz, hzK⟩, hzK⟩
    have hreg : ∀ k, x ∈ regularLocus (n := n) (W \ interior W) k ↔
        x ∈ regularLocus (n := n) W k := fun k =>
      ⟨RegularPointDimension.regularAtDim_of_inter_eq hN hx heq,
        RegularPointDimension.regularAtDim_of_inter_eq hN hx heq.symm⟩
    constructor
    · rintro ⟨hx0, hx0reg⟩
      refine ⟨hx0.1, fun hreg' => hx0reg ?_⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp hreg'
      exact mem_iUnion.mpr ⟨k, (hreg k).mpr hk⟩
    · rintro ⟨hxW, hxreg⟩
      refine ⟨⟨hxW, hx⟩, fun hreg' => hxreg ?_⟩
      obtain ⟨k, hk⟩ := mem_iUnion.mp hreg'
      exact mem_iUnion.mpr ⟨k, (hreg k).mp hk⟩

/-- The interior of `W` does not meet the singular set. -/
theorem disjoint_interior_singularSet (W : Set M) : Disjoint (interior W) (singularSet (n := n) W) := by
  refine disjoint_left.mpr fun x hx hxS => hxS.2 ?_
  exact mem_iUnion.mpr ⟨n, regularAtDim_of_mem_nhds' (mem_interior_iff_mem_nhds.mp hx)⟩

/-- **Removing the interior.**  A resolution of `W \ interior W` by its strict transform is a
resolution of `W`: the interior of `W` is open and closed and consists of regular points, and it
is carried along unchanged.  No compactness is used. -/
theorem isStrictTransformResolution_of_diff_interior {W : Set M}
    (hWa : IsComplexAnalyticSubset (n := n) W)
    {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
    {σ : M' → M} {E : List (Set M')}
    (h₀ : IsStrictTransformResolution n (W \ interior W) σ E) :
    IsStrictTransformResolution n W σ E := by
  set K := interior W with hKdef
  have hKc : IsClosed K := hWa.isClosed_interior
  have hKW : K ⊆ W := interior_subset
  have hS : singularSet (n := n) (W \ K) = singularSet (n := n) W := singularSet_diff_interior hWa
  have hKS : Disjoint K (singularSet (n := n) W) := disjoint_interior_singularSet W
  have hcont : Continuous σ := h₀.contMDiff.continuous
  have hsurj : Function.Surjective σ :=
    HironakaLocalPrincipalization.IsBlowupSequence.surjective h₀.isBlowupSequence
  have hexc := HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop
    h₀.admissible
  simp only [List.length_nil, List.drop_zero] at hexc
  rw [hS] at hexc
  -- the strict transforms of `W` and `W \ K`
  have hKexc : Disjoint (σ ⁻¹' K) (exceptionalLocus n σ) := by
    refine disjoint_left.mpr fun y hyK hyE => ?_
    exact disjoint_left.mp hKS hyK (hexc.2 (hexc.1 hyE))
  have hW' : strictTransform n σ W = strictTransform n σ (W \ K) ∪ σ ⁻¹' K := by
    have hWu : σ ⁻¹' W = σ ⁻¹' (W \ K) ∪ σ ⁻¹' K := by
      rw [← preimage_union, sdiff_union_self, union_eq_left.mpr hKW]
    rw [strictTransform, strictTransform, hWu, union_sdiff_distrib, closure_union,
      hKexc.sdiff_eq_left, (hKc.preimage hcont).closure_eq]
  have hW₀K : Disjoint (strictTransform n σ (W \ K)) (σ ⁻¹' K) := by
    refine disjoint_left.mpr fun y hy hyK => ?_
    exact (h₀.strictTransform_subset_preimage hy).2 hyK
  have hKopen : IsOpen (σ ⁻¹' K) := isOpen_interior.preimage hcont
  refine ⟨hS ▸ h₀.admissible, h₀.snc, ?_, ?_, hS ▸ h₀.isIsomorphismOver, ?_, ?_, ?_⟩
  · -- closed submanifold
    refine ⟨?_, fun y hy => ?_⟩
    · rw [hW']
      exact h₀.isClosed_strictTransform.union (hKc.preimage hcont)
    · by_cases hyK : y ∈ σ ⁻¹' K
      · refine ⟨n, ?_⟩
        refine regularAtDim_of_mem_nhds' (Filter.mem_of_superset (hKopen.mem_nhds hyK) ?_)
        rw [hW']
        exact subset_union_right
      · have hy₀ : y ∈ strictTransform n σ (W \ K) := by
          rw [hW'] at hy
          exact hy.resolve_right hyK
        obtain ⟨k, hk⟩ := h₀.isClosedSubmanifold.2 y hy₀
        refine ⟨k, RegularPointDimension.regularAtDim_of_inter_eq
          (hKc.preimage hcont).isOpen_compl hyK ?_ hk⟩
        rw [hW', union_inter_distrib_right, compl_eq_univ_sdiff, inter_sdiff_self, union_empty]
  · -- image
    rw [hW', image_union, h₀.image_eq, image_preimage_eq K hsurj, sdiff_union_self,
      union_eq_left.mpr hKW]
  · -- over the regular part
    ext y
    constructor
    · rintro ⟨hy, hyS⟩
      rw [hW'] at hy
      rcases hy with hy | hyK
      · have hmem : y ∈ strictTransform n σ (W \ K) ∩ σ ⁻¹' (singularSet (n := n) (W \ K))ᶜ :=
          ⟨hy, by rw [hS]; exact hyS⟩
        rw [h₀.inter_preimage_compl, hS] at hmem
        exact ⟨hmem.1.1, hmem.2⟩
      · exact ⟨hKW hyK, hyS⟩
    · rintro ⟨hyW, hyS⟩
      refine ⟨?_, hyS⟩
      rw [hW']
      by_cases hyK : σ y ∈ K
      · exact Or.inr hyK
      · left
        have hmem : y ∈ σ ⁻¹' ((W \ K) \ singularSet (n := n) (W \ K)) := by
          rw [hS]
          exact ⟨⟨hyW, hyK⟩, hyS⟩
        rw [← h₀.inter_preimage_compl] at hmem
        exact hmem.1
  · -- closure of the preimage of the regular part
    have hreg : σ ⁻¹' (W \ singularSet (n := n) W) =
        σ ⁻¹' ((W \ K) \ singularSet (n := n) (W \ K)) ∪ σ ⁻¹' K := by
      rw [hS, ← preimage_union]
      congr 1
      ext x
      constructor
      · rintro ⟨hxW, hxS⟩
        by_cases hxK : x ∈ K
        · exact Or.inr hxK
        · exact Or.inl ⟨⟨hxW, hxK⟩, hxS⟩
      · rintro (⟨⟨hxW, -⟩, hxS⟩ | hxK)
        · exact ⟨hxW, hxS⟩
        · exact ⟨hKW hxK, disjoint_left.mp hKS hxK⟩
    rw [hW', hreg, closure_union, ← h₀.eq_closure, (hKc.preimage hcont).closure_eq]
  · -- the trace of the exceptional divisor
    have hKE : Disjoint (σ ⁻¹' K) (⋃ H ∈ E, H) := by
      refine disjoint_left.mpr fun y hyK hyE => ?_
      exact disjoint_left.mp hKS hyK (hexc.2 hyE)
    have hKS' : Disjoint (σ ⁻¹' K) (σ ⁻¹' singularSet (n := n) W) := hKS.preimage σ
    rw [hW', union_inter_distrib_right, union_inter_distrib_right, hKS'.inter_eq, hKE.inter_eq,
      union_empty, union_empty, ← hS, h₀.inter_preimage_singular]

/-- **Resolution of an arbitrary closed analytic subset of a compact complex manifold (goal
G11a).**  The embedded resolution of `W \ interior W` resolves `W`. -/
theorem exists_isStrictTransformResolution_of_isAnalytic [CompactSpace M] {W : Set M}
    (hWa : IsComplexAnalyticSubset (n := n) W) :
    ∃ (M' : Type u) (_ : TopologicalSpace M') (_ : ChartedSpace (ComplexModel n) M')
      (_ : IsComplexManifold n M') (σ : M' → M) (E : List (Set M')),
      CompactSpace M' ∧ IsStrictTransformResolution n W σ E := by
  obtain ⟨M', _, _, _, σ, E, hcpt, h₀, -⟩ :=
    exists_isStrictTransformResolution (isComplexAnalyticSubset_diff_interior hWa)
      (interior_diff_interior W)
  exact ⟨M', inferInstance, inferInstance, inferInstance, σ, E, hcpt,
    isStrictTransformResolution_of_diff_interior hWa h₀⟩

end Interior

end

end Hironaka.HironakaResolutionSpace
