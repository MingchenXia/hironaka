/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.IrreducibleNonemptyExact
import Hironaka.Analytic.RemmertStatements
import Hironaka.Analytic.ConstantRankImage
import Hironaka.Analytic.ClosureDifferenceAnalytic

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Remmert's theorem for an irreducible source (Step 1 of the induction)

Blueprint `rem:proper-image-irreducible` (Demailly, *Complex analytic and differential geometry*,
II.8.8).  Assume `(R_{m-1})` and `(RS_m)` (`RemmertStatements`).  Let `A ⊆ X` be irreducible
analytic with `dim A ≤ m` and `F|_A` proper.  Then `F(A)` is analytic.

`A` has pure dimension `d ≤ m`; `r` is the largest rank of `F` at regular points of `A`, and
`S = S_r(F, A)` (singular points and points of smaller rank, `RankDegeneracy`) is a proper analytic
subset, so `dim S ≤ m - 1` and `F(S)` is analytic by `(R_{m-1})`.  The saturation
`A' = A ∩ F⁻¹ F(S)` is analytic with `F(A') = F(S)`.  If `A'` is not all of `A` it is thin; off
`F(S)` the set `A \ A'` is a manifold of dimension `d` on which `F` has constant rank `r`, so
`E = F(A \ A')` is analytic in `Y \ F(S)` with `dim_y E ≥ r` (constant-rank pieces, glued by
properness: `nonempty_presentation_image`) and `dim E ≤ r`; by the fibre lower bound and the image
bound, every regular point of `F(S) = F(A')` has dimension `< r`.  `(RS_m)` gives that
`closure E = F(A)` is analytic.

* `isClosed_image_of_properOn`: images of proper maps into a manifold are closed;
* `rankAt_congr`: the rank of `F` on a set depends only on the germ of the set;
* `exists_maxRank`: the maximal rank on the regular locus is attained;
* `nonempty_presentation_image`: the image of a constant-rank manifold piece is analytic near any
  point over which the piece exhausts a set on which `F` is proper (relative form of
  `ConstantRankImage.constantRankImage`, part 1);
* `isComplexAnalyticSubset_image_of_irreducible`: the lemma.

Sorry-free.
-/

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.ProperImageIrreducible

open Hironaka.RegularLocusDense AnalyticDimensionBasics AnalyticSubsetOpens
  RemmertStatements RankDegeneracy ConstantRankImage AnalyticSubsetPreimage
  FibreDimensionLowerBound AnalyticImageDimension DimensionMonotone ThinDimensionDrop
  HolomorphicIdealSheaves

universe u₁ u₂

section Tools

variable {n k : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y]
  [IsComplexManifold k Y]

/-- The image of a set on which a continuous map into a manifold is proper is closed. -/
theorem isClosed_image_of_properOn {X' Y' : Type*} [TopologicalSpace X'] [TopologicalSpace Y']
    [LocallyCompactSpace Y'] [T2Space Y'] {F : X' → Y'} (hF : Continuous F) {A : Set X'}
    (hprop : ProperOn F A) : IsClosed (F '' A) := by
  refine isClosed_of_closure_subset fun y hy => ?_
  obtain ⟨K, hKc, hKy⟩ := exists_compact_mem_nhds y
  have hc : IsClosed (F '' (A ∩ F ⁻¹' K)) := ((hprop K hKc).image hF).isClosed
  have hy' : y ∈ closure (F '' (A ∩ F ⁻¹' K)) := by
    rw [mem_closure_iff_nhds] at hy ⊢
    intro t ht
    obtain ⟨z, hzt, x, hxA, rfl⟩ := hy (t ∩ K) (inter_mem ht hKy)
    exact ⟨F x, hzt.1, x, ⟨hxA, hzt.2⟩, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hc.closure_subset hy'
  exact ⟨x, hx.1, rfl⟩

/-- **The rank depends only on the germ of the set.** -/
theorem rankAt_congr {F : X → Y} {A P : Set X} {x : X} {O : Set X} (hO : IsOpen O) (hxO : x ∈ O)
    (hPA : P ∩ O = A ∩ O) :
    rankAt (n := n) (n' := k) F P x = rankAt (n := n) (n' := k) F A x := by
  have hmem : ∀ g : X → ℂ, (vanishingIdeal (n := n) P).mem x g ↔
      (vanishingIdeal (n := n) A).mem x g := by
    intro g
    change (_ ∧ _) ↔ (_ ∧ _)
    refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
    · filter_upwards [h, hO.mem_nhds hxO] with y hy hyO hyA
      have : y ∈ P ∩ O := by rw [hPA]; exact ⟨hyA, hyO⟩
      exact hy this.1
    · filter_upwards [h, hO.mem_nhds hxO] with y hy hyO hyP
      have : y ∈ A ∩ O := by rw [← hPA]; exact ⟨hyP, hyO⟩
      exact hy this.1
  have hT : tangentSpaceIn (complexChartAt (n := n) x) P x =
      tangentSpaceIn (complexChartAt (n := n) x) A x := by
    ext v
    simp only [mem_tangentSpaceIn, hmem]
  simp only [rankAt, rankIn]
  rw [hT]

/-- **The maximal rank on the regular locus is attained.** -/
theorem exists_maxRank (F : X → Y) {A : Set X} {d : ℕ} {x₀ : X}
    (hx₀ : RegularAtDim (n := n) A x₀ d) :
    ∃ r, r ≤ d ∧ (∃ y, RegularAtDim (n := n) A y d ∧ rankAt (n := n) (n' := k) F A y = r) ∧
      ∀ y, RegularAtDim (n := n) A y d → rankAt (n := n) (n' := k) F A y ≤ r := by
  classical
  let Q : ℕ → Prop := fun j => ∃ y, RegularAtDim (n := n) A y d ∧
    rankAt (n := n) (n' := k) F A y = j
  refine ⟨Nat.findGreatest Q d, Nat.findGreatest_le d, ?_, fun y hy => ?_⟩
  · exact Nat.findGreatest_spec (P := Q) (m := rankAt (n := n) (n' := k) F A x₀)
      (rankAt_le_of_regularAtDim F hx₀) ⟨x₀, hx₀, rfl⟩
  · exact Nat.le_findGreatest (P := Q) (rankAt_le_of_regularAtDim F hy) ⟨y, hy, rfl⟩

/-- **Images of constant-rank pieces are analytic over a proper exhaustion** (the gluing of
`ConstantRankImage.constantRankImage`, relative to a neighbourhood).  Let `P` be a manifold of
dimension `d` (`P` regular of dimension `d` at each of its points) on which `G` has rank `r`,
contained in a set `A` on which `G` is proper, and let `N` be a neighbourhood of `y` such that every
point of `A` over `N` lies in `P`.  Then `G(P)` has a presentation at `y`. -/
theorem nonempty_presentation_image {P A : Set X} {d r : ℕ}
    (hPreg : ∀ x ∈ P, RegularAtDim (n := n) P x d) {G : X → Y}
    (hG : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel k) ∞ G)
    (hrank : ∀ x ∈ P, rankAt (n := n) (n' := k) G P x = r) (hPA : P ⊆ A) (hprop : ProperOn G A)
    {y : Y}
    {N : Set Y} (hN : N ∈ 𝓝 y) (hAP : ∀ x ∈ A, G x ∈ N → x ∈ P) :
    Nonempty (ComplexAnalyticPresentationAt (n := k) (G '' P) y) := by
  classical
  have : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace (ComplexModel k) Y
  choose! V hVo hxV hVs W h hWo hhd hmem hreg using
    fun x (hx : x ∈ P) => exists_local_piece hPreg hG hrank hx
  set e' := chartAt (ComplexModel k) y with he'
  set Fy : Set X := A ∩ G ⁻¹' {y} with hFy
  have hFc : IsCompact Fy := hprop {y} isCompact_singleton
  have hFP : ∀ x ∈ Fy, x ∈ P := fun x hx => hAP x hx.1 (by rw [hx.2]; exact mem_of_mem_nhds hN)
  obtain ⟨t, ht⟩ := hFc.elim_finite_subcover (fun x : Fy => V x) (fun x => hVo x (hFP x x.2))
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV x (hFP x hx)⟩)
  have hGt : ∀ i : Fy, G i = y := fun i => i.2.2
  have hiP : ∀ i : Fy, (i : X) ∈ P := fun i => hFP i i.2
  obtain ⟨K, ⟨hKy, hKc⟩, hKN⟩ := (compact_basis_nhds y).mem_iff.mp hN
  set C : Set X := (A ∩ G ⁻¹' K) \ ⋃ i ∈ t, V i with hC
  have hCc : IsCompact C :=
    (hprop K hKc).diff (isOpen_biUnion fun i _ => hVo i (hiP i))
  have hCK : IsCompact (G '' C) := hCc.image hG.continuous
  have hyC : y ∉ G '' C := by
    rintro ⟨x, ⟨⟨hxA, -⟩, hxV'⟩, hxy⟩
    exact hxV' (ht ⟨hxA, hxy⟩)
  have hWt : IsOpen (⋂ i ∈ t, W i) := isOpen_biInter_finset fun i _ => hWo i (hiP i)
  set Wo : Set Y := (interior K ∩ (G '' C)ᶜ) ∩ (e'.source ∩ e' ⁻¹' ⋂ i ∈ t, W i) with hWo'
  have hWoo : IsOpen Wo :=
    (isOpen_interior.inter hCK.isClosed.isOpen_compl).inter (e'.isOpen_inter_preimage hWt)
  have hyWo : y ∈ Wo := by
    refine ⟨⟨mem_interior_iff_mem_nhds.mpr hKy, hyC⟩, mem_chart_source _ y, ?_⟩
    rw [mem_preimage, mem_iInter₂]
    intro i _
    have hyi : y ∈ G '' (P ∩ V i) := ⟨i, ⟨hiP i, hxV i (hiP i)⟩, hGt i⟩
    have := (hmem i (hiP i) y (by rw [hGt i]; exact mem_chart_source _ y)).mp hyi
    rw [hGt i] at this
    exact this.1
  refine nonempty_presentation_of_preimage_val (U := ⟨Wo, hWoo⟩) ?_ hyWo
  have hset : ((↑) ⁻¹' (G '' P) : Set (⟨Wo, hWoo⟩ : Opens Y)) =
      ⋃ i ∈ t, {y' : (⟨Wo, hWoo⟩ : Opens Y) | h i (e' y') = 0} := by
    ext y'
    have hy'W := y'.2
    have hy's : (y' : Y) ∈ e'.source := hy'W.2.1
    simp only [mem_preimage, mem_iUnion, mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨x', hx'P, hx'y⟩
      have hx'K : x' ∈ G ⁻¹' K := by
        rw [mem_preimage, hx'y]
        exact interior_subset hy'W.1.1
      have hx'A : x' ∈ A := hPA hx'P
      have hx'V : x' ∈ ⋃ i ∈ t, V i := by
        by_contra hn
        exact hy'W.1.2 ⟨x', ⟨⟨hx'A, hx'K⟩, hn⟩, hx'y⟩
      obtain ⟨i, hit, hx'i⟩ := mem_iUnion₂.mp hx'V
      refine ⟨i, hit, ?_⟩
      have := (hmem i (hiP i) y' (by rw [hGt i]; exact hy's)).mp ⟨x', ⟨hx'P, hx'i⟩, hx'y⟩
      rw [hGt i] at this
      exact this.2
    · rintro ⟨i, hit, hi⟩
      have hWi : e' y' ∈ W i := by
        have := hy'W.2.2
        rw [mem_preimage, mem_iInter₂] at this
        exact this i hit
      have hmi := hmem i (hiP i) y' (by rw [hGt i]; exact hy's)
      rw [hGt i] at hmi
      obtain ⟨x', ⟨hx'P, -⟩, hx'y⟩ := hmi.mpr ⟨hWi, hi⟩
      exact ⟨x', hx'P, hx'y⟩
  rw [hset]
  refine isComplexAnalyticSubset_biUnion t fun i hit => ?_
  have hzero : {y' : (⟨Wo, hWoo⟩ : Opens Y) | h i (e' y') = 0} =
      (fun y' : (⟨Wo, hWoo⟩ : Opens Y) => h i (e' y')) ⁻¹' {0} := rfl
  rw [hzero]
  refine isComplexAnalyticSubset_preimage (n := k) ?_
    (isComplexAnalyticSubset_singleton (n := k) (0 : ComplexModel k))
  refine contMDiff_restrict (U := ⟨Wo, hWoo⟩) (f := fun y' => h i (e' y')) fun y' hy' => ?_
  have hy'W : e' y' ∈ W i := by
    have := hy'.2.2
    rw [mem_preimage, mem_iInter₂] at this
    exact this i hit
  have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ (h i) (e' y') :=
    (contDiffAt_of_differentiableOn_complex (hhd i (hiP i)) (hWo i (hiP i)) hy'W).contMDiffAt
  have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel k) ∞ e' y' :=
    (contMDiffOn_chart (n := ∞)).contMDiffAt (e'.open_source.mem_nhds hy'.2.1)
  exact (h1.comp y' h2).contMDiffWithinAt

end Tools

/-- **Remmert's theorem for an irreducible source** (`rem:proper-image-irreducible`): under
`(R_{m-1})` and `(RS_m)`, the image of an irreducible analytic set of dimension `≤ m` under a
holomorphic map which is proper on it is analytic. -/
theorem isComplexAnalyticSubset_image_of_irreducible {m : ℕ}
    (hR : ProperImageStatement.{u₁, u₂} (m - 1)) (hRS : RemmertSteinStatement.{u₂} m)
    {n k : ℕ} {X : Type u₁} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X] {Y : Type u₂} [TopologicalSpace Y] [ChartedSpace (ComplexModel k) Y]
    [IsComplexManifold k Y] {F : X → Y}
    (hF : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel k) ∞ F) {A : Set X}
    (hA : IsComplexAnalyticallyIrreducible (n := n) A) (hdim : DimLE (n := n) A m)
    (hprop : ProperOn F A) : IsComplexAnalyticSubset (n := k) (F '' A) := by
  classical
  have hAa := hA.analytic
  -- pure dimension `d`
  obtain ⟨z₀, hz₀⟩ := hA.nonempty
  obtain ⟨x₀, -, d, hx₀⟩ := exists_regularAtDim_mem_nhds hAa hz₀ univ_mem
  let V : ClosedIrreducibleAnalyticSubvariety n X :=
    { carrier := A, isClosed_carrier := hAa.isClosed, irreducible_carrier := hA, dim := d
      dim_le := hx₀.1, regularLocus_nonempty := ⟨x₀, hx₀⟩ }
  have hpure : IsPureDim (n := n) A d := fun y j hy => PureDimension.eq_dim_of_regularAtDim V hy
  have hdm : d ≤ m := hdim x₀ d hx₀
  -- the maximal rank and the bad set
  obtain ⟨r, hrd, ⟨y₀, hy₀, hy₀r⟩, hrmax⟩ := exists_maxRank (k := k) F hx₀
  set S := rankDegeneracyLocus n k F A d r with hSdef
  have hSa : IsComplexAnalyticSubset (n := n) S :=
    isComplexAnalyticSubset_rankDegeneracyLocus hAa hpure (hF.mdifferentiable (by simp)) r
  have hSA : S ⊆ A := rankDegeneracyLocus_subset F A d r
  have hy₀S : y₀ ∉ S := by
    rintro (⟨-, hy⟩ | ⟨-, hy⟩)
    · exact hy hy₀
    · omega
  -- proper analytic subsets of `A` are thin
  have hthin_of : ∀ T : Set X, IsComplexAnalyticSubset (n := n) T → T ⊆ A → T ≠ A →
      ∀ O : Set X, IsOpen O → O ∩ A ⊆ T → O ∩ A = ∅ := by
    intro T hT hTA hne O hO hOT
    by_contra hOA
    refine hne (ClosureDifferenceAnalytic.eq_of_subset_of_inter_open_subset hT hA hTA hO ?_ ?_)
    · obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr hOA
      exact ⟨x, hx.2, hx.1⟩
    · intro x hx
      exact hOT ⟨hx.2, hx.1⟩
  have hSne : S ≠ A := fun h => hy₀S (h ▸ hy₀.2.1)
  have hSdim : DimLE (n := n) S (m - 1) := fun y j hy => by
    have := lt_of_regularAtDim_of_thin hAa hSA (hthin_of S hSa hSA hSne) hpure.dimLE hy
    omega
  have hSprop : ProperOn F S := fun K hK =>
    (hprop K hK).of_isClosed_subset (hSa.isClosed.inter (hK.isClosed.preimage hF.continuous))
      (inter_subset_inter_left _ hSA)
  have hFS : IsComplexAnalyticSubset (n := k) (F '' S) := hR hF hSa hSdim hSprop
  -- the saturation `A'`
  set A' := A ∩ F ⁻¹' (F '' S) with hA'def
  have hA'a : IsComplexAnalyticSubset (n := n) A' :=
    hAa.inter (isComplexAnalyticSubset_preimage hF hFS)
  have hA'A : A' ⊆ A := inter_subset_left
  have hFA' : F '' A' = F '' S := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨x, ⟨hSA hx, x, hx, rfl⟩, rfl⟩
  by_cases hA'eq : A' = A
  · rw [← hA'eq, hFA']
    exact hFS
  have hA'thin := hthin_of A' hA'a hA'A hA'eq
  -- the regular part `P = A \ A'` off `F(S)`
  set P := A \ A' with hPdef
  set Y' : Set Y := (F '' S)ᶜ with hY'
  have hY'o : IsOpen Y' := hFS.isClosed.isOpen_compl
  have hX'o : IsOpen (F ⁻¹' Y') := hY'o.preimage hF.continuous
  have hAX' : A ∩ F ⁻¹' Y' = P ∩ F ⁻¹' Y' := by
    ext x
    simp only [hPdef, hA'def, hY', mem_inter_iff, Set.mem_sdiff, mem_preimage, mem_compl_iff]
    tauto
  have hPX' : P ⊆ F ⁻¹' Y' := fun x hx => hx.2 ∘ fun h => ⟨hx.1, h⟩
  have hPS : ∀ x ∈ P, x ∉ S := fun x hx hxS => hx.2 ⟨hx.1, x, hxS, rfl⟩
  have hPreg : ∀ x ∈ P, RegularAtDim (n := n) P x d := by
    intro x hx
    have hxA : RegularAtDim (n := n) A x d := by
      by_contra hreg
      exact hPS x hx (Or.inl ⟨hx.1, hreg⟩)
    exact RegularPointDimension.regularAtDim_of_inter_eq hX'o (hPX' hx) hAX' hxA
  have hrank : ∀ x ∈ P, rankAt (n := n) (n' := k) F P x = r := by
    intro x hx
    have hxA : RegularAtDim (n := n) A x d := by
      by_contra hreg
      exact hPS x hx (Or.inl ⟨hx.1, hreg⟩)
    rw [rankAt_congr hX'o (hPX' hx) hAX'.symm]
    refine le_antisymm (hrmax x hxA) ?_
    by_contra hlt
    exact hPS x hx (Or.inr ⟨hxA, by omega⟩)
  set E := F '' P with hEdef
  -- `F(A) = closure E`
  have : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace (ComplexModel k) Y
  have hFAc : IsClosed (F '' A) := isClosed_image_of_properOn hF.continuous hprop
  have hclos : closure E = F '' A := by
    apply Subset.antisymm
    · exact hFAc.closure_subset_iff.mpr (image_mono sdiff_subset)
    · rintro _ ⟨x, hx, rfl⟩
      have hxc : x ∈ closure P := by
        rw [mem_closure_iff]
        intro O hO hxO
        by_contra hempty
        have hsub : O ∩ A ⊆ A' := by
          intro z hz
          by_contra hz'
          exact hempty ⟨z, hz.1, hz.2, hz'⟩
        have := hA'thin O hO hsub
        exact this.subset ⟨hxO, hx⟩
      exact image_closure_subset_closure_image hF.continuous (mem_image_of_mem F hxc)
  -- the fibre lower bound on `A`
  have hfibA : ∀ x ∈ A, LocDimGE (n := n) (A ∩ F ⁻¹' {F x}) x (d - r) := fun x hx =>
    locDimGE_fibre hAa hpure hF (fun y hy => hrmax y hy) hx
  -- `E` is analytic off `F(S)`
  have hEpres : ∀ y, y ∉ F '' S → Nonempty (ComplexAnalyticPresentationAt (n := k) E y) := by
    intro y hy
    refine nonempty_presentation_image hPreg hF hrank sdiff_subset hprop (hY'o.mem_nhds hy) ?_
    intro x hxA hxY
    refine ⟨hxA, fun hxA' => hxY hxA'.2⟩
  have hdisj : Disjoint E (F '' S) := by
    rw [disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ hxS
    exact hx.2 ⟨hx.1, hxS⟩
  -- `dim E ≤ m`
  have hEdim : DimLE (n := k) E m := by
    intro y j hy
    have hyY' : y ∈ Y' := disjoint_left.mp hdisj hy.2.1
    have hEA : E ∩ Y' = F '' A ∩ Y' := by
      ext z
      constructor
      · rintro ⟨⟨x, hx, rfl⟩, hz⟩
        exact ⟨⟨x, hx.1, rfl⟩, hz⟩
      · rintro ⟨⟨x, hx, rfl⟩, hz⟩
        exact ⟨⟨x, ⟨hx, fun h => hz h.2⟩, rfl⟩, hz⟩
    have hyA := RegularPointDimension.regularAtDim_of_inter_eq hY'o hyY' hEA hy
    have := add_le_of_regularAtDim_image hF hAa hpure.dimLE hfibA hyA
    omega
  -- `dim_y E ≥ r`
  have hEana' : IsComplexAnalyticSubset (n := k) ((↑) ⁻¹' E : Set (⟨Y', hY'o⟩ : Opens Y)) :=
    isComplexAnalyticSubset_preimage_val_of_forall fun y hy => hEpres y hy
  have hEloc : ∀ y ∈ E, LocDimGE (n := k) E y r := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨V, -, hxV, -, -, -, -, -, -, hreg⟩ := exists_local_piece hPreg hF hrank hx
    have hyY' : F x ∈ Y' := hPX' hx
    have hsub : ((↑) ⁻¹' (F '' (P ∩ V)) : Set (⟨Y', hY'o⟩ : Opens Y)) ⊆ (↑) ⁻¹' E :=
      preimage_mono (image_mono inter_subset_left)
    have hreg' : RegularAtDim (n := k) ((↑) ⁻¹' (F '' (P ∩ V)) : Set (⟨Y', hY'o⟩ : Opens Y))
        ⟨F x, hyY'⟩ r :=
      regularAtDim_preimage_val_iff.mpr (hreg (F x) ⟨x, ⟨hx, hxV⟩, rfl⟩)
    exact locDimGE_preimage_val_iff.mp (locDimGE_of_regularAtDim_subset hEana' hsub hreg')
  -- regular points of `F(S)` have dimension `< r`
  have hBdim : ∀ y j, RegularAtDim (n := k) (F '' S) y j → j < r := by
    intro y j hy
    rw [← hFA'] at hy
    obtain ⟨x, hxA', -⟩ := hy.2.1
    obtain ⟨x', -, j', hx'⟩ := exists_regularAtDim_mem_nhds hA'a hxA' univ_mem
    have hj'd := lt_of_regularAtDim_of_thin hAa hA'A hA'thin hpure.dimLE hx'
    have hA'dim : DimLE (n := n) A' (d - 1) := fun z i hz => by
      have := lt_of_regularAtDim_of_thin hAa hA'A hA'thin hpure.dimLE hz
      omega
    have hfib' : ∀ x ∈ A', LocDimGE (n := n) (A' ∩ F ⁻¹' {F x}) x (d - r) := by
      intro x hx
      have hset : A' ∩ F ⁻¹' {F x} = A ∩ F ⁻¹' {F x} := by
        ext z
        simp only [hA'def, mem_inter_iff, mem_preimage, mem_singleton_iff]
        constructor
        · rintro ⟨⟨hz, -⟩, hzx⟩
          exact ⟨hz, hzx⟩
        · rintro ⟨hz, hzx⟩
          exact ⟨⟨hz, by rw [hzx]; exact hx.2⟩, hzx⟩
      rw [hset]
      exact hfibA x hx.1
    have := add_le_of_regularAtDim_image hF hA'a hA'dim hfib' hy
    omega
  rw [← hclos]
  exact hRS hFS hBdim hdisj hEpres hEdim hEloc

end Hironaka.ProperImageIrreducible
