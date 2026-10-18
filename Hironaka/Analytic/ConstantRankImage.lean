/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.FibreDimensionLowerBound
import Hironaka.Analytic.AnalyticImageDimension
import Hironaka.Analytic.ConstantRankSubmanifold

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Images of proper constant-rank maps

Blueprint `rem:constant-rank-image` (Demailly, *Complex analytic and differential geometry*,
II.8.8; step M8 of the route to Remmert's proper mapping theorem, `blueprint/src/remmert.tex`).

Let `P` be a closed complex submanifold of dimension `m` of a complex manifold `X`, `G : X → Y`
holomorphic with `rank d(G|P) = r` at every point of `P`, and `G|P` proper.  Then `G(P)` is
analytic, `dim_y G(P) ≥ r` at every `y ∈ G(P)`, and every regular point of `G(P)` has dimension `r`
(`constantRankImage`).  (The source states it for open subsets `X' ⊆ X`, `Y' ⊆ Y`; these are complex
manifolds, `AnalyticSubsetOpens`.)

* `IsComplexAnalyticSubset.union`, `isComplexAnalyticSubset_biUnion`: finite unions of analytic
  sets are analytic (products of the local equations).
* `exists_local_piece`: near `x ∈ P` the image of a neighbourhood `P ∩ V` is, in the chart at `G x`,
  the zero set of a holomorphic map on an open set, and each of its points is a regular point of
  dimension `r` (`ConstantRankSubmanifold.exists_image_eq_graph` on the parametrization of `P`,
  whose rank is `rank d(G|P)` by `RankDegeneracy.rankAt_param_eq`).
* `constantRankImage`: the compact fibre over `y` is covered by finitely many such pieces;
  properness gives a neighbourhood `W` of `y` over which `P` lies in their union, so
  `G(P) ∩ W` is a finite union of zero sets.  The local dimension `≥ r` is monotonicity of
  dimension; the regular points have dimension `≤ r` by the fibre lower bound
  (`FibreDimensionLowerBound`) and the dimension of an image (`AnalyticImageDimension`).

Sorry-free.
-/

open Set Filter Topology Metric Module TopologicalSpace
open scoped Manifold ContDiff

noncomputable section

namespace Hironaka.ConstantRankImage

open Hironaka.RegularLocusDense AnalyticDimensionBasics AnalyticSubsetOpens
  AnalyticSubsetPreimage RankDegeneracy FiniteMapDimension StokesSingularLocusAnalytic
  DimensionMonotone FibreDimensionLowerBound AnalyticImageDimension ConstantRankSubmanifold

/-! ### Finite unions -/

section Union

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- Products of the local equations present a union. -/
def presentationUnion {A B : Set M} {x : M} (pA : ComplexAnalyticPresentationAt (n := n) A x)
    (pB : ComplexAnalyticPresentationAt (n := n) B x) :
    ComplexAnalyticPresentationAt (n := n) (A ∪ B) x where
  generatorCount := pA.generatorCount * pB.generatorCount
  generator := fun ij z =>
    pA.generator (finProdFinEquiv.symm ij).1 z * pB.generator (finProdFinEquiv.symm ij).2 z
  coordinateNeighborhood := pA.coordinateNeighborhood ∩ pB.coordinateNeighborhood
  isOpen_coordinateNeighborhood :=
    pA.isOpen_coordinateNeighborhood.inter pB.isOpen_coordinateNeighborhood
  center_mem_coordinateNeighborhood :=
    ⟨pA.center_mem_coordinateNeighborhood, pB.center_mem_coordinateNeighborhood⟩
  coordinateNeighborhood_subset_target :=
    inter_subset_left.trans pA.coordinateNeighborhood_subset_target
  generator_holomorphic := fun _ =>
    ((pA.generator_holomorphic _).mono inter_subset_left).mul
      ((pB.generator_holomorphic _).mono inter_subset_right)
  zeroLocus := by
    intro y hy hyN
    rw [mem_union, pA.zeroLocus hy hyN.1, pB.zeroLocus hy hyN.2]
    constructor
    · rintro (h | h) ij
      · rw [h, zero_mul]
      · rw [h, mul_zero]
    · intro h
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := hcon
      have := h (finProdFinEquiv (i, j))
      simp only [Equiv.symm_apply_apply] at this
      exact mul_ne_zero hi hj this

/-- The union of two analytic subsets is analytic. -/
theorem IsComplexAnalyticSubset.union {A B : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    (hB : IsComplexAnalyticSubset (n := n) B) : IsComplexAnalyticSubset (n := n) (A ∪ B) :=
  fun x => ⟨presentationUnion (hA x).some (hB x).some⟩

/-- A finite union of analytic subsets is analytic. -/
theorem isComplexAnalyticSubset_biUnion {ι : Type*} (t : Finset ι) {S : ι → Set M}
    (hS : ∀ i ∈ t, IsComplexAnalyticSubset (n := n) (S i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i ∈ t, S i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.set_biUnion_insert]
    exact IsComplexAnalyticSubset.union (hS a (Finset.mem_insert_self a t))
      (ih fun i hi => hS i (Finset.mem_insert_of_mem hi))

end Union

/-! ### Local pieces and the image -/

section Image

variable {n n' : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel n') Y]
  [IsComplexManifold n' Y]

/-- **A local piece of a constant-rank image.**  Near `x ∈ P` the image `G(P ∩ V)` lies in the
chart at `G x`, is there the zero set of a holomorphic map `h` on an open set `W`, and each of its
points is a regular point of `G(P ∩ V)` of dimension `r`. -/
theorem exists_local_piece {P : Set X} {m r : ℕ}
    (hPreg : ∀ x ∈ P, RegularAtDim (n := n) P x m) {G : X → Y}
    (hG : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') ∞ G)
    (hrank : ∀ x ∈ P, rankAt (n := n) (n' := n') G P x = r) {x : X} (hx : x ∈ P) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      G '' (P ∩ V) ⊆ (chartAt (ComplexModel n') (G x)).source ∧
      ∃ (W : Set (ComplexModel n')) (h : ComplexModel n' → ComplexModel n'),
        IsOpen W ∧ DifferentiableOn ℂ h W ∧
        (∀ y ∈ (chartAt (ComplexModel n') (G x)).source, (y ∈ G '' (P ∩ V) ↔
          (chartAt (ComplexModel n') (G x) y ∈ W ∧ h (chartAt (ComplexModel n') (G x) y) = 0))) ∧
        ∀ y ∈ G '' (P ∩ V), RegularAtDim (n := n') (G '' (P ∩ V)) y r := by
  have hxm := hPreg x hx
  have hmn : m ≤ n := hxm.1
  set e := complexChartAt (n := n) x with he
  set e'C := complexChartAt (n := n') (G x) with he'C
  set e' := chartAt (ComplexModel n') (G x) with he'
  have hxe : x ∈ e.val.source := mem_complexChartAt_source x
  obtain ⟨Ψ, hΨt, hΨ0, hflat⟩ := exists_chartFlattening hxm e hxe
  set Ω : Set (ComplexModel m) :=
    coordinateInclusion n m ⁻¹' Ψ.target ∩ param e Ψ m ⁻¹' (G ⁻¹' e'.source) with hΩ
  have hΩo : IsOpen Ω :=
    (continuousOn_param e Ψ hΨt m).isOpen_inter_preimage
      (Ψ.isOpen_target.preimage (coordinateInclusion n m).continuous)
      (e'.open_source.preimage hG.continuous)
  have hP0 : param e Ψ m 0 = x := by
    simp only [param]
    rw [map_zero, ← hΨ0, Ψ.left_inv _ Ψ.center_mem_source, e.val.left_inv hxe]
  have h0 : (0 : ComplexModel m) ∈ Ω := by
    refine ⟨?_, ?_⟩
    · rw [mem_preimage, map_zero, ← hΨ0]
      exact Ψ.mapsTo_toFun Ψ.center_mem_source
    · change G (param e Ψ m 0) ∈ e'.source
      rw [hP0]
      exact mem_chart_source _ (G x)
  set H : ComplexModel m → ComplexModel n' := fun w => e' (G (param e Ψ m w)) with hH
  have hHd : DifferentiableOn ℂ H Ω := fun w hw =>
    (differentiableAt_param e e'C Ψ hΨt (hG.mdifferentiable (by simp)) hw.1 hw.2).differentiableWithinAt
  have hHr : ∀ w ∈ Ω, finrank ℂ (LinearMap.range
      ((fderiv ℂ H w : ComplexModel m →L[ℂ] ComplexModel n') :
        ComplexModel m →ₗ[ℂ] ComplexModel n')) = r := by
    intro w hw
    obtain ⟨hwP, hrk⟩ := rankAt_param_eq hmn e e'C Ψ hΨt hflat hw.1 hw.2
      (hG.mdifferentiable (by simp) _)
    exact hrk.symm.trans (hrank _ hwP)
  obtain ⟨O, W, h, hOo, h0O, hOΩ, hWo, hhd, hHO, hreg⟩ := exists_image_eq_graph hΩo hHd hHr h0
  -- the neighbourhood `V` with `P ∩ V = param(O)`
  set V : Set X := e.val.source ∩
    e.val ⁻¹' (Ψ.source ∩ (fun z => coordinateProjection n m (Ψ.toFun z)) ⁻¹' O) with hV
  have hVo : IsOpen V :=
    e.val.isOpen_inter_preimage
      (((coordinateProjection n m).continuous.comp_continuousOn
        Ψ.toFun_holomorphic.continuousOn).isOpen_inter_preimage Ψ.isOpen_source hOo)
  have hxV : x ∈ V := by
    refine ⟨hxe, Ψ.center_mem_source, ?_⟩
    change coordinateProjection n m (Ψ.toFun (e.val x)) ∈ O
    rw [hΨ0, map_zero]
    exact h0O
  have hPV : P ∩ V = param e Ψ m '' O := by
    ext y
    constructor
    · rintro ⟨hyP, hys, hyΨ, hyO⟩
      refine ⟨_, hyO, ?_⟩
      have hpl : Ψ.toFun (e.val y) ∈ complexCoordinatePlane n m :=
        (hflat _ hyΨ).mp (by rw [e.val.left_inv hys]; exact hyP)
      simp only [param]
      rw [coordinateInclusion_coordinateProjection hpl, Ψ.left_inv _ hyΨ, e.val.left_inv hys]
    · rintro ⟨w, hwO, rfl⟩
      have hwΩ := hOΩ hwO
      have hs := Ψ.mapsTo_invFun hwΩ.1
      refine ⟨param_mem e Ψ hflat hwΩ.1, e.val.map_target (hΨt hs), ?_, ?_⟩
      · change e.val (e.val.symm _) ∈ Ψ.source
        rw [e.val.right_inv (hΨt hs)]
        exact hs
      · change coordinateProjection n m (Ψ.toFun (e.val (e.val.symm _))) ∈ O
        rw [e.val.right_inv (hΨt hs), Ψ.right_inv _ hwΩ.1,
          coordinateProjection_coordinateInclusion hmn]
        exact hwO
  have hGPV : G '' (P ∩ V) = (fun w => G (param e Ψ m w)) '' O := by
    rw [hPV, image_image]
  have hsrc : G '' (P ∩ V) ⊆ e'.source := by
    rw [hGPV]
    rintro _ ⟨w, hwO, rfl⟩
    exact (hOΩ hwO).2
  have hmem : ∀ y ∈ e'.source, (y ∈ G '' (P ∩ V) ↔ e' y ∈ H '' O) := by
    intro y hy
    rw [hGPV]
    constructor
    · rintro ⟨w, hwO, rfl⟩
      exact ⟨w, hwO, rfl⟩
    · rintro ⟨w, hwO, hw⟩
      exact ⟨w, hwO, e'.injOn (hOΩ hwO).2 hy hw⟩
  refine ⟨V, hVo, hxV, hsrc, W, h, hWo, hhd, fun y hy => ?_, fun y hy => ?_⟩
  · rw [hmem y hy, hHO]
    rfl
  · have hys := hsrc hy
    obtain ⟨hrn, -, Φ, -, -, hΦ⟩ := hreg (e' y) ((hmem y hys).mp hy)
    simp only [complexChartAt, chartAt_self_eq, OpenPartialHomeomorph.refl_source,
      OpenPartialHomeomorph.refl_apply, id_eq, mem_univ, forall_const] at hΦ
    have hc : e' y ∈ Φ.source := by
      have := Φ.center_mem_source
      simpa [complexChartAt, chartAt_self_eq] using this
    refine regularAtDim_of_flattening_of_mem (x := G x) hrn Φ (fun {y'} hy' hy'Φ => ?_) hy hys hc
    rw [hmem y' hy']
    exact hΦ hy'Φ

/-- **Images of proper constant-rank maps** (`rem:constant-rank-image`, `demailly-cadg:II.8.8`).
If `P` is a closed complex submanifold of dimension `m`, `G` is holomorphic with
`rank d(G|P) = r` on `P` and `G|P` is proper, then `G(P)` is analytic, `dim_y G(P) ≥ r` at every
`y ∈ G(P)`, and every regular point of `G(P)` has dimension `r`. -/
theorem constantRankImage {P : Set X} {m r : ℕ} (hPc : IsClosed P)
    (hPreg : ∀ x ∈ P, RegularAtDim (n := n) P x m) {G : X → Y}
    (hG : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n') ∞ G)
    (hrank : ∀ x ∈ P, rankAt (n := n) (n' := n') G P x = r) (hprop : ProperOn G P) :
    IsComplexAnalyticSubset (n := n') (G '' P) ∧
      (∀ y ∈ G '' P, LocDimGE (n := n') (G '' P) y r) ∧
      ∀ y k, RegularAtDim (n := n') (G '' P) y k → k = r := by
  classical
  choose! V hVo hxV hVs W h hWo hhd hmem hreg using
    fun x (hx : x ∈ P) => exists_local_piece hPreg hG hrank hx
  -- (a) `G(P)` is analytic
  have hana : IsComplexAnalyticSubset (n := n') (G '' P) := by
    refine isComplexAnalyticSubset_of_forall_opens fun y => ?_
    set e' := chartAt (ComplexModel n') y with he'
    set Fy : Set X := P ∩ G ⁻¹' {y} with hFy
    have hFc : IsCompact Fy := hprop {y} isCompact_singleton
    obtain ⟨t, ht⟩ := hFc.elim_finite_subcover (fun x : Fy => V x) (fun x => hVo x x.2.1)
      (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hxV x hx.1⟩)
    have hGt : ∀ i : Fy, G i = y := fun i => i.2.2
    set C : Set X := P \ ⋃ i ∈ t, V i with hC
    have hCc : IsClosed C := hPc.sdiff (isOpen_biUnion fun i _ => hVo i i.2.1)
    have : LocallyCompactSpace Y := ChartedSpace.locallyCompactSpace (ComplexModel n') Y
    obtain ⟨K, hKc, hKy⟩ := exists_compact_mem_nhds y
    have hCK : IsCompact (G '' (C ∩ G ⁻¹' K)) :=
      ((hprop K hKc).of_isClosed_subset (hCc.inter (hKc.isClosed.preimage hG.continuous))
        (inter_subset_inter_left _ sdiff_subset)).image hG.continuous
    have hyC : y ∉ G '' (C ∩ G ⁻¹' K) := by
      rintro ⟨x, ⟨⟨hxP, hxV'⟩, -⟩, hxy⟩
      exact hxV' (ht ⟨hxP, hxy⟩)
    have hWt : IsOpen (⋂ i ∈ t, W i) := isOpen_biInter_finset fun i _ => hWo i i.2.1
    set Wo : Set Y := (interior K ∩ (G '' (C ∩ G ⁻¹' K))ᶜ) ∩ (e'.source ∩ e' ⁻¹' ⋂ i ∈ t, W i)
      with hWo'
    have hWoo : IsOpen Wo :=
      (isOpen_interior.inter hCK.isClosed.isOpen_compl).inter (e'.isOpen_inter_preimage hWt)
    have hyWo : y ∈ Wo := by
      refine ⟨⟨mem_interior_iff_mem_nhds.mpr hKy, hyC⟩, mem_chart_source _ y, ?_⟩
      rw [mem_preimage, mem_iInter₂]
      intro i _
      have hyi : y ∈ G '' (P ∩ V i) := ⟨i, ⟨i.2.1, hxV i i.2.1⟩, hGt i⟩
      have := (hmem i i.2.1 y (by rw [hGt i]; exact mem_chart_source _ y)).mp hyi
      rw [hGt i] at this
      exact this.1
    refine ⟨⟨Wo, hWoo⟩, hyWo, ?_⟩
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
        have hx'C : x' ∉ C := fun hx'C => hy'W.1.2 ⟨x', ⟨hx'C, hx'K⟩, hx'y⟩
        have hx'V : x' ∈ ⋃ i ∈ t, V i := by
          by_contra hn
          exact hx'C ⟨hx'P, hn⟩
        obtain ⟨i, hit, hx'i⟩ := mem_iUnion₂.mp hx'V
        refine ⟨i, hit, ?_⟩
        have := (hmem i i.2.1 y' (by rw [hGt i]; exact hy's)).mp ⟨x', ⟨hx'P, hx'i⟩, hx'y⟩
        rw [hGt i] at this
        exact this.2
      · rintro ⟨i, hit, hi⟩
        have hWi : e' y' ∈ W i := by
          have := hy'W.2.2
          rw [mem_preimage, mem_iInter₂] at this
          exact this i hit
        have hmi := hmem i i.2.1 y' (by rw [hGt i]; exact hy's)
        rw [hGt i] at hmi
        obtain ⟨x', ⟨hx'P, -⟩, hx'y⟩ := hmi.mpr ⟨hWi, hi⟩
        exact ⟨x', hx'P, hx'y⟩
    rw [hset]
    refine isComplexAnalyticSubset_biUnion t fun i hit => ?_
    have hzero : {y' : (⟨Wo, hWoo⟩ : Opens Y) | h i (e' y') = 0} =
        (fun y' : (⟨Wo, hWoo⟩ : Opens Y) => h i (e' y')) ⁻¹' {0} := rfl
    rw [hzero]
    refine isComplexAnalyticSubset_preimage (n := n') ?_ (isComplexAnalyticSubset_singleton (n := n') (0 : ComplexModel n'))
    refine contMDiff_restrict (U := ⟨Wo, hWoo⟩) (f := fun y' => h i (e' y')) fun y' hy' => ?_
    have hy'W : e' y' ∈ W i := by
      have := hy'.2.2
      rw [mem_preimage, mem_iInter₂] at this
      exact this i hit
    have h1 : ContMDiffAt 𝓘(ℂ, ComplexModel n') 𝓘(ℂ, ComplexModel n') ∞ (h i) (e' y') :=
      (contDiffAt_of_differentiableOn_complex (hhd i i.2.1) (hWo i i.2.1) hy'W).contMDiffAt
    have h2 : ContMDiffAt 𝓘(ℂ, ComplexModel n') 𝓘(ℂ, ComplexModel n') ∞ e' y' :=
      (contMDiffOn_chart (n := ∞)).contMDiffAt (e'.open_source.mem_nhds hy'.2.1)
    exact (h1.comp y' h2).contMDiffWithinAt
  -- (b) local dimension `≥ r`
  have hloc : ∀ y ∈ G '' P, LocDimGE (n := n') (G '' P) y r := by
    rintro _ ⟨x, hx, rfl⟩
    exact locDimGE_of_regularAtDim_subset hana (image_mono inter_subset_left)
      (hreg x hx (G x) ⟨x, ⟨hx, hxV x hx⟩, rfl⟩)
  refine ⟨hana, hloc, fun y k hy => ?_⟩
  -- (c) regular points have dimension `r`
  have hPa : IsComplexAnalyticSubset (n := n) P :=
    isComplexAnalyticSubset_of_isClosedSubmanifold ⟨hPc, fun x hx => ⟨m, hPreg x hx⟩⟩
  have hpure : IsPureDim (n := n) P m := fun y j hy =>
    RegularPointDimension.eq_of_regularAtDim hy (hPreg y hy.2.1)
  obtain ⟨x₀, hx₀, -⟩ := hy.2.1
  have hrm : r ≤ m := by
    rw [← hrank x₀ hx₀]
    exact rankAt_le_of_regularAtDim G (hPreg x₀ hx₀)
  have hfib : ∀ x ∈ P, LocDimGE (n := n) (P ∩ G ⁻¹' {G x}) x (m - r) := fun x hx =>
    locDimGE_fibre hPa hpure hG (fun y hy => (hrank y hy.2.1).le) hx
  have hle := add_le_of_regularAtDim_image hG hPa hpure.dimLE hfib hy
  have hge := (hloc y hy.2.1).le_of_locDimLE (locDimLE_of_regularAtDim hy)
  omega

end Image

end Hironaka.ConstantRankImage
