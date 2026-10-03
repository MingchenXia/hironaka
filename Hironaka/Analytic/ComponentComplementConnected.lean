/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.RegularLocusComponent
import Hironaka.Analytic.HypersurfaceComplementConnected
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.RegularLocusDense
import Hironaka.Analytic.HolomorphicZeroSetThin
set_option autoImplicit false

/-!
# The complement of an analytic set in a regular component

Let `C` be the connected component through a regular point `c` of the regular locus of an
analytic subset `A` of a complex manifold, and `T` an analytic subset not containing `C`.

* `exists_isOpen_isPreconnected_diff`: every point of `C` has an open neighbourhood `W` such
  that `(W ∩ C) \ T` is preconnected and dense in `W ∩ C`.  On a flattened ball `W ∩ C` is
  parametrized by a ball of `ℂ^j`; some local equation `g` of `T` does not vanish identically
  there (otherwise `T ⊇ C` by the identity theorem along the component), and
  `(W ∩ C) \ T` is the image of the path-connected dense set `ball \ g⁻¹(0)`.
* `isPreconnected_component_diff_and_subset_closure`: `C \ T` is preconnected and dense in
  `C`.  An open cover of `C \ T` by two relatively disjoint pieces propagates along `C`
  through the local neighbourhoods above, which are then all on one side by connectedness
  of `C`.
-/

open Set Filter Metric
open scoped Topology

namespace Hironaka.ComponentComplementConnected

open RegularLocusDense RegularLocusComponent HypersurfaceComplementConnected

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- The inclusion `ℂ^j → ℂ^n` preserves norms. -/
theorem norm_coordinateInclusion {j : ℕ} (hj : j ≤ n) (w : ComplexModel j) :
    ‖coordinateInclusion n j w‖ = ‖w‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [coordinateInclusion_apply]
  let g : ℕ → ℝ := fun k => if h : k < j then ‖w ⟨k, h⟩‖ ^ 2 else 0
  have h1 : ∑ i : Fin n, ‖(if h : i.1 < j then w ⟨i.1, h⟩ else 0)‖ ^ 2 =
      ∑ i : Fin n, g i := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g]
    split_ifs <;> simp
  have h2 : ∑ a : Fin j, ‖w a‖ ^ 2 = ∑ a : Fin j, g a :=
    Finset.sum_congr rfl fun a _ => by simp [g, a.2]
  rw [h1, h2, Fin.sum_univ_eq_sum_range g, Fin.sum_univ_eq_sum_range g]
  refine (Finset.sum_subset (Finset.range_mono hj) fun k _ hk => ?_).symm
  simp only [Finset.mem_range, not_lt] at hk
  simp [g, not_lt.mpr hk]

omit [IsComplexManifold n M] in
theorem preimage_coordinateInclusion_ball {j : ℕ} (hj : j ≤ n) (r : ℝ) :
    coordinateInclusion n j ⁻¹' ball (0 : ComplexModel n) r = ball (0 : ComplexModel j) r := by
  ext u
  simp [norm_coordinateInclusion hj]

/-- **Local statement.**  Near every point of the component `C`, `C \ T` is preconnected and
dense in `C`. -/
theorem exists_isOpen_isPreconnected_diff {A T : Set M}
    (hT : IsComplexAnalyticSubset (n := n) T) {c x : M}
    (hK : ¬ component (n := n) A c ⊆ T) (hx : x ∈ component (n := n) A c) :
    ∃ W : Set M, IsOpen W ∧ x ∈ W ∧
      IsPreconnected ((W ∩ component (n := n) A c) \ T) ∧
      W ∩ component (n := n) A c ⊆ closure ((W ∩ component (n := n) A c) \ T) := by
  obtain ⟨j, hj⟩ := component_subset_regularPoints (n := n) A c hx
  obtain ⟨P⟩ := hT x
  obtain ⟨F, hN⟩ := exists_flatBall hj P.isOpen_coordinateNeighborhood
    P.center_mem_coordinateNeighborhood
  set K := component (n := n) A c with hKdef
  set e := (complexChartAt (n := n) x).val with he
  have hWK : F.nbhd ∩ K = A ∩ F.nbhd :=
    Subset.antisymm (fun z hz => ⟨component_subset (n := n) A c hz.2, hz.1⟩)
      (fun z hz => ⟨hz.2, F.inter_nbhd_subset_component hx hz⟩)
  have hD := preimage_coordinateInclusion_ball (n := n) F.dim_le F.radius
  let ψ : ComplexModel j → M := fun u => F.param (coordinateInclusion n j u)
  let g : Fin P.generatorCount → ComplexModel j → ℂ :=
    fun i u => P.generator i (F.Φ.invFun (coordinateInclusion n j u))
  have hball : ∀ u ∈ ball (0 : ComplexModel j) F.radius,
      coordinateInclusion n j u ∈ ball (0 : ComplexModel n) F.radius := by
    intro u hu
    rw [← hD] at hu
    exact hu
  have hg : ∀ i, DifferentiableOn ℂ (g i) (ball (0 : ComplexModel j) F.radius) := fun i =>
    (P.generator_holomorphic i).comp
      (F.Φ.invFun_holomorphic.comp (coordinateInclusion n j).differentiableOn
        (fun u hu => F.ball_subset (hball u hu)))
      (fun u hu => hN _ (hball u hu))
  have hψ : ContinuousOn ψ (ball (0 : ComplexModel j) F.radius) :=
    F.continuousOn_param.comp (coordinateInclusion n j).continuous.continuousOn hball
  have hψmem : ∀ u ∈ ball (0 : ComplexModel j) F.radius, ψ u ∈ A ∩ F.nbhd := fun u hu =>
    ⟨F.param_mem (hball u hu) (coordinateInclusion_mem_complexCoordinatePlane u),
      F.param_mem_nbhd (hball u hu)⟩
  have hsurj : A ∩ F.nbhd ⊆ ψ '' ball (0 : ComplexModel j) F.radius := by
    rintro z ⟨hzA, hzW⟩
    have hzW' := F.mem_nbhd_iff.mp hzW
    have hp := (F.mem_iff_of_mem_nbhd hzW).mp hzA
    refine ⟨coordinateProjection n j (F.Φ.toFun (e z)), ?_, ?_⟩
    · rw [← hD]
      show coordinateInclusion n j _ ∈ ball (0 : ComplexModel n) F.radius
      rw [coordinateInclusion_coordinateProjection hp]
      exact hzW'.2.2
    · show F.param (coordinateInclusion n j _) = z
      rw [coordinateInclusion_coordinateProjection hp, F.param_chart hzW]
  have hTiff : ∀ u ∈ ball (0 : ComplexModel j) F.radius, ψ u ∈ T ↔ ∀ i, g i u = 0 := by
    intro u hu
    have hmem : e (ψ u) ∈ P.coordinateNeighborhood := by
      show e (F.param _) ∈ _
      rw [F.chart_param (hball u hu)]
      exact hN _ (hball u hu)
    rw [P.zeroLocus (F.param_mem_source (hball u hu)) hmem]
    show (∀ i, P.generator i (e (F.param (coordinateInclusion n j u))) = 0) ↔ _
    rw [F.chart_param (hball u hu)]
  obtain ⟨i, hi⟩ : ∃ i, ¬ ∀ᶠ u in 𝓝 (0 : ComplexModel j), g i u = 0 := by
    by_contra! h
    rw [← Filter.eventually_all] at h
    obtain ⟨ε, hε, hεs⟩ := Metric.eventually_nhds_iff_ball.mp h
    apply hK
    have hΦc : ContinuousOn (fun z => F.Φ.toFun (e z)) F.nbhd :=
      F.Φ.toFun_holomorphic.continuousOn.comp
        (e.continuousOn.mono fun z hz => (F.mem_nbhd_iff.mp hz).1)
        fun z hz => (F.mem_nbhd_iff.mp hz).2.1
    set O := F.nbhd ∩ (fun z => F.Φ.toFun (e z)) ⁻¹' ball (0 : ComplexModel n) ε with hOdef
    have hO : IsOpen O := hΦc.isOpen_inter_preimage F.isOpen_nbhd isOpen_ball
    have hxO : x ∈ O := by
      refine ⟨F.mem_nbhd, ?_⟩
      show F.Φ.toFun (e x) ∈ ball (0 : ComplexModel n) ε
      rw [F.map_center]
      exact mem_ball_self hε
    refine component_subset_of_isOpen hT F.isOpen_nbhd ⟨x, F.mem_nbhd, hx⟩ ?_
    rw [hWK]
    refine F.inter_nbhd_subset_of_isOpen P hN hO ⟨x, hxO, hj.2.1, F.mem_nbhd⟩ ?_
    rintro z ⟨hzO, hzAW⟩
    obtain ⟨u, hu, rfl⟩ := hsurj hzAW
    refine (hTiff u hu).mpr (hεs u ?_)
    have h1 : F.Φ.toFun (e (ψ u)) = coordinateInclusion n j u := by
      show F.Φ.toFun (e (F.param _)) = _
      rw [F.chart_param (hball u hu), F.Φ.right_inv _ (F.ball_subset (hball u hu))]
    have h2 : F.Φ.toFun (e (ψ u)) ∈ ball (0 : ComplexModel n) ε := hzO.2
    rw [h1] at h2
    rw [← preimage_coordinateInclusion_ball F.dim_le]
    exact h2
  set S := ball (0 : ComplexModel j) F.radius \ g i ⁻¹' {0} with hS
  have hSconn : IsPreconnected S :=
    (isPathConnected_ball_diff_zeroSet F.radius_pos (hg i) hi).isConnected.isPreconnected
  have hSdense : ball (0 : ComplexModel j) F.radius ⊆ closure S :=
    RiemannExtension.dense_compl_zeroSet isOpen_ball (convex_ball _ _).isPreconnected (hg i)
      (mem_ball_self F.radius_pos) hi
  have himS : ψ '' S ⊆ (F.nbhd ∩ K) \ T := by
    rintro _ ⟨u, ⟨hu, hu0⟩, rfl⟩
    rw [hWK]
    exact ⟨hψmem u hu, fun hT' => hu0 ((hTiff u hu).mp hT' i)⟩
  have hcl : F.nbhd ∩ K ⊆ closure (ψ '' S) := by
    rw [hWK]
    intro z hz
    obtain ⟨u, hu, rfl⟩ := hsurj hz
    exact ((hψ u hu).mono sdiff_subset).mem_closure_image (hSdense hu)
  refine ⟨F.nbhd, F.isOpen_nbhd, F.mem_nbhd, ?_, hcl.trans (closure_mono himS)⟩
  exact (hSconn.image ψ (hψ.mono sdiff_subset)).subset_closure himS (sdiff_subset.trans hcl)

theorem isPreconnected_component_diff_and_subset_closure {A T : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hT : IsComplexAnalyticSubset (n := n) T)
    {c : M} {k : ℕ} (hc : RegularAtDim (n := n) A c k)
    (hK : ¬ RegularLocusComponent.component (n := n) A c ⊆ T) :
    IsPreconnected (RegularLocusComponent.component (n := n) A c \ T) ∧
      RegularLocusComponent.component (n := n) A c ⊆
        closure (RegularLocusComponent.component (n := n) A c \ T) := by
  have _ := hA
  have _ := hc
  set K := component (n := n) A c with hKdef
  have hloc := fun {x : M} (hx : x ∈ K) => exists_isOpen_isPreconnected_diff hT hK hx
  refine ⟨?_, fun x hx => ?_⟩
  swap
  · obtain ⟨W, -, hxW, -, hWcl⟩ := hloc hx
    exact closure_mono (sdiff_subset_sdiff_left inter_subset_right) (hWcl ⟨hxW, hx⟩)
  rw [isPreconnected_iff_subset_of_disjoint]
  intro u v hu hv huv hdisj
  let u' := ⋃₀ {W : Set M | IsOpen W ∧ W ∩ K ⊆ closure ((W ∩ K) \ T) ∧ (W ∩ K) \ T ⊆ u}
  let v' := ⋃₀ {W : Set M | IsOpen W ∧ W ∩ K ⊆ closure ((W ∩ K) \ T) ∧ (W ∩ K) \ T ⊆ v}
  have hu' : IsOpen u' := isOpen_sUnion fun W hW => hW.1
  have hv' : IsOpen v' := isOpen_sUnion fun W hW => hW.1
  have hcover : K ⊆ u' ∪ v' := by
    intro x hx
    obtain ⟨W, hW, hxW, hWc, hWcl⟩ := hloc hx
    have hsub : (W ∩ K) \ T ⊆ u ∪ v :=
      fun z hz => huv ⟨hz.1.2, hz.2⟩
    have hdisj' : (W ∩ K) \ T ∩ (u ∩ v) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      have : z ∈ (K \ T) ∩ (u ∩ v) := ⟨⟨hz.1.1.2, hz.1.2⟩, hz.2⟩
      rw [hdisj] at this
      exact this
    rcases isPreconnected_iff_subset_of_disjoint.mp hWc u v hu hv hsub hdisj' with h | h
    · exact Or.inl (mem_sUnion.mpr ⟨W, ⟨hW, hWcl, h⟩, hxW⟩)
    · exact Or.inr (mem_sUnion.mpr ⟨W, ⟨hW, hWcl, h⟩, hxW⟩)
  have hdisjK : K ∩ (u' ∩ v') = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro x ⟨hxK, hxu, hxv⟩
    obtain ⟨W₁, ⟨hW₁, hW₁cl, hW₁u⟩, hxW₁⟩ := mem_sUnion.mp hxu
    obtain ⟨W₂, ⟨hW₂, -, hW₂v⟩, hxW₂⟩ := mem_sUnion.mp hxv
    obtain ⟨z, hzW₂, hz⟩ := mem_closure_iff.mp (hW₁cl ⟨hxW₁, hxK⟩) W₂ hW₂ hxW₂
    have : z ∈ (K \ T) ∩ (u ∩ v) :=
      ⟨⟨hz.1.2, hz.2⟩, hW₁u hz, hW₂v ⟨⟨hzW₂, hz.1.2⟩, hz.2⟩⟩
    rw [hdisj] at this
    exact this
  rcases isPreconnected_iff_subset_of_disjoint.mp isPreconnected_connectedComponentIn u' v' hu'
      hv' hcover hdisjK with h | h
  · left
    intro z hz
    obtain ⟨W, ⟨-, -, hWu⟩, hzW⟩ := mem_sUnion.mp (h hz.1)
    exact hWu ⟨⟨hzW, hz.1⟩, hz.2⟩
  · right
    intro z hz
    obtain ⟨W, ⟨-, -, hWv⟩, hzW⟩ := mem_sUnion.mp (h hz.1)
    exact hWv ⟨⟨hzW, hz.1⟩, hz.2⟩

end Hironaka.ComponentComplementConnected
