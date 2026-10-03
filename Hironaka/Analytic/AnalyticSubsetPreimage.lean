/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.PureDimension
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
set_option autoImplicit false

/-!
# Local analyticity, closed submanifolds and holomorphic preimages

Elementary closure properties of `IsComplexAnalyticSubset`.

* `isComplexAnalyticSubset_of_locally_eq`: a closed set which near each of its points agrees
  with a fixed analytic set is analytic.  Off the closed set the constant equation `1 = 0`
  works; at its points one restricts a presentation of the analytic set to the chart image of
  the neighbourhood of agreement.
* `isComplexAnalyticSubset_of_isClosedSubmanifold`: a closed complex submanifold is analytic;
  near a point where it is flattened to `ℂ^k × {0}` by `Φ`, it is cut out by the last `n - k`
  coordinates of `Φ`.
* `isComplexAnalyticSubset_preimage`: the preimage of an analytic set under a holomorphic map
  of complex manifolds is analytic; the generators are the pulled-back local equations,
  written in charts.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.AnalyticSubsetPreimage

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A closed set agreeing near each of its points with an analytic set is analytic. -/
theorem isComplexAnalyticSubset_of_locally_eq {A B : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (hB : IsClosed B)
    (h : ∀ y ∈ B, ∃ N : Set M, IsOpen N ∧ y ∈ N ∧ A ∩ N = B ∩ N) :
    IsComplexAnalyticSubset (n := n) B := by
  intro x
  by_cases hx : x ∈ B
  swap
  · exact PureDimension.nonempty_presentation_of_not_mem hB Subset.rfl hx
  obtain ⟨N, hNo, hxN, hAN⟩ := h x hx
  obtain ⟨P⟩ := hA x
  set e := (complexChartAt (n := n) x).val with he
  have hxs : x ∈ e.source := mem_complexChartAt_source x
  refine ⟨{ generatorCount := P.generatorCount
            generator := P.generator
            coordinateNeighborhood := P.coordinateNeighborhood ∩ (e.target ∩ e.symm ⁻¹' N)
            isOpen_coordinateNeighborhood :=
              P.isOpen_coordinateNeighborhood.inter (e.isOpen_inter_preimage_symm hNo)
            center_mem_coordinateNeighborhood := ⟨P.center_mem_coordinateNeighborhood,
              e.map_source hxs, by
                change e.symm (e x) ∈ N
                rw [e.left_inv hxs]
                exact hxN⟩
            coordinateNeighborhood_subset_target := fun _ hz => hz.2.1
            generator_holomorphic := fun i =>
              (P.generator_holomorphic i).mono inter_subset_left
            zeroLocus := ?_ }⟩
  intro y hy hyU
  have hyN : y ∈ N := by
    have h2 : e.symm (e y) ∈ N := hyU.2.2
    rwa [e.left_inv hy] at h2
  rw [← P.zeroLocus hy hyU.1]
  constructor
  · intro hyB
    have : y ∈ A ∩ N := hAN ▸ (⟨hyB, hyN⟩ : y ∈ B ∩ N)
    exact this.1
  · intro hyA
    have : y ∈ B ∩ N := hAN ▸ (⟨hyA, hyN⟩ : y ∈ A ∩ N)
    exact this.1

/-- A closed complex submanifold is an analytic subset. -/
theorem isComplexAnalyticSubset_of_isClosedSubmanifold {C : Set M}
    (hC : BlowupSequences.IsClosedSubmanifold n C) : IsComplexAnalyticSubset (n := n) C := by
  classical
  intro x
  by_cases hx : x ∈ C
  swap
  · exact PureDimension.nonempty_presentation_of_not_mem hC.1 Subset.rfl hx
  obtain ⟨k, -, -, Φ, hΦt, -, hΦ⟩ := hC.2 x hx
  refine ⟨{ generatorCount := n
            generator := fun i w => if k ≤ i.1 then Φ.toFun w i else 0
            coordinateNeighborhood := Φ.source
            isOpen_coordinateNeighborhood := Φ.isOpen_source
            center_mem_coordinateNeighborhood := Φ.center_mem_source
            coordinateNeighborhood_subset_target := hΦt
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · intro i
    by_cases hi : k ≤ i.1
    · simp only [hi, if_true]
      exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable.comp_differentiableOn
        Φ.toFun_holomorphic
    · simp only [hi, if_false]
      exact differentiableOn_const 0
  · intro y hy hyU
    rw [hΦ hy hyU]
    simp only [complexCoordinatePlane, mem_ofPred_eq]
    refine forall_congr' fun i => ?_
    by_cases hi : k ≤ i.1 <;> simp [hi]

variable {m : ℕ} {Z : Type*} [TopologicalSpace Z] [ChartedSpace (ComplexModel m) Z]
  [IsComplexManifold m Z]

/-- The preimage of an analytic subset under a holomorphic map is analytic. -/
theorem isComplexAnalyticSubset_preimage {g : Z → M}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g) {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) :
    IsComplexAnalyticSubset (n := m) (g ⁻¹' A) := by
  intro z
  obtain ⟨P⟩ := hA (g z)
  set e := (complexChartAt (n := m) z).val with he
  set e' := (complexChartAt (n := n) (g z)).val with he'
  have hzs : z ∈ e.source := mem_complexChartAt_source z
  have hgzs : g z ∈ e'.source := mem_complexChartAt_source (g z)
  let U : Set (ComplexModel m) :=
    {w | w ∈ e.target ∧ g (e.symm w) ∈ e'.source ∧ e' (g (e.symm w)) ∈ P.coordinateNeighborhood}
  have hUo : IsOpen U := by
    have hc : ContinuousOn (g ∘ e.symm) e.target :=
      hg.continuous.comp_continuousOn e.continuousOn_symm
    have := hc.isOpen_inter_preimage e.open_target
      (e'.isOpen_inter_preimage P.isOpen_coordinateNeighborhood)
    convert this using 1
    ext w
    simp only [U, mem_ofPred_eq, mem_inter_iff, mem_preimage, Function.comp_apply]
  have hdiff : ∀ w ∈ U, DifferentiableAt ℂ (fun v => e' (g (e.symm v))) w := by
    intro w hw
    have hws : e.symm w ∈ e.source := e.map_target hw.1
    have h1 := (contMDiffAt_iff_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, ComplexModel m)) (n := ∞) z)
      (IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℂ, ComplexModel n)) (n := ∞) (g z))
      hws hw.2.1).mp (hg (e.symm w))
    have h2 := h1.2
    simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id,
      contDiffWithinAt_univ] at h2
    have h3 : ContDiffAt ℂ ∞ (fun v => e' (g (e.symm v))) (e (e.symm w)) := h2
    rw [e.right_inv hw.1] at h3
    exact h3.differentiableAt (by simp)
  refine ⟨{ generatorCount := P.generatorCount
            generator := fun i w => P.generator i (e' (g (e.symm w)))
            coordinateNeighborhood := U
            isOpen_coordinateNeighborhood := hUo
            center_mem_coordinateNeighborhood := ?_
            coordinateNeighborhood_subset_target := fun _ hw => hw.1
            generator_holomorphic := ?_
            zeroLocus := ?_ }⟩
  · refine ⟨e.map_source hzs, ?_, ?_⟩
    · rw [e.left_inv hzs]; exact hgzs
    · rw [e.left_inv hzs]; exact P.center_mem_coordinateNeighborhood
  · intro i w hw
    exact (((P.generator_holomorphic i).differentiableAt
      (P.isOpen_coordinateNeighborhood.mem_nhds hw.2.2)).comp w
      (hdiff w hw)).differentiableWithinAt
  · intro y hy hyU
    change y ∈ e.source at hy
    have hyU' : e y ∈ U := hyU
    have hinv : e.symm (e y) = y := e.left_inv hy
    simp only [U, mem_ofPred_eq, hinv] at hyU'
    change g y ∈ A ↔ ∀ i, P.generator i (e' (g (e.symm (e y)))) = 0
    rw [hinv, P.zeroLocus hyU'.2.1 hyU'.2.2]

end Hironaka.AnalyticSubsetPreimage
