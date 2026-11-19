import Hironaka.Blowup.BlowupSequencePotentialDescent
import Hironaka.Blowup.BlowupSequenceIsomorphismOff
import Hironaka.Analytic.DivisorSingularProjection
import Hironaka.Analytic.DemaillyApproximantDivisorialLelong

set_option autoImplicit false

/-!
# Actual chart-null exceptional sets for finite blowup sequences

Actual invertible divisor generators give null coordinate support.
A finite smooth-centre blowup sequence has its exceptional locus in a
constructed genuine effective divisor and has singleton fibres off it.
This produces the literal existing null-injectivity predicate without
null-set, discrepancy, or positivity certificates.
-/

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupSequenceInjectiveOffNull

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupExceptionalDivisor GermIdealTotalTransform DemaillyApproximantDivisorialLelong

variable {n : ℕ} {Y : Type u} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- Actual invertible divisor generators produce null support in every
preferred chart, without compactness or a global manifold measure. -/
theorem measure_chart_image_support_eq_zero (D : EffectiveDivisor n Y) (c : Y) :
    volume ((complexChartAt (n := n) c).val ''
      (D.support ∩ (complexChartAt (n := n) c).val.source)) = 0 := by
  classical
  let e := complexChartAt (n := n) c
  let T : Set (ComplexModel n) := e.val '' (D.support ∩ e.val.source)
  have hlocal : ∀ z ∈ T, ∃ N ∈ 𝓝 z, volume (id '' (N ∩ T)) = 0 := by
    rintro _ ⟨a, ⟨haD, hae⟩, rfl⟩
    obtain ⟨U, hU, haU, h, hhol, hnv, hgen⟩ := D.isInvertible a
    have hUopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' U) :=
      e.val.isOpen_inter_preimage_symm hU
    have haU' : e.val a ∈ e.val.target ∩ e.val.symm ⁻¹' U := by
      refine ⟨e.val.map_source hae, ?_⟩
      simpa only [mem_preimage, e.val.left_inv hae] using haU
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hUopen _ haU'
    let B := ball (e.val a) r
    have hBU : B ⊆ e.val.target ∩ e.val.symm ⁻¹' U := hrsub
    have hH : DifferentiableOn ℂ (fun z => h (e.val.symm z)) B :=
      (Hironaka.differentiableOn_comp_chartSymm c hhol).mono hBU
    have hOopen : IsOpen (e.val.source ∩ e.val ⁻¹' B) :=
      e.val.isOpen_inter_preimage isOpen_ball
    have hOU : e.val.source ∩ e.val ⁻¹' B ⊆ U := by
      intro y hy
      have := (hBU hy.2).2
      simpa only [mem_preimage, e.val.left_inv hy.1] using this
    obtain ⟨a₁, ha₁, hne⟩ := hnv _ hOopen hOU ⟨a, hae, mem_ball_self hr⟩
    have hnull : volume (B ∩ (fun z => h (e.val.symm z)) ⁻¹' {0}) = 0 :=
      HolomorphicZeroSetNull.measure_inter_preimage_zero_eq_zero volume isOpen_ball
        (convex_ball _ _) hH ha₁.2 (by simpa only [e.val.left_inv ha₁.1] using hne)
    have hsub : B ∩ T ⊆ B ∩ (fun z => h (e.val.symm z)) ⁻¹' {0} := by
      rintro z ⟨hzB, a', ⟨ha'D, ha'e⟩, heq⟩
      have ha'U : a' ∈ U := by
        have := (hBU hzB).2
        simpa only [mem_preimage, ← heq, e.val.left_inv ha'e] using this
      have hhat : HolomorphicAt n h a' := by
        filter_upwards [hU.mem_nhds ha'U] with y hy
        exact (hhol y hy).mdifferentiableAt (hU.mem_nhds hy)
      have hhmem : D.ideal.mem a' h :=
        (hgen a' ha'U h).mpr (InvertibleIdealQuotient.isInSpanAt_self rfl hhat)
      refine ⟨hzB, ?_⟩
      have hhzero : h a' = 0 := ha'D h hhmem
      simpa only [mem_preimage, mem_singleton_iff, ← heq, e.val.left_inv ha'e] using hhzero
    refine ⟨B, isOpen_ball.mem_nhds (mem_ball_self hr), ?_⟩
    simpa only [image_id] using measure_mono_null hsub hnull
  have hnull := DivisorSingularProjection.measure_image_null_of_local
    (μ := (volume : Measure (ComplexModel n))) (T := T) id hlocal
  simpa only [image_id] using hnull

variable {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- A genuine effective divisor containing the exceptional locus is
constructed by induction on the actual finite blowup sequence. -/
theorem exists_effectiveDivisor_exceptionalLocus_subset {π : Y → X}
    (hπ : IsBlowupSequence n X Y π) :
    ∃ D : EffectiveDivisor n Y, exceptionalLocus n π ⊆ D.support := by
  induction hπ with
  | refl =>
      refine ⟨⟨IdealWeightPowers.unitIdeal n X, isInvertible_unitIdeal⟩, ?_⟩
      simp only [exceptionalLocus_id, empty_subset]
  | step f C g hf hg ih =>
      obtain ⟨D, hD⟩ := ih
      let D₁ := BlowupExceptionalDivisor.totalTransform hg D
      let D₂ := exceptionalDivisor hg
      refine ⟨GermIdealTotalTransform.EffectiveDivisor.add D₁ D₂, ?_⟩
      rw [exceptionalLocus_comp (hf.contMDiff.mdifferentiable (by simp))
        (hg.contMDiff.mdifferentiable (by simp))]
      intro y hy b hb
      obtain ⟨-, N, s, a, hs, -, heq⟩ := hb
      rw [heq.self_of_nhds]
      apply Finset.sum_eq_zero
      intro i _
      obtain ⟨p, q, hp, hq, hsi⟩ := hs i
      rcases hy with hy | hy
      · have hyD₂ : y ∈ D₂.support := exceptionalLocus_subset_support_exceptionalDivisor hg hy
        have hzero : q y = 0 := hyD₂ q hq
        simp only [hsi, Pi.mul_apply, hzero, mul_zero]
      · have hyD₁ : y ∈ D₁.support := by
          rw [support_totalTransform]
          exact hD hy
        have hzero : p y = 0 := hyD₁ p hp
        simp only [hsi, Pi.mul_apply, hzero, zero_mul, mul_zero]

/-- The geometric null-injectivity hypothesis is internally produced
for every actual finite smooth-centre blowup sequence. -/
theorem isInjectiveOffNull_of_isBlowupSequence {m : ℕ}
    {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
    [IsComplexManifold (m + 1) X]
    {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel (m + 1)) Y]
    [IsComplexManifold (m + 1) Y] {π : Y → X}
    (hπ : IsBlowupSequence (m + 1) X Y π) : IsInjectiveOffNull m π := by
  obtain ⟨D, hD⟩ := exists_effectiveDivisor_exceptionalLocus_subset hπ
  refine ⟨exceptionalLocus (m + 1) π, ?_, ?_⟩
  · intro y
    exact measure_mono_null (image_mono (inter_subset_inter_left _ hD))
      (measure_chart_image_support_eq_zero D y)
  · intro y hy y' _ hyy'
    exact (BlowupSequenceIsomorphismOff.eq_of_apply_eq_of_not_mem_exceptionalLocus
      hπ hy hyy'.symm).symm

end Hironaka.BlowupSequenceInjectiveOffNull
