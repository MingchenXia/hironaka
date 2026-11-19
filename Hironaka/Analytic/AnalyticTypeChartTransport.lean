import Hironaka.Analytic.DemaillyAnalyticType
import Hironaka.Manifold.HolomorphicMaps

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.QuasiEquisingularAtlasTransport

open Hironaka.HolomorphicMaps DemaillyAnalyticType

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

private theorem holomorphicGeneratorsAt_chartTransition_precompose
    {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source)
    {N : ℕ} {g : Fin N → ComplexModel n → ℂ}
    (hg : HolomorphicGeneratorsAt g (chartTransition e f z)) :
    HolomorphicGeneratorsAt (fun i y => g i (chartTransition e f y)) z := by
  obtain ⟨V, hV, hzV, hgV⟩ := hg
  let t := chartTransition e f
  let U : Set (ComplexModel n) := t.source ∩ t ⁻¹' V
  have hU : IsOpen U := t.continuousOn.isOpen_inter_preimage t.open_source hV
  have hzU : z ∈ U := ⟨hz, hzV⟩
  refine ⟨U, hU, hzU, ?_⟩
  intro i
  change DifferentiableOn ℂ (g i ∘ t) U
  apply (hgV i).comp
  · intro y hy
    exact ((chartTransition_contDiffAt e f hy.1).differentiableAt (by simp)).differentiableWithinAt
  · intro y hy
    exact hy.2

omit [IsComplexManifold n M] in
private theorem boundedRealGermAt_chartTransition_precompose
    {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source)
    {b : ComplexModel n → ℝ}
    (hb : BoundedRealGermAt b (chartTransition e f z)) :
    BoundedRealGermAt (fun y => b (chartTransition e f y)) z := by
  obtain ⟨C, hC0, hC⟩ := hb
  refine ⟨C, hC0, ?_⟩
  change ∀ᶠ y in 𝓝 z, |b (chartTransition e f y)| ≤ C
  exact ((chartTransition e f).continuousAt hz) hC

/-- A smooth remainder remains smooth after a complex-chart transition.
The source condition is included explicitly: it is the domain on which the
transition has the required real smoothness. -/
private theorem eventually_contDiffAt_chartTransition_precompose
    {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source)
    {b : ComplexModel n → ℝ}
    (hb : ∀ᶠ y in 𝓝 (chartTransition e f z), ContDiffAt ℝ ∞ b y) :
    ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ (fun y => b (chartTransition e f y)) y := by
  have hb' : ∀ᶠ y in 𝓝 z, ContDiffAt ℝ ∞ b (chartTransition e f y) :=
    ((chartTransition e f).continuousAt hz) hb
  filter_upwards [hb',
    (chartTransition e f).open_source.mem_nhds hz] with y hy hys
  exact hy.comp y (chartTransition_contDiffAt_real e f hys)

theorem LogarithmicTypeAt.chartTransition_precompose
    {u : M → EReal} {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source)
    {c : ℝ} {N : ℕ} {g : Fin N → ComplexModel n → ℂ}
    (hu : LogarithmicTypeAt (chartFunction u f) c g (chartTransition e f z)) :
    LogarithmicTypeAt (chartFunction u e) c
      (fun i y => g i (chartTransition e f y)) z := by
  obtain ⟨hc, hg, b, hb, hub⟩ := hu
  refine ⟨hc, holomorphicGeneratorsAt_chartTransition_precompose hz hg,
    fun y => b (chartTransition e f y),
    boundedRealGermAt_chartTransition_precompose hz hb, ?_⟩
  have hcoord : chartFunction u e =ᶠ[𝓝 z]
      fun y => chartFunction u f (chartTransition e f y) := by
    filter_upwards [(chartTransition e f).open_source.mem_nhds hz] with y hy
    have hys : y ∈ e.val.target ∩ e.val.symm ⁻¹' f.val.source := by
      simpa only [chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source] using hy
    change u (e.val.symm y) = u (f.val.symm (f.val (e.val.symm y)))
    rw [f.val.left_inv hys.2]
  have hpre := hub.comp_tendsto ((chartTransition e f).continuousAt hz)
  filter_upwards [hcoord, hpre] with y hycoord hypre
  rw [hycoord]
  have hypre' : chartFunction u f (chartTransition e f y) =
      (c : EReal) * generatorLog g (chartTransition e f y) +
        (b (chartTransition e f y) : EReal) := by
    simpa only [Function.comp_apply] using hypre
  rw [hypre']
  rfl

theorem HasAnalyticSingularityTypeAt.chartTransition_precompose
    {u : M → EReal} {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source)
    (hu : HasAnalyticSingularityTypeAt (chartFunction u f)
      (chartTransition e f z)) :
    HasAnalyticSingularityTypeAt (chartFunction u e) z := by
  obtain ⟨c, N, g, hg⟩ := hu
  exact ⟨c, N, fun i y => g i (chartTransition e f y),
    LogarithmicTypeAt.chartTransition_precompose hz hg⟩

/-- Smooth analytic singularities are intrinsic under changes of complex
coordinates.  This is the CT22 convention: the coefficient remains real and
the transported remainder is smooth, rather than merely bounded. -/
theorem SmoothLogarithmicTypeAt.chartTransition_precompose
    {u : M → EReal} {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source)
    {c : ℝ} {N : ℕ} {g : Fin N → ComplexModel n → ℂ}
    (hu : SmoothLogarithmicTypeAt (chartFunction u f)
      c g (chartTransition e f z)) :
    SmoothLogarithmicTypeAt (chartFunction u e) c
      (fun i y => g i (chartTransition e f y)) z := by
  obtain ⟨hc, hg, b, hb, hub⟩ := hu
  refine ⟨hc, holomorphicGeneratorsAt_chartTransition_precompose hz hg,
    fun y => b (chartTransition e f y),
    eventually_contDiffAt_chartTransition_precompose hz hb, ?_⟩
  have hcoord : chartFunction u e =ᶠ[𝓝 z]
      fun y => chartFunction u f (chartTransition e f y) := by
    filter_upwards [(chartTransition e f).open_source.mem_nhds hz] with y hy
    have hys : y ∈ e.val.target ∩ e.val.symm ⁻¹' f.val.source := by
      simpa only [chartTransition, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source] using hy
    change u (e.val.symm y) = u (f.val.symm (f.val (e.val.symm y)))
    rw [f.val.left_inv hys.2]
  have hpre := hub.comp_tendsto ((chartTransition e f).continuousAt hz)
  filter_upwards [hcoord, hpre] with y hycoord hypre
  rw [hycoord]
  have hypre' : chartFunction u f (chartTransition e f y) =
      (c : EReal) * generatorLog g (chartTransition e f y) +
        (b (chartTransition e f y) : EReal) := by
    simpa only [Function.comp_apply] using hypre
  rw [hypre']
  rfl

/-- The chartwise strong analytic-singularity condition can be transported to
any overlapping complex chart. -/
theorem HasSmoothAnalyticSingularitiesAt.chartTransition_precompose
    {u : M → EReal} {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source)
    (hu : HasSmoothAnalyticSingularitiesAt (chartFunction u f)
      (chartTransition e f z)) :
    HasSmoothAnalyticSingularitiesAt (chartFunction u e) z := by
  obtain ⟨c, N, g, hg⟩ := hu
  exact ⟨c, N, fun i y => g i (chartTransition e f y),
    SmoothLogarithmicTypeAt.chartTransition_precompose hz hg⟩

omit [IsComplexManifold n M] in
/-- The chart representative of a global potential is, as a germ, the
representative in an overlapping chart precomposed with the transition. -/
private theorem chartFunction_eventuallyEq_comp_chartTransition
    {u : M → EReal} {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source) :
    chartFunction u e =ᶠ[𝓝 z] fun y => chartFunction u f (chartTransition e f y) := by
  filter_upwards [(chartTransition e f).open_source.mem_nhds hz] with y hy
  have hys : y ∈ e.val.target ∩ e.val.symm ⁻¹' f.val.source := by
    simpa only [chartTransition, OpenPartialHomeomorph.trans_source,
      OpenPartialHomeomorph.symm_source] using hy
  change u (e.val.symm y) = u (f.val.symm (f.val (e.val.symm y)))
  rw [f.val.left_inv hys.2]

/-- **The off-pole smoothness clause of the `I-0489` convention transports.**
Its hypothesis is an implication guarded by the pole set of the family, and the
pole set of the transported family is the preimage of the pole set, so the guard
transports with the transition and the conclusion composes. -/
private theorem eventually_contDiffAt_offPole_chartTransition_precompose
    {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source)
    {N : ℕ} {g : Fin N → ComplexModel n → ℂ} {b : ComplexModel n → ℝ}
    (hb : ∀ᶠ y in 𝓝 (chartTransition e f z),
      generatorNormSq g y ≠ 0 → ContDiffAt ℝ ∞ b y) :
    ∀ᶠ y in 𝓝 z,
      generatorNormSq (fun i y => g i (chartTransition e f y)) y ≠ 0 →
        ContDiffAt ℝ ∞ (fun y => b (chartTransition e f y)) y := by
  have hb' : ∀ᶠ y in 𝓝 z, generatorNormSq g (chartTransition e f y) ≠ 0 →
      ContDiffAt ℝ ∞ b (chartTransition e f y) :=
    ((chartTransition e f).continuousAt hz) hb
  filter_upwards [hb', (chartTransition e f).open_source.mem_nhds hz] with y hy hys
  intro hne
  exact (hy hne).comp y (chartTransition_contDiffAt_real e f hys)

/-- **Analytic singularities in the `I-0489` convention are intrinsic under
changes of complex coordinates.**  This is the missing companion of
`LogarithmicTypeAt.chartTransition_precompose` (bounded remainder) and
`SmoothLogarithmicTypeAt.chartTransition_precompose` (remainder smooth across
the poles): here the remainder is bounded near the point and `C^∞` only off the
pole set, and each of the three clauses transports separately. -/
theorem BoundedSmoothOffPoleLogarithmicTypeAt.chartTransition_precompose
    {u : M → EReal} {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source)
    {c : ℝ} {N : ℕ} {g : Fin N → ComplexModel n → ℂ}
    (hu : BoundedSmoothOffPoleLogarithmicTypeAt (chartFunction u f) c g
      (chartTransition e f z)) :
    BoundedSmoothOffPoleLogarithmicTypeAt (chartFunction u e) c
      (fun i y => g i (chartTransition e f y)) z := by
  obtain ⟨hc, hg, b, hb, hsm, hub⟩ := hu
  refine ⟨hc, holomorphicGeneratorsAt_chartTransition_precompose hz hg,
    fun y => b (chartTransition e f y),
    boundedRealGermAt_chartTransition_precompose hz hb,
    eventually_contDiffAt_offPole_chartTransition_precompose hz hsm, ?_⟩
  have hpre := hub.comp_tendsto ((chartTransition e f).continuousAt hz)
  filter_upwards [chartFunction_eventuallyEq_comp_chartTransition (u := u) hz, hpre]
    with y hycoord hypre
  rw [hycoord]
  have hypre' : chartFunction u f (chartTransition e f y) =
      (c : EReal) * generatorLog g (chartTransition e f y) +
        (b (chartTransition e f y) : EReal) := by
    simpa only [Function.comp_apply] using hypre
  rw [hypre']
  rfl

/-- The chartwise `I-0489` analytic-singularity condition can be transported to
any overlapping complex chart. -/
theorem HasAnalyticSingularitiesSmoothOffPoleAt.chartTransition_precompose
    {u : M → EReal} {e f : ComplexChart n M} {z : ComplexModel n}
    (hz : z ∈ (chartTransition e f).source)
    (hu : HasAnalyticSingularitiesSmoothOffPoleAt (chartFunction u f)
      (chartTransition e f z)) :
    HasAnalyticSingularitiesSmoothOffPoleAt (chartFunction u e) z := by
  obtain ⟨c, N, g, hg⟩ := hu
  exact ⟨c, N, fun i y => g i (chartTransition e f y),
    BoundedSmoothOffPoleLogarithmicTypeAt.chartTransition_precompose hz hg⟩

end Hironaka.QuasiEquisingularAtlasTransport
