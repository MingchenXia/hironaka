import Hironaka.Analytic.DemaillyApproximationUniform
import Hironaka.Analytic.LocalBergmanFiniteAtlas

set_option autoImplicit false

/-!
# Local Bergman patches retaining uniform domination

`UniformLocalBergmanPatch` wraps the established `LocalBergmanPatch` without
changing it.  In addition to its ordinary finite-generator fields it retains
the weighted Bergman unit-ball estimate from the Demailly construction.  This
is precisely the data needed to compare an independently specified finite
normalized family with the branch generators on the same patch.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka.QuasiEquisingularBergmanAtlas


open DemaillyAnalyticType
open DemaillyApproximation

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A local Bergman patch together with the universal bound on the weighted
Bergman unit ball from which its generators were selected. -/
structure UniformLocalBergmanPatch (θ : SmoothRealForm n M 2)
    (u : M → EReal) (m : ℕ) where
  patch : LocalBergmanPatch θ u m
  center : ComplexModel n
  radius : ℝ
  radius_pos : 0 < radius
  /-- The coordinate centre remains in the smaller comparison domain. -/
  center_mem_domain : center ∈ patch.domain
  weight : ComplexModel n → EReal
  weight_eq_corrected : weight = patch.corrected
  uniform_radius : ℝ
  uniform_radius_pos : 0 < uniform_radius
  generator_unitBall : by
    letI : MeasurableSpace (ComplexModel n) := borel _
    letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
    exact ∀ l, patch.generator l ∈ BergmanGenerators.bergmanUnitBall center radius
      (fun x => multiplierWeight (m : ℝ) (weight x))
  /-- The very ball used by the weighted Bergman norm stays inside the target
  of the retained chart.  This is stronger than `patch.domain_le_target`: it
  makes coordinate representatives meaningful on the whole integration ball. -/
  double_radius_subset_target : ball center (2 * radius) ⊆ patch.chart.val.target
  domain_subset_uniformBall : (patch.domain : Set (ComplexModel n)) ⊆
    ball center uniform_radius
  uniform_constant : ℝ
  uniform_domination : by
    letI : MeasurableSpace (ComplexModel n) := borel _
    letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
    exact ∀ f ∈ BergmanGenerators.bergmanUnitBall center radius
      (fun x => multiplierWeight (m : ℝ) (weight x)), ∀ y ∈ patch.domain,
        ‖f y‖ ^ 2 ≤ uniform_constant * ∑ l, ‖patch.generator l y‖ ^ 2

/-- The local theta-PSH construction can choose a patch while retaining its
coordinate-level uniform weighted Bergman estimate. -/
theorem exists_uniformLocalBergmanPatch_containing
    {θ : SmoothRealForm n M 2} {u : M → EReal}
    (hu : IsThetaPshPotential θ u) (m : ℕ) (hm : 0 < m) (x : M) :
    ∃ D : UniformLocalBergmanPatch θ u m, x ∈ D.patch.source := by
  let e : ComplexChart n M := complexChartAt (n := n) x
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  have hz : e.val x ∈ e.val.target := e.val.map_source hx
  obtain ⟨W, ρ, hzW, hρ, hpsh⟩ := hu.1 e (e.val x) hz
  let P : ComplexModel n → EReal := fun z => chartFunction u e z + (ρ z : EReal)
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  obtain ⟨B⟩ := exists_uniform_weightedL2_generators W P hρ.1 hpsh (e.val x) hzW m hm
  let D : LocalBergmanPatch θ u m := {
    chart := e
    domain := ⟨B.domain, B.domain_open⟩
    domain_le_target := B.domain_subset.trans hρ.2.1
    potential := ρ
    localPotential := hρ.mono B.domain_open B.domain_subset
    plurisubharmonic := hpsh.mono B.domain_subset
    N := B.N
    generator := B.generator
    generator_analytic := B.generator_analytic
    generator_weighted := by
      change ∀ l, WeightedL2On P m (B.generator l) B.domain volume
      exact B.generator_weighted
    domination := ⟨B.C, B.C_ne_top, B.pointwise_domination⟩
    analyticType := fun y hy =>
      hasAnalyticSingularityTypeAt_inv_nat_generatorLog hm B.domain_open B.generator_analytic hy }
  refine ⟨{
    patch := D
    center := e.val x
    radius := B.radius
    radius_pos := B.radius_pos
    center_mem_domain := B.center_mem_domain
    weight := P
    weight_eq_corrected := by rfl
    uniform_radius := B.uniform_radius
    uniform_radius_pos := B.uniform_radius_pos
    generator_unitBall := by simpa only [D, P] using B.generator_unitBall
    double_radius_subset_target := B.double_radius_subset.trans hρ.2.1
    domain_subset_uniformBall := by
      change B.domain ⊆ ball (e.val x) B.uniform_radius
      exact B.domain_subset_uniformBall
    uniform_constant := B.uniform_constant
    uniform_domination := by
      change ∀ f ∈ BergmanGenerators.bergmanUnitBall (e.val x) B.radius
        (fun x => multiplierWeight (m : ℝ) (P x)), ∀ y ∈ B.domain,
          ‖f y‖ ^ 2 ≤ B.uniform_constant * ∑ l, ‖B.generator l y‖ ^ 2
      exact B.uniform_domination
  }, ?_⟩
  change x ∈ e.val.source ∩ e.val ⁻¹' B.domain
  exact ⟨hx, B.center_mem_domain⟩

/-- The inverse coordinate map of a point in the retained integration ball is
in the source of the patch chart.  No claim is made that it lies in the smaller
Bergman comparison domain. -/
theorem UniformLocalBergmanPatch.chart_symm_mem_chart_source_of_mem_double_radius
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m) {z : ComplexModel n}
    (hz : z ∈ ball D.center (2 * D.radius)) :
    D.patch.chart.val.symm z ∈ D.patch.chart.val.source :=
  D.patch.chart.val.map_target (D.double_radius_subset_target hz)

/-- On the retained integration ball, applying the chart after its inverse
returns the original coordinate. -/
theorem UniformLocalBergmanPatch.chart_apply_symm_of_mem_double_radius
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m) {z : ComplexModel n}
    (hz : z ∈ ball D.center (2 * D.radius)) :
    D.patch.chart.val (D.patch.chart.val.symm z) = z :=
  D.patch.chart.val.right_inv (D.double_radius_subset_target hz)

/-- The retained centre belongs to the source of the local Bergman patch.
This uses both the fixed-domain centre witness and the double-radius chart
target certificate. -/
theorem UniformLocalBergmanPatch.centerPoint_mem_patch_source
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m) :
    D.patch.chart.val.symm D.center ∈ D.patch.source := by
  have hball : D.center ∈ ball D.center (2 * D.radius) :=
    mem_ball_self (by linarith [D.radius_pos])
  refine ⟨D.chart_symm_mem_chart_source_of_mem_double_radius hball, ?_⟩
  change D.patch.chart.val (D.patch.chart.val.symm D.center) ∈ D.patch.domain
  rw [D.chart_apply_symm_of_mem_double_radius hball]
  exact D.center_mem_domain

/-- A positive multiplicative comparison of squared generator norms gives the
corresponding logarithmic comparison. -/
theorem generatorLog_le_add_of_generatorNormSq_le
    {q N : ℕ} {f : Fin q → ComplexModel n → ℂ}
    {g : Fin N → ComplexModel n → ℂ} {y : ComplexModel n} {A : ℝ}
    (hA : 0 < A)
    (hfg : generatorNormSq f y ≤ A * generatorNormSq g y) :
    generatorLog f y ≤ generatorLog g y + (Real.log A : EReal) := by
  rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum]
  calc
    ENNReal.log (ENNReal.ofReal (∑ i, ‖f i y‖ ^ 2)) ≤
        ENNReal.log (ENNReal.ofReal (A * ∑ j, ‖g j y‖ ^ 2)) :=
      ENNReal.log_monotone (ENNReal.ofReal_le_ofReal (by
        simpa only [generatorNormSq] using hfg))
    _ = ENNReal.log (ENNReal.ofReal A *
        ENNReal.ofReal (∑ j, ‖g j y‖ ^ 2)) := by
      rw [ENNReal.ofReal_mul hA.le]
    _ = ENNReal.log (ENNReal.ofReal (∑ j, ‖g j y‖ ^ 2)) +
        (Real.log A : EReal) := by
      rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hA, add_comm]

/-- Every finite normalized family in the retained weighted unit ball is
logarithmically controlled on the uniform patch domain by the generators of
that patch. -/
theorem UniformLocalBergmanPatch.exists_generatorLog_domination
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : UniformLocalBergmanPatch θ u m)
    {q : ℕ} {f : Fin q → ComplexModel n → ℂ}
    (hf : by
      letI : MeasurableSpace (ComplexModel n) := borel _
      letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
      exact ∀ i, f i ∈ BergmanGenerators.bergmanUnitBall D.center D.radius
        (fun x => multiplierWeight (m : ℝ) (D.weight x))) :
    ∃ A : ℝ, 0 < A ∧ ∀ y ∈ D.patch.domain,
      generatorLog f y ≤ generatorLog D.patch.generator y + (Real.log A : EReal) := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  set K' : ℝ := max D.uniform_constant 0 + 1 with hK'
  have hK'pos : 0 < K' := by
    rw [hK']
    linarith [le_max_right D.uniform_constant 0]
  set A : ℝ := ((q : ℝ) + 1) * K' with hA
  have hApos : 0 < A := by
    rw [hA]
    positivity
  refine ⟨A, hApos, fun y hy => ?_⟩
  apply generatorLog_le_add_of_generatorNormSq_le hApos
  have hsum : 0 ≤ ∑ l, ‖D.patch.generator l y‖ ^ 2 :=
    Finset.sum_nonneg fun l _ => sq_nonneg _
  have hKle : D.uniform_constant ≤ K' := by
    rw [hK']
    linarith [le_max_left D.uniform_constant 0]
  have hterm : ∀ i, ‖f i y‖ ^ 2 ≤ K' * ∑ l, ‖D.patch.generator l y‖ ^ 2 := by
    intro i
    exact (D.uniform_domination (f i) (hf i) y hy).trans
      (mul_le_mul_of_nonneg_right hKle hsum)
  rw [generatorNormSq, generatorNormSq]
  calc
    (∑ i, ‖f i y‖ ^ 2) ≤
        ∑ _i : Fin q, K' * ∑ l, ‖D.patch.generator l y‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (q : ℝ) * (K' * ∑ l, ‖D.patch.generator l y‖ ^ 2) := by simp
    _ = ((q : ℝ) * K') * ∑ l, ‖D.patch.generator l y‖ ^ 2 := by ring
    _ ≤ (((q : ℝ) + 1) * K') * ∑ l, ‖D.patch.generator l y‖ ^ 2 := by
      gcongr
      nlinarith
    _ = A * ∑ l, ‖D.patch.generator l y‖ ^ 2 := by rw [hA]

end

end Hironaka.QuasiEquisingularBergmanAtlas
