import Hironaka.Analytic.KahlerCurrentRegularizationBergmanBranch
import Hironaka.Analytic.BergmanGenerators
import Hironaka.Analytic.PotentialTheory.AnalyticSingularities

set_option autoImplicit false

/-!
# Finite local one-sided Bergman regularization data

For every positive exponent, the local weighted Bergman construction yields a
finite cover by theta-PSH branches.  Each branch gives the one-sided lower
bound required by quantitative regularization for its own finite generator
family.  This is deliberately local: the outstanding global step is to glue
these branches with controlled curvature and to show that their generators
span the full multiplier ideal.
-/

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ENNReal

namespace Hironaka.QuantitativeRegularizationLocalBergman


open Hironaka.AnalyticGluingData
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch
open KahlerCurrentRegularizationBergmanBranch

noncomputable section

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- A positive multiplicative comparison of squared generator norms gives the
corresponding logarithmic comparison. -/
theorem generatorLog_le_add_of_generatorNormSq_le
    {q N : ℕ} {f : Fin q → ComplexModel d → ℂ}
    {g : Fin N → ComplexModel d → ℂ} {y : ComplexModel d} {M : ℝ}
    (hM : 0 < M)
    (hfg : generatorNormSq f y ≤ M * generatorNormSq g y) :
    generatorLog f y ≤ generatorLog g y + (Real.log M : EReal) := by
  rw [generatorLog_eq_log_sum, generatorLog_eq_log_sum]
  calc
    ENNReal.log (ENNReal.ofReal (∑ i, ‖f i y‖ ^ 2)) ≤
        ENNReal.log (ENNReal.ofReal (M * ∑ j, ‖g j y‖ ^ 2)) :=
      ENNReal.log_monotone (ENNReal.ofReal_le_ofReal (by
        simpa only [generatorNormSq] using hfg))
    _ = ENNReal.log (ENNReal.ofReal M *
        ENNReal.ofReal (∑ j, ‖g j y‖ ^ 2)) := by
      rw [ENNReal.ofReal_mul hM.le]
    _ = ENNReal.log (ENNReal.ofReal (∑ j, ‖g j y‖ ^ 2)) +
        (Real.log M : EReal) := by
      rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hM, add_comm]

/-- Uniform Bergman domination controls the logarithmic norm of every finite
family in the weighted unit ball on one smaller ball.  No statement here says
that the resulting generators generate a multiplier ideal. -/
theorem exists_uniform_generatorLog_domination
    [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]
    {z : ComplexModel d} {R : ℝ} {w : ComplexModel d → ℝ≥0∞}
    (hR : 0 < R) (hw : AEMeasurable w (volume.restrict (ball z (2 * R))))
    {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ y ∈ ball z (2 * R), ENNReal.ofReal δ ≤ w y)
    {q : ℕ} {f : Fin q → ComplexModel d → ℂ}
    (hf : ∀ i, f i ∈ BergmanGenerators.bergmanUnitBall z R w) :
    ∃ (N : ℕ) (g : Fin N → ComplexModel d → ℂ) (r M : ℝ),
      0 < r ∧ 0 < M ∧
      (∀ l, g l ∈ BergmanGenerators.bergmanUnitBall z R w) ∧
      ∀ y ∈ ball z r,
        generatorLog f y ≤ generatorLog g y + (Real.log M : EReal) := by
  obtain ⟨N, g, r, K, hr, hg, hdom⟩ :=
    BergmanGenerators.exists_uniform_generators hR hw hδ hlow
  set K' : ℝ := max K 0 + 1 with hK'
  have hK'pos : 0 < K' := by
    rw [hK']
    linarith [le_max_right K 0]
  set M : ℝ := ((q : ℝ) + 1) * K' with hM
  have hMpos : 0 < M := by
    rw [hM]
    positivity
  refine ⟨N, g, r, M, hr, hMpos, hg, fun y hy => ?_⟩
  apply generatorLog_le_add_of_generatorNormSq_le hMpos
  have hsum : 0 ≤ ∑ l, ‖g l y‖ ^ 2 :=
    Finset.sum_nonneg fun l _ => sq_nonneg _
  have hKle : K ≤ K' := by
    rw [hK']
    linarith [le_max_left K 0]
  have hterm : ∀ i, ‖f i y‖ ^ 2 ≤ K' * ∑ l, ‖g l y‖ ^ 2 := by
    intro i
    exact (hdom (f i) (hf i) y hy).trans
      (mul_le_mul_of_nonneg_right hKle hsum)
  rw [generatorNormSq, generatorNormSq]
  calc
    (∑ i, ‖f i y‖ ^ 2) ≤ ∑ _i : Fin q, K' * ∑ l, ‖g l y‖ ^ 2 :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = (q : ℝ) * (K' * ∑ l, ‖g l y‖ ^ 2) := by simp
    _ = ((q : ℝ) * K') * ∑ l, ‖g l y‖ ^ 2 := by ring
    _ ≤ (((q : ℝ) + 1) * K') * ∑ l, ‖g l y‖ ^ 2 := by
      gcongr
      nlinarith
    _ = M * ∑ l, ‖g l y‖ ^ 2 := by rw [hM]

/-- The global function obtained by reading one local Bergman generator through
its patch chart.  Only its germ on the patch source is used below. -/
def manifoldGenerator
    {theta : SmoothRealForm d Z 2} {phi : Z → EReal} {m : ℕ}
    (D : LocalBergmanPatch theta phi m) (i : Fin D.N) : Z → ℂ :=
  fun y => D.generator i (D.chart.val y)

/-- On the source of a local Bergman patch, its theta-PSH branch dominates the
normalized logarithmic weight of its finite generator family, up to a bounded
constant. -/
theorem exists_branch_generator_lowerBound
    {theta : SmoothRealForm d Z 2} {phi : Z → EReal} {m : ℕ}
    (D : LocalBergmanPatch theta phi m) {x : Z} (hx : x ∈ D.source) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      (((m : ℝ)⁻¹ : ℝ) : EReal) *
          generatorLog (fun i => manifoldGenerator D i) y - (C : EReal) ≤
        bergmanBranch D y := by
  have hbounded : BoundedRealGermAt D.potential (D.chart.val x) :=
    boundedRealGermAt_of_continuousAt
      ((D.localPotential.2.2.1 (D.chart.val x) hx.2).contDiffAt
        (D.localPotential.1.mem_nhds hx.2)).continuousAt
  obtain ⟨C, hCnonneg, hC⟩ := hbounded
  refine ⟨C, ?_⟩
  filter_upwards [D.source.isOpen.mem_nhds hx,
    (D.chart.val.continuousAt hx.1) hC] with y hy hyC
  have hpot : (D.potential (D.chart.val y) : EReal) ≤ (C : EReal) :=
    EReal.coe_le_coe_iff.mpr ((le_abs_self _).trans hyC)
  change (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog D.generator (D.chart.val y) -
      (C : EReal) ≤ bergmanBranch D y
  rw [bergmanBranch]
  split
  · exact EReal.sub_le_sub le_rfl hpot
  · rename_i hy'
    exact (hy' hy).elim

/-- **Finite local quantitative data.**  Every positive exponent admits a
finite cover by branches that are theta-PSH on their own sources and satisfy
the desired one-sided generator inequality there. -/
theorem exists_finiteLocalBergmanBranch_lowerBounds [CompactSpace Z]
    {theta : SmoothRealForm d Z 2} {phi : Z → EReal}
    (hphi : IsThetaPshPotential theta phi) (m : ℕ) (hm : 0 < m) :
    ∃ A : FiniteLocalBergmanAtlas theta phi m,
      ∀ i : Fin A.count,
        ThetaPlurisubharmonicOn theta (bergmanBranch (A.patch i)) (A.patch i).source ∧
        ∀ x ∈ (A.patch i).source, ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
          (((m : ℝ)⁻¹ : ℝ) : EReal) *
              generatorLog (fun j => manifoldGenerator (A.patch i) j) y - (C : EReal) ≤
            bergmanBranch (A.patch i) y := by
  obtain ⟨A⟩ := nonempty_finiteLocalBergmanAtlas hphi m hm
  refine ⟨A, fun i => ⟨?_, fun x hx => ?_⟩⟩
  · exact bergmanBranch_thetaPlurisubharmonicOn (A.patch i) hm
  · exact exists_branch_generator_lowerBound (A.patch i) hx

end

end Hironaka.QuantitativeRegularizationLocalBergman
