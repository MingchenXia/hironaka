import Hironaka.Analytic.HormanderInterface
import Hironaka.Analytic.HormanderAbstract
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Geometry.Manifold.PartitionOfUnity

set_option autoImplicit false

/-!
# Weighted `L²` spaces on open subsets of `ℂⁿ`

Basic facts about `weightedVolume D w = e^{-w} dλ|_D` for a weight `w` continuous on an open
set `D`: its density can be taken measurable, integrals against it are weighted integrals over
`D`, it is finite on compact subsets of `D`, and continuous functions with compact support in
`D` are square integrable for it.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Hironaka.Hormander

noncomputable section



variable {n : ℕ} {D : Set (ComplexModel n)} {w : ComplexModel n → ℝ}

/-- The density of `weightedVolume`, cut off outside `D`. -/
def weightDensity (D : Set (ComplexModel n)) (w : ComplexModel n → ℝ) (x : ComplexModel n) :
    ℝ≥0∞ :=
  D.indicator (fun x ↦ ENNReal.ofReal (Real.exp (-w x))) x

theorem measurable_weightDensity (hD : IsOpen D) (hw : ContinuousOn w D) :
    Measurable (weightDensity D w) := by
  classical
  have h : ContinuousOn (fun x ↦ ENNReal.ofReal (Real.exp (-w x))) D :=
    ENNReal.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn hw.neg)
  have := ContinuousOn.measurable_piecewise h (continuousOn_const (c := (0 : ℝ≥0∞)))
    hD.measurableSet
  convert this using 1
  funext x
  by_cases hx : x ∈ D <;> simp [weightDensity, hx]

theorem weightedVolume_eq_withDensity_weightDensity (hD : IsOpen D) :
    weightedVolume D w = (volume.restrict D).withDensity (weightDensity D w) := by
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
  simp [weightDensity, hx]

theorem weightDensity_lt_top (x : ComplexModel n) : weightDensity D w x < ∞ := by
  unfold weightDensity
  by_cases hx : x ∈ D <;> simp [hx]

/-- Integrals against the weighted volume. -/
theorem integral_weightedVolume {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (hD : IsOpen D) (hw : ContinuousOn w D) (F : ComplexModel n → V) :
    ∫ x, F x ∂(weightedVolume D w) = ∫ x in D, Real.exp (-w x) • F x := by
  rw [weightedVolume_eq_withDensity_weightDensity hD,
    integral_withDensity_eq_integral_toReal_smul (measurable_weightDensity hD hw)
      (Eventually.of_forall fun x ↦ weightDensity_lt_top x)]
  refine setIntegral_congr_fun hD.measurableSet fun x hx ↦ ?_
  simp [weightDensity, hx, (Real.exp_pos _).le]

theorem lintegral_weightedVolume (hD : IsOpen D) (hw : ContinuousOn w D)
    (F : ComplexModel n → ℝ≥0∞) :
    ∫⁻ x, F x ∂(weightedVolume D w) = ∫⁻ x in D, ENNReal.ofReal (Real.exp (-w x)) * F x := by
  rw [weightedVolume_eq_withDensity_weightDensity hD,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _ (measurable_weightDensity hD hw)
      (Eventually.of_forall fun x ↦ weightDensity_lt_top x)]
  refine setLIntegral_congr_fun hD.measurableSet fun x hx ↦ ?_
  simp [weightDensity, hx]

/-- The weighted volume is finite on compact subsets of `D`. -/
theorem weightedVolume_lt_top_of_isCompact (hD : IsOpen D) (hw : ContinuousOn w D)
    {Q : Set (ComplexModel n)} (hQ : IsCompact Q) (hQD : Q ⊆ D) :
    weightedVolume D w Q < ∞ := by
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Q, -w x ≤ M := by
    obtain ⟨M, hM⟩ := (hQ.exists_bound_of_continuousOn (hw.mono hQD).neg)
    exact ⟨M, fun x hx ↦ (Real.le_norm_self _).trans (hM x hx)⟩
  rw [weightedVolume_eq_withDensity_weightDensity hD,
    withDensity_apply' _ Q]
  calc ∫⁻ x in Q, weightDensity D w x ∂volume.restrict D
      ≤ ∫⁻ _ in Q, ENNReal.ofReal (Real.exp M) ∂volume.restrict D := by
        refine setLIntegral_mono_ae (by fun_prop) (Eventually.of_forall fun x hx ↦ ?_)
        unfold weightDensity
        by_cases hxD : x ∈ D
        · simp only [hxD, Set.indicator_of_mem]
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hM x hx))
        · simp [hxD]
    _ = ENNReal.ofReal (Real.exp M) * (volume.restrict D) Q := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((Measure.restrict_apply_le _ _).trans_lt hQ.measure_lt_top)

/-- Continuous functions with compact support in `D` are in every weighted `Lᵖ`. -/
theorem memLp_weightedVolume_of_continuous {V : Type*} [NormedAddCommGroup V]
    (hD : IsOpen D) (hw : ContinuousOn w D) {F : ComplexModel n → V} (hF : Continuous F)
    (hFc : HasCompactSupport F) (hFD : tsupport F ⊆ D) (p : ℝ≥0∞) :
    MemLp F p (weightedVolume D w) := by
  have hfin : weightedVolume D w (tsupport F) < ∞ :=
    weightedVolume_lt_top_of_isCompact hD hw hFc hFD
  have : IsFiniteMeasure ((weightedVolume D w).restrict (tsupport F)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C, hC⟩ := hF.bounded_above_of_compact_support hFc
  have hres : MemLp F p ((weightedVolume D w).restrict (tsupport F)) :=
    MemLp.of_bound hF.aestronglyMeasurable C (Eventually.of_forall hC)
  rwa [← memLp_indicator_iff_restrict (isClosed_tsupport F).measurableSet,
    Set.indicator_eq_self.mpr (subset_tsupport F)] at hres

/-- A smooth cutoff with values in `[0,1]`, equal to `1` near a compact `K ⊆ D` and with compact
support in `D`. -/
theorem exists_contDiff_cutoff {K : Set (ComplexModel n)} (hK : IsCompact K) (hD : IsOpen D)
    (hKD : K ⊆ D) :
    ∃ θ : ComplexModel n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧ HasCompactSupport θ ∧
      tsupport θ ⊆ D ∧ (∀ᶠ x in 𝓝ˢ K, θ x = 1) ∧ ∀ x, θ x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨K'', hK''c, hKK'', hK''D⟩ := exists_compact_between hK hD hKD
  obtain ⟨θ, h1, h0, h01⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (modelWithCornersSelf ℝ (ComplexModel n)) (n := (⊤ : ℕ∞)) hK.isClosed hKK''
  have hsupp : tsupport θ ⊆ K'' := by
    refine closure_minimal (fun x hx ↦ ?_) hK''c.isClosed
    by_contra hx'
    exact hx (h0 x hx')
  exact ⟨θ, contMDiff_iff_contDiff.mp θ.contMDiff,
    hK''c.of_isClosed_subset (isClosed_tsupport _) hsupp, hsupp.trans hK''D, h1, h01⟩

/-- A function smooth on `D` agrees near a compact `K ⊆ D` with a globally smooth function. -/
theorem exists_contDiff_eventuallyEq_nhdsSet {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : ComplexModel n → V} (hD : IsOpen D) (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f D)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ F : ComplexModel n → V, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
      ∀ᶠ x in 𝓝ˢ K, F x = f x := by
  obtain ⟨θ, hθ, -, hθD, hθ1, -⟩ := exists_contDiff_cutoff hK hD hKD
  refine ⟨fun x ↦ θ x • f x, contDiff_iff_contDiffAt.mpr fun x ↦ ?_, ?_⟩
  · by_cases hx : x ∈ D
    · exact hθ.contDiffAt.smul (hf.contDiffAt (hD.mem_nhds hx))
    · have hxs : x ∉ tsupport θ := fun h ↦ hx (hθD h)
      have h0 : (fun x ↦ θ x • f x) =ᶠ[𝓝 x] fun _ ↦ (0 : V) := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hxs] with y hy
        simp [hy]
      exact (contDiffAt_const).congr_of_eventuallyEq h0
  · filter_upwards [hθ1] with x hx
    simp [hx]

end

end Hironaka.Hormander
