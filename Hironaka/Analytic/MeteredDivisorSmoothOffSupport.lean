import Hironaka.Analytic.MeteredDivisorSingleGenerator
import Hironaka.Analytic.MeteredDivisorPositivity
import Hironaka.Analytic.MeteredDivisorWeightBounds
import Hironaka.Analytic.PluriharmonicLogNorm

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

/-!
# Off its support, the weight of a metered divisor is a smooth potential of `-Θ_E`

A `MeteredEffectiveQDivisor` `E` records `ψ_E` and `Θ_E` with `ddᶜ ψ_E = [E] - Θ_E`.
Away from the support the divisor current `[E]` vanishes, so there `ψ_E` is an honest
smooth real function and an exact local potential of `-Θ_E`.

`Hironaka.MeteredDivisorPositivity` proves the global inequality `[E] ≥ 0`; what a
pushforward across a blown-up centre needs is the *equality* off the support, in the form
`IsSmoothLocalPotential`.  The route is the single-generator presentation
`ψ_E = (1/q) log |G|² + h`, `Θ_E = -ddᶜ h` (`exists_localSingleGenerator_curvature`, the
statement of `Hironaka.MeteredDivisorSingleGenerator.exists_localSingleGenerator` with the
curvature clause of the presentation carried along), together with the pluriharmonicity of
`log |G|²` at a nonvanishing point
(`Hironaka.PluriharmonicLogNorm.smoothDDC_log_normSq_eq_zero`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.MeteredDivisorSmoothOffSupport

open Hironaka.HolomorphicIdealSheaves MeteredDivisorPositivity
  MeteredDivisorSingleGenerator MeteredDivisorWeightBounds PluriharmonicLogNorm

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **The single-generator presentation, with the curvature clause.**  This is
`Hironaka.MeteredDivisorSingleGenerator.exists_localSingleGenerator` together with the
clause `Θ_E = -ddᶜ h` of the defining presentation, for the same smooth term `h`. -/
theorem exists_localSingleGenerator_curvature (E : MeteredEffectiveQDivisor n M) (x : M) :
    ∃ (U : Set M), IsOpen U ∧ x ∈ U ∧ ∃ (q : ℕ) (G : M → ℂ) (h : M → ℝ),
      0 < q ∧
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) G U ∧
      (∀ e : ComplexChart n M,
        ContDiffOn ℝ ∞ (fun z => h (e.val.symm z)) (e.val.target ∩ e.val.symm ⁻¹' U)) ∧
      (∀ y ∈ U, E.weight y
        = ((1 / (q : ℝ) : ℝ) : EReal) * singleLog G y + (h y : EReal)) ∧
      ∀ (e : ComplexChart n M) (z : ComplexModel n), z ∈ e.val.target →
        e.val.symm z ∈ U →
          E.curvature.val.coeff e z = -smoothDDC (fun y => h (e.val.symm y)) z := by
  classical
  obtain ⟨U, hUopen, hxU, N, a, g, h, hanonneg, hgdiff, -, hsmooth, hweight, hcurv⟩ :=
    E.local_presentation x
  obtain ⟨q, p, hqpos, hpq⟩ := exists_commonDenominator a hanonneg
  refine ⟨U, hUopen, hxU, q, ∏ i, (g i) ^ (p i), h, hqpos,
    MDifferentiableOn.prod fun i _ => (hgdiff i).pow (p i), hsmooth, ?_, hcurv⟩
  intro y hyU
  rw [hweight y hyU]
  congr 1
  have hq0 : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
  have hstep : ∀ i : Fin N,
      ((a i : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g i) y
        = ((1 / (q : ℝ) : ℝ) : EReal) * (p i • singleLog (g i) y) := by
    intro i
    rw [← coe_natCast_mul_eq_nsmul, ← mul_assoc, ← EReal.coe_mul, hpq i]
    congr 2
    field_simp
  calc (∑ i, ((a i : ℝ) : EReal) * generatorLog (fun _ : Fin 1 => g i) y)
      = ∑ i, ((1 / (q : ℝ) : ℝ) : EReal) * (p i • singleLog (g i) y) :=
        Finset.sum_congr rfl fun i _ => hstep i
    _ = ((1 / (q : ℝ) : ℝ) : EReal) * ∑ i, (p i • singleLog (g i) y) :=
        (coe_mul_finsetSum hq0 _ _).symm
    _ = ((1 / (q : ℝ) : ℝ) : EReal) * singleLog (∏ i, (g i) ^ (p i)) y := by
        rw [singleLog_prod]
        exact congrArg _ (Finset.sum_congr rfl fun i _ => (singleLog_pow (g i) (p i) y).symm)

/-- `log ‖F‖²` is smooth near a point where the holomorphic `F` does not vanish. -/
theorem contDiffAt_log_normSq {F : ComplexModel n → ℂ} {U : Set (ComplexModel n)}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {z : ComplexModel n} (hz : z ∈ U)
    (hFz : F z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (Complex.normSq (F y))) z := by
  have hFC : ContDiffOn ℂ ∞ F U := contDiffOn_of_differentiableOn_complex hF hU
  have hFR : ContDiffAt ℝ ∞ F z :=
    ((hFC.restrict_scalars ℝ) z hz).contDiffAt (hU.mem_nhds hz)
  have hre : ContDiffAt ℝ ∞ (fun y => (F y).re) z :=
    (Complex.reCLM.contDiff.contDiffAt).comp z hFR
  have him : ContDiffAt ℝ ∞ (fun y => (F y).im) z :=
    (Complex.imCLM.contDiff.contDiffAt).comp z hFR
  have hns : ContDiffAt ℝ ∞ (fun y => Complex.normSq (F y)) z := by
    have hfun : (fun y => Complex.normSq (F y))
        = fun y => (F y).re * (F y).re + (F y).im * (F y).im := by
      funext y; simp [Complex.normSq_apply]
    rw [hfun]
    exact (hre.mul hre).add (him.mul him)
  have hne : Complex.normSq (F z) ≠ 0 := by
    simpa [Complex.normSq_eq_zero] using hFz
  exact (Real.contDiffAt_log.mpr hne).comp z hns

/-- **Off its support, the weight of a metered effective `ℚ`-divisor is a smooth local
potential of `-Θ_E`.**  Read in an arbitrary chart of the atlas: on a neighbourhood of the
point the extended-real weight takes real values, is `C^∞` there, and its `ddᶜ` is `-Θ_E`. -/
theorem exists_isSmoothLocalPotential_neg_curvature (E : MeteredEffectiveQDivisor n M)
    {x : M} (hx : x ∉ E.support) (e : ComplexChart n M) (hxe : x ∈ e.val.source) :
    ∃ W : Set (ComplexModel n), e.val x ∈ W ∧
      IsSmoothLocalPotential (-E.curvature).val e W
        (fun ζ => (E.weight (e.val.symm ζ)).toReal) := by
  classical
  obtain ⟨U, hUopen, hxU, q, G, h, hqpos, hGdiff, hsmooth, hweight, hcurv⟩ :=
    exists_localSingleGenerator_curvature E x
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
  -- the generator does not vanish at `x`
  have hGx : G x ≠ 0 := by
    intro h0
    refine hx ?_
    show E.weight x = ⊥
    rw [hweight x hxU, (singleLog_eq_bot_iff G x).mpr h0,
      EReal.coe_mul_bot_of_pos (by positivity)]
    simp
  -- the chart picture
  set F : ComplexModel n → ℂ := fun ζ => G (e.val.symm ζ) with hF
  set T : Set (ComplexModel n) := e.val.target ∩ e.val.symm ⁻¹' U with hT
  have hTopen : IsOpen T := e.val.isOpen_inter_preimage_symm hUopen
  have hFdiff : DifferentiableOn ℂ F T := differentiableOn_comp_chartSymm e hGdiff
  have hxT : e.val x ∈ T := ⟨e.val.map_source hxe, by
    rw [mem_preimage, e.val.left_inv hxe]; exact hxU⟩
  have hFx : F (e.val x) ≠ 0 := by
    rw [hF]; simpa [e.val.left_inv hxe] using hGx
  -- shrink to where the generator is nonzero
  have hFcont : ContinuousOn F T := hFdiff.continuousOn
  set W : Set (ComplexModel n) := T ∩ F ⁻¹' {z : ℂ | z ≠ 0} with hW
  have hWopen : IsOpen W := hFcont.isOpen_inter_preimage hTopen isOpen_ne
  have hxW : e.val x ∈ W := ⟨hxT, hFx⟩
  have hWT : W ⊆ T := inter_subset_left
  -- the smooth expression of the weight on `W`
  have hlogsmooth : ∀ ζ ∈ W, ContDiffAt ℝ ∞ (fun y => Real.log (Complex.normSq (F y))) ζ :=
    fun ζ hζ => contDiffAt_log_normSq hTopen hFdiff (hWT hζ) hζ.2
  have hlogC : ContDiffOn ℝ ∞ (fun y => Real.log (Complex.normSq (F y))) W :=
    fun ζ hζ => (hlogsmooth ζ hζ).contDiffWithinAt
  have hsmulC : ContDiffOn ℝ ∞
      (fun y => (1 / (q : ℝ)) • Real.log (Complex.normSq (F y))) W := hlogC.const_smul _
  have hhC : ContDiffOn ℝ ∞ (fun ζ => h (e.val.symm ζ)) W := (hsmooth e).mono hWT
  have hrhoC : ContDiffOn ℝ ∞
      (fun ζ => (1 / (q : ℝ)) • Real.log (Complex.normSq (F ζ)) + h (e.val.symm ζ)) W :=
    hsmulC.add hhC
  have heqOn : EqOn (fun ζ => (E.weight (e.val.symm ζ)).toReal)
      (fun ζ => (1 / (q : ℝ)) • Real.log (Complex.normSq (F ζ)) + h (e.val.symm ζ)) W := by
    intro ζ hζ
    show (E.weight (e.val.symm ζ)).toReal
      = (1 / (q : ℝ)) • Real.log (Complex.normSq (F ζ)) + h (e.val.symm ζ)
    have hyU : e.val.symm ζ ∈ U := (hWT hζ).2
    have hne : G (e.val.symm ζ) ≠ 0 := hζ.2
    have hlog : singleLog G (e.val.symm ζ)
        = ((Real.log (Complex.normSq (G (e.val.symm ζ))) : ℝ) : EReal) := by
      rw [singleLog, generatorLog_single_eq_coe hne, Complex.normSq_eq_norm_sq]
    rw [hweight _ hyU, hlog, ← EReal.coe_mul, ← EReal.coe_add, EReal.toReal_coe]
    simp [hF, smul_eq_mul]
  refine ⟨W, hxW, hWopen, hWT.trans inter_subset_left, hrhoC.congr heqOn, ?_⟩
  intro ζ hζ
  have hddc : smoothDDC (fun y => (E.weight (e.val.symm y)).toReal) ζ
      = smoothDDC
        (fun y => (1 / (q : ℝ)) • Real.log (Complex.normSq (F y)) + h (e.val.symm y)) ζ :=
    smoothDDC_congr (Filter.eventuallyEq_of_mem (hWopen.mem_nhds hζ) heqOn)
  have hsplit := smoothDDC_add hWopen hsmulC hhC hζ
  have hkey : smoothDDC (fun y => (E.weight (e.val.symm y)).toReal) ζ
      = smoothDDC (fun y => (1 / (q : ℝ)) • Real.log (Complex.normSq (F y))) ζ
        + smoothDDC (fun y => h (e.val.symm y)) ζ := hddc.trans hsplit
  have hharm : smoothDDC (fun y => Real.log (Complex.normSq (F y))) ζ = 0 :=
    smoothDDC_log_normSq_eq_zero
      (Filter.eventually_of_mem (hTopen.mem_nhds (hWT hζ))
        (fun y hy => (hFdiff y hy).differentiableAt (hTopen.mem_nhds hy))) hζ.2
  have hzero : smoothDDC (fun y => (1 / (q : ℝ)) • Real.log (Complex.normSq (F y))) ζ = 0 := by
    rw [smoothDDC_smul hWopen hlogC (1 / (q : ℝ)) hζ, hharm, smul_zero]
  rw [hkey, hzero, zero_add, ClosedRealOneOneForm.coeff_neg,
    hcurv e ζ (hWT hζ).1 (hWT hζ).2, neg_neg]

end

end Hironaka.MeteredDivisorSmoothOffSupport
