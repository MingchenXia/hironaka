import Hironaka.Analytic.QuasiEquisingularApproximation
import Hironaka.Analytic.ERealChordUSC

set_option autoImplicit false

/-!
# Elementary facts about quasi-equisingular approximations

Multiplier ideals of a quasi-PSH germ shrink as the exponent grows:
`I(dφ) ⊆ I(cφ)` for `0 < c ≤ d`, since `φ` is locally bounded above.
Consequently a theta-PSH potential which already has analytic singularity
type is its own (constant) quasi-equisingular approximation, and every tail
of a quasi-equisingular approximation is again one.

The existence theorem for general potentials (Demailly regularization) is
not addressed here.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka

noncomputable section

section Local

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {φ : E → EReal} {x : E}

/-- A quasi-PSH germ is quasi-PSH on one open neighborhood. -/
theorem QuasiPlurisubharmonicAt.exists_isOpen_quasiPlurisubharmonicOn
    (hφ : QuasiPlurisubharmonicAt φ x) :
    ∃ U : Set E, IsOpen U ∧ x ∈ U ∧ QuasiPlurisubharmonicOn φ U := by
  obtain ⟨p, h, ⟨P, hP, hxP, hp⟩, hh, heq⟩ := hφ
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp (hh.and heq)
  refine ⟨P ∩ V, hP.inter hV, ⟨hxP, hxV⟩, ?_⟩
  intro y hy
  refine ⟨p, h, ⟨P ∩ V, hP.inter hV, hy, hp.mono inter_subset_left⟩, ?_, ?_⟩
  · exact Filter.eventually_of_mem ((hP.inter hV).mem_nhds hy)
      (fun z hz => (hVsub hz.2).1)
  · exact Filter.eventually_of_mem ((hP.inter hV).mem_nhds hy)
      (fun z hz => (hVsub hz.2).2)

/-- A quasi-PSH germ is bounded above by a real constant near its center. -/
theorem QuasiPlurisubharmonicAt.eventually_le_const
    (hφ : QuasiPlurisubharmonicAt φ x) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x, φ y ≤ C := by
  obtain ⟨C, hC, -⟩ :=
    EReal.lt_iff_exists_real_btwn.mp (lt_top_iff_ne_top.mpr hφ.ne_top)
  exact ⟨C, (hφ.upperSemicontinuousAt C hC).mono fun _ hy => hy.le⟩

/-- For `0 < c ≤ d` and `a ≤ C`, the weight `e^{-ca}` is at most
`e^{(d-c)C} e^{-da}`; the pole `a = ⊥` is handled in `ℝ≥0∞`. -/
theorem multiplierWeight_le_of_exponent_le {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    {a : EReal} {C : ℝ} (ha : a ≤ C) :
    multiplierWeight c a ≤ EReal.exp (((d - c) * C : ℝ) : EReal) * multiplierWeight d a := by
  have hd : 0 < d := hc.trans_le hcd
  by_cases habot : a = ⊥
  · have hKpos : 0 < EReal.exp (((d - c) * C : ℝ) : EReal) := by
      rw [EReal.exp_coe]
      exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    rw [habot, multiplierWeight_bot hd, ENNReal.mul_top hKpos.ne']
    exact le_top
  have hatop : a ≠ ⊤ := fun h => EReal.coe_ne_top C (top_le_iff.mp (h ▸ ha))
  have haReal : (a.toReal : EReal) = a := EReal.coe_toReal hatop habot
  have haC : a.toReal ≤ C := by
    rw [← haReal] at ha
    exact EReal.coe_le_coe_iff.mp ha
  rw [← haReal, multiplierWeight_coe, multiplierWeight_coe, EReal.exp_coe,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  nlinarith

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E}

/-- On an open quasi-PSH domain, the weighted squared norm of a continuous
function is measurable for the restricted measure. -/
theorem aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn
    {U : Set E} (hU : IsOpen U) (hφ : QuasiPlurisubharmonicOn φ U) {c : ℝ}
    (hc : c ≠ 0) {f : E → ℂ} (hf : ContinuousOn f U) :
    AEMeasurable (multiplierDensity φ c f) (μ.restrict U) := by
  classical
  let v : E → EReal := fun y => if y ∈ U then φ y else ⊤
  have hv : UpperSemicontinuous v := by
    intro y a hya
    by_cases hy : y ∈ U
    · have hua : φ y < a := by simpa [v, hy] using hya
      have hlocal := hφ.upperSemicontinuousOn y hy a hua
      rw [hU.nhdsWithin_eq hy] at hlocal
      filter_upwards [hlocal, hU.mem_nhds hy] with z hz hzU
      simpa [v, hzU] using hz
    · simp [v, hy] at hya
  have hφmeas : AEMeasurable φ (μ.restrict U) := by
    apply hv.measurable.aemeasurable.congr
    filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
    simp [v, hy]
  have hcmul : AEMeasurable (fun y => (c : EReal) * φ y) (μ.restrict U) :=
    (Hironaka.continuous_eReal_const_mul hc).measurable.comp_aemeasurable' hφmeas
  have hweight : AEMeasurable (fun y => multiplierWeight c (φ y)) (μ.restrict U) := by
    have hneg : AEMeasurable (fun y => -((c : EReal) * φ y)) (μ.restrict U) :=
      continuous_neg.measurable.comp_aemeasurable' hcmul
    simpa only [multiplierWeight] using EReal.measurable_exp.comp_aemeasurable' hneg
  exact (((hf.aemeasurable hU.measurableSet).norm.pow_const 2).ennreal_ofReal).mul hweight

/-- Multiplier ideals of a quasi-PSH germ decrease in the exponent:
`I(dφ) ⊆ I(cφ)` for `0 < c ≤ d`. -/
theorem multiplierIntegrableAt_of_exponent_le (hφ : QuasiPlurisubharmonicAt φ x)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) {f : E → ℂ}
    (hf : MultiplierIntegrableAt φ d f x μ) : MultiplierIntegrableAt φ c f x μ := by
  obtain ⟨-, U, hU, hxU, hfhol, hfint⟩ := hf
  obtain ⟨C, hC⟩ := Hironaka.QuasiPlurisubharmonicAt.eventually_le_const hφ
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hC
  obtain ⟨Q, hQ, hxQ, hφQ⟩ :=
    Hironaka.QuasiPlurisubharmonicAt.exists_isOpen_quasiPlurisubharmonicOn hφ
  let W := (U ∩ V) ∩ Q
  have hW : IsOpen W := (hU.inter hV).inter hQ
  have hWU : W ⊆ U := fun _ hy => hy.1.1
  have hhol := hfhol.mono hWU
  let K : ℝ≥0∞ := EReal.exp (((d - c) * C : ℝ) : EReal)
  have hpoint : ∀ y ∈ W,
      multiplierDensity φ c f y ≤ K * multiplierDensity φ d f y := by
    intro y hy
    have hweight := multiplierWeight_le_of_exponent_le hc hcd (hVsub hy.1.2)
    unfold multiplierDensity
    calc
      ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight c (φ y) ≤
          ENNReal.ofReal (‖f y‖ ^ 2) * (K * multiplierWeight d (φ y)) := by gcongr
      _ = K * (ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight d (φ y)) := by ac_rfl
  refine ⟨hc, W, hW, ⟨⟨hxU, hxV⟩, hxQ⟩, hhol,
    aemeasurable_multiplierDensity_restrict_of_quasiPlurisubharmonicOn hW
      (fun y hy => hφQ y hy.2) hc.ne' hhol.continuousOn, ?_⟩
  calc
    (∫⁻ y in W, multiplierDensity φ c f y ∂μ) ≤
        ∫⁻ y in W, K * multiplierDensity φ d f y ∂μ :=
      setLIntegral_mono_ae' hW.measurableSet
        (Filter.Eventually.of_forall fun y hy => hpoint y hy)
    _ = K * ∫⁻ y in W, multiplierDensity φ d f y ∂μ := by
      rw [lintegral_const_mul' K _ (by simp [K])]
    _ < ⊤ := ENNReal.mul_lt_top (by simp [K]) (hfint.mono hWU).2

end Local

open Hironaka.PositiveClasses
open Hironaka.QuasiEquisingularApproximation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `I(du) ⊆ I(cu)` on every chart for a quasi-PSH potential and `0 < c ≤ d`. -/
theorem multiplierIdealIncluded_self_of_exponent_le {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) {c d : ℝ} (hc : 0 < c)
    (hcd : c ≤ d) : MultiplierIdealIncluded (n := n) u d u c := by
  intro e z hz f _ hmem
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  exact multiplierIntegrableAt_of_exponent_le (hu e z hz) hc hcd hmem

/-- A theta-PSH potential with analytic singularity type is its own
quasi-equisingular approximation, with zero error. -/
theorem isQuasiEquisingularApproximation_const
    (omega : KahlerBackground n M) (θ : ClosedRealOneOneForm n M)
    {u : M → EReal} (hu : IsThetaPshPotential θ.val u)
    (hsing : HasManifoldAnalyticSingularityType (n := n) u) :
    IsQuasiEquisingularApproximation omega θ u (fun _ => 0) (fun _ => u) := by
  refine ⟨hu, ⟨fun _ => le_rfl, antitone_const, tendsto_const_nhds⟩, ?_, fun _ => hsing,
    ⟨fun _ => antitone_const, fun _ => tendsto_const_nhds⟩, ?_⟩
  · intro k
    simpa using hu
  · intro c d hc hcd
    exact Eventually.of_forall fun _ =>
      multiplierIdealIncluded_self_of_exponent_le hu.1.quasiPlurisubharmonic hc hcd.le

/-- Every tail of a quasi-equisingular approximation is again one. -/
theorem IsQuasiEquisingularApproximation.comp_add
    {omega : KahlerBackground n M} {θ : ClosedRealOneOneForm n M}
    {u : M → EReal} {ε : ℕ → ℝ} {uSeq : ℕ → M → EReal}
    (h : IsQuasiEquisingularApproximation omega θ u ε uSeq) (m : ℕ) :
    IsQuasiEquisingularApproximation omega θ u (fun k => ε (k + m))
      (fun k => uSeq (k + m)) := by
  have hmono : Monotone fun k : ℕ => k + m := fun _ _ hab => Nat.add_le_add_right hab m
  refine ⟨h.target, ⟨fun k => h.error_nonneg _, h.error_antitone.comp_monotone hmono,
    (tendsto_add_atTop_iff_nat m).mpr h.error_tendsto⟩, fun k => h.term _,
    fun k => h.term_hasAnalyticSingularityType _,
    ⟨fun x => (h.term_antitone x).comp_monotone hmono,
      fun x => (tendsto_add_atTop_iff_nat m).mpr (h.term_tendsto x)⟩, ?_⟩
  intro c d hc hcd
  exact (tendsto_add_atTop_nat m).eventually (h.eventually_multiplierIdealIncluded hc hcd)

end

end Hironaka
