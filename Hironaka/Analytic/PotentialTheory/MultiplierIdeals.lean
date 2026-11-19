import Hironaka.Analytic.PotentialTheory.MultiplierIdealsBasic
import Hironaka.Analytic.ERealChordUSC
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Local multiplier compatibility interfaces

Source: `transcendental-nakamaye-copy4-20260911:sec:qpsh`.
The local weighted-integrability predicate is closed under addition and
multiplication by a holomorphic germ, and it is transported to a less singular
quasi-PSH potential. Neither this module nor its predicates assert coherence,
integral closedness, subadditivity, or a sheaf on a complex manifold.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]
  {φ ψ : E → EReal} {c : ℝ} {f g : E → ℂ} {x : E}

/-- A quasi-PSH germ is represented by quasi-PSH germs on one open
neighborhood.  This is the local-domain form needed for measurability below. -/
private theorem exists_open_quasiPlurisubharmonicOn_of_at
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

variable [MeasurableSpace E] {μ : Measure E}

/-- Relative upper semicontinuity on an open domain gives a measurable
representative for every restricted Borel measure. -/
private theorem aemeasurable_restrict_of_isOpen_of_upperSemicontinuousOn
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] {ν : Measure X} {u : X → EReal} {U : Set X}
    (hu : UpperSemicontinuousOn u U) (hU : IsOpen U) :
    AEMeasurable u (ν.restrict U) := by
  classical
  let v : X → EReal := fun y => if y ∈ U then u y else ⊤
  have hv : UpperSemicontinuous v := by
    intro y a hya
    by_cases hy : y ∈ U
    · have hua : u y < a := by simpa [v, hy] using hya
      have hlocal := hu y hy a hua
      rw [hU.nhdsWithin_eq hy] at hlocal
      filter_upwards [hlocal, hU.mem_nhds hy] with z hz hzU
      simpa [v, hzU] using hz
    · simp [v, hy] at hya
  apply hv.measurable.aemeasurable.congr
  filter_upwards [ae_restrict_mem hU.measurableSet] with y hy
  simp [v, hy]

/-- On an open quasi-PSH domain, a continuous complex representative has a
measurable extended weighted squared norm. -/
private theorem aemeasurable_multiplierDensity_restrict
    [BorelSpace E] {U : Set E} (hU : IsOpen U)
    (hφ : QuasiPlurisubharmonicOn φ U) (hc : c ≠ 0)
    (hf : ContinuousOn f U) :
    AEMeasurable (multiplierDensity φ c f) (μ.restrict U) := by
  have hφmeas : AEMeasurable φ (μ.restrict U) :=
    aemeasurable_restrict_of_isOpen_of_upperSemicontinuousOn
      hφ.upperSemicontinuousOn hU
  have hcmul : AEMeasurable (fun y => (c : EReal) * φ y) (μ.restrict U) :=
    (Hironaka.continuous_eReal_const_mul hc).measurable.comp_aemeasurable' hφmeas
  have hweight : AEMeasurable (fun y => multiplierWeight c (φ y)) (μ.restrict U) := by
    have hneg : AEMeasurable (fun y => -((c : EReal) * φ y)) (μ.restrict U) :=
      continuous_neg.measurable.comp_aemeasurable' hcmul
    simpa only [multiplierWeight] using EReal.measurable_exp.comp_aemeasurable' hneg
  have hfmeas : AEMeasurable f (μ.restrict U) :=
    hf.aemeasurable hU.measurableSet
  exact ((hfmeas.norm.pow_const 2).ennreal_ofReal).mul hweight

/-- Additive comparison of potentials gives the precise exponential comparison
of multiplier weights.  The pole case is kept in `EReal`; only the finite case
is reduced to an inequality of real exponents. -/
private theorem multiplierWeight_le_of_le_add (hc : 0 < c) {a b : EReal} {C : ℝ}
    (hbtop : b ≠ ⊤) (hab : a ≤ b + (C : EReal)) :
    multiplierWeight c b ≤ EReal.exp ((c * C : ℝ) : EReal) * multiplierWeight c a := by
  by_cases habot : a = ⊥
  · have hKpos : 0 < EReal.exp ((c * C : ℝ) : EReal) := by
      rw [EReal.exp_coe]
      exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    rw [habot, multiplierWeight_bot hc]
    calc
      multiplierWeight c b ≤ ⊤ := le_top
      _ = EReal.exp ((c * C : ℝ) : EReal) * ⊤ :=
        (ENNReal.mul_top hKpos.ne').symm
  have hbaddtop : b + (C : EReal) ≠ ⊤ := EReal.add_ne_top hbtop (EReal.coe_ne_top C)
  have hatop : a ≠ ⊤ := fun ha => hbaddtop ((top_le_iff.mp (ha ▸ hab)))
  by_cases hbbot : b = ⊥
  · have : a = ⊥ := le_bot_iff.mp (by simpa [hbbot] using hab)
    exact (habot this).elim
  have haReal : (a.toReal : EReal) = a := EReal.coe_toReal hatop habot
  have hbReal : (b.toReal : EReal) = b := EReal.coe_toReal hbtop hbbot
  have habReal : a.toReal ≤ b.toReal + C := by
    rw [← haReal, ← hbReal] at hab
    simpa [← EReal.coe_add] using hab
  have hmulReal : c * a.toReal ≤ c * (b.toReal + C) :=
    mul_le_mul_of_nonneg_left habReal hc.le
  have hargReal : -(c * b.toReal) ≤ c * C + -(c * a.toReal) := by
    nlinarith
  have harg : -((c : EReal) * b) ≤
      ((c * C : ℝ) : EReal) + -((c : EReal) * a) := by
    rw [← haReal, ← hbReal]
    simpa [← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_add] using
      (EReal.coe_le_coe_iff.mpr hargReal)
  calc
    multiplierWeight c b ≤
        EReal.exp (((c * C : ℝ) : EReal) + -((c : EReal) * a)) :=
      EReal.exp_monotone harg
    _ = EReal.exp ((c * C : ℝ) : EReal) * multiplierWeight c a := by
      rw [EReal.exp_add]
      rfl

/-- Local measurable weights and `|f+g|² ≤ 2(|f|²+|g|²)` give
additive closure after intersecting the two integration neighborhoods. -/
theorem multiplierIntegrableAt_add [BorelSpace E] (hφ : QuasiPlurisubharmonicAt φ x)
    (hf : MultiplierIntegrableAt φ c f x μ) (hg : MultiplierIntegrableAt φ c g x μ) :
    MultiplierIntegrableAt φ c (fun y => f y + g y) x μ := by
  obtain ⟨hc, U, hU, hxU, hfhol, hfint⟩ := hf
  obtain ⟨_, V, hV, hxV, hghol, hgint⟩ := hg
  obtain ⟨Q, hQ, hxQ, hφQ⟩ := exists_open_quasiPlurisubharmonicOn_of_at hφ
  let W := (U ∩ V) ∩ Q
  have hW : IsOpen W := (hU.inter hV).inter hQ
  have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxQ⟩
  have hWU : W ⊆ U := fun _ hy => hy.1.1
  have hWV : W ⊆ V := fun _ hy => hy.1.2
  have hWQ : W ⊆ Q := fun _ hy => hy.2
  have hfW := hfint.mono hWU
  have hgW := hgint.mono hWV
  have hhol : DifferentiableOn ℂ (fun y => f y + g y) W :=
    (hfhol.mono hWU).add (hghol.mono hWV)
  refine ⟨hc, W, hW, hxW, hhol, ?_⟩
  refine ⟨aemeasurable_multiplierDensity_restrict hW (hφQ.mono hWQ) hc.ne'
    hhol.continuousOn, ?_⟩
  have hpoint : ∀ y,
      multiplierDensity φ c (fun z => f z + g z) y ≤
        (2 : ℝ≥0∞) * (multiplierDensity φ c f y + multiplierDensity φ c g y) := by
    intro y
    have hnorm : ‖f y + g y‖ ^ 2 ≤ 2 * (‖f y‖ ^ 2 + ‖g y‖ ^ 2) := by
      have htri := norm_add_le (f y) (g y)
      have hf0 := norm_nonneg (f y)
      have hg0 := norm_nonneg (g y)
      have hsum0 := norm_nonneg (f y + g y)
      nlinarith [sq_nonneg (‖f y‖ - ‖g y‖)]
    have hofReal : ENNReal.ofReal (‖f y + g y‖ ^ 2) ≤
        (2 : ℝ≥0∞) *
          (ENNReal.ofReal (‖f y‖ ^ 2) + ENNReal.ofReal (‖g y‖ ^ 2)) := by
      calc
        ENNReal.ofReal (‖f y + g y‖ ^ 2) ≤
            ENNReal.ofReal (2 * (‖f y‖ ^ 2 + ‖g y‖ ^ 2)) :=
          ENNReal.ofReal_le_ofReal hnorm
        _ = (2 : ℝ≥0∞) *
            (ENNReal.ofReal (‖f y‖ ^ 2) + ENNReal.ofReal (‖g y‖ ^ 2)) := by
          rw [ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
          norm_num
    unfold multiplierDensity
    calc
      ENNReal.ofReal (‖f y + g y‖ ^ 2) * multiplierWeight c (φ y) ≤
          ((2 : ℝ≥0∞) *
            (ENNReal.ofReal (‖f y‖ ^ 2) + ENNReal.ofReal (‖g y‖ ^ 2))) *
              multiplierWeight c (φ y) := by
        gcongr
      _ = (2 : ℝ≥0∞) *
          (ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight c (φ y) +
            ENNReal.ofReal (‖g y‖ ^ 2) * multiplierWeight c (φ y)) := by
        simp only [mul_add, add_mul]
        ac_rfl
  calc
    (∫⁻ y in W, multiplierDensity φ c (fun z => f z + g z) y ∂μ) ≤
        ∫⁻ y in W, (2 : ℝ≥0∞) *
          (multiplierDensity φ c f y + multiplierDensity φ c g y) ∂μ :=
      lintegral_mono hpoint
    _ = (2 : ℝ≥0∞) *
        ∫⁻ y in W, multiplierDensity φ c f y + multiplierDensity φ c g y ∂μ := by
      rw [lintegral_const_mul' (2 : ℝ≥0∞) _ (by norm_num)]
    _ = (2 : ℝ≥0∞) *
        ((∫⁻ y in W, multiplierDensity φ c f y ∂μ) +
          ∫⁻ y in W, multiplierDensity φ c g y ∂μ) := by
      rw [lintegral_add_left' hfW.1]
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num)
      (ENNReal.add_lt_top.mpr ⟨hfW.2, hgW.2⟩)

/-- A holomorphic germ is bounded on a smaller neighborhood, so
its product with a weighted-L2 holomorphic germ is again weighted L2. -/
theorem multiplierIntegrableAt_holomorphic_mul [BorelSpace E]
    (hφ : QuasiPlurisubharmonicAt φ x)
    (hf : MultiplierIntegrableAt φ c f x μ) (hg : AnalyticAt ℂ g x) :
    MultiplierIntegrableAt φ c (fun y => g y * f y) x μ := by
  obtain ⟨hc, U, hU, hxU, hfhol, hfint⟩ := hf
  have hgbound : ∀ᶠ y in 𝓝 x, ‖g y‖ ≤ ‖g x‖ + 1 := by
    have hnorm : Tendsto (fun y => ‖g y‖) (𝓝 x) (𝓝 ‖g x‖) :=
      Filter.Tendsto.norm (f := g) (a := g x) hg.continuousAt
    have hconst : Tendsto (fun _ : E => ‖g x‖ + 1) (𝓝 x) (𝓝 (‖g x‖ + 1)) :=
      tendsto_const_nhds
    have hlt : ∀ᶠ y in 𝓝 x, ‖g y‖ < ‖g x‖ + 1 :=
      Filter.Tendsto.eventually_lt hnorm hconst (by linarith)
    exact hlt.mono (fun _ hy => hy.le)
  obtain ⟨V, hVsub, hV, hxV⟩ :=
    mem_nhds_iff.mp (hg.eventually_analyticAt.and hgbound)
  obtain ⟨Q, hQ, hxQ, hφQ⟩ := exists_open_quasiPlurisubharmonicOn_of_at hφ
  let W := (U ∩ V) ∩ Q
  have hW : IsOpen W := (hU.inter hV).inter hQ
  have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxQ⟩
  have hWU : W ⊆ U := fun _ hy => hy.1.1
  have hWV : W ⊆ V := fun _ hy => hy.1.2
  have hWQ : W ⊆ Q := fun _ hy => hy.2
  have hgW : DifferentiableOn ℂ g W := fun y hy =>
    (hVsub hy.1.2).1.differentiableAt.differentiableWithinAt
  have hhol : DifferentiableOn ℂ (fun y => g y * f y) W :=
    hgW.mul (hfhol.mono hWU)
  have hfW := hfint.mono hWU
  refine ⟨hc, W, hW, hxW, hhol, ?_⟩
  refine ⟨aemeasurable_multiplierDensity_restrict hW (hφQ.mono hWQ) hc.ne'
    hhol.continuousOn, ?_⟩
  let B : ℝ := ‖g x‖ + 1
  let K : ℝ≥0∞ := ENNReal.ofReal (B ^ 2)
  have hpoint : ∀ y ∈ W,
      multiplierDensity φ c (fun z => g z * f z) y ≤
        K * multiplierDensity φ c f y := by
    intro y hy
    have hgy : ‖g y‖ ≤ B := (hVsub hy.1.2).2
    have hB0 : 0 ≤ B := by dsimp [B]; positivity
    have hsq : ‖g y‖ ^ 2 ≤ B ^ 2 := by
      nlinarith [norm_nonneg (g y)]
    have hofReal : ENNReal.ofReal (‖g y‖ ^ 2) ≤ K := by
      exact ENNReal.ofReal_le_ofReal hsq
    unfold multiplierDensity
    rw [norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    calc
      (ENNReal.ofReal (‖g y‖ ^ 2) * ENNReal.ofReal (‖f y‖ ^ 2)) *
          multiplierWeight c (φ y) ≤
        (K * ENNReal.ofReal (‖f y‖ ^ 2)) * multiplierWeight c (φ y) :=
          by gcongr
      _ = K * (ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight c (φ y)) := by
        ac_rfl
  calc
    (∫⁻ y in W, multiplierDensity φ c (fun z => g z * f z) y ∂μ) ≤
        ∫⁻ y in W, K * multiplierDensity φ c f y ∂μ :=
      setLIntegral_mono_ae' hW.measurableSet
        (Filter.Eventually.of_forall fun y hy => hpoint y hy)
    _ = K * ∫⁻ y in W, multiplierDensity φ c f y ∂μ := by
      rw [lintegral_const_mul' K _ (by simp [K])]
    _ < ⊤ := ENNReal.mul_lt_top (by simp [K]) hfW.2

/-- The manuscript's order gives the inclusion in this direction:
`φ ≤ ψ + C` implies `I(cφ) ⊆ I(cψ)`, since the latter weight is at most
`exp(cC)` times the former. Positive c is part of `hf`. -/
theorem multiplierIntegrableAt_of_moreSingularAt [BorelSpace E]
    (hψ : QuasiPlurisubharmonicAt ψ x)
    (hcomp : MoreSingularAt φ ψ x) (hf : MultiplierIntegrableAt φ c f x μ) :
    MultiplierIntegrableAt ψ c f x μ := by
  obtain ⟨hc, U, hU, hxU, hfhol, hfint⟩ := hf
  obtain ⟨C, hC⟩ := hcomp
  obtain ⟨V, hVsub, hV, hxV⟩ := mem_nhds_iff.mp hC
  obtain ⟨Q, hQ, hxQ, hψQ⟩ := exists_open_quasiPlurisubharmonicOn_of_at hψ
  let W := (U ∩ V) ∩ Q
  have hW : IsOpen W := (hU.inter hV).inter hQ
  have hxW : x ∈ W := ⟨⟨hxU, hxV⟩, hxQ⟩
  have hWU : W ⊆ U := fun _ hy => hy.1.1
  have hWV : W ⊆ V := fun _ hy => hy.1.2
  have hWQ : W ⊆ Q := fun _ hy => hy.2
  have hfW := hfint.mono hWU
  have hhol := hfhol.mono hWU
  let K : ℝ≥0∞ := EReal.exp ((c * C : ℝ) : EReal)
  have hpoint : ∀ y ∈ W,
      multiplierDensity ψ c f y ≤ K * multiplierDensity φ c f y := by
    intro y hy
    have hweight : multiplierWeight c (ψ y) ≤ K * multiplierWeight c (φ y) :=
      multiplierWeight_le_of_le_add hc (hψQ y (hWQ hy)).ne_top (hVsub (hWV hy))
    unfold multiplierDensity
    calc
      ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight c (ψ y) ≤
          ENNReal.ofReal (‖f y‖ ^ 2) * (K * multiplierWeight c (φ y)) :=
        by gcongr
      _ = K * (ENNReal.ofReal (‖f y‖ ^ 2) * multiplierWeight c (φ y)) := by
        ac_rfl
  refine ⟨hc, W, hW, hxW, hhol, ?_⟩
  refine ⟨aemeasurable_multiplierDensity_restrict hW (hψQ.mono hWQ) hc.ne'
    hhol.continuousOn, ?_⟩
  calc
    (∫⁻ y in W, multiplierDensity ψ c f y ∂μ) ≤
        ∫⁻ y in W, K * multiplierDensity φ c f y ∂μ :=
      setLIntegral_mono_ae' hW.measurableSet
        (Filter.Eventually.of_forall fun y hy => hpoint y hy)
    _ = K * ∫⁻ y in W, multiplierDensity φ c f y ∂μ := by
      rw [lintegral_const_mul' K _ (by simp [K])]
    _ < ⊤ := ENNReal.mul_lt_top (by simp [K]) hfW.2

/-- Equal singularity types give the same local multiplier-integrability
predicate by applying the proved comparison in both directions. -/
theorem multiplierIntegrableAt_iff_of_sameSingularityTypeOn
    [BorelSpace E]
    (hφ : QuasiPlurisubharmonicAt φ x) (hψ : QuasiPlurisubharmonicAt ψ x)
    {U : Set E} (hU : U ∈ 𝓝 x) (hcomp : SameSingularityTypeOn φ ψ U) :
    MultiplierIntegrableAt φ c f x μ ↔ MultiplierIntegrableAt ψ c f x μ :=
  ⟨multiplierIntegrableAt_of_moreSingularAt hψ (hcomp.1.moreSingularAt hU),
    multiplierIntegrableAt_of_moreSingularAt hφ (hcomp.2.moreSingularAt hU)⟩

end Hironaka
