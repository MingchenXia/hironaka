import Hironaka.Analytic.HiepStrongOpenness
import Hironaka.Analytic.HiepThreeTermEstimate

set_option autoImplicit false

/-!
# Hiep's strong effective openness from a local uniform bound

`HiepStrongEffectiveOpenness n` (`Hironaka.HiepStrongOpenness`) is part (ii) of the Main
theorem of Hiep, *The weighted log canonical threshold* (`hiep14-weighted-lct`).  Its proof
(`hiep14-weighted-lct:proof-ii`) has two halves:

* an analytic half, which from the Ohsawa--Takegoshi extension (Lemma 2.1), standard
  bases and Galligo's division estimate produces, near every point, a **uniform bound at a
  strictly higher exponent**: a ball `B(z, ρ)`, an exponent `d > c` and `M < ∞` with
  `∫_{B(z,ρ)} |f|² e^{-dψ_j} ≤ M` for all large `j`;
* a measure-theoretic half, which turns that bound into `L¹` convergence.

`HiepLocalUniformBound n` states the output of the analytic half, on a ball, for sequences.
It is a consequence of Hiep's theorem: by the strong openness corollary of (ii) there is
`d > c` with `∫ |f|² e^{-dφ} < ∞` near `z`, and (ii) at exponent `d` makes
`∫ |f|² e^{-dψ_j}` converge to it, hence eventually bounded.  The requirement `ρ ≤ R` is
essential: outside the ball the `ψ_j` are unconstrained.

`hiepStrongEffectiveOpenness_of_localUniformBound` proves the measure-theoretic half,
sorry-free:

1. every subsequence of `ψ_j` has a further subsequence converging to `φ` almost everywhere
   on `Ω'`, because `∫ (φ - ψ_j)⁺ → 0` (`exists_subseq_ae_tendsto_zero_of_tendsto_lintegral`,
   `tendsto_of_toENNReal_sub_tendsto_zero`);
2. `closure Ω''` is covered by finitely many balls carrying the uniform bound and a real
   upper bound for `φ`;
3. on each ball, Hiep's three-term estimate (`tendsto_lintegral_sub_of_uniform_bound`) gives
   `L¹` convergence along the subsequence; summing over the cover and passing from
   sub-subsequences to the sequence (`tendsto_of_subseq_tendsto`) concludes.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka

noncomputable section

open Hironaka

/-! ### Measure-theoretic helpers -/

/-- A sequence of nonnegative functions whose integrals tend to zero has a subsequence
tending to zero almost everywhere. -/
theorem exists_subseq_ae_tendsto_zero_of_tendsto_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {h : ℕ → α → ℝ≥0∞} (hm : ∀ j, AEMeasurable (h j) μ)
    (hl : Tendsto (fun j => ∫⁻ x, h j x ∂μ) atTop (𝓝 0)) :
    ∃ ms : ℕ → ℕ, StrictMono ms ∧ ∀ᵐ x ∂μ, Tendsto (fun k => h (ms k) x) atTop (𝓝 0) := by
  have hev : ∀ k : ℕ, ∀ᶠ j in atTop, ∫⁻ x, h j x ∂μ ≤ (2⁻¹ : ℝ≥0∞) ^ k := fun k =>
    hl.eventually (Iic_mem_nhds (ENNReal.pow_pos (by norm_num) k))
  obtain ⟨ms, hms, hle⟩ := extraction_forall_of_eventually hev
  refine ⟨ms, hms, ?_⟩
  have hsum : ∫⁻ x, ∑' k, h (ms k) x ∂μ ≠ ∞ := by
    rw [lintegral_tsum fun k => hm _]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  filter_upwards [ae_lt_top' (AEMeasurable.tsum fun k => hm _) hsum] with x hx
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne

/-- If `b j ≤ a < ⊤` and the deficits `(a - b j)⁺` tend to zero, then `b j → a`. -/
theorem tendsto_of_toENNReal_sub_tendsto_zero {a : EReal} {b : ℕ → EReal} (ha : a ≠ ⊤)
    (hb : ∀ j, b j ≤ a) (h : Tendsto (fun j => (a - b j).toENNReal) atTop (𝓝 0)) :
    Tendsto b atTop (𝓝 a) := by
  induction a using EReal.rec with
  | bot =>
      have hbot : b = fun _ => ⊥ := funext fun j => le_bot_iff.mp (hb j)
      rw [hbot]
      exact tendsto_const_nhds
  | top => exact absurd rfl ha
  | coe p =>
      refine tendsto_order.2 ⟨fun a' ha' => ?_, fun a' ha' =>
        Eventually.of_forall fun j => (hb j).trans_lt ha'⟩
      obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.mp ha'
      have hpq : (0 : ℝ≥0∞) < ENNReal.ofReal (p - q) :=
        ENNReal.ofReal_pos.mpr (sub_pos.mpr (EReal.coe_lt_coe_iff.mp hq2))
      filter_upwards [h.eventually (Iio_mem_nhds hpq)] with j hj
      refine hq1.trans (lt_of_not_ge fun hbq => (not_le.mpr hj) ?_)
      have hsub : ((p : EReal) - (q : EReal)) ≤ (p : EReal) - b j := EReal.sub_le_sub le_rfl hbq
      rw [← EReal.coe_sub] at hsub
      have htoe := EReal.toENNReal_le_toENNReal hsub
      rwa [EReal.real_coe_toENNReal] at htoe

theorem lintegral_biUnion_finset_le {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : α → ℝ≥0∞) (t : Finset ι) (s : ι → Set α) :
    ∫⁻ x in ⋃ i ∈ t, s i, f x ∂μ ≤ ∑ i ∈ t, ∫⁻ x in s i, f x ∂μ := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
      rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
      exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)

/-! ### The interface and the reduction -/

/-- **Hiep's local uniform bound**: the output of the `L²`-extension half of the proof of
Hiep's Main theorem (ii) (`hiep14-weighted-lct:proof-ii`), on a ball and for sequences.
An interface, not a theorem of this workspace. -/
def HiepLocalUniformBound (n : ℕ) : Prop := by
  letI : MeasurableSpace (ComplexModel n) := borel _
  letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
  exact ∀ (z : ComplexModel n) (R : ℝ) (φ : ComplexModel n → EReal)
      (f : ComplexModel n → ℂ) (c : ℝ),
    0 < R → PlurisubharmonicOn φ (ball z R) → DifferentiableOn ℂ f (ball z R) → 0 < c →
    (∫⁻ x in ball z R, multiplierDensity φ c f x) < ⊤ →
    ∀ ψ : ℕ → ComplexModel n → EReal, (∀ j, PlurisubharmonicOn (ψ j) (ball z R)) →
      (∀ j, ∀ x ∈ ball z R, ψ j x ≤ φ x) →
      Tendsto (fun j => ∫⁻ x in ball z R, (φ x - ψ j x).toENNReal) atTop (𝓝 0) →
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ R ∧ ∃ d : ℝ, c < d ∧ ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
        ∀ᶠ j in atTop, ∫⁻ x in ball z ρ, multiplierDensity (ψ j) d f x ≤ M

/-- The measure-theoretic half of Hiep's proof of (ii): a local uniform bound at a higher
exponent gives strong effective openness. -/
theorem hiepStrongEffectiveOpenness_of_localUniformBound (n : ℕ)
    (hU : HiepLocalUniformBound n) : HiepStrongEffectiveOpenness n := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  have _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro Ω' φ f c hΩ' hφ hf hc hint ψ hψ hle hL1 Ω'' _ hcomp hsub
  -- Local data at every point of the compact closure.
  have hloc : ∀ z ∈ closure Ω'', ∃ ρ : ℝ, 0 < ρ ∧ ball z ρ ⊆ Ω' ∧ ∃ d : ℝ, c < d ∧
      ∃ M : ℝ≥0∞, M ≠ ⊤ ∧
        (∀ᶠ j in atTop, ∫⁻ x in ball z ρ, multiplierDensity (ψ j) d f x ≤ M) ∧
        ∃ C : ℝ, ∀ x ∈ ball z ρ, φ x ≤ (C : EReal) := by
    intro z hz
    obtain ⟨R, hR, hRsub⟩ := Metric.isOpen_iff.mp hΩ' z (hsub hz)
    have hconvR : Tendsto (fun j => ∫⁻ x in ball z R, (φ x - ψ j x).toENNReal) atTop
        (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hL1 (fun _ => bot_le)
        (fun _ => lintegral_mono_set hRsub)
    obtain ⟨ρ, hρ, hρR, d, hcd, M, hM, hbd⟩ := hU z R φ f c hR (hφ.mono hRsub)
      (hf.mono hRsub) hc ((lintegral_mono_set hRsub).trans_lt hint) ψ
      (fun j => (hψ j).mono hRsub) (fun j x hx => hle j x (hRsub hx)) hconvR
    have hcl : closedBall z (ρ / 2) ⊆ ball z R :=
      (closedBall_subset_ball (by linarith)).trans (ball_subset_ball hρR)
    obtain ⟨C, -, hC⟩ := (hφ.mono hRsub).exists_nonnegative_compact_upper_bound
      (isCompact_closedBall z (ρ / 2)) hcl
    refine ⟨ρ / 2, by positivity, (ball_subset_closedBall.trans hcl).trans hRsub, d, hcd, M,
      hM, ?_, C, fun x hx => hC x (ball_subset_closedBall hx)⟩
    filter_upwards [hbd] with j hj
    exact (lintegral_mono_set (ball_subset_ball (by linarith))).trans hj
  choose! ρ hρ hρsub d hd M hM hbd C hC using hloc
  obtain ⟨t, ht, hcover⟩ := hcomp.elim_nhds_subcover (fun z => ball z (ρ z))
    (fun z hz => ball_mem_nhds z (hρ z hz))
  have hφusc : UpperSemicontinuousOn φ Ω' := hφ.discPshOn.upperSemicontinuousOn
  have hφtop : ∀ x ∈ Ω', φ x ≠ ⊤ := hφ.discPshOn.ne_top
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  -- An almost everywhere convergent further subsequence on `Ω'`.
  obtain ⟨ms, hms, hae⟩ := exists_subseq_ae_tendsto_zero_of_tendsto_lintegral
    (μ := volume.restrict Ω') (h := fun j x => (φ x - ψ (ns j) x).toENNReal)
    (fun j => ((hφusc.aemeasurable_restrict_of_isOpen hΩ').add
      (((hψ (ns j)).discPshOn.upperSemicontinuousOn.aemeasurable_restrict_of_isOpen
        hΩ').neg)).ereal_toENNReal)
    (hL1.comp hns)
  have hlim : ∀ᵐ x ∂(volume.restrict Ω'),
      Tendsto (fun k => ψ (ns (ms k)) x) atTop (𝓝 (φ x)) := by
    filter_upwards [hae, ae_restrict_mem hΩ'.measurableSet] with x hx hxΩ'
    exact tendsto_of_toENNReal_sub_tendsto_zero (hφtop x hxΩ')
      (fun k => hle _ x hxΩ') hx
  have hsubseq : Tendsto (fun k => ns (ms k)) atTop atTop := hns.comp hms.tendsto_atTop
  refine ⟨ms, ?_⟩
  -- The three-term estimate on each ball of the cover.
  have hball : ∀ z ∈ t, Tendsto (fun k => ∫⁻ x in ball z (ρ z),
      (multiplierDensity (ψ (ns (ms k))) c f x - multiplierDensity φ c f x)) atTop (𝓝 0) := by
    intro z hz
    have hzcl := ht z hz
    have hBΩ' := hρsub z hzcl
    exact tendsto_lintegral_sub_of_uniform_bound (μ := volume.restrict (ball z (ρ z)))
      (g := fun x => ENNReal.ofReal (‖f x‖ ^ 2)) (C := C z) hc (hd z hzcl)
      (((hf.continuousOn.mono hBΩ').aemeasurable measurableSet_ball).norm.pow_const 2
        |>.ennreal_ofReal)
      ((hφusc.mono hBΩ').aemeasurable_restrict_of_isOpen isOpen_ball)
      (fun k => ((hψ _).discPshOn.upperSemicontinuousOn.mono hBΩ').aemeasurable_restrict_of_isOpen
        isOpen_ball)
      ((ae_restrict_mem measurableSet_ball).mono fun x hx => hC z hzcl x hx)
      (ae_restrict_of_ae_restrict_of_subset hBΩ' hlim)
      ((lintegral_mono_set hBΩ').trans_lt hint).ne (hM z hzcl)
      (hsubseq.eventually (hbd z hzcl))
  have hsum := tendsto_finsetSum t hball
  rw [Finset.sum_const_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => bot_le) (fun k => ?_)
  exact (lintegral_mono_set (subset_closure.trans hcover)).trans
    (lintegral_biUnion_finset_le _ t _)

/-- **Strong openness for increasing sequences from Hiep's local uniform bound.** -/
theorem increasingStrongOpenness_of_hiepLocalUniformBound (n : ℕ)
    (hU : HiepLocalUniformBound n) : IncreasingStrongOpenness n :=
  increasingStrongOpenness_of_hiep n (hiepStrongEffectiveOpenness_of_localUniformBound n hU)

end

end Hironaka
