import Hironaka.Analytic.OTChenExtension
import Hironaka.Analytic.WeightedL2ExtensionLimit

set_option autoImplicit false

/-!
# Chen's extension on a relatively compact convex piece

* `integral_chenRHS_le`: the right-hand side of the twisted estimate is bounded by the slice
  integral `S = ∫_{Ωs} |f|² e^{-ϕ ∘ ι}`, with a constant independent of `ε` and `δ`.
* `exists_chen_delta_bound`: for each `δ ∈ (0, ε]`, a holomorphic `G` on `K` with
  `∫_K |χ f̃ - G|² e^{-ϕ} / (L η (|z_n|² + δ²)) ≤ 9600 π M² k S`.
* `exists_chen_extension`: letting `δ → 0` (Montel and Fatou), a holomorphic extension of
  `f` to `K` with `∫_K |F|² e^{-ϕ} ≤ C R² S`.
-/

open Set Filter MeasureTheory Complex Metric
open scoped Topology ContDiff ComplexConjugate ENNReal NNReal

namespace Hironaka.OTChen

noncomputable section

open CauchyGreen Hormander

variable {m : ℕ}

/-- **The right-hand side is controlled by the slice integral.** -/
theorem integral_chenRHS_le {D' : Set (ComplexModel (m + 1))} (hD'o : IsOpen D')
    {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) {ϕ : ComplexModel (m + 1) → ℝ}
    {f : ComplexModel m → ℂ} {Ωs : Set (ComplexModel m)} (hΩs : MeasurableSet Ωs)
    {lam₁ : ComplexModel (m + 1) → ℝ} (hl₁ : ∀ x ∈ D', 0 ≤ lam₁ x)
    {Mχ : ℝ} (hMχ : ∀ x, |deriv chenCutoff x| ≤ Mχ)
    (hslice : ∀ z ∈ D', coordSq (Fin.last m) z ≤ ε ^ 2 → initCoords z ∈ Ωs ∧
      Real.exp (-ϕ z) ≤ 2 * Real.exp (-ϕ (hyperplaneEmbedding m (initCoords z))))
    (hgm : AEMeasurable (fun w ↦ ENNReal.ofReal (‖f w‖ ^ 2 *
      Real.exp (-ϕ (hyperplaneEmbedding m w)))) (volume.restrict Ωs))
    (hS : ∫⁻ w in Ωs, ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-ϕ (hyperplaneEmbedding m w))) ≠ ⊤) :
    ∫ x in D', 25 * ‖chenV ε f x‖ ^ 2 * (coordSq (Fin.last m) x + ε ^ 2) ^ 2 / ε ^ 2 *
        Real.exp (-(chenPhi ϕ δ x + lam₁ x)) ≤
      200 * Real.pi * Mχ ^ 2 * (splitFactor m : ℝ) *
        (∫⁻ w in Ωs, ENNReal.ofReal (‖f w‖ ^ 2 *
          Real.exp (-ϕ (hyperplaneEmbedding m w)))).toReal := by
  set q := coordSq (Fin.last m) with hq
  set S := ∫⁻ w in Ωs, ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-ϕ (hyperplaneEmbedding m w)))
    with hSdef
  set A : ComplexModel (m + 1) → ℝ := fun x ↦ 25 * ‖chenV ε f x‖ ^ 2 * (q x + ε ^ 2) ^ 2 /
    ε ^ 2 * Real.exp (-(chenPhi ϕ δ x + lam₁ x)) with hA
  have hMχ0 : 0 ≤ Mχ := (abs_nonneg _).trans (hMχ 0)
  set c : ℝ := 200 * Mχ ^ 2 / ε ^ 2 with hc
  set g : ComplexModel m → ℝ≥0∞ := Ωs.indicator fun w ↦ ENNReal.ofReal c *
    ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-ϕ (hyperplaneEmbedding m w))) with hg
  have hgae : AEMeasurable g := (aemeasurable_indicator_iff hΩs).mpr (hgm.const_mul _)
  have hpt : ∀ z, D'.indicator (fun x ↦ ENNReal.ofReal (A x)) z ≤
      (closedBall (0 : ℂ) ε).indicator (fun _ ↦ g (initCoords z)) (z (Fin.last m)) := by
    intro z
    by_cases hzD : z ∈ D'
    · rw [indicator_of_mem hzD]
      by_cases hV0 : chenV ε f z = 0
      · simp [hA, hV0]
      · have hqz := coordSq_le_of_chenV_ne_zero hε hV0
        obtain ⟨hΩ, hexp⟩ := hslice z hzD hqz
        have hball : z (Fin.last m) ∈ closedBall (0 : ℂ) ε := by
          rw [mem_closedBall, dist_zero_right]
          have : ‖z (Fin.last m)‖ ^ 2 ≤ ε ^ 2 := hqz
          exact le_of_pow_le_pow_left₀ two_ne_zero hε.le this
        rw [indicator_of_mem hball, hg, indicator_of_mem hΩ, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hq0 : 0 ≤ q z := coordSq_nonneg z
        have hP : 0 < q z + δ ^ 2 := by positivity
        simp only [hA]
        rw [norm_chenV_sq_eq, exp_neg_chenPhi_add hδ]
        have h1 : (deriv chenCutoff (q z / ε ^ 2) / ε ^ 2) ^ 2 ≤ Mχ ^ 2 / ε ^ 4 := by
          have h0 : deriv chenCutoff (q z / ε ^ 2) ^ 2 ≤ Mχ ^ 2 :=
            sq_le_sq' (abs_le.mp (hMχ _)).1 (abs_le.mp (hMχ _)).2
          rw [div_pow, ← pow_mul]
          exact div_le_div_of_nonneg_right h0 (by positivity)
        have h2 : (q z + ε ^ 2) ^ 2 ≤ 4 * ε ^ 4 := by nlinarith
        have h3 : q z / (q z + δ ^ 2) ≤ 1 := (div_le_one hP).mpr (by nlinarith)
        have h4 : Real.exp (-lam₁ z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hl₁ z hzD])
        set F := ‖f (initCoords z)‖ ^ 2 with hF
        set e₀ := Real.exp (-ϕ (hyperplaneEmbedding m (initCoords z))) with he₀
        have hF0 : 0 ≤ F := by positivity
        have he₀0 : 0 ≤ e₀ := (Real.exp_pos _).le
        have hd0 : 0 ≤ (deriv chenCutoff (q z / ε ^ 2) / ε ^ 2) ^ 2 := by positivity
        calc 25 * ((deriv chenCutoff (q z / ε ^ 2) / ε ^ 2) ^ 2 * q z * F) *
              (q z + ε ^ 2) ^ 2 / ε ^ 2 *
              (Real.exp (-ϕ z) * Real.exp (-lam₁ z) / (q z + δ ^ 2))
            = 25 / ε ^ 2 * ((deriv chenCutoff (q z / ε ^ 2) / ε ^ 2) ^ 2 * (q z + ε ^ 2) ^ 2 *
                F * (q z / (q z + δ ^ 2)) * (Real.exp (-ϕ z) * Real.exp (-lam₁ z))) := by
              field_simp
          _ ≤ 25 / ε ^ 2 * (Mχ ^ 2 / ε ^ 4 * (4 * ε ^ 4) * F * 1 * (2 * e₀ * 1)) := by
              gcongr
          _ = c * (F * e₀) := by simp only [hc]; field_simp; ring
    · rw [indicator_of_notMem hzD]
      exact zero_le
  have hlint : ∫⁻ x in D', ENNReal.ofReal (A x) ≤
      splitFactor m * (volume (closedBall (0 : ℂ) ε) * ∫⁻ w, g w) := by
    rw [← lintegral_indicator hD'o.measurableSet]
    exact lintegral_le_of_le_indicator_closedBall hgae hpt
  have hgint : ∫⁻ w, g w = ENNReal.ofReal c * S := by
    rw [hg, lintegral_indicator hΩs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hvol : volume (closedBall (0 : ℂ) ε) * ENNReal.ofReal c =
      ENNReal.ofReal (200 * Real.pi * Mχ ^ 2) := by
    rw [Complex.volume_closedBall, ← ENNReal.ofReal_pow hε.le, ← ENNReal.ofReal_coe_nnreal,
      NNReal.coe_real_pi, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [hc]
    field_simp
  have hbound : ∫⁻ x in D', ENNReal.ofReal (A x) ≤
      (splitFactor m : ℝ≥0∞) * (ENNReal.ofReal (200 * Real.pi * Mχ ^ 2) * S) := by
    refine hlint.trans_eq ?_
    rw [hgint, ← mul_assoc (volume _), hvol]
  have hfin : (splitFactor m : ℝ≥0∞) * (ENNReal.ofReal (200 * Real.pi * Mχ ^ 2) * S) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS)
  have hMχ2 : 0 ≤ 200 * Real.pi * Mχ ^ 2 * (splitFactor m : ℝ) * S.toReal := by positivity
  by_cases hAm : AEStronglyMeasurable A (volume.restrict D')
  swap
  · change ∫ x in D', A x ≤ _
    rw [integral_non_aestronglyMeasurable hAm]
    exact hMχ2
  change ∫ x in D', A x ≤ _
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x ↦ by simp only [hA]; positivity)
    hAm]
  calc (∫⁻ x in D', ENNReal.ofReal (A x)).toReal
      ≤ ((splitFactor m : ℝ≥0∞) * (ENNReal.ofReal (200 * Real.pi * Mχ ^ 2) * S)).toReal :=
        ENNReal.toReal_mono hfin hbound
    _ = _ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
        simp only [ENNReal.coe_toReal]
        ring

/-- **One value of `δ`.** -/
theorem exists_chen_delta_bound (hH : HormanderL2Estimate (m + 1)) {R ε δ : ℝ} (hε : 0 < ε)
    (hεR : ε ≤ R) (hδ : 0 < δ) {D : Set (ComplexModel (m + 1))} (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hDb : Bornology.IsBounded D) (hDR : ∀ z ∈ D, ‖z (Fin.last m)‖ < R)
    {ϕ : ComplexModel (m + 1) → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ x ∈ D, ∀ ξ, 0 ≤ leviForm ϕ x ξ) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    {f : ComplexModel m → ℂ} {W : Set (ComplexModel m)} (hW : IsOpen W)
    (hf : DifferentiableOn ℂ f W) {Ωs : Set (ComplexModel m)} (hΩs : MeasurableSet Ωs)
    (hDslice : ∀ z ∈ D, coordSq (Fin.last m) z ≤ ε ^ 2 → initCoords z ∈ Ωs ∧
      initCoords z ∈ W ∧
      Real.exp (-ϕ z) ≤ 2 * Real.exp (-ϕ (hyperplaneEmbedding m (initCoords z))))
    {Mf : ℝ} (hMf : ∀ z ∈ D, coordSq (Fin.last m) z ≤ ε ^ 2 → ‖f (initCoords z)‖ ≤ Mf)
    {Mχ : ℝ} (hMχ : ∀ x, |deriv chenCutoff x| ≤ Mχ)
    (hgm : AEMeasurable (fun w ↦ ENNReal.ofReal (‖f w‖ ^ 2 *
      Real.exp (-ϕ (hyperplaneEmbedding m w)))) (volume.restrict Ωs))
    (hS : ∫⁻ w in Ωs, ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-ϕ (hyperplaneEmbedding m w))) ≠ ⊤)
    {K Kc : Set (ComplexModel (m + 1))} (hKo : IsOpen K) (hKKc : K ⊆ Kc) (hKc : IsCompact Kc)
    (hKcD : Kc ⊆ D) :
    ∃ G : ComplexModel (m + 1) → ℂ, DifferentiableOn ℂ G K ∧
      ∫⁻ z in K, ENNReal.ofReal (‖chenA ε f z - G z‖ ^ 2 * Real.exp (-ϕ z) /
        (chenL R ε (coordSq (Fin.last m) z) * chenEta R ε (coordSq (Fin.last m) z) *
          (coordSq (Fin.last m) z + δ ^ 2))) ≤
      ENNReal.ofReal (9600 * Real.pi * Mχ ^ 2 * (splitFactor m : ℝ) *
        (∫⁻ w in Ωs, ENNReal.ofReal (‖f w‖ ^ 2 *
          Real.exp (-ϕ (hyperplaneEmbedding m w)))).toReal) := by
  set q := coordSq (Fin.last m) with hq
  have hL0 : 1 ≤ chenL R ε 0 := one_le_chenL hε le_rfl (by
    have := pow_le_pow_left₀ hε.le hεR 2; nlinarith)
  set t := 1 / (24 * chenL R ε 0) with ht_def
  have ht : 0 < t := by positivity
  obtain ⟨D', U₀, lam₁, lam₂, hD'o, -, hD'D, -, hKcU₀, hU₀D', hl₁, hl₂, hl, hl0, hest⟩ :=
    hH D hDo hDc hDb Kc hKc hKcD t ht
  have hD'sub : D' ⊆ D := subset_closure.trans hD'D
  have hD'b : Bornology.IsBounded D' := hDb.subset hD'sub
  have hDW : ∀ z ∈ D, q z ≤ ε ^ 2 → initCoords z ∈ W := fun z hz hqz ↦ (hDslice z hz hqz).2.1
  obtain ⟨G, hG, hmem, horth⟩ := exists_holomorphic_minimal_solution hDo hD'o hD'sub hD'b hε hδ
    hϕ hϕL hBϕ hW hf hDW hMf hMχ hl₁ hl₂ hl hest
  obtain ⟨hint, hest2⟩ := chen_twisted_estimate hDo hD'o hD'sub hD'b hε hεR hδ hDR hϕ hϕL hBϕ
    hW hf hDW hMf hMχ hl₁ hl₂ hl ht.le le_rfl hest hG hmem horth
  have hrhs := integral_chenRHS_le hD'o hε hδ hΩs (fun x hx ↦ (hl x hx).1) hMχ
    (fun z hz hqz ↦ ⟨(hDslice z (hD'sub hz) hqz).1, (hDslice z (hD'sub hz) hqz).2.2⟩) hgm hS
  have hKD' : K ⊆ D' := hKKc.trans (hKcU₀.trans hU₀D')
  refine ⟨G, hG.mono hKD', ?_⟩
  have hsR : ∀ z ∈ D, q z + ε ^ 2 ≤ 2 * R ^ 2 := by
    intro z hz
    have h1 : q z ≤ R ^ 2 := by
      simp only [hq, coordSq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hDR z hz).le 2
    have h2 : ε ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hε.le hεR 2
    linarith
  have hY0 : ∀ x ∈ D', 0 ≤ ‖chenA ε f x - G x‖ ^ 2 * Real.exp (-(chenPhi ϕ δ x + lam₁ x)) /
      (24 * chenL R ε (q x) * chenEta R ε (q x)) := by
    intro x hx
    obtain ⟨-, hL, hη⟩ := chen_good hε (coordSq_nonneg x) (hsR x (hD'sub hx))
    positivity
  calc ∫⁻ z in K, ENNReal.ofReal (‖chenA ε f z - G z‖ ^ 2 * Real.exp (-ϕ z) /
        (chenL R ε (q z) * chenEta R ε (q z) * (q z + δ ^ 2)))
      ≤ ∫⁻ z in D', ENNReal.ofReal (24 * (‖chenA ε f z - G z‖ ^ 2 *
          Real.exp (-(chenPhi ϕ δ z + lam₁ z)) / (24 * chenL R ε (q z) * chenEta R ε (q z)))) := by
        refine (setLIntegral_mono' hKo.measurableSet fun z hz ↦ le_of_eq ?_).trans
          (lintegral_mono_set hKD')
        congr 1
        have hl0z := (hl0 z (hKcU₀ (hKKc hz))).1
        rw [exp_neg_chenPhi_add hδ, hl0z, neg_zero, Real.exp_zero, mul_one]
        obtain ⟨-, hL, hη⟩ : 0 < q z + ε ^ 2 ∧ 0 < chenL R ε (q z) ∧ 0 < chenEta R ε (q z) :=
          chen_good hε (coordSq_nonneg z) (hsR z (hD'sub (hKD' hz)))
        have hP : 0 < q z + δ ^ 2 := by have := coordSq_nonneg z; positivity
        field_simp
        exact (mul_div_cancel_right₀ _ hP.ne').symm
    _ = ENNReal.ofReal (∫ z in D', 24 * (‖chenA ε f z - G z‖ ^ 2 *
          Real.exp (-(chenPhi ϕ δ z + lam₁ z)) / (24 * chenL R ε (q z) * chenEta R ε (q z)))) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hint.const_mul 24)]
        exact (ae_restrict_iff' hD'o.measurableSet).mpr (Eventually.of_forall fun x hx ↦
          mul_nonneg (by norm_num) (hY0 x hx))
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul]
        linarith

theorem chenL_eta_mul_le {R ε δ s : ℝ} (hε : 0 < ε) (hR : 0 < R) (hs : 0 ≤ s)
    (hsR : s + ε ^ 2 ≤ 2 * R ^ 2) (hδε : δ ≤ ε) (hδ : 0 ≤ δ) :
    chenL R ε s * chenEta R ε s * (s + δ ^ 2) ≤ 8 * R ^ 2 := by
  have hL := one_le_chenL hε hs hsR
  have hη := chenEta_le_two_mul hε hs hsR
  have hLη := chenL_le_chenEta hε hs hsR
  have hsq := chenL_sq_mul_le hε hR hs hsR
  have hδ2 : δ ^ 2 ≤ ε ^ 2 := pow_le_pow_left₀ hδ hδε 2
  have h1 : chenL R ε s * chenEta R ε s ≤ 2 * chenL R ε s ^ 2 := by nlinarith
  have h2 : 0 ≤ s + δ ^ 2 := by positivity
  calc chenL R ε s * chenEta R ε s * (s + δ ^ 2)
      ≤ 2 * chenL R ε s ^ 2 * (s + ε ^ 2) := by
        apply mul_le_mul h1 (by linarith) h2 (by positivity)
    _ ≤ 8 * R ^ 2 := by nlinarith

/-- **Chen's extension on `K`**: letting `δ → 0`. -/
theorem exists_chen_extension (hH : HormanderL2Estimate (m + 1)) {R ε : ℝ} (hR : 0 < R)
    (hε : 0 < ε) (hεR : ε ≤ R) {D : Set (ComplexModel (m + 1))} (hDo : IsOpen D)
    (hDc : Convex ℝ D) (hDb : Bornology.IsBounded D) (hDR : ∀ z ∈ D, ‖z (Fin.last m)‖ < R)
    {ϕ : ComplexModel (m + 1) → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ x ∈ D, ∀ ξ, 0 ≤ leviForm ϕ x ξ) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    {f : ComplexModel m → ℂ} {W : Set (ComplexModel m)} (hW : IsOpen W)
    (hf : DifferentiableOn ℂ f W) {Ωs : Set (ComplexModel m)} (hΩs : MeasurableSet Ωs)
    (hDslice : ∀ z ∈ D, coordSq (Fin.last m) z ≤ ε ^ 2 → initCoords z ∈ Ωs ∧
      initCoords z ∈ W ∧
      Real.exp (-ϕ z) ≤ 2 * Real.exp (-ϕ (hyperplaneEmbedding m (initCoords z))))
    {Mf : ℝ} (hMf : ∀ z ∈ D, coordSq (Fin.last m) z ≤ ε ^ 2 → ‖f (initCoords z)‖ ≤ Mf)
    {Mχ : ℝ} (hMχ : ∀ x, |deriv chenCutoff x| ≤ Mχ)
    (hgm : AEMeasurable (fun w ↦ ENNReal.ofReal (‖f w‖ ^ 2 *
      Real.exp (-ϕ (hyperplaneEmbedding m w)))) (volume.restrict Ωs))
    (hS : ∫⁻ w in Ωs, ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-ϕ (hyperplaneEmbedding m w))) ≠ ⊤)
    {K Kc : Set (ComplexModel (m + 1))} (hKo : IsOpen K) (hKKc : K ⊆ Kc) (hKc : IsCompact Kc)
    (hKcD : Kc ⊆ D) :
    ∃ F : ComplexModel (m + 1) → ℂ, DifferentiableOn ℂ F K ∧
      (∀ w, hyperplaneEmbedding m w ∈ K → F (hyperplaneEmbedding m w) = f w) ∧
      ∫⁻ z in K, ENNReal.ofReal (‖F z‖ ^ 2) * ENNReal.ofReal (Real.exp (-ϕ z)) ≤
        ENNReal.ofReal ((4 * Real.pi + 16 * 9600 * Real.pi * Mχ ^ 2) * R ^ 2 *
          (splitFactor m : ℝ) * (∫⁻ w in Ωs, ENNReal.ofReal (‖f w‖ ^ 2 *
            Real.exp (-ϕ (hyperplaneEmbedding m w)))).toReal) := by
  set q := coordSq (Fin.last m) with hq
  set S := ∫⁻ w in Ωs, ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-ϕ (hyperplaneEmbedding m w)))
    with hSdef
  set k : ℝ := (splitFactor m : ℝ) with hk
  have hk0 : 0 ≤ k := NNReal.coe_nonneg _
  have hMχ0 : 0 ≤ Mχ := (abs_nonneg _).trans (hMχ 0)
  set B : ℝ := 9600 * Real.pi * Mχ ^ 2 * k * S.toReal with hB
  have hB0 : 0 ≤ B := by positivity
  set a := chenA ε f with ha
  have hKD : K ⊆ D := hKKc.trans hKcD
  have hKm : MeasurableSet K := hKo.measurableSet
  have hsR : ∀ z ∈ D, q z + ε ^ 2 ≤ 2 * R ^ 2 := by
    intro z hz
    have h1 : q z ≤ R ^ 2 := by
      simp only [hq, coordSq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hDR z hz).le 2
    have h2 : ε ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hε.le hεR 2
    linarith
  -- The sequence of solutions.
  set δs : ℕ → ℝ := fun j ↦ ε / ((j : ℝ) + 1) with hδs
  have hδpos : ∀ j, 0 < δs j := fun j ↦ by positivity
  have hδle : ∀ j, δs j ≤ ε := fun j ↦
    div_le_self hε.le (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
  have hδlim : Tendsto δs atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε
    simpa [hδs, div_eq_mul_inv] using this
  have hex := fun j ↦ exists_chen_delta_bound hH hε hεR (hδpos j) hDo hDc hDb hDR hϕ hϕL hBϕ
    hW hf hΩs hDslice hMf hMχ hgm hS hKo hKKc hKc hKcD
  choose G hGd hGb using hex
  -- Continuity facts.
  have haD : ContDiffOn ℝ ∞ a D := fun z hz ↦
    (contDiffAt_chenA hε hW hf (hDslice z hz · |>.2.1)).contDiffWithinAt
  have hac : ContinuousOn a K := haD.continuousOn.mono hKD
  have hϕc : ContinuousOn ϕ D := hϕ.continuousOn
  have hgood : ∀ z ∈ D, 0 < q z + ε ^ 2 ∧ 0 < chenL R ε (q z) ∧ 0 < chenEta R ε (q z) :=
    fun z hz ↦ chen_good hε (coordSq_nonneg z) (hsR z hz)
  have hqc : Continuous q := (contDiff_coordSq (Fin.last m)).continuous
  have hLc : ContinuousOn (fun x ↦ chenL R ε (q x)) D := fun x hx ↦
    ((hasDerivAt_chenL R ε (hgood x hx).1).continuousAt.comp hqc.continuousAt).continuousWithinAt
  have hηc : ContinuousOn (fun x ↦ chenEta R ε (q x)) D := fun x hx ↦
    ((hasDerivAt_chenEta R ε (hgood x hx).1 (hgood x hx).2.1).continuousAt.comp
      hqc.continuousAt).continuousWithinAt
  -- The cutoff part of the bound.
  have hA0 : ∫⁻ z in K, ENNReal.ofReal (‖a z‖ ^ 2) * ENNReal.ofReal (Real.exp (-ϕ z)) ≤
      ENNReal.ofReal (2 * k * Real.pi * R ^ 2 * S.toReal) := by
    set g : ComplexModel m → ℝ≥0∞ := Ωs.indicator fun w ↦ ENNReal.ofReal 2 *
      ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-ϕ (hyperplaneEmbedding m w))) with hg
    have hgae : AEMeasurable g := (aemeasurable_indicator_iff hΩs).mpr (hgm.const_mul _)
    have hpt : ∀ z, K.indicator (fun z ↦ ENNReal.ofReal (‖a z‖ ^ 2) *
        ENNReal.ofReal (Real.exp (-ϕ z))) z ≤
        (closedBall (0 : ℂ) ε).indicator (fun _ ↦ g (initCoords z)) (z (Fin.last m)) := by
      intro z
      by_cases hzK : z ∈ K
      · rw [indicator_of_mem hzK]
        by_cases hqz : q z ≤ ε ^ 2
        · obtain ⟨hΩ, -, hexp⟩ := hDslice z (hKD hzK) hqz
          have hball : z (Fin.last m) ∈ closedBall (0 : ℂ) ε := by
            rw [mem_closedBall, dist_zero_right]
            exact le_of_pow_le_pow_left₀ two_ne_zero hε.le hqz
          rw [indicator_of_mem hball, hg, indicator_of_mem hΩ,
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : ‖a z‖ ^ 2 ≤ ‖f (initCoords z)‖ ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_chenA_le ε f z) 2
          calc ‖a z‖ ^ 2 * Real.exp (-ϕ z)
              ≤ ‖f (initCoords z)‖ ^ 2 *
                  (2 * Real.exp (-ϕ (hyperplaneEmbedding m (initCoords z)))) :=
                mul_le_mul h1 hexp (Real.exp_pos _).le (by positivity)
            _ = _ := by ring
        · have h0 : a z = 0 := chenA_eq_zero_of_lt hε (not_le.mp hqz)
          rw [h0]
          simp
      · rw [indicator_of_notMem hzK]
        exact zero_le
    have hlint := lintegral_le_of_le_indicator_closedBall hgae hpt
    rw [lintegral_indicator hKm] at hlint
    refine hlint.trans ?_
    rw [hg, lintegral_indicator hΩs, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      Complex.volume_closedBall]
    have e : (splitFactor m : ℝ≥0∞) * (ENNReal.ofReal ε ^ 2 * (NNReal.pi : ℝ≥0∞) *
        (ENNReal.ofReal 2 * S)) = ENNReal.ofReal (k * (ε ^ 2 * Real.pi * (2 * S.toReal))) := by
      rw [ENNReal.ofReal_mul hk0, ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_toReal hS, ENNReal.ofReal_pow hε.le, hk, ENNReal.ofReal_coe_nnreal,
        ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
    refine (le_of_eq e).trans (ENNReal.ofReal_le_ofReal ?_)
    have hε2 : ε ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hε.le hεR 2
    have hS0 : 0 ≤ S.toReal := ENNReal.toReal_nonneg
    nlinarith [mul_nonneg (mul_nonneg hk0 Real.pi_pos.le) hS0]
  -- The bound for every `G j`.
  set Btot : ℝ := (4 * Real.pi + 16 * 9600 * Real.pi * Mχ ^ 2) * R ^ 2 * k * S.toReal with hBtot
  have hGbound : ∀ j, ∫⁻ z in K, ENNReal.ofReal (‖G j z‖ ^ 2) *
      ENNReal.ofReal (Real.exp (-ϕ z)) ≤ ENNReal.ofReal Btot := by
    intro j
    set Y : ComplexModel (m + 1) → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (‖a z - G j z‖ ^ 2 *
      Real.exp (-ϕ z) / (chenL R ε (q z) * chenEta R ε (q z) * (q z + δs j ^ 2))) with hY
    have hpt : ∀ z ∈ K, ENNReal.ofReal (‖G j z‖ ^ 2) * ENNReal.ofReal (Real.exp (-ϕ z)) ≤
        ENNReal.ofReal 2 * (ENNReal.ofReal (‖a z‖ ^ 2) * ENNReal.ofReal (Real.exp (-ϕ z))) +
          ENNReal.ofReal (16 * R ^ 2) * Y z := by
      intro z hz
      obtain ⟨-, hL, hη⟩ : 0 < q z + ε ^ 2 ∧ 0 < chenL R ε (q z) ∧ 0 < chenEta R ε (q z) :=
        hgood z (hKD hz)
      have hq0 := coordSq_nonneg z
      have hden : 0 < chenL R ε (q z) * chenEta R ε (q z) * (q z + δs j ^ 2) := by
        have := hδpos j; positivity
      have hden8 := chenL_eta_mul_le hε hR hq0 (hsR z (hKD hz)) (hδle j) (hδpos j).le
      simp only [hY]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      set e := Real.exp (-ϕ z) with he
      have he0 : 0 < e := Real.exp_pos _
      have htri : ‖G j z‖ ^ 2 ≤ 2 * ‖a z‖ ^ 2 + 2 * ‖a z - G j z‖ ^ 2 := by
        have h := norm_sub_le (a z) (a z - G j z)
        rw [sub_sub_cancel] at h
        nlinarith [sq_nonneg (‖a z‖ - ‖a z - G j z‖), norm_nonneg (a z),
          norm_nonneg (a z - G j z), norm_nonneg (G j z)]
      have h8 : ‖a z - G j z‖ ^ 2 * e ≤ 8 * R ^ 2 * (‖a z - G j z‖ ^ 2 * e /
          (chenL R ε (q z) * chenEta R ε (q z) * (q z + δs j ^ 2))) := by
        rw [mul_div_assoc', le_div_iff₀ hden]
        have h0 : 0 ≤ ‖a z - G j z‖ ^ 2 * e := by positivity
        nlinarith
      nlinarith
    calc ∫⁻ z in K, ENNReal.ofReal (‖G j z‖ ^ 2) * ENNReal.ofReal (Real.exp (-ϕ z))
        ≤ ∫⁻ z in K, (ENNReal.ofReal 2 * (ENNReal.ofReal (‖a z‖ ^ 2) *
            ENNReal.ofReal (Real.exp (-ϕ z))) + ENNReal.ofReal (16 * R ^ 2) * Y z) :=
          setLIntegral_mono' hKm hpt
      _ = ENNReal.ofReal 2 * (∫⁻ z in K, ENNReal.ofReal (‖a z‖ ^ 2) *
            ENNReal.ofReal (Real.exp (-ϕ z))) + ENNReal.ofReal (16 * R ^ 2) * ∫⁻ z in K, Y z := by
          have hmeas : AEMeasurable (fun z ↦ ENNReal.ofReal 2 * (ENNReal.ofReal (‖a z‖ ^ 2) *
              ENNReal.ofReal (Real.exp (-ϕ z)))) (volume.restrict K) :=
            ((((ENNReal.continuous_ofReal.comp_continuousOn (hac.norm.pow 2))).aemeasurable
              hKm).mul ((ENNReal.continuous_ofReal.comp_continuousOn
                ((hϕc.mono hKD).neg.rexp)).aemeasurable hKm)).const_mul _
          rw [lintegral_add_left' hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal (2 * k * Real.pi * R ^ 2 * S.toReal) +
            ENNReal.ofReal (16 * R ^ 2) * ENNReal.ofReal B := by
          exact add_le_add (mul_le_mul_of_nonneg_left hA0 zero_le)
            (mul_le_mul_of_nonneg_left (hGb j) zero_le)
      _ = ENNReal.ofReal Btot := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          simp only [hBtot, hB]
          ring
  -- Montel.
  have hloc : ∀ x ∈ K, ∃ r > 0, ∃ M : ℝ, ∀ᶠ i in atTop,
      DifferentiableOn ℂ (G i) (ball x r) ∧ ∀ y ∈ ball x r, ‖G i y‖ ≤ M := by
    intro x hx
    have hcont : ContinuousAt ϕ x := hϕc.continuousAt (hDo.mem_nhds (hKD hx))
    obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
    refine exists_eventually_norm_le_of_weighted_bounds (U := fun _ ↦ K)
      (w := fun _ z ↦ ENNReal.ofReal (Real.exp (-ϕ z))) (fun _ ↦ hKo) monotone_const
      (fun _ _ ↦ monotone_const) hGd ENNReal.ofReal_ne_top hGbound (mem_iUnion.mpr ⟨0, hx⟩) hr
      (Real.exp_pos (-(ϕ x + 1))) fun y hy ↦ ?_
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have h1 := hball (mem_ball.mp hy)
    rw [Real.dist_eq] at h1
    linarith [le_abs_self (ϕ y - ϕ x)]
  obtain ⟨ψ, F, hψ, hF, hconv⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn_of_eventually_bounded hKo G hloc
  have hpt : ∀ x ∈ K, Tendsto (fun i ↦ G (ψ i) x) atTop (𝓝 (F x)) := fun x hx ↦
    hconv.tendsto_at hx
  have hFc : ContinuousOn F K := hF.continuousOn
  have hexpc : ContinuousOn (fun z ↦ Real.exp (-ϕ z)) K := (hϕc.mono hKD).neg.rexp
  -- Fatou for the weighted norm.
  have hFbound : ∫⁻ z in K, ENNReal.ofReal (‖F z‖ ^ 2) * ENNReal.ofReal (Real.exp (-ϕ z)) ≤
      ENNReal.ofReal Btot := by
    have hmeas : ∀ i, AEMeasurable (fun z ↦ ENNReal.ofReal (‖G (ψ i) z‖ ^ 2) *
        ENNReal.ofReal (Real.exp (-ϕ z))) (volume.restrict K) := fun i ↦
      ((ENNReal.continuous_ofReal.comp_continuousOn
        ((hGd (ψ i)).continuousOn.norm.pow 2)).aemeasurable hKm).mul
        ((ENNReal.continuous_ofReal.comp_continuousOn hexpc).aemeasurable hKm)
    calc ∫⁻ z in K, ENNReal.ofReal (‖F z‖ ^ 2) * ENNReal.ofReal (Real.exp (-ϕ z))
        ≤ ∫⁻ z in K, liminf (fun i ↦ ENNReal.ofReal (‖G (ψ i) z‖ ^ 2) *
            ENNReal.ofReal (Real.exp (-ϕ z))) atTop := by
          refine setLIntegral_mono' hKm fun z hz ↦ ?_
          have ht : Tendsto (fun i ↦ ENNReal.ofReal (‖G (ψ i) z‖ ^ 2) *
              ENNReal.ofReal (Real.exp (-ϕ z))) atTop
              (𝓝 (ENNReal.ofReal (‖F z‖ ^ 2) * ENNReal.ofReal (Real.exp (-ϕ z)))) :=
            ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal (((hpt z hz).norm).pow 2))
              (Or.inr ENNReal.ofReal_ne_top)
          exact ht.liminf_eq.ge
      _ ≤ liminf (fun i ↦ ∫⁻ z in K, ENNReal.ofReal (‖G (ψ i) z‖ ^ 2) *
            ENNReal.ofReal (Real.exp (-ϕ z))) atTop := lintegral_liminf_le' hmeas
      _ ≤ ENNReal.ofReal Btot :=
          liminf_le_of_frequently_le' (Frequently.of_forall fun i ↦ hGbound (ψ i))
  -- Fatou for the singular weight.
  have hδψ : Tendsto (fun i ↦ δs (ψ i)) atTop (𝓝 0) := hδlim.comp hψ.tendsto_atTop
  have hYfin : ∫⁻ z in K, ENNReal.ofReal (‖a z - F z‖ ^ 2 * Real.exp (-ϕ z) /
      (chenL R ε (q z) * chenEta R ε (q z) * q z)) ≤ ENNReal.ofReal B := by
    have hmeas : ∀ i, AEMeasurable (fun z ↦ ENNReal.ofReal (‖a z - G (ψ i) z‖ ^ 2 *
        Real.exp (-ϕ z) / (chenL R ε (q z) * chenEta R ε (q z) * (q z + δs (ψ i) ^ 2))))
        (volume.restrict K) := by
      intro i
      refine (ENNReal.continuous_ofReal.comp_continuousOn ?_).aemeasurable hKm
      refine (((hac.sub (hGd (ψ i)).continuousOn).norm.pow 2).mul hexpc).div
        (((hLc.mono hKD).mul (hηc.mono hKD)).mul (hqc.continuousOn.add continuousOn_const))
        fun z hz ↦ ?_
      obtain ⟨-, hL, hη⟩ : 0 < q z + ε ^ 2 ∧ 0 < chenL R ε (q z) ∧ 0 < chenEta R ε (q z) :=
        hgood z (hKD hz)
      have := coordSq_nonneg z
      have := hδpos (ψ i)
      exact (mul_pos (mul_pos hL hη) (by positivity)).ne'
    calc ∫⁻ z in K, ENNReal.ofReal (‖a z - F z‖ ^ 2 * Real.exp (-ϕ z) /
          (chenL R ε (q z) * chenEta R ε (q z) * q z))
        ≤ ∫⁻ z in K, liminf (fun i ↦ ENNReal.ofReal (‖a z - G (ψ i) z‖ ^ 2 *
            Real.exp (-ϕ z) / (chenL R ε (q z) * chenEta R ε (q z) * (q z + δs (ψ i) ^ 2))))
            atTop := by
          refine setLIntegral_mono' hKm fun z hz ↦ ?_
          obtain ⟨-, hL, hη⟩ : 0 < q z + ε ^ 2 ∧ 0 < chenL R ε (q z) ∧ 0 < chenEta R ε (q z) :=
            hgood z (hKD hz)
          by_cases hq0 : q z = 0
          · rw [hq0, mul_zero, div_zero, ENNReal.ofReal_zero]
            exact zero_le
          · have hqpos : 0 < q z := lt_of_le_of_ne (coordSq_nonneg z) (Ne.symm hq0)
            have ht : Tendsto (fun i ↦ ENNReal.ofReal (‖a z - G (ψ i) z‖ ^ 2 *
                Real.exp (-ϕ z) / (chenL R ε (q z) * chenEta R ε (q z) * (q z + δs (ψ i) ^ 2))))
                atTop (𝓝 (ENNReal.ofReal (‖a z - F z‖ ^ 2 * Real.exp (-ϕ z) /
                  (chenL R ε (q z) * chenEta R ε (q z) * q z)))) := by
              refine ENNReal.tendsto_ofReal (Tendsto.div ?_ ?_ (by positivity))
              · exact ((tendsto_const_nhds.sub (hpt z hz)).norm.pow 2).mul_const _
              · have := ((hδψ.pow 2).const_add (q z)).const_mul
                  (chenL R ε (q z) * chenEta R ε (q z))
                simpa using this
            exact ht.liminf_eq.ge
      _ ≤ liminf (fun i ↦ ∫⁻ z in K, ENNReal.ofReal (‖a z - G (ψ i) z‖ ^ 2 *
            Real.exp (-ϕ z) / (chenL R ε (q z) * chenEta R ε (q z) * (q z + δs (ψ i) ^ 2))))
            atTop := lintegral_liminf_le' hmeas
      _ ≤ ENNReal.ofReal B :=
          liminf_le_of_frequently_le' (Frequently.of_forall fun i ↦ hGb (ψ i))
  -- Vanishing on the hyperplane.
  have hvanish : ∀ w, hyperplaneEmbedding m w ∈ K → F (hyperplaneEmbedding m w) = f w := by
    intro w hw
    have hWc : ContinuousOn (fun z ↦ Real.exp (-ϕ z) / (chenL R ε (q z) * chenEta R ε (q z)))
        K := hexpc.div ((hLc.mono hKD).mul (hηc.mono hKD)) fun z hz ↦
          (mul_pos (hgood z (hKD hz)).2.1 (hgood z (hKD hz)).2.2).ne'
    have hWpos : ∀ z ∈ K, 0 < Real.exp (-ϕ z) / (chenL R ε (q z) * chenEta R ε (q z)) :=
      fun z hz ↦ div_pos (Real.exp_pos _) (mul_pos (hgood z (hKD hz)).2.1 (hgood z (hKD hz)).2.2)
    have hfin : ∫⁻ z in K, ENNReal.ofReal (‖a z - F z‖ ^ 2 *
        (Real.exp (-ϕ z) / (chenL R ε (q z) * chenEta R ε (q z))) /
          ‖z (Fin.last m)‖ ^ 2) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans (le_of_eq ?_) hYfin)
      refine setLIntegral_congr_fun hKm fun z _ ↦ ?_
      simp only [hq, coordSq]
      congr 1
      ring
    have h0 := eq_zero_of_lintegral_div_normSq_ne_top hKo (hac.sub hFc) hWc hWpos hfin hw
      (hyperplaneEmbedding_last m w)
    have ha' : a (hyperplaneEmbedding m w) = f w := chenA_hyperplaneEmbedding ε f w
    rw [← ha']
    exact (sub_eq_zero.mp h0).symm
  refine ⟨F, hF, hvanish, hFbound.trans_eq ?_⟩
  simp only [hBtot, hk]

end

end Hironaka.OTChen
