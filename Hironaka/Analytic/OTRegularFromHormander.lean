import Hironaka.Analytic.OTChenLimit
import Hironaka.Analytic.OhsawaTakegoshiRegularReduction
import Hironaka.Analytic.ConvexExhaustion
import Hironaka.Analytic.SmoothPshHessian

set_option autoImplicit false

/-!
# The regular Ohsawa--Takegoshi theorem from Hörmander's estimate

`ohsawaTakegoshiHyperplaneRegular_of_hormander` derives `OhsawaTakegoshiHyperplaneRegular`
from `Hormander.HormanderL2Estimate` in every dimension, following B.-Y. Chen
(arXiv:1105.2430).

* `exists_extension_on_piece`: on a bounded open `K` with `closure K ⊆ Ω`, shrink `Ω` to the
  convex set `D = {z ∈ Ω : infDist z Ωᶜ > δ₀/2}`, choose `ε` so that `(z', 0) ∈ Ω` and
  `e^{-ϕ(z)} ≤ 2 e^{-ϕ(z', 0)}` whenever `z ∈ D` and `|z_n| ≤ ε`, and apply
  `exists_chen_extension`.
* `regularHyperplaneExtension_of_hormander`: exhaust `Ω` by bounded convex sets and pass to the
  limit with `exists_differentiableOn_extension_of_weighted_bounds`.

The constant is `C = (4π + 153600 π M²) R² k_m`, where `M` bounds the derivative of the cutoff
and `k_m` is the Haar factor of the splitting `ℂ^{m+1} = ℂ^m × ℂ`.
-/

open Set Filter MeasureTheory Complex Metric
open scoped Topology ContDiff ComplexConjugate ENNReal NNReal

namespace Hironaka.OTChen

noncomputable section

open CauchyGreen Hormander

variable {m : ℕ}

theorem dist_hyperplaneEmbedding_initCoords (z : ComplexModel (m + 1)) :
    dist z (hyperplaneEmbedding m (initCoords z)) = ‖z (Fin.last m)‖ := by
  rw [dist_eq_norm]
  have h := norm_sq_eq_initCoords (z - hyperplaneEmbedding m (initCoords z))
  rw [initCoords_sub, initCoords_hyperplaneEmbedding, sub_self, norm_zero] at h
  simp only [PiLp.sub_apply, hyperplaneEmbedding_last, sub_zero] at h
  have h2 : ‖z - hyperplaneEmbedding m (initCoords z)‖ ^ 2 = ‖z (Fin.last m)‖ ^ 2 := by
    rw [h]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- The Ohsawa--Takegoshi constant produced by Chen's argument. -/
def chenConstant (m : ℕ) (R Mχ : ℝ) : ℝ :=
  (4 * Real.pi + 16 * 9600 * Real.pi * Mχ ^ 2) * R ^ 2 * (splitFactor m : ℝ)

theorem chenConstant_pos {R : ℝ} (hR : 0 < R) (Mχ : ℝ) : 0 < chenConstant m R Mχ := by
  unfold chenConstant
  have := splitFactor_pos m
  have : (0 : ℝ) < splitFactor m := by exact_mod_cast this
  positivity

/-- **One piece of the exhaustion.** -/
theorem exists_extension_on_piece (hH : HormanderL2Estimate (m + 1)) {R : ℝ} (hR : 0 < R)
    {Mχ : ℝ} (hMχ : ∀ x, |deriv chenCutoff x| ≤ Mχ)
    {Ω : Set (ComplexModel (m + 1))} (hΩo : IsOpen Ω) (hΩc : Convex ℝ Ω)
    (hΩb : Bornology.IsBounded Ω) (hΩR : ∀ z ∈ Ω, ‖z (Fin.last m)‖ < R)
    {U : Set (ComplexModel (m + 1))} (hUo : IsOpen U) (hΩU : closure Ω ⊆ U)
    {φ : ComplexModel (m + 1) → ℝ} (hφs : ContDiffOn ℝ ∞ φ U)
    (hφpsh : PlurisubharmonicOn (fun z ↦ (φ z : EReal)) U) {c : ℝ} (hc : 0 < c)
    {f : ComplexModel m → ℂ} (hf : DifferentiableOn ℂ f (hyperplaneEmbedding m ⁻¹' U))
    (hS : ∫⁻ w in hyperplaneEmbedding m ⁻¹' Ω, ENNReal.ofReal (‖f w‖ ^ 2 *
      Real.exp (-(c * φ (hyperplaneEmbedding m w)))) ≠ ⊤)
    {K : Set (ComplexModel (m + 1))} (hKo : IsOpen K) (hKb : Bornology.IsBounded K)
    (hKΩ : closure K ⊆ Ω) :
    ∃ F : ComplexModel (m + 1) → ℂ, DifferentiableOn ℂ F K ∧
      (∀ w, hyperplaneEmbedding m w ∈ K → F (hyperplaneEmbedding m w) = f w) ∧
      ∫⁻ z in K, ENNReal.ofReal (‖F z‖ ^ 2) * ENNReal.ofReal (Real.exp (-(c * φ z))) ≤
        ENNReal.ofReal (chenConstant m R Mχ *
          (∫⁻ w in hyperplaneEmbedding m ⁻¹' Ω, ENNReal.ofReal (‖f w‖ ^ 2 *
            Real.exp (-(c * φ (hyperplaneEmbedding m w))))).toReal) := by
  set ι := hyperplaneEmbedding m with hι
  set ϕ : ComplexModel (m + 1) → ℝ := fun z ↦ c * φ z with hϕdef
  have hclΩ : IsCompact (closure Ω) := hΩb.isCompact_closure
  have hΩne : Ωᶜ.Nonempty := by
    refine ⟨EuclideanSpace.single (Fin.last m) (R : ℂ), fun h ↦ ?_⟩
    have h1 := hΩR _ h
    simp [abs_of_pos hR] at h1
  have hϕU : ContDiffOn ℝ ∞ ϕ U := contDiffOn_const.mul hφs
  have hϕcl : ContinuousOn ϕ (closure Ω) := hϕU.continuousOn.mono hΩU
  obtain ⟨Bϕ, hBϕ⟩ := hclΩ.exists_bound_of_continuousOn hϕcl
  obtain ⟨ρ, hρ, hρϕ⟩ := Metric.uniformContinuousOn_iff.mp
    (hclΩ.uniformContinuousOn_of_continuous hϕcl) (Real.log 2) (Real.log_pos one_lt_two)
  have hιc : Continuous ι := continuous_hyperplaneEmbedding m
  have hsl : IsCompact (ι ⁻¹' closure Ω) := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_closure.preimage hιc) ?_
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ComplexModel (m + 1))).mp
      hΩb.closure
    refine (Metric.isBounded_iff_subset_closedBall (0 : ComplexModel m)).mpr ⟨r, fun w hw ↦ ?_⟩
    have := hr hw
    rw [mem_closedBall, dist_zero_right, hι, norm_hyperplaneEmbedding] at this
    rwa [mem_closedBall, dist_zero_right]
  obtain ⟨Mf, hMf⟩ := hsl.exists_bound_of_continuousOn
    (hf.continuousOn.mono (preimage_mono hΩU))
  have hKc : IsCompact (closure K) := hKb.isCompact_closure
  obtain ⟨δ₀, hδ₀, hthick⟩ := hKc.exists_thickening_subset_open hΩo hKΩ
  set D : Set (ComplexModel (m + 1)) := {z | z ∈ Ω ∧ δ₀ / 2 < infDist z Ωᶜ} with hD
  have hDo : IsOpen D := hΩo.inter (isOpen_lt continuous_const (continuous_infDist_pt Ωᶜ))
  have hDc : Convex ℝ D := (concaveOn_infDist_compl hΩc hΩne).convex_gt (δ₀ / 2)
  have hDΩ : D ⊆ Ω := fun z hz ↦ hz.1
  have hDb : Bornology.IsBounded D := hΩb.subset hDΩ
  have hKcD : closure K ⊆ D := by
    intro z hz
    refine ⟨hKΩ hz, lt_of_lt_of_le (half_lt_self hδ₀) ((le_infDist hΩne).mpr fun y hy ↦ ?_)⟩
    by_contra hlt
    exact hy (hthick (mem_thickening_iff.mpr ⟨z, hz, by rw [dist_comm]; exact not_le.mp hlt⟩))
  have hDball : ∀ z ∈ D, ∀ y, dist y z < δ₀ / 2 → y ∈ Ω := by
    intro z hz y hy
    by_contra hyΩ
    have := infDist_le_dist_of_mem (x := z) (show y ∈ Ωᶜ from hyΩ)
    rw [dist_comm] at hy
    linarith [hz.2]
  set ε := min (min (δ₀ / 4) R) (ρ / 2) with hεdef
  have hε : 0 < ε := lt_min (lt_min (by positivity) hR) (by positivity)
  have hεR : ε ≤ R := (min_le_left _ _).trans (min_le_right _ _)
  have hεδ : ε < δ₀ / 2 := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _))
    (by linarith)
  have hερ : ε < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hΩs : MeasurableSet (ι ⁻¹' Ω) := (hΩo.preimage hιc).measurableSet
  have hDslice : ∀ z ∈ D, coordSq (Fin.last m) z ≤ ε ^ 2 → initCoords z ∈ ι ⁻¹' Ω ∧
      initCoords z ∈ ι ⁻¹' U ∧ Real.exp (-ϕ z) ≤ 2 * Real.exp (-ϕ (ι (initCoords z))) := by
    intro z hz hqz
    have hlast : ‖z (Fin.last m)‖ ≤ ε := le_of_pow_le_pow_left₀ two_ne_zero hε.le hqz
    have hd : dist (ι (initCoords z)) z ≤ ε := by
      rw [dist_comm, hι, dist_hyperplaneEmbedding_initCoords]; exact hlast
    have hyΩ : ι (initCoords z) ∈ Ω := hDball z hz _ (lt_of_le_of_lt hd hεδ)
    refine ⟨hyΩ, hΩU (subset_closure hyΩ), ?_⟩
    have h1 := hρϕ z (subset_closure (hDΩ hz)) _ (subset_closure hyΩ)
      (by rw [dist_comm]; exact lt_of_le_of_lt hd hερ)
    rw [Real.dist_eq] at h1
    have h2 : -ϕ z ≤ -ϕ (ι (initCoords z)) + Real.log 2 := by
      linarith [neg_abs_le (ϕ z - ϕ (ι (initCoords z)))]
    calc Real.exp (-ϕ z) ≤ Real.exp (-ϕ (ι (initCoords z)) + Real.log 2) :=
          Real.exp_le_exp.mpr h2
      _ = 2 * Real.exp (-ϕ (ι (initCoords z))) := by
          rw [Real.exp_add, Real.exp_log two_pos]; ring
  have hMf' : ∀ z ∈ D, coordSq (Fin.last m) z ≤ ε ^ 2 → ‖f (initCoords z)‖ ≤ Mf :=
    fun z hz hqz ↦ hMf _ (subset_closure (hDslice z hz hqz).1)
  have hBϕ' : ∀ z ∈ D, -Bϕ ≤ ϕ z := by
    intro z hz
    have := hBϕ z (subset_closure (hDΩ hz))
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (ϕ z)]
  have hDU : D ⊆ U := hDΩ.trans (subset_closure.trans hΩU)
  have hϕD : ContDiffOn ℝ ∞ ϕ D := hϕU.mono hDU
  have hϕL : ∀ x ∈ D, ∀ ξ, 0 ≤ leviForm ϕ x ξ := by
    intro x hx ξ
    let Uo : TopologicalSpace.Opens (ComplexModel (m + 1)) := ⟨U, hUo⟩
    have h0 := leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (U := Uo) hφs hφpsh (hDU hx) ξ
    have h2 : ContDiffAt ℝ 2 φ x :=
      ((hφs x (hDU hx)).contDiffAt (hUo.mem_nhds (hDU hx))).of_le
        (WithTop.coe_le_coe.mpr le_top)
    have h3 := leviForm_smul h2 c ξ
    change 0 ≤ leviForm (c • φ) x ξ
    rw [h3]
    exact mul_nonneg hc.le h0
  have hgm : AEMeasurable (fun w ↦ ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-ϕ (ι w))))
      (volume.restrict (ι ⁻¹' Ω)) := by
    refine (ENNReal.continuous_ofReal.comp_continuousOn ?_).aemeasurable hΩs
    refine ((hf.continuousOn.mono (preimage_mono (subset_closure.trans hΩU))).norm.pow 2).mul ?_
    exact ((hϕU.continuousOn.comp hιc.continuousOn fun w hw ↦ hΩU (subset_closure hw)).neg).rexp
  obtain ⟨F, hF, hFext, hFb⟩ := exists_chen_extension hH hR hε hεR hDo hDc hDb
    (fun z hz ↦ hΩR z (hDΩ hz)) hϕD hϕL hBϕ' (hUo.preimage hιc) hf hΩs hDslice hMf' hMχ hgm
    hS hKo subset_closure hKc hKcD
  exact ⟨F, hF, hFext, hFb⟩

/-- **The regular Ohsawa--Takegoshi extension property from Hörmander's estimate**, for the
default measurable structures. -/
theorem regularHyperplaneExtension_of_hormander (hH : HormanderL2Estimate (m + 1)) {R : ℝ}
    (hR : 0 < R) {Mχ : ℝ} (hMχ : ∀ x, |deriv chenCutoff x| ≤ Mχ) :
    RegularHyperplaneExtension m R (chenConstant m R Mχ) := by
  intro Ω hΩo hΩc hΩb hΩR U hUo hΩU φ hφs hφpsh c hc f hf
  set ι := hyperplaneEmbedding m with hι
  set S' := ∫⁻ w in ι ⁻¹' Ω, ENNReal.ofReal (‖f w‖ ^ 2 * Real.exp (-(c * φ (ι w)))) with hS'
  have hSeq : ∫⁻ w in ι ⁻¹' Ω, multiplierDensity (fun w ↦ (φ (ι w) : EReal)) c f w = S' := by
    refine lintegral_congr fun w ↦ ?_
    simp only [multiplierDensity, multiplierWeight_coe]
    rw [ENNReal.ofReal_mul (sq_nonneg _)]
  have hιc : Continuous ι := continuous_hyperplaneEmbedding m
  have hS : S' ≠ ⊤ := by
    have hclΩ : IsCompact (closure Ω) := hΩb.isCompact_closure
    have hsl : IsCompact (ι ⁻¹' closure Ω) := by
      refine Metric.isCompact_of_isClosed_isBounded (isClosed_closure.preimage hιc) ?_
      obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ComplexModel (m + 1))).mp
        hΩb.closure
      refine (Metric.isBounded_iff_subset_closedBall (0 : ComplexModel m)).mpr
        ⟨r, fun w hw ↦ ?_⟩
      have := hr hw
      rw [mem_closedBall, dist_zero_right, hι, norm_hyperplaneEmbedding] at this
      rwa [mem_closedBall, dist_zero_right]
    obtain ⟨Mf, hMf⟩ := hsl.exists_bound_of_continuousOn
      (hf.continuousOn.mono (preimage_mono hΩU))
    obtain ⟨Bφ, hBφ⟩ := hclΩ.exists_bound_of_continuousOn (hφs.continuousOn.mono hΩU)
    have hbdd : Bornology.IsBounded (ι ⁻¹' Ω) :=
      hsl.isBounded.subset (preimage_mono subset_closure)
    have hle : S' ≤ ∫⁻ w in ι ⁻¹' Ω, ENNReal.ofReal (Mf ^ 2 * Real.exp (c * Bφ)) := by
      refine setLIntegral_mono' ((hΩo.preimage hιc).measurableSet) fun w hw ↦ ?_
      refine ENNReal.ofReal_le_ofReal (mul_le_mul ?_ ?_ (Real.exp_pos _).le ?_)
      · exact pow_le_pow_left₀ (norm_nonneg _) (hMf w (subset_closure hw)) 2
      · refine Real.exp_le_exp.mpr ?_
        have h1 := hBφ (ι w) (subset_closure hw)
        rw [Real.norm_eq_abs] at h1
        nlinarith [neg_abs_le (φ (ι w))]
      · exact (norm_nonneg _).trans (hMf w (subset_closure hw)) |> fun h ↦ by positivity
    refine ne_top_of_le_ne_top ?_ hle
    rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hbdd.measure_lt_top.ne
  obtain ⟨Kseq, hKo, hKc, hKb, hKcl, hKΩ, hKU⟩ := exists_bounded_convex_exhaustion hΩo hΩc
  have hpiece := fun k ↦ exists_extension_on_piece hH hR hMχ hΩo hΩc hΩb hΩR hUo hΩU hφs hφpsh
    hc hf hS (hKo k) (hKb k) ((hKcl k).trans (hKΩ (k + 1)))
  choose F hFd hFext hFb using hpiece
  have hKmono : Monotone Kseq := monotone_nat_of_le_succ fun k ↦ subset_closure.trans (hKcl k)
  have hφΩ : ContinuousOn φ Ω := hφs.continuousOn.mono (subset_closure.trans hΩU)
  obtain ⟨G, hG, hGext, hGint⟩ := exists_differentiableOn_extension_of_weighted_bounds
    (ι := ι) (g := f) (U := Kseq) (w := fun _ z ↦ ENNReal.ofReal (Real.exp (-(c * φ z))))
    hKo hKmono (fun _ _ ↦ monotone_const)
    (fun _ ↦ by
      rw [hKU]
      exact (ENNReal.continuous_ofReal.comp_continuousOn
        ((continuousOn_const.mul hφΩ).neg.rexp)).aemeasurable hΩo.measurableSet)
    (fun x hx ↦ by
      rw [hKU] at hx
      have hcont : ContinuousAt φ x :=
        hφs.continuousOn.continuousAt (hUo.mem_nhds (hΩU (subset_closure hx)))
      obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
      refine ⟨r, hr, Real.exp (-(c * (φ x + 1))), Real.exp_pos _, fun y hy ↦ ?_⟩
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have h1 := hball (mem_ball.mp hy)
      rw [Real.dist_eq] at h1
      have h2 : φ y ≤ φ x + 1 := by linarith [le_abs_self (φ y - φ x)]
      nlinarith)
    hFd (fun i a ha ↦ hFext i a ha) ENNReal.ofReal_ne_top hFb
  simp only [hKU, iSup_const] at hG hGext hGint
  refine ⟨G, hG, fun w hw ↦ hGext w hw, ?_⟩
  rw [hSeq]
  calc ∫⁻ z in Ω, multiplierDensity (fun z ↦ (φ z : EReal)) c G z
      = ∫⁻ z in Ω, ENNReal.ofReal (‖G z‖ ^ 2) * ENNReal.ofReal (Real.exp (-(c * φ z))) := by
        simp only [multiplierDensity, multiplierWeight_coe]
    _ ≤ ENNReal.ofReal (chenConstant m R Mχ * S'.toReal) := hGint
    _ = ENNReal.ofReal (chenConstant m R Mχ) * S' := by
        rw [ENNReal.ofReal_mul (chenConstant_pos hR Mχ).le, ENNReal.ofReal_toReal hS]

/-- The same, for arbitrary Borel measurable structures. -/
theorem regularHyperplaneExtension_of_hormander_of_borelSpace
    [mA : MeasurableSpace (ComplexModel m)] [hA : BorelSpace (ComplexModel m)]
    [mB : MeasurableSpace (ComplexModel (m + 1))] [hB : BorelSpace (ComplexModel (m + 1))]
    (hH : HormanderL2Estimate (m + 1)) {R : ℝ} (hR : 0 < R) {Mχ : ℝ}
    (hMχ : ∀ x, |deriv chenCutoff x| ≤ Mχ) :
    RegularHyperplaneExtension m R (chenConstant m R Mχ) := by
  have e1 : mA = WithLp.measurableSpace 2 (Fin m → ℂ) :=
    hA.measurable_eq.trans (@BorelSpace.measurable_eq (ComplexModel m) _
      (WithLp.measurableSpace 2 (Fin m → ℂ)) inferInstance).symm
  have e2 : mB = WithLp.measurableSpace 2 (Fin (m + 1) → ℂ) :=
    hB.measurable_eq.trans (@BorelSpace.measurable_eq (ComplexModel (m + 1)) _
      (WithLp.measurableSpace 2 (Fin (m + 1) → ℂ)) inferInstance).symm
  subst e1 e2
  exact regularHyperplaneExtension_of_hormander hH hR hMχ

end

end Hironaka.OTChen

namespace Hironaka

open OTChen

/-- **The regular Ohsawa--Takegoshi theorem from Hörmander's `L²` estimate** (after
B.-Y. Chen, arXiv:1105.2430).  The constant is `(4π + 153600 π M²) R² k_m`. -/
theorem ohsawaTakegoshiHyperplaneRegular_of_hormander
    (hH : ∀ n, Hormander.HormanderL2Estimate n) : OhsawaTakegoshiHyperplaneRegular := by
  obtain ⟨Mχ, -, hMχ⟩ := exists_abs_deriv_chenCutoff_le
  intro m
  let _ : MeasurableSpace (Hironaka.ComplexModel m) := borel _
  have _ : BorelSpace (Hironaka.ComplexModel m) := ⟨rfl⟩
  let _ : MeasurableSpace (Hironaka.ComplexModel (m + 1)) := borel _
  have _ : BorelSpace (Hironaka.ComplexModel (m + 1)) := ⟨rfl⟩
  intro R hR
  exact ⟨chenConstant m R Mχ, chenConstant_pos hR Mχ,
    regularHyperplaneExtension_of_hormander_of_borelSpace (hH (m + 1)) hR hMχ⟩

end Hironaka
