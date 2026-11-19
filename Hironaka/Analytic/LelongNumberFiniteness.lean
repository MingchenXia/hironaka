import Hironaka.Analytic.SingularLocus
import Hironaka.Analytic.PshLogExponentBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Finiteness of Lelong numbers

Source: Demailly, *Complex analytic and differential geometry*, III.5.

`Hironaka.lelongNumber u x` is the supremum of the exponents `γ ≥ 0` admitting
a bound `u ≤ γ log‖· - x‖ + O(1)` on a punctured neighbourhood of `x`, computed in the
preferred chart.  This file transports `Hironaka.PshLogExponentBound` from a plurisubharmonic
germ on a ball of `ComplexModel n` to a quasi-plurisubharmonic function on a manifold, and
concludes that the supremum is finite.

Both hypotheses of the conclusion are used exactly once and neither can be dropped:

* `0 < n` produces a point of the chart at positive distance from the centre — in dimension `0`
  the punctured-neighbourhood filter is `⊥`, every exponent is admissible, and the Lelong
  number really is `⊤`;
* `LocallyNondegenerate` produces a point near that one where the potential is finite — the
  identically `⊥` germ satisfies `ManifoldQuasiPlurisubharmonic` and again has Lelong number `⊤`.

No module in the root import closure imports this file.
-/

open Set Filter Metric
open scoped Topology ENNReal NNReal ContDiff

namespace Hironaka.LelongNumberFiniteness

open Hironaka.PshLogExponentBound

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A uniform bound for the admissible exponents at a point.**  The bound does not depend on
the exponent's own punctured neighbourhood, so it bounds the supremum. -/
theorem exists_bound_forall_admissible_exponent (hn : 0 < n) {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hnd : LocallyNondegenerate u) (x : M) :
    ∃ s : ℝ, ∀ γ : ℝ≥0, (∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
        u y ≤ (((γ : ℝ) * Real.log
          ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
            EReal)) → (γ : ℝ) ≤ s := by
  classical
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  set p : ComplexModel n := e.val x with hp
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hptarget : p ∈ e.val.target := e.val.map_source hxs
  -- the quasi-psh decomposition of the chart representative at `p`
  obtain ⟨P, hreal, hP, hsmooth, heq⟩ := hu e p hptarget
  obtain ⟨W, hWopen, hpW, hdisc⟩ := hP
  have hnbhd : {z : ComplexModel n | chartFunction u e z = P z + (hreal z : EReal)} ∩
      ({z | ContDiffAt ℝ ∞ hreal z} ∩ (W ∩ e.val.target)) ∈ 𝓝 p := by
    filter_upwards [heq, hsmooth, hWopen.mem_nhds hpW, e.val.open_target.mem_nhds hptarget]
      with z h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨R, hRpos, hRsub⟩ := Metric.mem_nhds_iff.mp hnbhd
  have hRW : ball p R ⊆ W := fun z hz => (hRsub hz).2.2.1
  have hRtarget : ball p R ⊆ e.val.target := fun z hz => (hRsub hz).2.2.2
  have hRsplit : ∀ z ∈ ball p R, chartFunction u e z = P z + (hreal z : EReal) :=
    fun z hz => (hRsub hz).1
  have hPball : PlurisubharmonicOn P (ball p R) :=
    ((hdisc.mono hRW).plurisubharmonicOn isOpen_ball)
  -- `hreal` is continuous, hence bounded, on the closed half-ball
  have hhalf : closedBall p (R / 2) ⊆ ball p R := fun z hz =>
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  have hcont : ContinuousOn hreal (closedBall p (R / 2)) := by
    intro z hz
    have hcz : ContDiffAt ℝ ∞ hreal z := (hRsub (hhalf hz)).2.1
    exact hcz.continuousAt.continuousWithinAt
  obtain ⟨Mh, hMh⟩ :=
    (isCompact_closedBall p (R / 2)).exists_bound_of_continuousOn hcont
  -- a point of the chart at positive distance from `p`, using `0 < n`
  set w : ComplexModel n := EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℂ) with hw
  have hwnorm : ‖w‖ = 1 := by simp [hw]
  set q : ComplexModel n := p + ((R / 4 : ℝ) : ℂ) • w with hq
  have hqp : ‖q - p‖ = R / 4 := by
    rw [hq, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ R / 4), hwnorm, mul_one]
  have hOsub : ball q (R / 8) ⊆ ball p R := by
    intro z hz
    have h1 : ‖z - q‖ < R / 8 := by rwa [mem_ball, dist_eq_norm] at hz
    refine mem_ball.mpr ?_
    rw [dist_eq_norm]
    calc ‖z - p‖ = ‖(z - q) + (q - p)‖ := by rw [sub_add_sub_cancel]
      _ ≤ ‖z - q‖ + ‖q - p‖ := norm_add_le _ _
      _ < R / 8 + R / 4 := by rw [hqp]; linarith
      _ < R := by linarith
  -- local nondegeneracy supplies a non-pole point of the small ball around `q`
  have hR8 : (0:ℝ) < R / 8 := by linarith
  have hqtarget : q ∈ e.val.target := (hOsub.trans hRtarget) (mem_ball_self hR8)
  have hVopen' : IsOpen (e.val.source ∩ e.val ⁻¹' ball q (R / 8)) :=
    e.val.isOpen_inter_preimage isOpen_ball
  have hqV : e.val.symm q ∈ e.val.source ∩ e.val ⁻¹' ball q (R / 8) := by
    refine ⟨e.val.symm.map_source hqtarget, ?_⟩
    show e.val (e.val.symm q) ∈ ball q (R / 8)
    rw [e.val.right_inv hqtarget]
    exact mem_ball_self hR8
  obtain ⟨yM, hyM, hyMbot⟩ := hnd (e.val.symm q) _ hVopen' hqV
  set y₀ : ComplexModel n := e.val yM with hy₀def
  have hy₀O : y₀ ∈ ball q (R / 8) := hyM.2
  have hy₀bot : chartFunction u e y₀ ≠ ⊥ := by
    simpa [chartFunction, hy₀def, e.val.left_inv hyM.1] using hyMbot
  have hy₀ball : y₀ ∈ ball p R := hOsub hy₀O
  have hy₀norm : ‖y₀ - p‖ < R := by rwa [mem_ball, dist_eq_norm] at hy₀ball
  have hy₀ne : y₀ ≠ p := by
    intro hzero
    have h1 : ‖y₀ - q‖ < R / 8 := by rw [mem_ball, dist_eq_norm] at hy₀O; exact hy₀O
    rw [hzero] at h1
    rw [show ‖p - q‖ = ‖q - p‖ from norm_sub_rev p q, hqp] at h1
    linarith
  have hPy₀ : P y₀ ≠ ⊥ := by
    intro hbot
    exact hy₀bot (by rw [hRsplit y₀ hy₀ball, hbot, EReal.bot_add])
  obtain ⟨s, hs⟩ := exists_bound_forall_log_exponent hPball hy₀norm hy₀ne hPy₀
  refine ⟨s, ?_⟩
  rintro γ ⟨C, hC⟩
  -- transport the admissible bound into the chart
  obtain ⟨V, hVsub, hVopen, hxV⟩ :=
    mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hC)
  have hTopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) :=
    e.val.isOpen_inter_preimage_symm hVopen
  have hpT : p ∈ e.val.target ∩ e.val.symm ⁻¹' V := by
    refine ⟨hptarget, ?_⟩
    show e.val.symm p ∈ V
    rw [hp, e.val.left_inv hxs]
    exact hxV
  obtain ⟨ρ₀, hρ₀pos, hρ₀sub⟩ := Metric.isOpen_iff.mp hTopen p hpT
  refine hs (γ : ℝ) (C + Mh) (min ρ₀ (R / 2)) (lt_min hρ₀pos (by linarith)) ?_
  intro z hz0 hzρ
  have hzρ₀ : ‖z - p‖ < ρ₀ := lt_of_lt_of_le hzρ (min_le_left _ _)
  have hzhalf : ‖z - p‖ < R / 2 := lt_of_lt_of_le hzρ (min_le_right _ _)
  have hzball : z ∈ ball p ρ₀ := mem_ball.mpr (by rwa [dist_eq_norm])
  obtain ⟨hztarget, hzV⟩ := hρ₀sub hzball
  have hzR : z ∈ ball p R := mem_ball.mpr (by rw [dist_eq_norm]; linarith)
  have hzhalfball : z ∈ closedBall p (R / 2) :=
    mem_closedBall.mpr (by rw [dist_eq_norm]; linarith)
  -- the point of `M` corresponding to `z`
  have hyne : e.val.symm z ≠ x := by
    intro hzx
    have : z = p := by
      rw [hp, ← hzx, e.val.right_inv hztarget]
    rw [this] at hz0
    simp at hz0
  have hchartz : e.val (e.val.symm z) = z := e.val.right_inv hztarget
  have hbound : chartFunction u e z ≤
      (((γ : ℝ) * Real.log ‖z - p‖ + C : ℝ) : EReal) := by
    have := hVsub hzV hyne
    rw [hchartz] at this
    exact this
  -- subtract the smooth part
  have hsplit := hRsplit z hzR
  have hMhz : -hreal z ≤ Mh := by
    have := hMh z hzhalfball
    rw [Real.norm_eq_abs] at this
    cases abs_le.mp this with
    | intro h1 h2 => linarith
  have hfinal : P z ≤ (((γ : ℝ) * Real.log ‖z - p‖ + (C + Mh) : ℝ) : EReal) := by
    have hle : P z + (hreal z : EReal) ≤ (((γ : ℝ) * Real.log ‖z - p‖ + C : ℝ) : EReal) := by
      rw [← hsplit]; exact hbound
    rcases eq_or_ne (P z) ⊥ with hbot | hbot
    · rw [hbot]; exact bot_le
    have htop : P z ≠ ⊤ := (hPball z hzR).ne_top
    have hvz : P z = (((P z).toReal : ℝ) : EReal) := (EReal.coe_toReal htop hbot).symm
    rw [hvz] at hle ⊢
    rw [← EReal.coe_add] at hle
    have hreal' : (P z).toReal + hreal z ≤ (γ : ℝ) * Real.log ‖z - p‖ + C :=
      EReal.coe_le_coe_iff.mp hle
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  exact hfinal

/-- **Lelong numbers are finite** (Demailly, CADG III.5). -/
theorem lelongNumber_ne_top_of_quasiPsh (hn : 0 < n) {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hnd : LocallyNondegenerate u) (x : M) :
    lelongNumber (n := n) u x ≠ ⊤ := by
  obtain ⟨s, hs⟩ := exists_bound_forall_admissible_exponent hn hu hnd x
  have hle : lelongNumber (n := n) u x ≤ ENNReal.ofReal s := by
    unfold lelongNumber
    refine iSup₂_le fun γ hγ => ?_
    have := hs γ hγ
    calc (γ : ℝ≥0∞) = ENNReal.ofReal (γ : ℝ) := by
          rw [ENNReal.ofReal_coe_nnreal]
      _ ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal this
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

end

end Hironaka.LelongNumberFiniteness
