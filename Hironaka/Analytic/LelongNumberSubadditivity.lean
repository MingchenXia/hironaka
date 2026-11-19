import Hironaka.Analytic.LelongNumberChartTransport
import Hironaka.Analytic.PshLocalLelongSubadditive

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-!
# Subadditivity of Lelong numbers

Source: Demailly, *Complex analytic and differential geometry*, III.5.

`Hironaka.PshLocalLelongSubadditive.le_slope_add_of_admissible_sum` is the analytic statement, for
plurisubharmonic `P, Q` on a ball of `ComplexModel n`.  This file transports it to a
quasi-plurisubharmonic pair on a manifold, using the chart dictionary of
`Hironaka.LelongNumberChartTransport`, and concludes `ν(u + v, x) ≤ ν(u, x) + ν(v, x)`.

The target carries neither `0 < n` nor `LocallyNondegenerate`, and both degenerate cases are
genuinely degenerate rather than excluded: in dimension `0` the punctured-neighbourhood filter
is `⊥`, and a potential that is identically `⊥` near `x` admits every exponent.  In both cases
the *right-hand* side is `⊤`, so the inequality holds for the reason that makes the hypotheses
unnecessary, and only the remaining case is analytic.

No module in the root import closure imports this file.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace Hironaka.LelongNumberSubadditivity

open Hironaka.PshBallSup Hironaka.PshBallSupSlope
  Hironaka.PshLocalLelongSubadditive Hironaka.LelongNumberChartTransport

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### Subadditivity -/

/-- **Subadditivity of Lelong numbers** (Demailly, CADG III.5).  Equality holds; only `≤` is
recorded here, because only `≤` is consumed.

Neither `0 < n` nor local nondegeneracy is assumed, and both omissions are genuine: in
dimension `0`, and when one of the two potentials is identically `⊥` near `x`, the
corresponding Lelong number on the RIGHT is already `⊤`. -/
theorem lelongNumber_add_le_of_quasiPsh {u v : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u)
    (hv : ManifoldQuasiPlurisubharmonic (n := n) v) (x : M) :
    lelongNumber (n := n) (fun y => u y + v y) x ≤
      lelongNumber (n := n) u x + lelongNumber (n := n) v x := by
  classical
  -- dimension zero: every punctured neighbourhood is empty, so the right-hand side is `⊤`
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · rw [lelongNumber_eq_top_of_eventually_bot (u := u) (x := x)
      (by rw [nhdsWithin_ne_eq_bot_of_dim_eq_zero hn0 x]; exact Filter.eventually_bot),
      top_add]
    exact le_top
  have : Nontrivial (ComplexModel n) := by
    refine ⟨⟨0, EuclideanSpace.single (⟨0, hn0⟩ : Fin n) (1 : ℂ), ?_⟩⟩
    intro hEq
    have h1 : ‖(EuclideanSpace.single (⟨0, hn0⟩ : Fin n) (1 : ℂ) : ComplexModel n)‖ = 1 := by
      simp
    rw [← hEq] at h1
    simp at h1
  obtain ⟨R₁, P, MP, hR₁, hR₁t, hPpsh, hPcmp⟩ := exists_chart_psh_comparison hu x
  obtain ⟨R₂, Q, MQ, hR₂, hR₂t, hQpsh, hQcmp⟩ := exists_chart_psh_comparison hv x
  have hRpos : 0 < min R₁ R₂ := lt_min hR₁ hR₂
  have hsub₁ : ball ((complexChartAt (n := n) x).val x) (min R₁ R₂) ⊆
      ball ((complexChartAt (n := n) x).val x) R₁ := ball_subset_ball (min_le_left _ _)
  have hsub₂ : ball ((complexChartAt (n := n) x).val x) (min R₁ R₂) ⊆
      ball ((complexChartAt (n := n) x).val x) R₂ := ball_subset_ball (min_le_right _ _)
  have hPpsh' : PlurisubharmonicOn P (ball ((complexChartAt (n := n) x).val x) (min R₁ R₂)) :=
    fun z hz => hPpsh z (hsub₁ hz)
  have hQpsh' : PlurisubharmonicOn Q (ball ((complexChartAt (n := n) x).val x) (min R₁ R₂)) :=
    fun z hz => hQpsh z (hsub₂ hz)
  -- a model identically `⊥` on the ball forces its own Lelong number to be `⊤`
  by_cases hPne : ∃ a ∈ ball ((complexChartAt (n := n) x).val x) (min R₁ R₂), P a ≠ ⊥
  swap
  · simp only [not_exists, not_and, ne_eq, not_not] at hPne
    have hbot : ∀ᶠ y in 𝓝[≠] x, u y = ⊥ := by
      filter_upwards [eventually_mem_chart_ball (n := n) (M := M) (x := x) hRpos] with y hy
      obtain ⟨hysrc, hy0, hyR⟩ := hy
      have hz : (complexChartAt (n := n) x).val y ∈
          ball ((complexChartAt (n := n) x).val x) (min R₁ R₂) :=
        mem_ball.mpr (by rwa [dist_eq_norm])
      have h1 := (hPcmp _ (hsub₁ hz)).1
      rw [hPne _ hz, EReal.bot_add] at h1
      rw [← chartFunction_apply_chart (u := u) hysrc]
      exact le_bot_iff.mp h1
    rw [lelongNumber_eq_top_of_eventually_bot hbot, top_add]
    exact le_top
  by_cases hQne : ∃ a ∈ ball ((complexChartAt (n := n) x).val x) (min R₁ R₂), Q a ≠ ⊥
  swap
  · simp only [not_exists, not_and, ne_eq, not_not] at hQne
    have hbot : ∀ᶠ y in 𝓝[≠] x, v y = ⊥ := by
      filter_upwards [eventually_mem_chart_ball (n := n) (M := M) (x := x) hRpos] with y hy
      obtain ⟨hysrc, hy0, hyR⟩ := hy
      have hz : (complexChartAt (n := n) x).val y ∈
          ball ((complexChartAt (n := n) x).val x) (min R₁ R₂) :=
        mem_ball.mpr (by rwa [dist_eq_norm])
      have h1 := (hQcmp _ (hsub₂ hz)).1
      rw [hQne _ hz, EReal.bot_add] at h1
      rw [← chartFunction_apply_chart (u := v) hysrc]
      exact le_bot_iff.mp h1
    rw [lelongNumber_eq_top_of_eventually_bot hbot, add_top]
    exact le_top
  -- the two ball-supremum slopes
  obtain ⟨sP, hsP0, ⟨CP, ρP, hρP, hPadm⟩, hslP⟩ :=
    exists_ballSup_slope (μ := volume) hRpos hPpsh' hPne
  obtain ⟨sQ, hsQ0, ⟨CQ, ρQ, hρQ, hQadm⟩, hslQ⟩ :=
    exists_ballSup_slope (μ := volume) hRpos hQpsh' hQne
  -- each slope is an admissible exponent for its own potential on the manifold
  have hsPle : ENNReal.ofReal sP ≤ lelongNumber (n := n) u x := by
    refine ofReal_le_lelongNumber (C := CP + MP) hsP0 ?_
    filter_upwards [eventually_mem_chart_ball (n := n) (M := M) (x := x)
      (lt_min hρP hRpos)] with y hy
    obtain ⟨hysrc, hy0, hylt⟩ := hy
    have hz : (complexChartAt (n := n) x).val y ∈
        ball ((complexChartAt (n := n) x).val x) (min R₁ R₂) :=
      mem_ball.mpr (by rw [dist_eq_norm]; exact lt_of_lt_of_le hylt (min_le_right _ _))
    have h1 := hPadm _ hy0 (lt_of_lt_of_le hylt (min_le_left _ _))
    have h2 := (hPcmp _ (hsub₁ hz)).1
    rw [← chartFunction_apply_chart (u := u) hysrc]
    calc chartFunction u (complexChartAt (n := n) x) ((complexChartAt (n := n) x).val y)
        ≤ P ((complexChartAt (n := n) x).val y) + (MP : EReal) := h2
      _ ≤ ((sP * Real.log ‖(complexChartAt (n := n) x).val y -
            (complexChartAt (n := n) x).val x‖ + CP : ℝ) : EReal) + (MP : EReal) :=
          add_le_add h1 le_rfl
      _ = ((sP * Real.log ‖(complexChartAt (n := n) x).val y -
            (complexChartAt (n := n) x).val x‖ + (CP + MP) : ℝ) : EReal) := by
          rw [← EReal.coe_add]
          congr 1
          ring
  have hsQle : ENNReal.ofReal sQ ≤ lelongNumber (n := n) v x := by
    refine ofReal_le_lelongNumber (C := CQ + MQ) hsQ0 ?_
    filter_upwards [eventually_mem_chart_ball (n := n) (M := M) (x := x)
      (lt_min hρQ hRpos)] with y hy
    obtain ⟨hysrc, hy0, hylt⟩ := hy
    have hz : (complexChartAt (n := n) x).val y ∈
        ball ((complexChartAt (n := n) x).val x) (min R₁ R₂) :=
      mem_ball.mpr (by rw [dist_eq_norm]; exact lt_of_lt_of_le hylt (min_le_right _ _))
    have h1 := hQadm _ hy0 (lt_of_lt_of_le hylt (min_le_left _ _))
    have h2 := (hQcmp _ (hsub₂ hz)).1
    rw [← chartFunction_apply_chart (u := v) hysrc]
    calc chartFunction v (complexChartAt (n := n) x) ((complexChartAt (n := n) x).val y)
        ≤ Q ((complexChartAt (n := n) x).val y) + (MQ : EReal) := h2
      _ ≤ ((sQ * Real.log ‖(complexChartAt (n := n) x).val y -
            (complexChartAt (n := n) x).val x‖ + CQ : ℝ) : EReal) + (MQ : EReal) :=
          add_le_add h1 le_rfl
      _ = ((sQ * Real.log ‖(complexChartAt (n := n) x).val y -
            (complexChartAt (n := n) x).val x‖ + (CQ + MQ) : ℝ) : EReal) := by
          rw [← EReal.coe_add]
          congr 1
          ring
  -- every admissible exponent of the sum is bounded by the sum of the slopes
  have hmain : lelongNumber (n := n) (fun y => u y + v y) x ≤ ENNReal.ofReal (sP + sQ) := by
    refine lelongNumber_le_ofReal fun γ hγ => ?_
    obtain ⟨C, hC⟩ := hγ
    obtain ⟨ρ, hρpos, hρ⟩ := exists_chart_radius_of_eventually (n := n) (M := M) hC
    refine le_slope_add_of_admissible_sum (μ := volume) hRpos hPpsh' hQpsh' hPne hQne
      hslP hslQ (γ := (γ : ℝ)) (C := C + MP + MQ) (ρ := min ρ (min R₁ R₂))
      γ.coe_nonneg (lt_min hρpos hRpos) ?_
    intro z hz0 hzρ
    obtain ⟨hztarget, hΦ⟩ := hρ z hz0 (lt_of_lt_of_le hzρ (min_le_left _ _))
    rw [(complexChartAt (n := n) x).val.right_inv hztarget] at hΦ
    have hzball : z ∈ ball ((complexChartAt (n := n) x).val x) (min R₁ R₂) :=
      mem_ball.mpr (by rw [dist_eq_norm]; exact lt_of_lt_of_le hzρ (min_le_right _ _))
    have hP2 := (hPcmp z (hsub₁ hzball)).2
    have hQ2 := (hQcmp z (hsub₂ hzball)).2
    calc P z + Q z
        ≤ (chartFunction u (complexChartAt (n := n) x) z + (MP : EReal)) +
          (chartFunction v (complexChartAt (n := n) x) z + (MQ : EReal)) := add_le_add hP2 hQ2
      _ = (chartFunction u (complexChartAt (n := n) x) z +
            chartFunction v (complexChartAt (n := n) x) z) + ((MP : EReal) + (MQ : EReal)) :=
          add_add_add_comm _ _ _ _
      _ ≤ (((γ : ℝ) * Real.log ‖z - (complexChartAt (n := n) x).val x‖ + C : ℝ) : EReal) +
            ((MP : EReal) + (MQ : EReal)) := add_le_add hΦ le_rfl
      _ = (((γ : ℝ) * Real.log ‖z - (complexChartAt (n := n) x).val x‖ + (C + MP + MQ) : ℝ) :
            EReal) := by
          rw [← EReal.coe_add, ← EReal.coe_add]
          congr 1
          ring
  calc lelongNumber (n := n) (fun y => u y + v y) x
      ≤ ENNReal.ofReal (sP + sQ) := hmain
    _ = ENNReal.ofReal sP + ENNReal.ofReal sQ := ENNReal.ofReal_add hsP0 hsQ0
    _ ≤ lelongNumber (n := n) u x + lelongNumber (n := n) v x := add_le_add hsPle hsQle

end

end Hironaka.LelongNumberSubadditivity
