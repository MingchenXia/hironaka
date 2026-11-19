import Hironaka.Analytic.SingularLocus
import Hironaka.Analytic.PshLogExponentBound

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Transport between a manifold and its preferred chart, for Lelong numbers

`Hironaka.lelongNumber u x` is defined as the supremum of the exponents `γ ≥ 0`
admitting a bound `u ≤ γ log‖· − x‖ + O(1)` on a punctured neighbourhood of `x`, computed in the
chart `complexChartAt x`.  Every consumer of that definition has to move between the manifold
and the chart in the same four ways, and this file names them once:

* the two directions of the punctured-neighbourhood transport
  (`eventually_mem_chart_ball`, `exists_chart_radius_of_eventually`);
* the local plurisubharmonic model of a quasi-plurisubharmonic function, with ONE constant
  bounding the difference from the chart representative in both directions
  (`exists_chart_psh_comparison`);
* the two faces of `lelongNumber` as a supremum of admissible exponents
  (`ofReal_le_lelongNumber`, `lelongNumber_le_ofReal`), and the degenerate case in which every
  exponent is admissible (`lelongNumber_eq_top_of_eventually_bot`).

Factored out of `Hironaka.LelongNumberSubadditivity` in answer to I-0285, which found the same
blocks written inline in `Hironaka.LelongNumberFiniteness` and `Hironaka.BlowupNonKahlerLocus`.

No module in the root import closure imports this file.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace Hironaka.LelongNumberChartTransport


noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-! ### The two degenerate cases -/

/-- A potential which is identically `⊥` on a punctured neighbourhood admits every logarithmic
exponent, so its Lelong number is `⊤`.  This covers both hypotheses the target omits: dimension
`0`, where the punctured-neighbourhood filter is `⊥`, and a germ that really is identically
`⊥`. -/
theorem lelongNumber_eq_top_of_eventually_bot {u : M → EReal} {x : M}
    (h : ∀ᶠ y in 𝓝[≠] x, u y = ⊥) : lelongNumber (n := n) u x = ⊤ := by
  rw [eq_top_iff, ← ENNReal.iSup_natCast]
  refine iSup_le fun k => ?_
  unfold lelongNumber
  refine le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
      u y ≤ (((γ : ℝ) * Real.log
        ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
          EReal)) => (γ : ℝ≥0∞)) (k : ℝ≥0)
    ⟨0, h.mono fun y hy => by rw [hy]; exact bot_le⟩ ?_
  simp

/-- In dimension `0` the punctured neighbourhoods of a point are empty. -/
theorem nhdsWithin_ne_eq_bot_of_dim_eq_zero (hn : n = 0) (x : M) : 𝓝[≠] x = ⊥ := by
  subst hn
  have hsub : (chartAt (ComplexModel 0) x).source ⊆ {x} := fun y hy =>
    (chartAt (ComplexModel 0) x).injOn hy (mem_chart_source _ x) (Subsingleton.elim _ _)
  rw [← empty_mem_iff_bot, mem_nhdsWithin]
  exact ⟨_, (chartAt (ComplexModel 0) x).open_source, mem_chart_source _ x,
    fun y hy => absurd (hsub hy.1) hy.2⟩

/-! ### Transport between the manifold and the preferred chart -/

/-- A punctured neighbourhood of `x` in `M` contains the preimage of a punctured ball of the
preferred chart. -/
theorem eventually_mem_chart_ball {x : M} {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ᶠ y in 𝓝[≠] x, y ∈ (complexChartAt (n := n) x).val.source ∧
      0 < ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ ∧
      ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ < ρ := by
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  set p : ComplexModel n := e.val x with hp
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hopen : IsOpen (e.val.source ∩ e.val ⁻¹' ball p ρ) :=
    e.val.isOpen_inter_preimage isOpen_ball
  have hx : x ∈ e.val.source ∩ e.val ⁻¹' ball p ρ := by
    refine ⟨hxs, ?_⟩
    show e.val x ∈ ball p ρ
    rw [← hp]
    exact mem_ball_self hρ
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hopen.mem_nhds hx] with y hy hyx
  have hyne : y ≠ x := hyx
  refine ⟨hy.1, ?_, ?_⟩
  · rw [norm_pos_iff, sub_ne_zero]
    exact fun hEq => hyne (e.val.injOn hy.1 hxs hEq)
  · have h2 : e.val y ∈ ball p ρ := hy.2
    rwa [mem_ball, dist_eq_norm] at h2

/-- Conversely, a property holding on a punctured neighbourhood of `x` holds at every point of
the chart coming from a small punctured ball. -/
theorem exists_chart_radius_of_eventually {x : M} {Φ : M → Prop}
    (hΦ : ∀ᶠ y in 𝓝[≠] x, Φ y) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ComplexModel n,
      0 < ‖z - (complexChartAt (n := n) x).val x‖ →
      ‖z - (complexChartAt (n := n) x).val x‖ < ρ →
      z ∈ (complexChartAt (n := n) x).val.target ∧
        Φ ((complexChartAt (n := n) x).val.symm z) := by
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  set p : ComplexModel n := e.val x with hp
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hptarget : p ∈ e.val.target := e.val.map_source hxs
  obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp hΦ)
  have hTopen : IsOpen (e.val.target ∩ e.val.symm ⁻¹' V) :=
    e.val.isOpen_inter_preimage_symm hVopen
  have hpT : p ∈ e.val.target ∩ e.val.symm ⁻¹' V := by
    refine ⟨hptarget, ?_⟩
    show e.val.symm p ∈ V
    rw [hp, e.val.left_inv hxs]
    exact hxV
  obtain ⟨ρ, hρpos, hρsub⟩ := Metric.isOpen_iff.mp hTopen p hpT
  refine ⟨ρ, hρpos, fun z hz0 hzρ => ?_⟩
  have hzball : z ∈ ball p ρ := mem_ball.mpr (by rwa [dist_eq_norm])
  obtain ⟨hztarget, hzV⟩ := hρsub hzball
  refine ⟨hztarget, hVsub hzV ?_⟩
  intro hzx
  have : z = p := by rw [hp, ← hzx, e.val.right_inv hztarget]
  rw [this] at hz0
  simp at hz0

/-! ### The local plurisubharmonic model of a quasi-psh function -/

/-- The data a quasi-plurisubharmonic function leaves in the preferred chart at `x`: a radius, a
plurisubharmonic model `P`, and one constant bounding the difference between `P` and the chart
representative in both directions. -/
theorem exists_chart_psh_comparison {u : M → EReal}
    (hu : ManifoldQuasiPlurisubharmonic (n := n) u) (x : M) :
    ∃ (R : ℝ) (P : ComplexModel n → EReal) (Mh : ℝ), 0 < R ∧
      ball ((complexChartAt (n := n) x).val x) R ⊆
        (complexChartAt (n := n) x).val.target ∧
      PlurisubharmonicOn P (ball ((complexChartAt (n := n) x).val x) R) ∧
      ∀ z ∈ ball ((complexChartAt (n := n) x).val x) R,
        chartFunction u (complexChartAt (n := n) x) z ≤ P z + (Mh : EReal) ∧
          P z ≤ chartFunction u (complexChartAt (n := n) x) z + (Mh : EReal) := by
  classical
  set e : ComplexChart n M := complexChartAt (n := n) x with he
  set p : ComplexModel n := e.val x with hp
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  have hptarget : p ∈ e.val.target := e.val.map_source hxs
  obtain ⟨P, hreal, hP, hsmooth, heq⟩ := hu e p hptarget
  obtain ⟨W, hWopen, hpW, hdisc⟩ := hP
  have hnbhd : {z : ComplexModel n | chartFunction u e z = P z + (hreal z : EReal)} ∩
      ({z | ContDiffAt ℝ ∞ hreal z} ∩ (W ∩ e.val.target)) ∈ 𝓝 p := by
    filter_upwards [heq, hsmooth, hWopen.mem_nhds hpW, e.val.open_target.mem_nhds hptarget]
      with z h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨R₀, hR₀pos, hR₀sub⟩ := Metric.mem_nhds_iff.mp hnbhd
  have hhalf : closedBall p (R₀ / 2) ⊆ ball p R₀ := fun z hz =>
    mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hz) (by linarith))
  have hcont : ContinuousOn hreal (closedBall p (R₀ / 2)) := by
    intro z hz
    have hcz : ContDiffAt ℝ ∞ hreal z := (hR₀sub (hhalf hz)).2.1
    exact hcz.continuousAt.continuousWithinAt
  obtain ⟨Mh, hMh⟩ := (isCompact_closedBall p (R₀ / 2)).exists_bound_of_continuousOn hcont
  have hsub : ball p (R₀ / 2) ⊆ ball p R₀ :=
    ball_subset_ball (by linarith)
  refine ⟨R₀ / 2, P, Mh, by linarith, ?_, ?_, ?_⟩
  · exact hsub.trans fun z hz => (hR₀sub hz).2.2.2
  · exact ((hdisc.mono (hsub.trans fun z hz => (hR₀sub hz).2.2.1)).plurisubharmonicOn isOpen_ball)
  · intro z hz
    have hzc : z ∈ closedBall p (R₀ / 2) := ball_subset_closedBall hz
    have hsplit : chartFunction u e z = P z + (hreal z : EReal) := (hR₀sub (hsub hz)).1
    have habs := hMh z hzc
    rw [Real.norm_eq_abs] at habs
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    constructor
    · rw [hsplit]
      exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hhi)
    · rw [hsplit]
      calc P z = P z + (0 : EReal) := (add_zero _).symm
        _ ≤ P z + (((hreal z + Mh : ℝ)) : EReal) :=
            add_le_add le_rfl (by exact_mod_cast (by linarith : (0:ℝ) ≤ hreal z + Mh))
        _ = P z + (hreal z : EReal) + (Mh : EReal) := by
            rw [EReal.coe_add, add_assoc]

/-- The chart representative read back at a point of the chart source. -/
theorem chartFunction_apply_chart {u : M → EReal} {e : ComplexChart n M} {y : M}
    (hy : y ∈ e.val.source) : chartFunction u e (e.val y) = u y := by
  show u (e.val.symm (e.val y)) = u y
  rw [e.val.left_inv hy]

/-! ### The Lelong number as a supremum of admissible exponents -/

/-- An admissible logarithmic exponent is a lower bound for the Lelong number. -/
theorem ofReal_le_lelongNumber {u : M → EReal} {x : M} {s C : ℝ} (hs : 0 ≤ s)
    (h : ∀ᶠ y in 𝓝[≠] x, u y ≤ ((s * Real.log
      ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
        EReal)) :
    ENNReal.ofReal s ≤ lelongNumber (n := n) u x := by
  rw [ENNReal.ofReal_eq_coe_nnreal hs]
  unfold lelongNumber
  exact le_iSup₂_of_le (f := fun (γ : ℝ≥0) (_ : ∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
    u y ≤ (((γ : ℝ) * Real.log
      ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
        EReal)) => (γ : ℝ≥0∞)) ⟨s, hs⟩ ⟨C, h⟩ le_rfl

/-- A uniform bound on the admissible exponents bounds the Lelong number. -/
theorem lelongNumber_le_ofReal {u : M → EReal} {x : M} {s : ℝ}
    (h : ∀ γ : ℝ≥0, (∃ C : ℝ, ∀ᶠ y in 𝓝[≠] x,
        u y ≤ (((γ : ℝ) * Real.log
          ‖(complexChartAt (n := n) x).val y - (complexChartAt (n := n) x).val x‖ + C : ℝ) :
            EReal)) → (γ : ℝ) ≤ s) :
    lelongNumber (n := n) u x ≤ ENNReal.ofReal s := by
  unfold lelongNumber
  refine iSup₂_le fun γ hγ => ?_
  calc (γ : ℝ≥0∞) = ENNReal.ofReal (γ : ℝ) := ENNReal.ofReal_coe_nnreal.symm
    _ ≤ ENNReal.ofReal s := ENNReal.ofReal_le_ofReal (h γ hγ)


end

end Hironaka.LelongNumberChartTransport
