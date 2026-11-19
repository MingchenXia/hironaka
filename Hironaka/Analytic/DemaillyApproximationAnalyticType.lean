import Hironaka.Analytic.DemaillyApproximationSequence
import Hironaka.Analytic.MultiplierIdealBergmanNadelManifold

set_option autoImplicit false

/-!
# Demailly's approximants have analytic singularities (clause (i), global form)

Clause (i) of Demailly 1992 (`bou02-volume:2.6`) in the global convention
`GlobalAnalyticSingularities.HasAnalyticSingularities`: the explicit approximant
`ψ_k = DemaillyApproximationSequence.seq F ρ ψ E k` (the `M_δ`-glued chart Bergman branches at
level `m = 2^k`, shifted by a constant) is, near every point, `m⁻¹ log ∑ |g_i|² + O(1)` with
`g_i` local generators of the multiplier ideal `𝓘(mψ)`, which is coherent by Nadel's theorem
(`MultiplierIdealBergmanNadelManifold.isCoherent_multiplierIdeal_of_pos`).  The coefficient is
the rational `2^{-k}` and the ideal is `𝓘(2^k ψ)`.

* lower bound: every branch dominates `m⁻¹ log ∑|g_i|² - C` for germs `g_i` of `𝓘(mψ)`
  (`QuantitativeRegularizationFixedCover.FixedChartCover.exists_const_eventually_le_branch`),
  and the glue dominates the branches;
* upper bound: the Bergman kernel of a chart ball is `≤ K ∑_l |h_l|²` near a point for finitely
  many `h_l` of its Bergman space (`BergmanGenerators.exists_uniform_generators`); each
  `h_l ∘ e_j` is a germ of `𝓘(mψ)` (`mem_multiplierIdeal_of_chart`), hence a holomorphic
  combination of the coherence generators (`normSq_le_of_isInSpanAt`); the glue is at most the
  largest active branch plus a constant (`DemaillySymmetricGluing.rglue_le`).

Programme `TN.3.3.DEMPROVE`, clause (i-g).
-/

open Set Filter MeasureTheory Metric
open scoped Topology Manifold ENNReal

namespace Hironaka.DemaillyApproximationAnalyticType

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.GlobalAnalyticSingularities
  BergmanSupWeight BergmanGenerators
  QuantitativeRegularizationChartBranch QuantitativeRegularizationFixedCover
  MultiplierIdealBergmanNadelManifold

/-! ### Charts of the atlas -/

section Charts

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- A function holomorphic near `e y` in the coordinates of an atlas chart `e`, composed with
`e`, is holomorphic near `y`. -/
theorem holomorphicAt_comp_atlas {e : ComplexChart n M} {y : M} (hy : y ∈ e.val.source)
    {W : ComplexModel n → ℂ} (hW : ∀ᶠ z in 𝓝 (e.val y), DifferentiableAt ℂ W z) :
    HolomorphicAt n (fun p => W (e.val p)) y := by
  filter_upwards [e.val.open_source.mem_nhds hy, (e.val.continuousAt hy).eventually hW]
    with p hp hWp
  have hWm : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) W (e.val p) := by
    rw [mdifferentiableAt_iff_differentiableAt]
    exact hWp
  exact hWm.comp p (mdifferentiableAt_atlas (I := 𝓘(ℂ, ComplexModel n)) e.2 hp)

/-- **A germ read in an atlas chart against a corrected weight lies in the multiplier ideal.**
If `G` is `L²` for `e^{-c(φ ∘ e⁻¹ + ρ)}` near `e y`, with `ρ` continuous near `e y`, then
`G ∘ e` is a germ of `𝓘(cφ)` at `y`. -/
theorem mem_multiplierIdeal_of_chart {θ : SmoothRealForm n M 2} {φ : M → EReal}
    (hφ : ThetaPlurisubharmonic θ φ) {c : ℝ} (hc : 0 < c) (e : ComplexChart n M)
    {W : Set (ComplexModel n)} (hW : IsOpen W) {ρ : ComplexModel n → ℝ} (hρ : ContinuousOn ρ W)
    {y : M} (hy : y ∈ e.val.source) (hyW : e.val y ∈ W) {G : ComplexModel n → ℂ}
    (hG : MultiplierIntegrableAt (fun w => chartFunction φ e w + (ρ w : EReal)) c G (e.val y)
      volume) :
    (multiplierIdeal (n := n) c φ).mem y (fun p => G (e.val p)) := by
  obtain ⟨U, hU, hyU, hGU, -⟩ := hG.2
  refine ⟨holomorphicAt_comp_atlas hy (Filter.eventually_of_mem (hU.mem_nhds hyU)
    fun z hz => hGU.differentiableAt (hU.mem_nhds hz)), ?_⟩
  have hmore : MoreSingularAt (fun w => chartFunction φ e w + (ρ w : EReal))
      (chartFunction φ e) (e.val y) := by
    have hcont : ContinuousAt ρ (e.val y) := (hρ _ hyW).continuousAt (hW.mem_nhds hyW)
    refine ⟨ρ (e.val y) + 1, ?_⟩
    filter_upwards [hcont.eventually (gt_mem_nhds (lt_add_one (ρ (e.val y))))] with w hw
    exact add_le_add le_rfl (EReal.coe_le_coe_iff.mpr hw.le)
  have hqu : QuasiPlurisubharmonicAt (chartFunction φ e) (e.val y) :=
    hφ.quasiPlurisubharmonic e (e.val y) (e.val.map_source hy)
  have h1 : MultiplierIntegrableAt (chartFunction φ e) c G (e.val y) volume :=
    multiplierIntegrableAt_of_moreSingularAt hqu hmore hG
  have h2 : MultiplierIntegrableAt (chartFunction φ e) c (fun z => G (e.val (e.val.symm z)))
      (e.val y) volume := by
    refine h1.congr (EventuallyEq.refl _ _) ?_
    filter_upwards [e.val.open_target.mem_nhds (e.val.map_source hy)] with z hz
    rw [e.val.right_inv hz]
  have husc : UpperSemicontinuousOn (chartFunction φ (complexChartAt (n := n) y))
      (ChartWeightedL2.overlapDomain (complexChartAt (n := n) y) e) :=
    (hφ.quasiPlurisubharmonic (complexChartAt (n := n) y)).upperSemicontinuousOn.mono
      fun _ hw => hw.1
  exact ChartWeightedL2.multiplierIntegrableAt_chart (μ := volume)
    (g := fun p => G (e.val p)) (complexChartAt (n := n) y) e (mem_complexChartAt_source y) hy
    husc hc.ne' h2

omit [IsComplexManifold n M] in
/-- A holomorphic combination of finitely many functions is dominated by them near the point:
`|h|² ≤ C ∑ |g_l|²`. -/
theorem exists_normSq_le_of_isInSpanAt {N : ℕ} {g : Fin N → M → ℂ} {x : M} {h : M → ℂ}
    (hh : IsInSpanAt (n := n) (· ∈ range g) x h) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x, ‖h y‖ ^ 2 ≤ C * ∑ l, ‖g l y‖ ^ 2 := by
  obtain ⟨-, N', s, a, hs, ha, he⟩ := hh
  choose l hl using hs
  have hbd : ∀ i, ∀ᶠ y in 𝓝 x, ‖a i y‖ ≤ ‖a i x‖ + 1 := fun i => by
    have hcont : ContinuousAt (a i) x := (ha i).self_of_nhds.continuousAt
    filter_upwards [hcont.norm.eventually (gt_mem_nhds (lt_add_one ‖a i x‖))] with y hy
    exact hy.le
  set A : ℝ := ∑ i, (‖a i x‖ + 1) with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => by positivity
  refine ⟨A ^ 2, ?_⟩
  filter_upwards [he, eventually_all.mpr hbd] with y hy hya
  set T : ℝ := ∑ l, ‖g l y‖ ^ 2 with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hgT : ∀ i, ‖s i y‖ ≤ Real.sqrt T := fun i => by
    rw [← hl i]
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun l => ‖g l y‖ ^ 2) (fun l _ => sq_nonneg _)
      (Finset.mem_univ (l i))
  have hnorm : ‖h y‖ ≤ A * Real.sqrt T := by
    rw [hy, hA, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hya i) (hgT i) (norm_nonneg _) (by positivity)
  calc ‖h y‖ ^ 2 ≤ (A * Real.sqrt T) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = A ^ 2 * T := by rw [mul_pow, Real.sq_sqrt hT0]

end Charts

/-! ### The Bergman kernel of a ball is dominated near a point by finitely many sections -/

section Kernel

variable {d : ℕ}

/-- **Upper bound for the Bergman kernel.**  If the weight `w` is bounded below by `δ > 0` on
`ball z₀ (2R) ⊆ B`, there are finitely many `h_l` in the Bergman unit ball of `ball z₀ (2R)` and
`r, K` with `K_{B,w}(z) ≤ K ∑ |h_l(z)|²` on `ball z₀ r`. -/
theorem exists_bergmanSup_le {B : Set (ComplexModel d)} {w : ComplexModel d → ℝ≥0∞}
    {z₀ : ComplexModel d} {R : ℝ} (hR : 0 < R) (hBR : ball z₀ (2 * R) ⊆ B)
    (hw : AEMeasurable w (volume.restrict (ball z₀ (2 * R)))) {δ : ℝ} (hδ : 0 < δ)
    (hlow : ∀ y ∈ ball z₀ (2 * R), ENNReal.ofReal δ ≤ w y) :
    ∃ (L : ℕ) (h : Fin L → ComplexModel d → ℂ) (r K : ℝ), 0 < r ∧
      (∀ l, h l ∈ bergmanUnitBall z₀ R w) ∧
      ∀ z ∈ ball z₀ r, bergmanSup B w z ≤ ENNReal.ofReal (K * ∑ l, ‖h l z‖ ^ 2) := by
  obtain ⟨L, h, r, K, hr, hhX, hdom⟩ := exists_uniform_generators hR hw hδ hlow
  refine ⟨L, h, r, K, hr, hhX, fun z hz => ?_⟩
  refine iSup₂_le fun f hf => ENNReal.ofReal_le_ofReal (hdom f ⟨hf.1.mono hBR, ?_⟩ z hz)
  exact (lintegral_mono_set hBR).trans hf.2

end Kernel

/-! ### The EReal bookkeeping of the upper bound -/

/-- `m⁻¹ log S - r ≤ m⁻¹ log T + (m⁻¹ log K + Cρ)` from `S ≤ K T` and `-r ≤ Cρ`, in `EReal`, with
`T` presented as `generatorLog`-style `ENNReal.log (ofReal T)`. -/
theorem inv_mul_log_sub_le {S : ℝ≥0∞} {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hS : S ≤ ENNReal.ofReal (K * T)) {μ : ℝ} (hμ : 0 < μ) {r Cρ : ℝ} (hr : -r ≤ Cρ) :
    ((μ : ℝ) : EReal) * ENNReal.log S - (r : EReal) ≤
      ((μ : ℝ) : EReal) * ENNReal.log (ENNReal.ofReal T) +
        ((μ * Real.log K + Cρ : ℝ) : EReal) := by
  by_cases hS0 : S = 0
  · rw [hS0, ENNReal.log_zero, EReal.coe_mul_bot_of_pos hμ, EReal.bot_sub]
    exact bot_le
  have hT0 : 0 < T := by
    rcases hT.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at hS
      exact absurd hS hS0
  have hStop : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hS
  set s : ℝ := S.toReal with hsdef
  have hs : 0 < s := ENNReal.toReal_pos hS0 hStop
  have hSs : S = ENNReal.ofReal s := (ENNReal.ofReal_toReal hStop).symm
  have hsKT : s ≤ K * T := by
    rw [hSs] at hS
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hS
  have hlog : Real.log s ≤ Real.log K + Real.log T := by
    rw [← Real.log_mul hK.ne' hT0.ne']
    exact Real.log_le_log hs hsKT
  rw [hSs, ENNReal.log_ofReal_of_pos hs, ENNReal.log_ofReal_of_pos hT0, ← EReal.coe_mul,
    ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  nlinarith

/-! ### One branch is bounded above by the coherence generators -/

section Branch

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

/-- **Upper bound of a chart Bergman branch by local generators of the multiplier ideal.**  If
the germs `g_i` generate `𝓘(mφ)_x` and `x` lies in the closure of the patch `V_j`, then near `x`
the branch `b_{m,j}` is at most `m⁻¹ log ∑|g_i|² + C`. -/
theorem exists_branch_le (F : FixedChartCover d Z) {ζ : SmoothRealForm d Z 2}
    {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential ζ (F.chart j) (ball (F.center j) (F.potentialRadius j)) (ρ j))
    {φ : Z → EReal} (hφ : ThetaPlurisubharmonic ζ φ) {m : ℕ} (hm : 0 < m) (j : F.t) {x : Z}
    (hx : x ∈ closure (F.cover.V j)) {N : ℕ} {g : Fin N → Z → ℂ}
    (hgx : ∀ h, (multiplierIdeal (n := d) (m : ℝ) φ).mem x h →
      IsInSpanAt (n := d) (· ∈ range g) x h) :
    ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      F.branch ρ φ m j y ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y + (C : EReal) := by
  classical
  set e := F.chart j with hedef
  set B := ball (F.center j) (F.bergmanRadius j) with hBdef
  set Ψ := correctedWeight e (ρ j) φ with hΨdef
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hxp := F.closure_V_subset_chartPatch j hx
  set z₀ := e.val x with hz₀
  have hz₀B : z₀ ∈ B := hxp.2
  obtain ⟨R₀, hR₀, hR₀B⟩ := Metric.isOpen_iff.mp isOpen_ball z₀ hz₀B
  set R : ℝ := R₀ / 4 with hRdef
  have hR : 0 < R := by positivity
  have hBR : ball z₀ (2 * R) ⊆ B := (ball_subset_ball (by rw [hRdef]; linarith)).trans hR₀B
  have hBP : B ⊆ ball (F.center j) (F.potentialRadius j) :=
    ball_subset_ball (F.bergmanRadius_lt_potentialRadius j).le
  have hcbP : closedBall z₀ (2 * R) ⊆ ball (F.center j) (F.potentialRadius j) :=
    ((closedBall_subset_ball (by rw [hRdef]; linarith)).trans hR₀B).trans hBP
  have hpsh := F.plurisubharmonicOn_correctedWeight hρ hφ j
  set w : ComplexModel d → ℝ≥0∞ := fun z => multiplierWeight m (Ψ z) with hwdef
  have hw : AEMeasurable w (volume.restrict (ball z₀ (2 * R))) :=
    DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
      (hpsh.upperSemicontinuousOn.mono (ball_subset_closedBall.trans hcbP)) hmR.ne'
  obtain ⟨Cu, -, hCu⟩ := hpsh.exists_nonnegative_compact_upper_bound
    (isCompact_closedBall z₀ (2 * R)) hcbP
  have hlow : ∀ y ∈ ball z₀ (2 * R), ENNReal.ofReal (Real.exp (-((m : ℝ) * Cu))) ≤ w y := by
    intro y hy
    rw [hwdef, ← multiplierWeight_coe]
    exact multiplierWeight_antitone hmR.le (hCu y (ball_subset_closedBall hy))
  obtain ⟨L, h, r, K, hr, hhX, hker⟩ := exists_bergmanSup_le hR hBR hw (Real.exp_pos _) hlow
  -- each `h_l ∘ e` is a germ of `𝓘(mφ)` at `x`, hence dominated by the generators
  have hdom : ∀ l, ∃ C : ℝ, ∀ᶠ y in 𝓝 x, ‖h l (e.val y)‖ ^ 2 ≤ C * ∑ i, ‖g i y‖ ^ 2 := by
    intro l
    have hG : MultiplierIntegrableAt (fun w => chartFunction φ e w + (ρ j w : EReal)) m (h l)
        (e.val x) volume := by
      refine ⟨hmR, ball z₀ (2 * R), isOpen_ball, mem_ball_self (by positivity), (hhX l).1, ?_, ?_⟩
      · exact ((ENNReal.continuous_ofReal.comp_continuousOn
          (((hhX l).1.continuousOn).norm.pow 2)).aemeasurable isOpen_ball.measurableSet).mul hw
      · exact (hhX l).2.trans_lt ENNReal.one_lt_top
    have hmem := mem_multiplierIdeal_of_chart hφ hmR e isOpen_ball (hρ j).2.2.1.continuousOn
      hxp.1 (hBP hz₀B) hG
    exact exists_normSq_le_of_isInSpanAt (hgx _ hmem)
  choose Cl hCl using hdom
  set K' : ℝ := |K| * ∑ l, |Cl l| + 1 with hK'
  have hK'pos : 0 < K' := by positivity
  -- `ρ_j` is bounded near `z₀`
  have hρc : ContinuousAt (ρ j) z₀ :=
    ((hρ j).2.2.1.continuousOn _ (hBP hz₀B)).continuousAt (isOpen_ball.mem_nhds (hBP hz₀B))
  set Cρ : ℝ := |ρ j z₀| + 1 with hCρ
  refine ⟨((m : ℝ)⁻¹) * Real.log K' + Cρ, ?_⟩
  have hT : Tendsto e.val (𝓝 x) (𝓝 z₀) := e.val.continuousAt hxp.1
  filter_upwards [e.val.open_source.mem_nhds hxp.1, hT.eventually (isOpen_ball.mem_nhds
    (mem_ball_self hr)), hT.eventually (isOpen_ball.mem_nhds hz₀B),
    eventually_all.mpr hCl, hT.eventually (hρc.eventually (Metric.ball_mem_nhds (ρ j z₀) one_pos))]
    with y hys hyr hyB hyC hyρ
  have hyp : y ∈ chartPatch e B := ⟨hys, hyB⟩
  rw [FixedChartCover.branch, chartBergmanBranch_of_mem hyp, bergmanLog,
    generatorLog_eq_log_sum]
  set T : ℝ := ∑ i, ‖g i y‖ ^ 2 with hTdef
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hS : bergmanSup B w (e.val y) ≤ ENNReal.ofReal (K' * T) := by
    refine (hker _ hyr).trans (ENNReal.ofReal_le_ofReal ?_)
    calc K * ∑ l, ‖h l (e.val y)‖ ^ 2 ≤ |K| * ∑ l, ‖h l (e.val y)‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self K) (Finset.sum_nonneg fun l _ => sq_nonneg _)
      _ ≤ |K| * ∑ l, |Cl l| * T := by
          gcongr with l
          exact (hyC l).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hT0)
      _ = (|K| * ∑ l, |Cl l|) * T := by rw [← Finset.sum_mul, mul_assoc]
      _ ≤ K' * T := mul_le_mul_of_nonneg_right (by linarith) hT0
  have hρy : -ρ j (e.val y) ≤ Cρ := by
    have h1 : dist (ρ j (e.val y)) (ρ j z₀) < 1 := hyρ
    rw [Real.dist_eq] at h1
    have h2 := neg_abs_le (ρ j z₀)
    rw [hCρ]
    linarith [(abs_lt.mp h1).1]
  exact inv_mul_log_sub_le hK'pos hT0 hS (inv_pos.mpr hmR) hρy

end Branch

/-! ### Clause (i-g) for Demailly's sequence -/

/-- A value squeezed between `a - C` and `a + C` is real and `C`-close to `a`. -/
theorem eq_coe_of_bounds {u : EReal} {a C : ℝ} (hlo : (a : EReal) - (C : EReal) ≤ u)
    (hhi : u ≤ (a : EReal) + (C : EReal)) :
    u = (u.toReal : EReal) ∧ |u.toReal - a| ≤ C := by
  have hbot : u ≠ ⊥ := by
    intro h
    rw [h, le_bot_iff, ← EReal.coe_sub] at hlo
    exact EReal.coe_ne_bot _ hlo
  have htop : u ≠ ⊤ := by
    intro h
    rw [h, top_le_iff, ← EReal.coe_add] at hhi
    exact EReal.coe_ne_top _ hhi
  have hu : u = (u.toReal : EReal) := (EReal.coe_toReal htop hbot).symm
  refine ⟨hu, abs_le.mpr ⟨?_, ?_⟩⟩
  · rw [hu, ← EReal.coe_sub, EReal.coe_le_coe_iff] at hlo
    linarith
  · rw [hu, ← EReal.coe_add, EReal.coe_le_coe_iff] at hhi
    linarith

section Seq

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

open DemaillyApproximationSequence DemaillySymmetricGluing DemaillySymmetricGluingLimit
  QuantitativeRegularizationMaxGluing SymmetricRegularizedMaxPsh

/-- **Clause (i), global form, with the type named: Demailly's approximant `ψ_k` has analytic
singularities of type `(2^{-k}, 𝓘(2^k ψ))`** -- coefficient the rational `2^{-k}`, ideal the
multiplier ideal `𝓘(2^k ψ)` (coherent by Nadel).  The named ideal is what the multiplier-ideal
clause of a quasi-equisingular approximation needs
(`QuasiEquisingularApproximationDemailly`). -/
theorem hasAnalyticSingularitiesOfType_seq (hd : 0 < d) (F : FixedChartCover d Z)
    {α : ClosedRealOneOneForm d Z} {ψ : Z → EReal} (hψ : IsThetaPshPotential α.val ψ)
    {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential α.val (F.chart j) (ball (F.center j) (F.potentialRadius j))
      (ρ j)) (E : ℝ) (k : ℕ) :
    HasAnalyticSingularitiesOfType (n := d) (seq F ρ ψ E k) (((2 ^ k : ℕ) : ℚ)⁻¹)
      (multiplierIdeal (n := d) ((2 ^ k : ℕ) : ℝ) ψ) := by
  classical
  set m : ℕ := 2 ^ k with hmdef
  have hm : 0 < m := by positivity
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set c : ℚ := ((m : ℚ))⁻¹ with hcdef
  have hc : 0 < c := by positivity
  have hcR : ((c : ℚ) : ℝ) = ((m : ℝ))⁻¹ := by rw [hcdef]; push_cast; ring
  have hcoh := isCoherent_multiplierIdeal_of_pos hd hψ.1 hmR
  refine ⟨hc, hcoh, fun x => ?_⟩
  obtain ⟨U₀, hU₀, hxU₀, N, g, hgd, hgen⟩ := hcoh x
  have hgx : ∀ h, (multiplierIdeal (n := d) (m : ℝ) ψ).mem x h →
      IsInSpanAt (n := d) (· ∈ range g) x h := fun h hh => (hgen x hxU₀ h).mp hh
  set A : ℝ := (F.CB + 1) / (m : ℝ) with hAdef
  set δ : ℝ := 1 / (2 * (m : ℝ)) with hδdef
  have hA0 : 0 ≤ A := by have := F.CB_nonneg; positivity
  have hδ : 0 < δ := by positivity
  -- lower bound
  obtain ⟨j₀, hxj₀⟩ := F.cover.cover x
  have hgmem : ∀ i, (multiplierIdeal (n := d) (m : ℝ) ψ).mem x (g i) := by
    intro i
    refine (hgen x hxU₀ (g i)).mpr ⟨?_, 1, fun _ => g i, fun _ _ => 1, fun _ => ⟨i, rfl⟩,
      fun _ => Eventually.of_forall fun _ => mdifferentiableAt_const, ?_⟩
    · filter_upwards [hU₀.mem_nhds hxU₀] with y hy
      exact (hgd i y hy).mdifferentiableAt (hU₀.mem_nhds hy)
    · exact Eventually.of_forall fun y => by simp
  obtain ⟨C₁, hC₁⟩ := F.exists_const_eventually_le_branch hd hρ hψ.1 hm j₀
    (F.cover.U_subset_V j₀ hxj₀) hgmem
  -- upper bound
  set J : Finset F.t := Finset.univ.filter fun j => x ∈ closure (F.cover.V j) with hJ
  have hup : ∀ j ∈ J, ∃ C : ℝ, ∀ᶠ y in 𝓝 x,
      F.branch ρ ψ m j y ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y + (C : EReal) :=
    fun j hj => exists_branch_le F hρ hψ.1 hm j (Finset.mem_filter.mp hj).2 hgx
  choose! Cj hCj using hup
  set C₂ : ℝ := ∑ j ∈ J, |Cj j| with hC₂
  have hactive : ∀ᶠ y in 𝓝 x, ∀ j, y ∈ F.cover.V j → j ∈ J := by
    have : ∀ j, ∀ᶠ y in 𝓝 x, y ∈ F.cover.V j → j ∈ J := fun j => by
      by_cases hj : x ∈ closure (F.cover.V j)
      · exact Eventually.of_forall fun _ _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
      · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hj] with y hy hyV
        exact absurd (subset_closure hyV) hy
    exact eventually_all.mpr this
  have hbr : ∀ᶠ y in 𝓝 x, ∀ j ∈ J,
      F.branch ρ ψ m j y ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y + (C₂ : EReal) := by
    rw [eventually_all_finset]
    intro j hj
    filter_upwards [hCj j hj] with y hy
    refine hy.trans (add_le_add le_rfl (EReal.coe_le_coe_iff.mpr ?_))
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun j => |Cj j|)
      (fun j _ => abs_nonneg _) hj)
  -- the neighbourhood
  set K : ℝ := |C₁| + C₂ + A + δ + |E * ((2 : ℝ) ^ k)⁻¹| with hKdef
  have hev : ∀ᶠ y in 𝓝 x, y ∈ U₀ ∧
      (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (K : EReal) ≤ seq F ρ ψ E k y ∧
      seq F ρ ψ E k y ≤ (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y + (K : EReal) := by
    filter_upwards [hU₀.mem_nhds hxU₀, hC₁, (F.cover.isOpen_V j₀).mem_nhds
      (F.cover.U_subset_V j₀ hxj₀), hactive, hbr] with y hyU hy₁ hyV hyact hybr
    refine ⟨hyU, ?_, ?_⟩
    · -- lower
      have h1 : F.branch ρ ψ m j₀ y ≤ glued F.cover F.CB (fun m => F.branch ρ ψ m) m y :=
        le_rglue F.cover hδ (F.branch ρ ψ m) hA0 hyV
      unfold DemaillyApproximationSequence.seq
      calc (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (K : EReal)
          ≤ ((((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y - (C₁ : EReal)) +
              ((E * ((2 : ℝ) ^ k)⁻¹ : ℝ) : EReal) := by
            have hne : (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y ≠ ⊤ := by
              induction hg : generatorLog g y using EReal.rec with
              | bot => rw [EReal.coe_mul_bot_of_pos (inv_pos.mpr hmR)]; exact bot_ne_top
              | top => exact absurd hg (generatorLog_ne_top g y)
              | coe t => rw [← EReal.coe_mul]; exact EReal.coe_ne_top _
            induction h : (((m : ℝ)⁻¹ : ℝ) : EReal) * generatorLog g y using EReal.rec with
            | bot => simp
            | top => exact absurd h hne
            | coe s =>
              rw [← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add, EReal.coe_le_coe_iff, hKdef]
              have := neg_abs_le (E * ((2 : ℝ) ^ k)⁻¹)
              have := le_abs_self C₁
              have : 0 ≤ C₂ := Finset.sum_nonneg fun j _ => abs_nonneg _
              linarith
        _ ≤ glued F.cover F.CB (fun m => F.branch ρ ψ m) m y +
              ((E * ((2 : ℝ) ^ k)⁻¹ : ℝ) : EReal) := by
            gcongr
            exact hy₁.trans h1
    · -- upper
      unfold DemaillyApproximationSequence.seq DemaillySymmetricGluingLimit.glued
      by_cases hg0 : generatorLog g y = ⊥
      · have hbot : rglue F.cover (1 / (2 * (m : ℝ))) (F.branch ρ ψ m) ((F.CB + 1) / (m : ℝ)) y
            = ⊥ := by
          refine ermax_of_bot fun j hj => ?_
          have hyj : y ∈ F.cover.V j := (mem_activeSet F.cover).mp hj
          have := hybr j (hyact j hyj)
          rw [hg0, EReal.coe_mul_bot_of_pos (inv_pos.mpr hmR), EReal.bot_add, le_bot_iff] at this
          simp [CutoffCover.branch, this]
        rw [hbot, EReal.bot_add]
        exact bot_le
      · obtain ⟨t, ht⟩ : ∃ t : ℝ, generatorLog g y = (t : EReal) :=
          ⟨(generatorLog g y).toReal, (EReal.coe_toReal (generatorLog_ne_top g y) hg0).symm⟩
        have hle := rglue_le F.cover hδ (F.branch ρ ψ m) (A := A) (c := (m : ℝ)⁻¹ * t + C₂)
          (y := y) fun j hyj => by
            have h1 := hybr j (hyact j hyj)
            rw [ht, ← EReal.coe_mul, ← EReal.coe_add] at h1
            have hχ : A * F.cover.χ j y ≤ A := mul_le_of_le_one_right hA0 (F.χ_le_one j y)
            calc F.branch ρ ψ m j y + ((A * F.cover.χ j y : ℝ) : EReal)
                ≤ (((m : ℝ)⁻¹ * t + C₂ : ℝ) : EReal) + ((A : ℝ) : EReal) :=
                  add_le_add h1 (EReal.coe_le_coe_iff.mpr hχ)
              _ = (((m : ℝ)⁻¹ * t + C₂ + A : ℝ) : EReal) := by rw [← EReal.coe_add]
        refine (add_le_add hle le_rfl).trans ?_
        rw [ht, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff, hKdef]
        have := le_abs_self (E * ((2 : ℝ) ^ k)⁻¹)
        have := abs_nonneg C₁
        linarith
  obtain ⟨U, hUev, hUo, hxU⟩ := _root_.eventually_nhds_iff.mp hev
  -- the remainder
  set R : Z → ℝ := fun y => if generatorLog g y = ⊥ then 0 else
    (seq F ρ ψ E k y).toReal - (m : ℝ)⁻¹ * (generatorLog g y).toReal with hRdef
  refine ⟨U, hUo, hxU, N, g, fun i => (hgd i).mono fun y hy => (hUev y hy).1,
    fun y hy h => hgen y (hUev y hy).1 h, R, K, fun y hy => ?_, fun y hy => ?_⟩
  · obtain ⟨-, hlo, hhi⟩ := hUev y hy
    by_cases hg0 : generatorLog g y = ⊥
    · simp only [hRdef, if_pos hg0, abs_zero]
      have : 0 ≤ C₂ := Finset.sum_nonneg fun j _ => abs_nonneg _
      rw [hKdef]
      positivity
    · obtain ⟨t, ht⟩ : ∃ t : ℝ, generatorLog g y = (t : EReal) :=
        ⟨(generatorLog g y).toReal, (EReal.coe_toReal (generatorLog_ne_top g y) hg0).symm⟩
      rw [ht, ← EReal.coe_mul] at hlo hhi
      have := (eq_coe_of_bounds hlo hhi).2
      simpa only [hRdef, if_neg hg0, ht, EReal.toReal_coe] using this
  · obtain ⟨-, hlo, hhi⟩ := hUev y hy
    rw [hcR]
    by_cases hg0 : generatorLog g y = ⊥
    · rw [hg0, EReal.coe_mul_bot_of_pos (inv_pos.mpr hmR), EReal.bot_add] at hhi ⊢
      exact le_bot_iff.mp hhi
    · obtain ⟨t, ht⟩ : ∃ t : ℝ, generatorLog g y = (t : EReal) :=
        ⟨(generatorLog g y).toReal, (EReal.coe_toReal (generatorLog_ne_top g y) hg0).symm⟩
      rw [ht, ← EReal.coe_mul] at hlo hhi
      have hu := (eq_coe_of_bounds hlo hhi).1
      simp only [hRdef, if_neg hg0, ht, EReal.toReal_coe]
      nth_rewrite 1 [hu]
      rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_eq_coe_iff]
      ring

/-- **Clause (i), global form: Demailly's approximants have analytic singularities**, of type
`(2^{-k}, 𝓘(2^k ψ))` (`hasAnalyticSingularitiesOfType_seq`). -/
theorem hasAnalyticSingularities_seq (hd : 0 < d) (F : FixedChartCover d Z)
    {α : ClosedRealOneOneForm d Z} {ψ : Z → EReal} (hψ : IsThetaPshPotential α.val ψ)
    {ρ : F.t → ComplexModel d → ℝ}
    (hρ : ∀ j, IsSmoothLocalPotential α.val (F.chart j) (ball (F.center j) (F.potentialRadius j))
      (ρ j)) (E : ℝ) (k : ℕ) :
    HasAnalyticSingularities (n := d) (seq F ρ ψ E k) :=
  ⟨_, _, hasAnalyticSingularitiesOfType_seq hd F hψ hρ E k⟩

end Seq

/-! ### Demailly 1992 without the smooth-off-pole clause -/

section Global

variable {d : ℕ} {Z : Type*} [TopologicalSpace Z]
  [ChartedSpace (ComplexModel d) Z] [IsComplexManifold d Z]

open DemaillyApproximationSequence Hironaka.PositiveClasses

/-- In dimension `0` a theta-PSH potential has analytic singularities of type `(1, 𝒪)`: the unit
ideal is coherent (generated by `1`) and `ψ = log |1|² + ψ` with `ψ` real at every point. -/
theorem hasAnalyticSingularities_of_dim_zero {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace (ComplexModel 0) Y] [IsComplexManifold 0 Y] {θ : SmoothRealForm 0 Y 2}
    {ψ : Y → EReal} (hψ : IsThetaPshPotential θ ψ) :
    HasAnalyticSingularities (n := 0) ψ := by
  let 𝔞 : GermIdeal 0 Y := ⟨fun y h => HolomorphicAt 0 h y⟩
  let one : Fin 1 → Y → ℂ := fun _ _ => 1
  have hspan : ∀ y h, 𝔞.mem y h ↔ IsInSpanAt (n := 0) (· ∈ range one) y h := by
    intro y h
    constructor
    · intro hh
      exact ⟨hh, 1, one, fun _ => h, fun _ => ⟨0, rfl⟩, fun _ => hh,
        Eventually.of_forall fun z => by simp [one]⟩
    · exact fun hh => hh.1
  have hone : ∀ i, MDifferentiableOn 𝓘(ℂ, ComplexModel 0) 𝓘(ℂ, ℂ) (one i) univ := fun i =>
    mdifferentiableOn_const
  refine ⟨1, 𝔞, one_pos, fun x => ⟨univ, isOpen_univ, mem_univ x, 1, one, hone,
    fun y _ h => hspan y h⟩, fun x => ?_⟩
  have hx : IsOpen ({x} : Set Y) := isOpen_singleton_of_dim_zero x
  have hbot : ψ x ≠ ⊥ := by
    obtain ⟨y, hy, hyψ⟩ := hψ.2 x {x} hx rfl
    rwa [mem_singleton_iff.mp hy] at hyψ
  have htop : ψ x ≠ ⊤ := by
    have hq := hψ.1.quasiPlurisubharmonic (complexChartAt (n := 0) x)
      ((complexChartAt (n := 0) x).val x)
      ((complexChartAt (n := 0) x).val.map_source (mem_complexChartAt_source x))
    obtain ⟨p, hh, hp, -, heq⟩ := hq
    have h1 := heq.self_of_nhds
    have h2 : chartFunction ψ (complexChartAt (n := 0) x)
        ((complexChartAt (n := 0) x).val x) = ψ x := by
      simp only [chartFunction, (complexChartAt (n := 0) x).val.left_inv
        (mem_complexChartAt_source x)]
    rw [h2] at h1
    rw [h1]
    obtain ⟨U, -, hxU, hU⟩ := hp
    exact (EReal.add_ne_top_iff_ne_top_left (EReal.coe_ne_bot _) (EReal.coe_ne_top _)).mpr
      (hU.ne_top _ hxU)
  refine ⟨{x}, hx, rfl, 1, one, fun i => (hone i).mono (subset_univ _),
    fun y _ h => hspan y h, fun _ => (ψ x).toReal, |(ψ x).toReal|, fun y _ => le_rfl,
    fun y hy => ?_⟩
  rw [mem_singleton_iff.mp hy]
  have hlog : generatorLog one x = 0 := by
    rw [generatorLog_eq_log_sum]
    simp [one]
  rw [hlog, mul_zero, zero_add, EReal.coe_toReal htop hbot]

/-- **Demailly 1992 without the smooth-off-pole clause (i-c)**, on every compact Kähler manifold
(no connectedness, dimension `0` included): the statement of
`Demailly1992AlgebraicApproximation.demailly1992_exists_algebraicApproximation` with the conjunct
`∀ k, HasManifoldAnalyticSingularitiesSmoothOffPole (psiSeq k)` removed. -/
theorem exists_algebraicApproximation_global [CompactSpace Z] (omega : KahlerBackground d Z)
    (α : ClosedRealOneOneForm d Z) (ψ : Z → EReal) (hψ : IsThetaPshPotential α.val ψ) :
    ∃ (psiSeq : ℕ → Z → EReal) (delta : ℕ → ℝ),
      (∀ k, HasAnalyticSingularities (n := d) (psiSeq k)) ∧
      (∀ x, Antitone fun k => psiSeq k x) ∧ (∀ x, ⨅ k, psiSeq k x = ψ x) ∧
      (∀ k, 0 ≤ delta k) ∧ Tendsto delta atTop (𝓝 0) ∧
      ∀ k, IsThetaPshPotential (α + delta k • omega.form).val (psiSeq k) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨fun _ => ψ, fun _ => 0, fun _ => hasAnalyticSingularities_of_dim_zero hψ,
      fun x => antitone_const, fun x => iInf_const, fun _ => le_rfl, tendsto_const_nhds,
      fun k => ?_⟩
    simpa only [zero_smul, add_zero] using hψ
  · obtain ⟨F⟩ := exists_fixedChartCover (Z := Z) hd
    obtain ⟨ρ, hρ⟩ := F.exists_potentials α
    obtain ⟨D, -, hD⟩ := exists_doublingConst F
    have hdouble := hD α.val ψ hψ.1 ρ hρ
    obtain ⟨Cχ, hCχ, hsemi⟩ := KahlerDomination.exists_pos_forall_isSemipositive_add_smul omega
      (fun j => ManifoldTubePositivity.ddcClosedForm (F.cover.χ j) (F.cover.χ_smooth j))
    refine ⟨seq F ρ ψ (2 * (D + 1 / 4)), fun k => (F.CB + 1) / ((2 ^ k : ℕ) : ℝ) * Cχ,
      fun k => hasAnalyticSingularities_seq hd F hψ hρ _ k,
      fun x => antitone_seq F hdouble x, fun x => iInf_seq F hψ.1 hρ hdouble x, fun k => ?_, ?_,
      fun k => isThetaPshPotential_seq hd F omega hsemi hψ hρ _ k⟩
    · have := F.CB_nonneg
      positivity
    · have h1 : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
      have h2 := h1.const_mul ((F.CB + 1) * Cχ)
      rw [mul_zero] at h2
      refine h2.congr fun k => ?_
      push_cast
      field_simp

end Global

end

end Hironaka.DemaillyApproximationAnalyticType
