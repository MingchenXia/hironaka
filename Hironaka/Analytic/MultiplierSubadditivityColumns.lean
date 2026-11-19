import Hironaka.Analytic.TorusCoefficientsProduct
import Hironaka.Analytic.MultiplierSubadditivityTools
import Hironaka.Analytic.MultiplierIdealBergmanNadelVanishing
import Hironaka.Analytic.DemaillyApproximation
import Hironaka.Manifold.HolomorphicContDiff

set_option autoImplicit false

/-!
# Column functions of an extension from the diagonal (DEL00 subadditivity, step 3)

Step 3 of our route to the
subadditivity of multiplier ideals (Demailly--Ein--Lazarsfeld, Michigan Math. J. **48** (2000),
Theorem 2.6; Copy-4 `eq:subadditivity`).  Let `G` be holomorphic on `B × B`, `B = B(x, r) ⊆ ℂ^d`,
with `∫∫_{B×B} |G(a,b)|² e^{-P₁(a)} e^{-P₂(b)} < ∞` for `P₁, P₂` plurisubharmonic near `B̄`.  For a
multi-index `β`, the **column function**

  `F_β(a) = torusCoeff x s β (G(a, ·))`

(the `β`-th torus coefficient of `G(a, ·)` on a torus of radius `s` inside `B(x, r/2)`) is
holomorphic on `B` and lies in `𝓘(P₁)_x`:

* `differentiableAt_torusCoeff_param` — holomorphic dependence of a torus coefficient on a
  parameter (differentiation under the integral sign over the compact angle box; the derivative
  bound is the continuity of `fderiv` on a compact tube, as in
  `RiemannExtension.differentiableAt_circleIntegral_param`);
* `ofReal_normSq_torusCoeff_le` — `|F_β(a)|² ≤ K ∫_B |G(a,b)|² e^{-P₂(b)} db`: the coefficient is
  bounded by `(2π)^d` times the supremum on the torus, and the sub-mean-value inequality on balls of
  radius `r/4` centred on the torus (`lintegral_ball_normSq_ge`), with `e^{-P₂} ≥ e^{-sup P₂}`;
* `multiplierIntegrableAt_torusCoeff_column` — Tonelli then gives
  `∫_B |F_β|² e^{-P₁} ≤ K ∫∫_{B×B} |G|² e^{-P₁} e^{-P₂} < ∞`.

The rows `b ↦ torusCoeff x s α (G(·, b))` are the columns of `G ∘ swap`
(`multiplierIntegrableAt_torusCoeff_row`), and the two iterated coefficients agree
(`torusCoeff_swap`, Fubini on the angle boxes).  `torusCoeff_finset_sum` is linearity over a finite
sum.

Sorry-free.
-/

open Set Filter MeasureTheory Metric Complex
open scoped Topology Real ENNReal

namespace Hironaka.MultiplierSubadditivityColumns

noncomputable section



/-! ### Holomorphic dependence on a parameter -/

/-- **A torus coefficient depends holomorphically on a parameter.**  If `Ψ` is complex
differentiable on an open set `O ⊆ P × ℂ^{m+1}` containing `{p₀} × Δ̄(x, s)`, then
`p ↦ torusCoeff x s β (Ψ(p, ·))` is complex differentiable at `p₀`. -/
theorem differentiableAt_torusCoeff_param {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    [FiniteDimensional ℂ P] {m : ℕ} {Ψ : P × EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    {O : Set (P × EuclideanSpace ℂ (Fin (m + 1)))} (hO : IsOpen O) (hΨ : DifferentiableOn ℂ Ψ O)
    {x : EuclideanSpace ℂ (Fin (m + 1))} {s : ℝ} (hs : 0 ≤ s) {p₀ : P}
    (hp₀ : ∀ z : EuclideanSpace ℂ (Fin (m + 1)), (∀ i, ‖z i - x i‖ ≤ s) → (p₀, z) ∈ O)
    (β : Fin (m + 1) → ℤ) :
    DifferentiableAt ℂ (fun p => torusCoeff x s β (fun z => Ψ (p, z))) p₀ := by
  set Q : Set (EuclideanSpace ℂ (Fin (m + 1))) := {z | ∀ i, ‖z i - x i‖ ≤ s} with hQdef
  have hQc : IsCompact Q := isCompact_closedPolydisc x hs
  have hK₀ : IsCompact (({p₀} : Set P) ×ˢ Q) := isCompact_singleton.prod hQc
  obtain ⟨δ, hδ, hδO⟩ := hK₀.exists_cthickening_subset_open hO (by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    rw [mem_singleton_iff] at hp
    subst hp
    exact hp₀ z hz)
  have hKO : closedBall p₀ δ ×ˢ Q ⊆ O := by
    rintro ⟨p, z⟩ ⟨hp, hz⟩
    refine hδO (Metric.mem_cthickening_of_dist_le _ (p₀, z) δ _ ⟨rfl, hz⟩ ?_)
    rw [Prod.dist_eq, dist_self, max_le_iff]
    exact ⟨hp, hδ.le⟩
  have hK : IsCompact (closedBall p₀ δ ×ˢ Q) := (isCompact_closedBall p₀ δ).prod hQc
  have hcd : ContinuousOn (fderiv ℂ Ψ) O :=
    (Hironaka.contDiffOn_of_differentiableOn_complex hΨ hO).continuousOn_fderiv_of_isOpen hO
      (by simp)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcd.mono hKO)
  have htQ : ∀ θ, torusPoint x s θ ∈ Q := fun θ i => (norm_torusPoint_sub x hs θ i).le
  have hmem : ∀ p ∈ closedBall p₀ δ, ∀ θ, (p, torusPoint x s θ) ∈ O :=
    fun p hp θ => hKO ⟨hp, htQ θ⟩
  set μ : Measure (Fin (m + 1) → ℝ) := volume.restrict (Icc 0 fun _ => 2 * π) with hμ
  set F : P → (Fin (m + 1) → ℝ) → ℂ := fun p θ => Ψ (p, torusPoint x s θ) * anglePhase β θ
    with hF
  set F' : P → (Fin (m + 1) → ℝ) → P →L[ℂ] ℂ := fun p θ =>
    anglePhase β θ • (fderiv ℂ Ψ (p, torusPoint x s θ)).comp
      (ContinuousLinearMap.inl ℂ P (EuclideanSpace ℂ (Fin (m + 1)))) with hF'
  have hFc : ∀ p ∈ closedBall p₀ δ, Continuous (F p) := fun p hp =>
    (hΨ.continuousOn.comp_continuous (continuous_const.prodMk (continuous_torusPoint x s))
      (hmem p hp)).mul (continuous_anglePhase β)
  have hbound : ∀ p ∈ closedBall p₀ δ, ∀ θ, ‖F' p θ‖ ≤ M := fun p hp θ => by
    simp only [hF', norm_smul, norm_anglePhase, one_mul]
    calc ‖(fderiv ℂ Ψ (p, torusPoint x s θ)).comp
            (ContinuousLinearMap.inl ℂ P (EuclideanSpace ℂ (Fin (m + 1))))‖
        ≤ ‖fderiv ℂ Ψ (p, torusPoint x s θ)‖ *
            ‖ContinuousLinearMap.inl ℂ P (EuclideanSpace ℂ (Fin (m + 1)))‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℂ Ψ (p, torusPoint x s θ)‖ * 1 := by
          gcongr
          exact ContinuousLinearMap.norm_inl_le_one ℂ P _
      _ ≤ M := by rw [mul_one]; exact hM _ ⟨hp, htQ θ⟩
  have hp₀δ : p₀ ∈ closedBall p₀ δ := mem_closedBall_self hδ.le
  have hderiv := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := μ) (F := F) (F' := F') (x₀ := p₀) (bound := fun _ => M) (ball_mem_nhds p₀ hδ)
    (eventually_of_mem (ball_mem_nhds p₀ hδ) fun p hp =>
      (hFc p (ball_subset_closedBall hp)).aestronglyMeasurable)
    ((hFc p₀ hp₀δ).integrableOn_Icc)
    (by
      refine Continuous.aestronglyMeasurable ?_
      simp only [hF']
      refine (continuous_anglePhase β).smul ?_
      refine Continuous.clm_comp ?_ continuous_const
      exact hcd.comp_continuous (continuous_const.prodMk (continuous_torusPoint x s))
        (hmem p₀ hp₀δ))
    (Eventually.of_forall fun θ p hp => hbound p (ball_subset_closedBall hp) θ)
    (integrableOn_const (by rw [Real.volume_Icc_pi]; exact ENNReal.prod_ne_top fun _ _ =>
      ENNReal.ofReal_ne_top))
    (Eventually.of_forall fun θ p hp => by
      have hd : HasFDerivAt Ψ (fderiv ℂ Ψ (p, torusPoint x s θ)) (p, torusPoint x s θ) :=
        (hΨ.differentiableAt (hO.mem_nhds (hmem p (ball_subset_closedBall hp) θ))).hasFDerivAt
      exact (hd.comp p (hasFDerivAt_prodMk_left (𝕜 := ℂ) p (torusPoint x s θ))).mul_const
        (anglePhase β θ))
  have heq : (fun p => torusCoeff x s β (fun z => Ψ (p, z))) =ᶠ[𝓝 p₀]
      fun p => ∫ θ, F p θ ∂μ := by
    filter_upwards [ball_mem_nhds p₀ hδ] with p hp
    exact (setIntegral_Icc_eq_angleIntegral (hFc p (ball_subset_closedBall hp))).symm
  exact hderiv.differentiableAt.congr_of_eventuallyEq heq

/-! ### Linearity over finite sums and Fubini -/

section Coefficients

variable {m : ℕ}

/-- Torus coefficients are additive over finite sums of functions continuous along the torus. -/
theorem torusCoeff_finset_sum {p : EuclideanSpace ℂ (Fin (m + 1))} {s : ℝ} {ι : Type*}
    (S : Finset ι) (q : ι → EuclideanSpace ℂ (Fin (m + 1)) → ℂ)
    (hq : ∀ i ∈ S, ContinuousOnTorus p s (q i)) (α : Fin (m + 1) → ℤ) :
    torusCoeff p s α (fun z => ∑ i ∈ S, q i z) = ∑ i ∈ S, torusCoeff p s α (q i) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact torusCoeff_zero p s α
  | insert j S hj ih =>
      have hS : ContinuousOnTorus p s (fun z => ∑ i ∈ S, q i z) := by
        unfold ContinuousOnTorus
        exact continuous_finsetSum _ fun i hi => hq i (Finset.mem_insert_of_mem hi)
      have h := torusCoeff_add (hq j (Finset.mem_insert_self j S)) hS α
      rw [Finset.sum_insert hj, ← ih fun i hi => hq i (Finset.mem_insert_of_mem hi), ← h]
      congr 1
      funext z
      simp [Finset.sum_insert hj]

/-- The iterated torus coefficient as an iterated set integral over the angle boxes. -/
theorem torusCoeff_iter_eq (x : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ) (α β : Fin (m + 1) → ℤ)
    (G : EuclideanSpace ℂ (Fin (m + 1)) → EuclideanSpace ℂ (Fin (m + 1)) → ℂ)
    (hG : Continuous fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
      G (torusPoint x s p.1) (torusPoint x s p.2)) :
    torusCoeff x s α (fun a => torusCoeff x s β (G a)) =
      ∫ θL in Icc (0 : Fin (m + 1) → ℝ) (fun _ => 2 * π),
        ∫ θR in Icc (0 : Fin (m + 1) → ℝ) (fun _ => 2 * π),
          G (torusPoint x s θL) (torusPoint x s θR) * (anglePhase β θR * anglePhase α θL) := by
  have hKc : Continuous fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
      G (torusPoint x s p.1) (torusPoint x s p.2) * anglePhase β p.2 :=
    hG.mul ((continuous_anglePhase β).comp continuous_snd)
  have hinner : ∀ θL, torusCoeff x s β (G (torusPoint x s θL)) =
      ∫ θR in Icc (0 : Fin (m + 1) → ℝ) (fun _ => 2 * π),
        G (torusPoint x s θL) (torusPoint x s θR) * anglePhase β θR := by
    intro θL
    have hc : Continuous fun θR =>
        G (torusPoint x s θL) (torusPoint x s θR) * anglePhase β θR :=
      ((hG.comp (continuous_const.prodMk continuous_id)).mul (continuous_anglePhase β))
    rw [setIntegral_Icc_eq_angleIntegral hc]
    rfl
  have hc2 : Continuous fun θL =>
      (∫ θR in Icc (0 : Fin (m + 1) → ℝ) (fun _ => 2 * π),
        G (torusPoint x s θL) (torusPoint x s θR) * anglePhase β θR) * anglePhase α θL :=
    (continuous_parametric_integral_of_continuous
      (f := fun θL θR => G (torusPoint x s θL) (torusPoint x s θR) * anglePhase β θR)
      hKc isCompact_Icc).mul (continuous_anglePhase α)
  have hrhs : torusCoeff x s α (fun a => torusCoeff x s β (G a)) =
      ∫ θL in Icc (0 : Fin (m + 1) → ℝ) (fun _ => 2 * π),
        (∫ θR in Icc (0 : Fin (m + 1) → ℝ) (fun _ => 2 * π),
          G (torusPoint x s θL) (torusPoint x s θR) * anglePhase β θR) * anglePhase α θL := by
    rw [setIntegral_Icc_eq_angleIntegral hc2]
    show angleIntegral (fun θL => torusCoeff x s β (G (torusPoint x s θL)) * anglePhase α θL) = _
    exact angleIntegral_congr fun θL => by rw [hinner θL]
  rw [hrhs]
  refine setIntegral_congr_fun measurableSet_Icc fun θL _ => ?_
  rw [← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Icc fun θR _ => ?_
  ring

/-- **Fubini for iterated torus coefficients.** -/
theorem torusCoeff_swap (x : EuclideanSpace ℂ (Fin (m + 1))) (s : ℝ) (α β : Fin (m + 1) → ℤ)
    (G : EuclideanSpace ℂ (Fin (m + 1)) → EuclideanSpace ℂ (Fin (m + 1)) → ℂ)
    (hG : Continuous fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
      G (torusPoint x s p.1) (torusPoint x s p.2)) :
    torusCoeff x s α (fun a => torusCoeff x s β (G a)) =
      torusCoeff x s β (fun b => torusCoeff x s α (fun a => G a b)) := by
  have hG' : Continuous fun p : (Fin (m + 1) → ℝ) × (Fin (m + 1) → ℝ) =>
      (fun b a => G a b) (torusPoint x s p.1) (torusPoint x s p.2) :=
    hG.comp continuous_swap
  rw [torusCoeff_iter_eq x s α β G hG, torusCoeff_iter_eq x s β α (fun b a => G a b) hG']
  set I : Set (Fin (m + 1) → ℝ) := Icc (0 : Fin (m + 1) → ℝ) (fun _ => 2 * π)
  have hint : Integrable (Function.uncurry fun θL θR =>
      G (torusPoint x s θL) (torusPoint x s θR) * (anglePhase β θR * anglePhase α θL))
      ((volume.restrict I).prod (volume.restrict I)) := by
    rw [Measure.prod_restrict]
    refine ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) ?_
    refine Continuous.continuousOn ?_
    exact hG.mul (((continuous_anglePhase β).comp continuous_snd).mul
      ((continuous_anglePhase α).comp continuous_fst))
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Icc fun θR _ => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun θL _ => ?_
  ring

end Coefficients

/-! ### The column functions lie in the multiplier ideal -/

section Column

variable {d' : ℕ} [MeasurableSpace (ComplexModel (d' + 1))] [BorelSpace (ComplexModel (d' + 1))]

/-- **Pointwise bound for a column function.**  For `g` holomorphic on `B = B(x, r)`, with the
closed polydisc `Δ̄(x, s)` inside `B(x, r/2)` and `w₂ ≥ δ₀ > 0` on `B`,
`|torusCoeff x s β g|² ≤ (2π)^{2(d'+1)} (δ₀ V)⁻¹ ∫_B |g|² w₂`, where `V` is the volume of a ball of
radius `r/4`. -/
theorem ofReal_normSq_torusCoeff_le {x : ComplexModel (d' + 1)} {r s : ℝ} (hr : 0 < r)
    (hs : 0 ≤ s)
    (hQ : ∀ z : ComplexModel (d' + 1), (∀ i, ‖z i - x i‖ ≤ s) → z ∈ ball x (r / 2))
    {w₂ : ComplexModel (d' + 1) → ℝ≥0∞} {δ₀ : ℝ≥0∞} (hδ₀ : δ₀ ≠ 0) (hδ₀top : δ₀ ≠ ⊤)
    (hw₂ : ∀ b ∈ ball x r, δ₀ ≤ w₂ b)
    {g : ComplexModel (d' + 1) → ℂ} (hg : DifferentiableOn ℂ g (ball x r)) (β : Fin (d' + 1) → ℤ) :
    ENNReal.ofReal (‖torusCoeff x s β g‖ ^ 2) ≤
      ENNReal.ofReal (((2 * π) ^ (d' + 1)) ^ 2) *
        ((δ₀ * volume (ball (0 : ComplexModel (d' + 1)) (r / 4)))⁻¹ *
          ∫⁻ b in ball x r, ENNReal.ofReal (‖g b‖ ^ 2) * w₂ b) := by
  set V : ℝ≥0∞ := volume (ball (0 : ComplexModel (d' + 1)) (r / 4)) with hV
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ (by positivity)).ne'
  have hVtop : V ≠ ⊤ := measure_ball_lt_top.ne
  have hδV0 : δ₀ * V ≠ 0 := mul_ne_zero hδ₀ hV0
  have hδVtop : δ₀ * V ≠ ⊤ := ENNReal.mul_ne_top hδ₀top hVtop
  set J : ℝ≥0∞ := ∫⁻ b in ball x r, ENNReal.ofReal (‖g b‖ ^ 2) * w₂ b with hJ
  set T : ℝ≥0∞ := (δ₀ * V)⁻¹ * J with hT
  have hπ0 : ENNReal.ofReal (((2 * π) ^ (d' + 1)) ^ 2) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  by_cases hJtop : J = ⊤
  · have hT' : T = ⊤ := by
      rw [hT, hJtop]
      exact ENNReal.mul_top (ENNReal.inv_ne_zero.mpr hδVtop)
    rw [hT', ENNReal.mul_top hπ0]
    exact le_top
  have hTtop : T ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hδV0) hJtop
  -- the sub-mean-value inequality at the torus points
  have hpt : ∀ θ, ENNReal.ofReal (‖g (torusPoint x s θ)‖ ^ 2) ≤ T := by
    intro θ
    set w := torusPoint x s θ with hwdef
    have hw : w ∈ ball x (r / 2) := hQ w fun i => (norm_torusPoint_sub x hs θ i).le
    have hsub : closedBall w (r / 4) ⊆ ball x r := by
      intro u hu
      rw [mem_closedBall] at hu
      rw [mem_ball] at hw ⊢
      have := dist_triangle u w x
      linarith
    have hmv := lintegral_ball_normSq_ge isOpen_ball hg (by positivity : 0 < r / 4) hsub
    rw [Measure.addHaar_ball_center] at hmv
    have hchain : (δ₀ * V) * ENNReal.ofReal (‖g w‖ ^ 2) ≤ J := by
      calc (δ₀ * V) * ENNReal.ofReal (‖g w‖ ^ 2)
          = δ₀ * (V * ENNReal.ofReal (‖g w‖ ^ 2)) := by ring
        _ ≤ δ₀ * ∫⁻ u in ball w (r / 4), ENNReal.ofReal (‖g u‖ ^ 2) := by gcongr
        _ = ∫⁻ u in ball w (r / 4), δ₀ * ENNReal.ofReal (‖g u‖ ^ 2) :=
            (lintegral_const_mul' _ _ hδ₀top).symm
        _ ≤ ∫⁻ u in ball w (r / 4), ENNReal.ofReal (‖g u‖ ^ 2) * w₂ u := by
            refine setLIntegral_mono' measurableSet_ball fun u hu => ?_
            rw [mul_comm]
            gcongr
            exact hw₂ u (hsub (ball_subset_closedBall hu))
        _ ≤ J := lintegral_mono_set (ball_subset_closedBall.trans hsub)
    calc ENNReal.ofReal (‖g w‖ ^ 2) = (δ₀ * V)⁻¹ * ((δ₀ * V) * ENNReal.ofReal (‖g w‖ ^ 2)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hδV0 hδVtop, one_mul]
      _ ≤ T := by rw [hT]; gcongr
  -- the bound on the coefficient
  have hnorm : ∀ θ, ‖g (torusPoint x s θ) * anglePhase β θ‖ ≤ Real.sqrt T.toReal := by
    intro θ
    rw [norm_mul, norm_anglePhase, mul_one]
    exact Real.le_sqrt_of_sq_le ((ENNReal.ofReal_le_iff_le_toReal hTtop).mp (hpt θ))
  have hcoef : ‖torusCoeff x s β g‖ ≤ (2 * π) ^ (d' + 1) * Real.sqrt T.toReal :=
    norm_angleIntegral_le hnorm
  have hsq : ‖torusCoeff x s β g‖ ^ 2 ≤ ((2 * π) ^ (d' + 1)) ^ 2 * T.toReal := by
    have h0 : 0 ≤ ‖torusCoeff x s β g‖ := norm_nonneg _
    calc ‖torusCoeff x s β g‖ ^ 2 ≤ ((2 * π) ^ (d' + 1) * Real.sqrt T.toReal) ^ 2 :=
          pow_le_pow_left₀ h0 hcoef 2
      _ = ((2 * π) ^ (d' + 1)) ^ 2 * T.toReal := by
          rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
  calc ENNReal.ofReal (‖torusCoeff x s β g‖ ^ 2)
      ≤ ENNReal.ofReal (((2 * π) ^ (d' + 1)) ^ 2 * T.toReal) := ENNReal.ofReal_le_ofReal hsq
    _ = ENNReal.ofReal (((2 * π) ^ (d' + 1)) ^ 2) * T := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hTtop]

/-- **The column functions lie in `𝓘(P₁)_x`** (DEL00 subadditivity, step 3).  Let `P₁, P₂` be
plurisubharmonic near `B̄ = B̄(x, r)`, `G` holomorphic on `B × B` with
`∫∫_{B×B} |G(a,b)|² e^{-P₁(a)} e^{-P₂(b)} < ∞`, and the closed polydisc `Δ̄(x, s)` inside
`B(x, r/2)`.  Then `a ↦ torusCoeff x s β (G(a, ·))` is holomorphic on `B` and `L²` for `e^{-P₁}`
on `B`. -/
theorem multiplierIntegrableAt_torusCoeff_column {Ω : Set (ComplexModel (d' + 1))}
    {P₁ P₂ : ComplexModel (d' + 1) → EReal} (hP₁ : PlurisubharmonicOn P₁ Ω)
    (hP₂ : PlurisubharmonicOn P₂ Ω) {x : ComplexModel (d' + 1)} {r s : ℝ} (hr : 0 < r)
    (hrΩ : closedBall x r ⊆ Ω) (hs : 0 ≤ s)
    (hQ : ∀ z : ComplexModel (d' + 1), (∀ i, ‖z i - x i‖ ≤ s) → z ∈ ball x (r / 2))
    {G : ComplexModel (d' + 1) × ComplexModel (d' + 1) → ℂ}
    (hG : DifferentiableOn ℂ G (ball x r ×ˢ ball x r))
    (hint : ∫⁻ p, ENNReal.ofReal (‖G p‖ ^ 2) *
        (multiplierWeight 1 (P₁ p.1) * multiplierWeight 1 (P₂ p.2))
          ∂((volume.restrict (ball x r)).prod (volume.restrict (ball x r))) ≠ ⊤)
    (β : Fin (d' + 1) → ℤ) :
    MultiplierIntegrableAt P₁ 1 (fun a => torusCoeff x s β (fun b => G (a, b))) x volume ∧
      DifferentiableOn ℂ (fun a => torusCoeff x s β (fun b => G (a, b))) (ball x r) := by
  set B : Set (ComplexModel (d' + 1)) := ball x r with hBdef
  have hBΩ : B ⊆ Ω := ball_subset_closedBall.trans hrΩ
  set w₁ : ComplexModel (d' + 1) → ℝ≥0∞ := fun a => multiplierWeight 1 (P₁ a) with hw₁def
  set w₂ : ComplexModel (d' + 1) → ℝ≥0∞ := fun b => multiplierWeight 1 (P₂ b) with hw₂def
  -- a lower bound for `e^{-P₂}` on `B`
  obtain ⟨C₂, -, hC₂⟩ := hP₂.exists_nonnegative_compact_upper_bound (isCompact_closedBall x r) hrΩ
  set δ₀ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-C₂)) with hδ₀def
  have hδ₀ : δ₀ ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hδ₀top : δ₀ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hw₂ : ∀ b ∈ B, δ₀ ≤ w₂ b := by
    intro b hb
    have h1 : multiplierWeight 1 (C₂ : EReal) = δ₀ := by
      rw [multiplierWeight_coe, one_mul]
    rw [← h1]
    exact multiplierWeight_antitone zero_le_one (hC₂ b (ball_subset_closedBall hb))
  -- the column function is holomorphic on `B`
  set F : ComplexModel (d' + 1) → ℂ := fun a => torusCoeff x s β (fun b => G (a, b)) with hFdef
  have hFd : DifferentiableOn ℂ F B := fun a ha =>
    (differentiableAt_torusCoeff_param (O := B ×ˢ B) (isOpen_ball.prod isOpen_ball) hG hs
      (p₀ := a) (fun z hz => ⟨ha, ball_subset_ball (by linarith) (hQ z hz)⟩) β).differentiableWithinAt
  have hGa : ∀ a ∈ B, DifferentiableOn ℂ (fun b => G (a, b)) B := fun a ha =>
    hG.comp ((differentiable_const a).prodMk differentiable_id).differentiableOn
      fun b hb => ⟨ha, hb⟩
  -- measurability
  have hw₁m : AEMeasurable w₁ (volume.restrict B) :=
    DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
      ((hP₁.mono hBΩ).upperSemicontinuousOn) one_ne_zero
  have hw₂m : AEMeasurable w₂ (volume.restrict B) :=
    DemaillyApproximation.aemeasurable_multiplierWeight_restrict isOpen_ball
      ((hP₂.mono hBΩ).upperSemicontinuousOn) one_ne_zero
  have hFm : AEMeasurable (multiplierDensity P₁ 1 F) (volume.restrict B) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn (hFd.continuousOn.norm.pow 2)).aemeasurable
      isOpen_ball.measurableSet).mul hw₁m
  have hprodm : AEMeasurable (fun p : ComplexModel (d' + 1) × ComplexModel (d' + 1) =>
      ENNReal.ofReal (‖G p‖ ^ 2) * (w₁ p.1 * w₂ p.2))
      ((volume.restrict B).prod (volume.restrict B)) := by
    refine AEMeasurable.mul ?_ (hw₁m.comp_fst.mul hw₂m.comp_snd)
    rw [Measure.prod_restrict]
    exact (ENNReal.continuous_ofReal.comp_continuousOn (hG.continuousOn.norm.pow 2)).aemeasurable
      (isOpen_ball.prod isOpen_ball).measurableSet
  -- the integral bound
  set V : ℝ≥0∞ := volume (ball (0 : ComplexModel (d' + 1)) (r / 4)) with hV
  set K : ℝ≥0∞ := ENNReal.ofReal (((2 * π) ^ (d' + 1)) ^ 2) * (δ₀ * V)⁻¹ with hK
  have hV0 : V ≠ 0 := (measure_ball_pos volume _ (by positivity)).ne'
  have hKtop : K ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.inv_ne_top.mpr (mul_ne_zero hδ₀ hV0))
  have hpt : ∀ a ∈ B, multiplierDensity P₁ 1 F a ≤
      K * (w₁ a * ∫⁻ b in B, ENNReal.ofReal (‖G (a, b)‖ ^ 2) * w₂ b) := by
    intro a ha
    have h := ofReal_normSq_torusCoeff_le hr hs hQ hδ₀ hδ₀top hw₂ (hGa a ha) β
    calc multiplierDensity P₁ 1 F a = ENNReal.ofReal (‖F a‖ ^ 2) * w₁ a := rfl
      _ ≤ (ENNReal.ofReal (((2 * π) ^ (d' + 1)) ^ 2) * ((δ₀ * V)⁻¹ *
            ∫⁻ b in B, ENNReal.ofReal (‖G (a, b)‖ ^ 2) * w₂ b)) * w₁ a := by gcongr
      _ = K * (w₁ a * ∫⁻ b in B, ENNReal.ofReal (‖G (a, b)‖ ^ 2) * w₂ b) := by
          rw [hK]; ring
  have hlt : ∫⁻ a in B, multiplierDensity P₁ 1 F a < ⊤ := by
    calc ∫⁻ a in B, multiplierDensity P₁ 1 F a
        ≤ ∫⁻ a in B, K * (w₁ a * ∫⁻ b in B, ENNReal.ofReal (‖G (a, b)‖ ^ 2) * w₂ b) :=
          setLIntegral_mono' isOpen_ball.measurableSet hpt
      _ = K * ∫⁻ a in B, w₁ a * ∫⁻ b in B, ENNReal.ofReal (‖G (a, b)‖ ^ 2) * w₂ b :=
          lintegral_const_mul' _ _ hKtop
      _ ≤ K * ∫⁻ a in B, ∫⁻ b in B, ENNReal.ofReal (‖G (a, b)‖ ^ 2) * (w₁ a * w₂ b) := by
          gcongr with a
          refine (lintegral_const_mul_le _ _).trans (le_of_eq ?_)
          refine lintegral_congr fun b => ?_
          ring
      _ = K * ∫⁻ p, ENNReal.ofReal (‖G p‖ ^ 2) * (w₁ p.1 * w₂ p.2)
            ∂((volume.restrict B).prod (volume.restrict B)) := by
          rw [lintegral_prod _ hprodm]
      _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hKtop) (lt_top_iff_ne_top.mpr hint)
  exact ⟨⟨one_pos, B, isOpen_ball, mem_ball_self hr, hFd, hFm, hlt⟩, hFd⟩

/-- **The row functions lie in `𝓘(P₂)_x`**: the columns of `G ∘ swap`. -/
theorem multiplierIntegrableAt_torusCoeff_row {Ω : Set (ComplexModel (d' + 1))}
    {P₁ P₂ : ComplexModel (d' + 1) → EReal} (hP₁ : PlurisubharmonicOn P₁ Ω)
    (hP₂ : PlurisubharmonicOn P₂ Ω) {x : ComplexModel (d' + 1)} {r s : ℝ} (hr : 0 < r)
    (hrΩ : closedBall x r ⊆ Ω) (hs : 0 ≤ s)
    (hQ : ∀ z : ComplexModel (d' + 1), (∀ i, ‖z i - x i‖ ≤ s) → z ∈ ball x (r / 2))
    {G : ComplexModel (d' + 1) × ComplexModel (d' + 1) → ℂ}
    (hG : DifferentiableOn ℂ G (ball x r ×ˢ ball x r))
    (hint : ∫⁻ p, ENNReal.ofReal (‖G p‖ ^ 2) *
        (multiplierWeight 1 (P₁ p.1) * multiplierWeight 1 (P₂ p.2))
          ∂((volume.restrict (ball x r)).prod (volume.restrict (ball x r))) ≠ ⊤)
    (α : Fin (d' + 1) → ℤ) :
    MultiplierIntegrableAt P₂ 1 (fun b => torusCoeff x s α (fun a => G (a, b))) x volume ∧
      DifferentiableOn ℂ (fun b => torusCoeff x s α (fun a => G (a, b))) (ball x r) := by
  have hG' : DifferentiableOn ℂ (fun p => G p.swap) (ball x r ×ˢ ball x r) :=
    hG.comp (differentiable_snd.prodMk differentiable_fst).differentiableOn
      fun p hp => ⟨hp.2, hp.1⟩
  have hint' : ∫⁻ p, ENNReal.ofReal (‖G p.swap‖ ^ 2) *
      (multiplierWeight 1 (P₂ p.1) * multiplierWeight 1 (P₁ p.2))
        ∂((volume.restrict (ball x r)).prod (volume.restrict (ball x r))) ≠ ⊤ := by
    have h := lintegral_prod_swap (μ := volume.restrict (ball x r))
      (ν := volume.restrict (ball x r)) (fun p : ComplexModel (d' + 1) × ComplexModel (d' + 1) =>
        ENNReal.ofReal (‖G p‖ ^ 2) *
          (multiplierWeight 1 (P₁ p.1) * multiplierWeight 1 (P₂ p.2)))
    rw [← h] at hint
    refine ne_of_eq_of_ne (lintegral_congr fun p => ?_) hint
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring
  exact multiplierIntegrableAt_torusCoeff_column hP₂ hP₁ hr hrΩ hs hQ hG' hint' α

end Column

end

end Hironaka.MultiplierSubadditivityColumns
