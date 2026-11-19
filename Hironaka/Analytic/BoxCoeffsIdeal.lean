import Hironaka.MarkedIdeal.GermIdealSliceClosure
import Hironaka.Analytic.LastVariableTaylorDivision

set_option autoImplicit false

/-!
# Vanishing box coefficients give membership in `((z_i - p_i)^K)_i`

Let `e` be holomorphic on the polydisc `Δ(p, s')` in `ℂ^{m+1}` and `0 < s < s'`.  If the torus
coefficients `torusCoeff p s α e` vanish for all `α ∈ [0, K)^{m+1}`, then near `p`
`e = ∑ᵢ (z_i - p_i)^K Q_i` with `Q_i` holomorphic near `p`
(`exists_eq_sum_pow_mul_of_boxCoeffs_eq_zero`).  This is the analytic input for identifying
torus-coefficient agreement below `K` with congruence modulo `𝔪^K` in the ring of germs.

The proof is by induction on `m`.  Write `t = z_last - p_last` and `w` for the first `m`
coordinates of `z - p` (sup-norm coordinates on `ℂ^m`, so the polydisc is a product of balls).
Taylor division in the last variable (`Hironaka.LastVariableTaylorDivision`) gives
`e = t^K Q_last + ∑_{k<K} c_k(w) t^k` (`eq_lastSub_pow_mul_add`), where
`c_k(w) = (2πi)⁻¹ ∮_{|ζ|=s} e(p + (w, ζ)) ζ^{-k-1} dζ` is holomorphic in `w`.

* Fubini on the angle box (`setIntegral_Icc_eq_angleIntegral`) and the definition of the circle
  integral (`intervalIntegral_torusPoint_snoc`) give
  `torusCoeff p s (β, k) e = 2π s^k · torusCoeff p' s β c_k` for `m ≥ 1`, with `p'` the first
  `m` coordinates of `p` (`torusCoeff_snoc_eq_mul_torusCoeff`).
* For `m = 0`, `c_k` is a constant and `torusCoeff p s (k) e = 2π s^k c_k`, so `c_k = 0` for
  `k < K` (`lastCoeff_eq_zero_of_torusCoeff_eq_zero`).
* For `m ≥ 1`, the induction hypothesis writes each `c_k`, `k < K`, as
  `∑_{i<m} (z_i - p_i)^K Q'_{k,i}` near `p'`; pulling back along the projection to the first
  `m` coordinates and regrouping gives the claim.
-/

open Set Filter MeasureTheory Complex
open scoped Real Topology

namespace Hironaka

noncomputable section

variable {m : ℕ}

/-! ### Fubini on the angle box -/

/-- The set integral over `[0, 2π]^{m+1}` of a continuous function is the iterated
`angleIntegral`. -/
theorem setIntegral_Icc_eq_angleIntegral {G : (Fin (m + 1) → ℝ) → ℂ} (hG : Continuous G) :
    ∫ θ in Icc (0 : Fin (m + 1) → ℝ) (fun _ => 2 * π), G θ = angleIntegral G := by
  set e : ℝ × (Fin m → ℝ) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last m)).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).symm _
  have heπ : (e ⁻¹' Icc 0 fun _ => 2 * π) =
      Icc 0 (2 * π) ×ˢ Icc (0 : Fin m → ℝ) fun _ => 2 * π :=
    ((Fin.insertNthOrderIso (fun _ => ℝ) (Fin.last m)).preimage_Icc _ _).trans
      (Icc_prod_eq _ _)
  have hint : IntegrableOn (fun z => G (e z))
      (Icc 0 (2 * π) ×ˢ Icc (0 : Fin m → ℝ) fun _ => 2 * π) (volume.prod volume) := by
    have : IntegrableOn G (Icc (0 : Fin (m + 1) → ℝ) fun _ => 2 * π) volume :=
      hG.integrableOn_Icc
    rwa [← hem.integrableOn_comp_preimage e.measurableEmbedding, heπ,
      Measure.volume_eq_prod] at this
  rw [← hem.map_eq, setIntegral_map_equiv, heπ, Measure.volume_eq_prod,
    ← setIntegral_prod_swap, setIntegral_prod (fun z => G (e z.swap)) hint.swap]
  unfold angleIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ' _ => ?_
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le, integral_Icc_eq_integral_Ioc]
  simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_last']

/-- The value of a set integral over the (one-point) box `[0, c]^0`. -/
theorem setIntegral_Icc_fin_zero (c : Fin 0 → ℝ) (F : (Fin 0 → ℝ) → ℂ) :
    ∫ θ in Icc (0 : Fin 0 → ℝ) c, F θ = F 0 := by
  have hc : c = 0 := Subsingleton.elim _ _
  subst hc
  simp only [Icc_self, Measure.restrict_singleton, volume_pi,
    Measure.pi_of_empty (fun _ : Fin 0 ↦ volume) 0, integral_dirac,
    Measure.dirac_apply_of_mem (mem_singleton _), integral_smul_measure]
  simp

/-! ### Coordinates -/

theorem differentiable_toLp_two (n : ℕ) :
    Differentiable ℂ (WithLp.toLp 2 : (Fin n → ℂ) → EuclideanSpace ℂ (Fin n)) :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm.differentiable

/-- The point `p + (w, t)` of `ℂ^{m+1}`, with `w ∈ ℂ^m` in sup-norm coordinates. -/
def snocPoint (p : EuclideanSpace ℂ (Fin (m + 1))) (x : (Fin m → ℂ) × ℂ) :
    EuclideanSpace ℂ (Fin (m + 1)) :=
  p + WithLp.toLp 2 (Fin.snoc (α := fun _ => ℂ) x.1 x.2)

theorem differentiable_snocPoint (p : EuclideanSpace ℂ (Fin (m + 1))) :
    Differentiable ℂ (snocPoint p) := by
  unfold snocPoint
  refine (differentiable_const p).add ((differentiable_toLp_two _).comp ?_)
  refine differentiable_pi.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]; fun_prop
  · simp only [Fin.snoc_castSucc]; fun_prop

/-- The first `m` coordinates of `z - p`. -/
def initSub (p z : EuclideanSpace ℂ (Fin (m + 1))) : Fin m → ℂ :=
  fun j => z j.castSucc - p j.castSucc

/-- The last coordinate of `z - p`. -/
def lastSub (p z : EuclideanSpace ℂ (Fin (m + 1))) : ℂ :=
  z (Fin.last m) - p (Fin.last m)

theorem differentiable_initSub_lastSub (p : EuclideanSpace ℂ (Fin (m + 1))) :
    Differentiable ℂ fun z => (initSub p z, lastSub p z) := by
  refine Differentiable.prodMk ?_ ?_
  · exact differentiable_pi.2 fun j =>
      ((EuclideanSpace.proj (𝕜 := ℂ) j.castSucc).differentiable).sub_const _
  · exact ((EuclideanSpace.proj (𝕜 := ℂ) (Fin.last m)).differentiable).sub_const _

theorem snocPoint_initSub_lastSub (p z : EuclideanSpace ℂ (Fin (m + 1))) :
    snocPoint p (initSub p z, lastSub p z) = z := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [snocPoint, initSub, lastSub]

theorem snocPoint_mem_openPolydisc {p : EuclideanSpace ℂ (Fin (m + 1))} {r : ℝ}
    {x : (Fin m → ℂ) × ℂ}
    (hx : x ∈ Metric.ball (0 : Fin m → ℂ) r ×ˢ Metric.ball (0 : ℂ) r) :
    snocPoint p x ∈ openPolydisc p r := by
  obtain ⟨h1, h2⟩ := hx
  rw [mem_ball_zero_iff] at h1 h2
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa [snocPoint] using h2
  · simpa [snocPoint] using (norm_le_pi_norm x.1 j).trans_lt h1

theorem initSub_lastSub_mem {p z : EuclideanSpace ℂ (Fin (m + 1))} {r : ℝ} (hr : 0 < r)
    (hz : z ∈ openPolydisc p r) :
    (initSub p z, lastSub p z) ∈
      Metric.ball (0 : Fin m → ℂ) r ×ˢ Metric.ball (0 : ℂ) r := by
  refine ⟨?_, ?_⟩
  · rw [mem_ball_zero_iff, pi_norm_lt_iff hr]
    exact fun j => hz j.castSucc
  · rw [mem_ball_zero_iff]
    exact hz (Fin.last m)

theorem differentiableOn_comp_snocPoint {p : EuclideanSpace ℂ (Fin (m + 1))} {r : ℝ}
    {e : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    (he : DifferentiableOn ℂ e (openPolydisc p r)) :
    DifferentiableOn ℂ (fun x => e (snocPoint p x))
      (Metric.ball (0 : Fin m → ℂ) r ×ˢ Metric.ball (0 : ℂ) r) :=
  he.comp (differentiable_snocPoint p).differentiableOn fun _ hx => snocPoint_mem_openPolydisc hx

/-! ### Division in the last variable -/

/-- **Division by `(z_last - p_last)^K`** on the polydisc: `e` is `(z_last - p_last)^K` times a
holomorphic function plus a polynomial of degree `< K` in `z_last - p_last` whose coefficients
are the circle coefficients in the last variable. -/
theorem eq_lastSub_pow_mul_add {p : EuclideanSpace ℂ (Fin (m + 1))} {s s' : ℝ} (hs : 0 < s)
    (hss' : s < s') {e : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    (he : DifferentiableOn ℂ e (openPolydisc p s')) (K : ℕ) :
    ∀ z ∈ openPolydisc p s', e z =
      lastSub p z ^ K * lastQuot (fun x => e (snocPoint p x)) s K (initSub p z, lastSub p z) +
        ∑ k ∈ Finset.range K,
          lastSub p z ^ k * lastCoeff (fun x => e (snocPoint p x)) s k (initSub p z) := by
  intro z hz
  have := eq_lastQuot_mul_add hs hss' (differentiableOn_comp_snocPoint he) K _
    (initSub_lastSub_mem (hs.trans hss') hz)
  simp only [snocPoint_initSub_lastSub] at this
  rw [this, mul_comm]
  simp only [mul_comm (lastSub p z ^ _)]

theorem differentiableOn_lastQuot_initSub {p : EuclideanSpace ℂ (Fin (m + 1))} {s s' : ℝ}
    (hs : 0 < s) (hss' : s < s') {e : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    (he : DifferentiableOn ℂ e (openPolydisc p s')) (K : ℕ) :
    DifferentiableOn ℂ
      (fun z => lastQuot (fun x => e (snocPoint p x)) s K (initSub p z, lastSub p z))
      (openPolydisc p s') :=
  (differentiableOn_lastQuot hs hss' (differentiableOn_comp_snocPoint he) K).comp
    (differentiable_initSub_lastSub p).differentiableOn
    fun _ hz => initSub_lastSub_mem (hs.trans hss') hz

/-! ### Torus coefficients and circle coefficients -/

/-- The phase of a multi-index `(β, k)` at angles `(θ', θ)`. -/
theorem anglePhase_snoc (β : Fin m → ℕ) (k : ℕ) (θ' : Fin m → ℝ) (θ : ℝ) :
    anglePhase (fun i => ((Fin.snoc (α := fun _ => ℕ) β k i : ℕ) : ℤ))
        (Fin.snoc (α := fun _ => ℝ) θ' θ) =
      exp (-(∑ i, (β i : ℂ) * (θ' i : ℂ)) * I) * exp (-((k : ℂ) * θ) * I) := by
  unfold anglePhase
  rw [Fin.sum_univ_castSucc, ← exp_add]
  congr 1
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Int.cast_natCast]
  ring

/-- The inner (last-angle) integral is `2π s^k` times the `k`-th circle coefficient. -/
theorem intervalIntegral_torusPoint_snoc (p : EuclideanSpace ℂ (Fin (m + 1)))
    {s : ℝ} (hs : 0 < s) (e : EuclideanSpace ℂ (Fin (m + 1)) → ℂ) (θ' : Fin m → ℝ)
    (k : ℕ) :
    ∫ θ in (0 : ℝ)..2 * π,
        e (torusPoint p s (Fin.snoc (α := fun _ => ℝ) θ' θ)) * exp (-((k : ℂ) * θ) * I) =
      2 * π * (s : ℂ) ^ k *
        lastCoeff (fun x => e (snocPoint p x)) s k (fun i => (s : ℂ) * exp (θ' i * I)) := by
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hci : (∮ ζ in C(0, s), e (snocPoint p ((fun i => (s : ℂ) * exp (θ' i * I)), ζ)) /
      ζ ^ (k + 1)) = ∫ θ in (0 : ℝ)..2 * π, (I / (s : ℂ) ^ k) *
        (e (torusPoint p s (Fin.snoc (α := fun _ => ℝ) θ' θ)) *
          exp (-((k : ℂ) * θ) * I)) := by
    unfold circleIntegral
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hT : torusPoint p s (Fin.snoc (α := fun _ => ℝ) θ' θ) =
        snocPoint p ((fun i => (s : ℂ) * exp (θ' i * I)), (s : ℂ) * exp (θ * I)) :=
      torusPoint_snoc p s θ' θ
    simp only [deriv_circleMap, circleMap, zero_add, smul_eq_mul, hT]
    generalize e (snocPoint p ((fun i => (s : ℂ) * exp (θ' i * I)),
      (s : ℂ) * exp (θ * I))) = E
    have hE : exp (-((k : ℂ) * θ) * I) = (exp (θ * I) ^ k)⁻¹ := by
      rw [← exp_nat_mul, ← exp_neg]; congr 1; ring
    rw [hE]
    have : exp (θ * I) ≠ 0 := exp_ne_zero _
    field_simp
    ring
  unfold lastCoeff
  rw [hci, intervalIntegral.integral_const_mul]
  generalize (∫ θ in (0 : ℝ)..2 * π,
    e (torusPoint p s (Fin.snoc (α := fun _ => ℝ) θ' θ)) * exp (-((k : ℂ) * θ) * I)) = X
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The torus coefficient of index `(β, k)` as an outer integral of circle coefficients. -/
theorem torusCoeff_snoc_eq (p : EuclideanSpace ℂ (Fin (m + 1))) {s : ℝ} (hs : 0 < s)
    (e : EuclideanSpace ℂ (Fin (m + 1)) → ℂ) (β : Fin m → ℕ) (k : ℕ) :
    torusCoeff p s (fun i => ((Fin.snoc (α := fun _ => ℕ) β k i : ℕ) : ℤ)) e =
      ∫ θ' in Icc (0 : Fin m → ℝ) (fun _ => 2 * π), 2 * π * (s : ℂ) ^ k *
        (lastCoeff (fun x => e (snocPoint p x)) s k (fun i => (s : ℂ) * exp (θ' i * I)) *
          exp (-(∑ i, (β i : ℂ) * (θ' i : ℂ)) * I)) := by
  unfold torusCoeff angleIntegral
  refine setIntegral_congr_fun measurableSet_Icc fun θ' _ => ?_
  simp only [anglePhase_snoc]
  simp only [← mul_assoc, mul_right_comm _ (exp (-(∑ i, (β i : ℂ) * (θ' i : ℂ)) * I))]
  rw [intervalIntegral.integral_mul_const, intervalIntegral_torusPoint_snoc p hs]

theorem two_pi_mul_pow_ne_zero {s : ℝ} (hs : 0 < s) (k : ℕ) :
    2 * π * (s : ℂ) ^ k ≠ 0 := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  exact mul_ne_zero (mul_ne_zero two_ne_zero hpi) (pow_ne_zero k hs0)

/-- In one variable (`m = 0`), vanishing torus coefficients below `K` make the circle
coefficients below `K` vanish. -/
theorem lastCoeff_eq_zero_of_torusCoeff_eq_zero {p : EuclideanSpace ℂ (Fin 1)} {s : ℝ}
    (hs : 0 < s) {e : EuclideanSpace ℂ (Fin 1) → ℂ} {K : ℕ}
    (hzero : ∀ α : Fin 1 → ℕ, (∀ i, α i < K) →
      torusCoeff p s (fun i => (α i : ℤ)) e = 0)
    {k : ℕ} (hk : k < K) (w : Fin 0 → ℂ) :
    lastCoeff (fun x => e (snocPoint p x)) s k w = 0 := by
  have h := hzero (Fin.snoc (α := fun _ => ℕ) (fun i => i.elim0) k) fun i => by
    refine Fin.lastCases ?_ (fun j => j.elim0) i
    simp only [Fin.snoc_last]
    exact hk
  rw [torusCoeff_snoc_eq p hs, setIntegral_Icc_fin_zero, Finset.univ_eq_empty,
    Finset.sum_empty, neg_zero, zero_mul, exp_zero, mul_one] at h
  rw [Subsingleton.elim w (fun i => (s : ℂ) * exp (((0 : Fin 0 → ℝ) i : ℂ) * I))]
  exact (mul_eq_zero.1 h).resolve_left (two_pi_mul_pow_ne_zero hs k)

/-! ### Passing to the first `m` coordinates -/

/-- The first `m` coordinates of a point of `ℂ^{m+1}`. -/
def initPoint (z : EuclideanSpace ℂ (Fin (m + 1))) : EuclideanSpace ℂ (Fin m) :=
  WithLp.toLp 2 fun j => z j.castSucc

theorem differentiable_initPoint : Differentiable ℂ (initPoint (m := m)) :=
  (differentiable_toLp_two m).comp (differentiable_pi.2 fun j =>
    (EuclideanSpace.proj (𝕜 := ℂ) j.castSucc).differentiable)

/-- The `k`-th circle coefficient in the last variable, as a function on `ℂ^m` centred at
the first `m` coordinates of `p`. -/
theorem differentiableOn_lastCoeff_sub {p : EuclideanSpace ℂ (Fin (m + 2))} {s s' : ℝ}
    (hs : 0 < s) (hss' : s < s') {e : EuclideanSpace ℂ (Fin (m + 2)) → ℂ}
    (he : DifferentiableOn ℂ e (openPolydisc p s')) (k : ℕ) :
    DifferentiableOn ℂ (fun z : EuclideanSpace ℂ (Fin (m + 1)) =>
        lastCoeff (fun x => e (snocPoint p x)) s k (fun j => z j - initPoint p j))
      (openPolydisc (initPoint p) s') :=
  (differentiableOn_lastCoeff hs hss' (differentiableOn_comp_snocPoint he) k).comp
    (differentiable_pi.2 fun j =>
      ((EuclideanSpace.proj (𝕜 := ℂ) j).differentiable).sub_const _).differentiableOn
    fun _ hz => by
      rw [mem_ball_zero_iff, pi_norm_lt_iff (hs.trans hss')]
      exact hz

/-- **The coefficient identity.**  The torus coefficient of index `(β, k)` of `e` is `2π s^k`
times the torus coefficient of index `β` of the `k`-th circle coefficient in the last
variable. -/
theorem torusCoeff_snoc_eq_mul_torusCoeff {p : EuclideanSpace ℂ (Fin (m + 2))} {s s' : ℝ}
    (hs : 0 < s) (hss' : s < s') {e : EuclideanSpace ℂ (Fin (m + 2)) → ℂ}
    (he : DifferentiableOn ℂ e (openPolydisc p s')) (β : Fin (m + 1) → ℕ) (k : ℕ) :
    torusCoeff p s (fun i => ((Fin.snoc (α := fun _ => ℕ) β k i : ℕ) : ℤ)) e =
      2 * π * (s : ℂ) ^ k * torusCoeff (initPoint p) s (fun i => (β i : ℤ))
        (fun z => lastCoeff (fun x => e (snocPoint p x)) s k (fun j => z j - initPoint p j)) := by
  have hcont : Continuous fun θ => (fun z : EuclideanSpace ℂ (Fin (m + 1)) =>
      lastCoeff (fun x => e (snocPoint p x)) s k (fun j => z j - initPoint p j))
        (torusPoint (initPoint p) s θ) * anglePhase (fun i => (β i : ℤ)) θ :=
    (continuousOnTorus_of_differentiableOn hs.le hss'
      (differentiableOn_lastCoeff_sub hs hss' he k)).mul (continuous_anglePhase _)
  rw [torusCoeff_snoc_eq p hs, integral_const_mul, torusCoeff,
    ← setIntegral_Icc_eq_angleIntegral hcont]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun θ' _ => ?_
  simp [torusPoint, anglePhase]

/-! ### The induction -/

theorem mem_openPolydisc_self (p : EuclideanSpace ℂ (Fin (m + 1))) {r : ℝ} (hr : 0 < r) :
    p ∈ openPolydisc p r := fun i => by simpa using hr

theorem eventually_differentiableAt_lastQuot_initSub {p : EuclideanSpace ℂ (Fin (m + 1))}
    {s s' : ℝ} (hs : 0 < s) (hss' : s < s') {e : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    (he : DifferentiableOn ℂ e (openPolydisc p s')) (K : ℕ) :
    ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ
      (fun z => lastQuot (fun x => e (snocPoint p x)) s K (initSub p z, lastSub p z)) z := by
  filter_upwards [(isOpen_openPolydisc p s').mem_nhds (mem_openPolydisc_self p (hs.trans hss'))]
    with z hz
  exact (differentiableOn_lastQuot_initSub hs hss' he K).differentiableAt
    ((isOpen_openPolydisc p s').mem_nhds hz)

/-- **Vanishing box coefficients give membership in `((z_i - p_i)^K)_i`.**  A function
holomorphic on the polydisc `Δ(p, s')` whose torus coefficients on the torus of radius `s < s'`
vanish on the box `[0, K)^{m+1}` is, as a germ at `p`, a combination
`∑ᵢ (z_i - p_i)^K Q_i` with `Q_i` holomorphic near `p`. -/
theorem exists_eq_sum_pow_mul_of_boxCoeffs_eq_zero {m : ℕ} {p : EuclideanSpace ℂ (Fin (m + 1))}
    {s s' : ℝ} (hs : 0 < s) (hss' : s < s') {e : EuclideanSpace ℂ (Fin (m + 1)) → ℂ}
    (he : DifferentiableOn ℂ e (openPolydisc p s')) (K : ℕ)
    (hzero : ∀ α : Fin (m + 1) → ℕ, (∀ i, α i < K) →
      torusCoeff p s (fun i => (α i : ℤ)) e = 0) :
    ∃ Q : Fin (m + 1) → EuclideanSpace ℂ (Fin (m + 1)) → ℂ,
      (∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (Q i) z) ∧
      e =ᶠ[𝓝 p] fun z => ∑ i, (z i - p i) ^ K * Q i z := by
  induction m with
  | zero =>
    have hnhds := (isOpen_openPolydisc p s').mem_nhds (mem_openPolydisc_self p (hs.trans hss'))
    refine ⟨fun _ z => lastQuot (fun x => e (snocPoint p x)) s K (initSub p z, lastSub p z),
      fun _ => eventually_differentiableAt_lastQuot_initSub hs hss' he K, ?_⟩
    filter_upwards [hnhds] with z hz
    rw [eq_lastSub_pow_mul_add hs hss' he K z hz, Finset.sum_eq_zero fun k hk => by
      rw [lastCoeff_eq_zero_of_torusCoeff_eq_zero hs hzero (Finset.mem_range.1 hk), mul_zero],
      add_zero, Fin.sum_univ_one]
    rfl
  | succ m ih =>
    have hQ' : ∀ k : Fin K, ∃ Q' : Fin (m + 1) → EuclideanSpace ℂ (Fin (m + 1)) → ℂ,
        (∀ i, ∀ᶠ z in 𝓝 (initPoint p), DifferentiableAt ℂ (Q' i) z) ∧
        (fun z => lastCoeff (fun x => e (snocPoint p x)) s k (fun j => z j - initPoint p j))
          =ᶠ[𝓝 (initPoint p)] fun z => ∑ i, (z i - initPoint p i) ^ K * Q' i z := by
      intro k
      refine ih (differentiableOn_lastCoeff_sub hs hss' he k) fun β hβ => ?_
      have h1 := hzero (Fin.snoc (α := fun _ => ℕ) β k) fun i => by
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp only [Fin.snoc_last]; exact k.isLt
        · simp only [Fin.snoc_castSucc]; exact hβ j
      rw [torusCoeff_snoc_eq_mul_torusCoeff hs hss' he] at h1
      exact (mul_eq_zero.1 h1).resolve_left (two_pi_mul_pow_ne_zero hs k)
    choose Q' hQ'd hQ'e using hQ'
    have hT : Tendsto initPoint (𝓝 p) (𝓝 (initPoint p)) :=
      (differentiable_initPoint (m := m + 1)).continuous.tendsto p
    have hlast : Differentiable ℂ (lastSub p) :=
      ((EuclideanSpace.proj (𝕜 := ℂ) (Fin.last (m + 1))).differentiable).sub_const _
    refine ⟨Fin.snoc (α := fun _ => EuclideanSpace ℂ (Fin (m + 2)) → ℂ)
      (fun i z => ∑ k : Fin K, lastSub p z ^ (k : ℕ) * Q' k i (initPoint z))
      (fun z => lastQuot (fun x => e (snocPoint p x)) s K (initSub p z, lastSub p z)),
      fun i => ?_, ?_⟩
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · simp only [Fin.snoc_last]
        exact eventually_differentiableAt_lastQuot_initSub hs hss' he K
      · simp only [Fin.snoc_castSucc]
        have hk : ∀ k : Fin K, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (Q' k i) (initPoint z) :=
          fun k => hT.eventually (hQ'd k i)
        filter_upwards [Filter.eventually_all.2 hk] with z hz
        refine DifferentiableAt.fun_sum fun k _ => ?_
        exact ((hlast z).pow _).mul ((hz k).comp z (differentiable_initPoint z))
    · have hk : ∀ k : Fin K, ∀ᶠ z in 𝓝 p,
          lastCoeff (fun x => e (snocPoint p x)) s k (initSub p z) =
            ∑ i, (z i.castSucc - p i.castSucc) ^ K * Q' k i (initPoint z) :=
        fun k => (hT.eventually (hQ'e k)).mono fun z hz => hz
      filter_upwards [Filter.eventually_all.2 hk,
        (isOpen_openPolydisc p s').mem_nhds (mem_openPolydisc_self p (hs.trans hss'))]
        with z hz hz'
      rw [eq_lastSub_pow_mul_add hs hss' he K z hz', Fin.sum_univ_castSucc, Finset.sum_range]
      simp only [Fin.snoc_castSucc, Fin.snoc_last, hz, Finset.mul_sum]
      rw [add_comm, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      ring

end

end Hironaka
