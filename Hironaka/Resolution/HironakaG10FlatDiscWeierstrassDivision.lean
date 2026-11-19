import Hironaka.Analytic.RiemannExtension
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Module.Cardinality

/-! # Weierstrass division by a parametric polynomial on a disc, with uniform bounds

Let `P` be a finite-dimensional complex normed space (the parameters), `U ⊆ P` open and
`W(z,w) = ∑_{k ≤ b} A_k(z) w^k` a polynomial in one variable `w` whose coefficients are
holomorphic on `U`, with `W(z, ζ) ≠ 0` for `z ∈ U` and `|ζ| = ρ`. For `h` holomorphic on
`U × D(0,R)`, `ρ < R`, the Cauchy integrals
* `divQuot (z,w) = (2πi)⁻¹ ∮_{|ζ|=ρ} h(z,ζ) / (W(z,ζ) (ζ - w)) dζ`,
* `remCoeff i z = (2πi)⁻¹ ∮_{|ζ|=ρ} h(z,ζ) c_i(z,ζ) / W(z,ζ) dζ`
(`c_i` the coefficients of the difference quotient `(W(ζ) - W(w))/(ζ - w) = ∑_{i<b} c_i(ζ) w^i`)
give the division `h = W · divQuot + ∑_{i<b} remCoeff i · w^i` on `U × D(0,ρ)`
(`division_eq`), with `divQuot` holomorphic on `U × D(0,ρ)` and every `remCoeff i`
holomorphic on `U` (`differentiableOn_divQuot`, `differentiableOn_remCoeff`), and with
explicit sup-norm bounds depending only on `ρ`, `|w|`, a bound for `h` on the circle, a lower
bound for `|W|` on the circle and bounds for the coefficients (`norm_remCoeff_le`,
`norm_divQuot_le`, `norm_diffCoeff_le`). These constants are UNIFORM in the parameter and in
the divisor: they hold for every divisor with the same bounds, which is what division at
varying centres needs.

Uniqueness (`eq_zero_of_mul_eval_eq`, `division_unique`): if `W(z,·)` is monic of degree `b`
with all its roots in `D(0,ρ)`, a division `h = q W + r` with `q` continuous on `D(0,ρ)` and
`r` a polynomial of degree `< b` is unique.

This is the one-variable division theorem with bounds on a fixed disc behind Douady's
privileged polydiscs (Frisch 1968, Lemme 3/4; Douady 1966 §7). No Banach-space or privilege
statement is made here. BP: hironaka-g10-flat-disc-weierstrass-division.tex. -/
set_option autoImplicit false
namespace Hironaka.HironakaG10FlatDiscWeierstrassDivision
open Complex Metric Set Filter Polynomial
open scoped Real Topology
noncomputable section

variable {P : Type*}

/-! ## The polynomial and its difference quotient -/

/-- The polynomial `W(z,w) = ∑_{k ≤ b} A_k(z) w^k`. -/
def polyEval (b : ℕ) (A : ℕ → P → ℂ) (z : P) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (b+1), A k z * w ^ k

/-- The coefficients of the difference quotient `(W(z,ζ) - W(z,w))/(ζ - w)` as a polynomial
in `w`: `c_i(z,ζ) = ∑_{i < k ≤ b} A_k(z) ζ^{k-1-i}`. -/
def diffCoeff (b : ℕ) (A : ℕ → P → ℂ) (i : ℕ) (z : P) (ζ : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (b+1), if i < k then A k z * ζ ^ (k - 1 - i) else 0

/-- The difference-quotient identity. -/
theorem polyEval_sub_eq (b : ℕ) (A : ℕ → P → ℂ) (z : P) (ζ w : ℂ) :
    polyEval b A z ζ - polyEval b A z w =
      (ζ - w) * ∑ i ∈ Finset.range b, diffCoeff b A i z ζ * w ^ i := by
  have key : ∀ k ∈ Finset.range (b+1),
      (∑ i ∈ Finset.range b, (if i < k then A k z * ζ ^ (k - 1 - i) else 0) * w ^ i) =
        A k z * ∑ i ∈ Finset.range k, w ^ i * ζ ^ (k - 1 - i) := by
    intro k hk
    have hkb : k ≤ b := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [Finset.mul_sum, ← Finset.sum_range_add_sum_Ico _ hkb]
    have h1 : ∑ i ∈ Finset.Ico k b, (if i < k then A k z * ζ ^ (k - 1 - i) else 0) * w ^ i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        rw [if_neg (by simp only [Finset.mem_Ico] at hi; omega), zero_mul]
    rw [h1, add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_pos (Finset.mem_range.mp hi)]
    ring
  have hgeom : ∀ k : ℕ, ζ ^ k - w ^ k = (ζ - w) * ∑ i ∈ Finset.range k, w ^ i * ζ ^ (k - 1 - i) := by
    intro k
    have := geom_sum₂_mul w ζ k
    linear_combination this
  calc polyEval b A z ζ - polyEval b A z w
      = ∑ k ∈ Finset.range (b+1), A k z * (ζ ^ k - w ^ k) := by
        simp only [polyEval, ← Finset.sum_sub_distrib, mul_sub]
    _ = ∑ k ∈ Finset.range (b+1), (ζ - w) *
          ∑ i ∈ Finset.range b, (if i < k then A k z * ζ ^ (k - 1 - i) else 0) * w ^ i := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [key k hk, hgeom k]
        ring
    _ = (ζ - w) * ∑ i ∈ Finset.range b, diffCoeff b A i z ζ * w ^ i := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        simp only [diffCoeff, Finset.sum_mul]

theorem continuous_polyEval (b : ℕ) (A : ℕ → P → ℂ) (z : P) : Continuous (polyEval b A z) :=
  continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_pow k)

theorem differentiable_polyEval (b : ℕ) (A : ℕ → P → ℂ) (z : P) :
    Differentiable ℂ (polyEval b A z) := by
  unfold polyEval
  exact Differentiable.fun_sum fun k _ => (differentiable_const _).mul (differentiable_pow k)

theorem continuous_diffCoeff (b : ℕ) (A : ℕ → P → ℂ) (i : ℕ) (z : P) :
    Continuous (diffCoeff b A i z) :=
  continuous_finsetSum _ fun k _ => by
    split_ifs
    · exact continuous_const.mul (continuous_pow _)
    · exact continuous_const

section Normed
variable [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- Joint holomorphy of `(z,ζ) ↦ W(z,ζ)` over `U`. -/
theorem differentiableOn_polyEval (b : ℕ) {A : ℕ → P → ℂ} {U : Set P}
    (hA : ∀ k, DifferentiableOn ℂ (A k) U) :
    DifferentiableOn ℂ (fun x : P × ℂ => polyEval b A x.1 x.2) (U ×ˢ univ) := by
  refine DifferentiableOn.fun_sum fun k _ => ?_
  exact ((hA k).comp differentiableOn_fst fun x hx => hx.1).mul
    (differentiableOn_snd.pow k)

theorem differentiableOn_diffCoeff (b : ℕ) {A : ℕ → P → ℂ} {U : Set P}
    (hA : ∀ k, DifferentiableOn ℂ (A k) U) (i : ℕ) :
    DifferentiableOn ℂ (fun x : P × ℂ => diffCoeff b A i x.1 x.2) (U ×ˢ univ) := by
  refine DifferentiableOn.fun_sum fun k _ => ?_
  split_ifs
  · exact ((hA k).comp differentiableOn_fst fun x hx => hx.1).mul
      (differentiableOn_snd.pow _)
  · exact differentiableOn_const 0

end Normed

/-- Uniform bound for the difference-quotient coefficients on the circle. -/
theorem norm_diffCoeff_le (b : ℕ) (A : ℕ → P → ℂ) (i : ℕ) (z : P) {ρ : ℝ} {ζ : ℂ}
    (hζ : ‖ζ‖ = ρ) :
    ‖diffCoeff b A i z ζ‖ ≤ ∑ k ∈ Finset.range (b+1), ‖A k z‖ * ρ ^ (k - 1 - i) := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  split_ifs
  · rw [norm_mul, norm_pow, hζ]
  · rw [norm_zero]
    exact mul_nonneg (norm_nonneg _) (pow_nonneg ((norm_nonneg ζ).trans_eq hζ) _)

/-! ## The division operators -/

variable (b : ℕ) (A : ℕ → P → ℂ) (h : P × ℂ → ℂ) (ρ : ℝ)

/-- The Cauchy quotient of the division of `h` by `W`. -/
def divQuot (x : P × ℂ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ ζ in C(0, ρ), h (x.1, ζ) / (polyEval b A x.1 ζ * (ζ - x.2))

/-- The `i`-th coefficient of the remainder of the division of `h` by `W`. -/
def remCoeff (i : ℕ) (z : P) : ℂ :=
  (2 * π * I)⁻¹ * ∮ ζ in C(0, ρ), h (z, ζ) * diffCoeff b A i z ζ / polyEval b A z ζ

/-- The remainder, a polynomial of degree `< b` in `w`. -/
def divRem (x : P × ℂ) : ℂ :=
  ∑ i ∈ Finset.range b, remCoeff b A h ρ i x.1 * x.2 ^ i

variable {b A h ρ}

section Division
variable [NormedAddCommGroup P] [NormedSpace ℂ P] {U : Set P} {R : ℝ}

/-- Joint holomorphy gives holomorphy of every slice. -/
theorem differentiableOn_slice (hh : DifferentiableOn ℂ h (U ×ˢ ball 0 R)) {z : P} (hz : z ∈ U) :
    DifferentiableOn ℂ (fun ζ => h (z, ζ)) (ball 0 R) :=
  hh.comp ((differentiableOn_const z).prodMk differentiableOn_id) fun _ hζ => ⟨hz, hζ⟩

omit [NormedAddCommGroup P] [NormedSpace ℂ P] in
/-- **Weierstrass division by `W`**: `h = W · divQuot + divRem` on `U × D(0,ρ)`. -/
theorem division_eq (hρ : 0 < ρ) (hρR : ρ < R) (z : P)
    (hh : DifferentiableOn ℂ (fun ζ => h (z, ζ)) (ball 0 R))
    (hW : ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0) {w : ℂ} (hw : w ∈ ball (0 : ℂ) ρ) :
    h (z, w) = polyEval b A z w * divQuot b A h ρ (z, w) + divRem b A h ρ (z, w) := by
  set f : ℂ → ℂ := fun ζ => h (z, ζ) with hf
  have hfd : DifferentiableOn ℂ f (ball 0 R) := hh
  have hcl : closedBall (0 : ℂ) ρ ⊆ ball 0 R := closedBall_subset_ball hρR
  have hsph : sphere (0 : ℂ) ρ ⊆ ball 0 R := sphere_subset_ball hρR
  have hcauchy : (∮ ζ in C(0, ρ), f ζ / (ζ - w)) = 2 * π * I * f w :=
    circleIntegral_div_sub_of_differentiable_on_off_countable countable_empty hw
      (hfd.continuousOn.mono hcl) fun ζ hζ =>
        hfd.differentiableAt (isOpen_ball.mem_nhds (ball_subset_ball hρR.le hζ.1))
  have hne : ∀ ζ ∈ sphere (0 : ℂ) ρ, ζ - w ≠ 0 := by
    intro ζ hζ h0
    rw [sub_eq_zero] at h0
    rw [h0, mem_sphere_zero_iff_norm] at hζ
    rw [mem_ball_zero_iff, hζ] at hw
    exact lt_irrefl _ hw
  have hfc : ContinuousOn f (sphere 0 ρ) := hfd.continuousOn.mono hsph
  have hWc : ContinuousOn (polyEval b A z) (sphere 0 ρ) := (continuous_polyEval b A z).continuousOn
  have hpt : EqOn (fun ζ => f ζ / (ζ - w))
      (fun ζ => polyEval b A z w * (f ζ / (polyEval b A z ζ * (ζ - w))) +
        ∑ i ∈ Finset.range b, w ^ i * (f ζ * diffCoeff b A i z ζ / polyEval b A z ζ))
      (sphere 0 ρ) := by
    intro ζ hζ
    have hW0 := hW ζ hζ
    have hw0 := hne ζ hζ
    have hid := polyEval_sub_eq b A z ζ w
    simp only
    rw [show (∑ i ∈ Finset.range b, w ^ i * (f ζ * diffCoeff b A i z ζ / polyEval b A z ζ)) =
        f ζ / polyEval b A z ζ * ∑ i ∈ Finset.range b, diffCoeff b A i z ζ * w ^ i by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring]
    field_simp
    linear_combination (f ζ) * hid
  have hint₀ : CircleIntegrable
      (fun ζ => polyEval b A z w * (f ζ / (polyEval b A z ζ * (ζ - w)))) 0 ρ :=
    (continuousOn_const.mul (hfc.div (hWc.mul (continuousOn_id.sub continuousOn_const))
      fun ζ hζ => mul_ne_zero (hW ζ hζ) (hne ζ hζ))).circleIntegrable hρ.le
  have hcontᵢ : ∀ i ∈ Finset.range b, ContinuousOn
      (fun ζ => w ^ i * (f ζ * diffCoeff b A i z ζ / polyEval b A z ζ)) (sphere 0 ρ) :=
    fun i _ => continuousOn_const.mul ((hfc.mul (continuous_diffCoeff b A i z).continuousOn).div
      hWc fun ζ hζ => hW ζ hζ)
  have hintᵢ : ∀ i ∈ Finset.range b, CircleIntegrable
      (fun ζ => w ^ i * (f ζ * diffCoeff b A i z ζ / polyEval b A z ζ)) 0 ρ :=
    fun i hi => (hcontᵢ i hi).circleIntegrable hρ.le
  have hintS : CircleIntegrable (fun ζ => ∑ i ∈ Finset.range b,
      w ^ i * (f ζ * diffCoeff b A i z ζ / polyEval b A z ζ)) 0 ρ :=
    (continuousOn_finsetSum _ hcontᵢ).circleIntegrable hρ.le
  rw [circleIntegral.integral_congr hρ.le hpt, circleIntegral.integral_add hint₀ hintS,
    circleIntegral.integral_const_mul, circleIntegral.integral_fun_sum hintᵢ] at hcauchy
  simp only [circleIntegral.integral_const_mul] at hcauchy
  have h2pi : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hfw : f w = (2 * π * I)⁻¹ * (2 * π * I * f w) := by field_simp
  rw [show h (z, w) = f w from rfl, hfw, ← hcauchy, divRem, divQuot, mul_add, Finset.mul_sum]
  simp only [remCoeff]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun i _ => by ring

end Division

section Holomorphy
variable [NormedAddCommGroup P] [NormedSpace ℂ P]

/-- Holomorphic dependence of `∮ N(p,ζ)/D(p,ζ) dζ` on a finite-dimensional parameter `p`. -/
theorem differentiableAt_circleIntegral_div {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    [FiniteDimensional ℂ Q] {N D : Q × ℂ → ℂ} {O₀ : Set (Q × ℂ)} (hO₀ : IsOpen O₀)
    (hN : DifferentiableOn ℂ N O₀) (hD : DifferentiableOn ℂ D O₀) {ρ : ℝ} (hρ : 0 ≤ ρ) {p₀ : Q}
    (hp₀ : ∀ ζ ∈ sphere (0 : ℂ) ρ, (p₀, ζ) ∈ O₀ ∧ D (p₀, ζ) ≠ 0) :
    DifferentiableAt ℂ (fun p => ∮ ζ in C(0, ρ), N (p, ζ) / D (p, ζ)) p₀ := by
  have hO : IsOpen (O₀ ∩ D ⁻¹' {0}ᶜ) :=
    hD.continuousOn.isOpen_inter_preimage hO₀ isOpen_compl_singleton
  have hΨ : DifferentiableOn ℂ (fun q => N q * (D q)⁻¹) (O₀ ∩ D ⁻¹' {0}ᶜ) :=
    (hN.mono inter_subset_left).mul ((hD.mono inter_subset_left).inv
      fun q (hq : q ∈ O₀ ∩ D ⁻¹' {0}ᶜ) => hq.2)
  simp only [div_eq_mul_inv]
  exact RiemannExtension.differentiableAt_circleIntegral_param (Ψ := fun q => N q * (D q)⁻¹)
    hO hΨ hρ fun ζ hζ => ⟨(hp₀ ζ hζ).1, (hp₀ ζ hζ).2⟩

omit [NormedAddCommGroup P] [NormedSpace ℂ P] in
/-- For a FIXED parameter, the quotient is holomorphic in `w` on `D(0,ρ)` (no hypothesis on
the other parameters). -/
theorem differentiableOn_divQuot_slice {R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (z : P)
    (hh : DifferentiableOn ℂ (fun ζ => h (z, ζ)) (ball 0 R))
    (hW : ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0) :
    DifferentiableOn ℂ (fun w => divQuot b A h ρ (z, w)) (ball 0 ρ) := by
  have hO₀ : IsOpen ((univ : Set ℂ) ×ˢ ball (0 : ℂ) R) := isOpen_univ.prod isOpen_ball
  have hN : DifferentiableOn ℂ (fun q : ℂ × ℂ => h (z, q.2)) ((univ : Set ℂ) ×ˢ ball (0 : ℂ) R) :=
    hh.comp differentiableOn_snd fun q hq => hq.2
  have hD : DifferentiableOn ℂ (fun q : ℂ × ℂ => polyEval b A z q.2 * (q.2 - q.1))
      ((univ : Set ℂ) ×ˢ ball (0 : ℂ) R) :=
    ((differentiable_polyEval b A z).comp differentiable_snd).differentiableOn.mul
      (differentiableOn_snd.sub differentiableOn_fst)
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  refine (differentiableAt_circleIntegral_div hO₀ hN hD hρ.le fun ζ hζ => ?_).const_mul _
  refine ⟨⟨mem_univ _, sphere_subset_ball hρR hζ⟩, ?_⟩
  change polyEval b A z ζ * (ζ - w) ≠ 0
  refine mul_ne_zero (hW ζ hζ) fun h0 => ?_
  rw [sub_eq_zero] at h0
  rw [h0, mem_sphere_zero_iff_norm] at hζ
  rw [mem_ball_zero_iff, hζ] at hw
  exact lt_irrefl _ hw

variable [FiniteDimensional ℂ P] {U : Set P} {R : ℝ}

/-- The quotient is holomorphic on `U × D(0,ρ)`. -/
theorem differentiableOn_divQuot (hU : IsOpen U) (hA : ∀ k, DifferentiableOn ℂ (A k) U)
    (hρ : 0 < ρ) (hρR : ρ < R) (hh : DifferentiableOn ℂ h (U ×ˢ ball 0 R))
    (hW : ∀ z ∈ U, ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0) :
    DifferentiableOn ℂ (divQuot b A h ρ) (U ×ˢ ball 0 ρ) := by
  let L : (P × ℂ) × ℂ →L[ℂ] P × ℂ :=
    ((ContinuousLinearMap.fst ℂ P ℂ).comp (ContinuousLinearMap.fst ℂ (P × ℂ) ℂ)).prod
      (ContinuousLinearMap.snd ℂ (P × ℂ) ℂ)
  let L₂ : (P × ℂ) × ℂ →L[ℂ] ℂ :=
    ContinuousLinearMap.snd ℂ (P × ℂ) ℂ -
      (ContinuousLinearMap.snd ℂ P ℂ).comp (ContinuousLinearMap.fst ℂ (P × ℂ) ℂ)
  have hO₀ : IsOpen ((U ×ˢ (univ : Set ℂ)) ×ˢ ball (0 : ℂ) R) :=
    (hU.prod isOpen_univ).prod isOpen_ball
  have hN : DifferentiableOn ℂ (fun q : (P × ℂ) × ℂ => h (L q))
      ((U ×ˢ (univ : Set ℂ)) ×ˢ ball (0 : ℂ) R) :=
    hh.comp L.differentiableOn fun q hq => ⟨hq.1.1, hq.2⟩
  have hD : DifferentiableOn ℂ
      (fun q : (P × ℂ) × ℂ => polyEval b A (L q).1 (L q).2 * L₂ q)
      ((U ×ˢ (univ : Set ℂ)) ×ˢ ball (0 : ℂ) R) :=
    ((differentiableOn_polyEval b hA).comp L.differentiableOn
      fun q hq => ⟨hq.1.1, mem_univ _⟩).mul L₂.differentiableOn
  rintro ⟨z, w⟩ ⟨hz, hw⟩
  refine DifferentiableAt.differentiableWithinAt ?_
  refine (differentiableAt_circleIntegral_div hO₀ hN hD hρ.le fun ζ hζ => ?_).const_mul _
  refine ⟨⟨⟨hz, mem_univ _⟩, sphere_subset_ball hρR hζ⟩, ?_⟩
  change polyEval b A z ζ * (ζ - w) ≠ 0
  refine mul_ne_zero (hW z hz ζ hζ) fun h0 => ?_
  rw [sub_eq_zero] at h0
  rw [h0, mem_sphere_zero_iff_norm] at hζ
  rw [mem_ball_zero_iff, hζ] at hw
  exact lt_irrefl _ hw

/-- Every remainder coefficient is holomorphic on `U`. -/
theorem differentiableOn_remCoeff (hU : IsOpen U) (hA : ∀ k, DifferentiableOn ℂ (A k) U)
    (hρ : 0 < ρ) (hρR : ρ < R) (hh : DifferentiableOn ℂ h (U ×ˢ ball 0 R))
    (hW : ∀ z ∈ U, ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0) (i : ℕ) :
    DifferentiableOn ℂ (remCoeff b A h ρ i) U := by
  have hO₀ : IsOpen (U ×ˢ ball (0 : ℂ) R) := hU.prod isOpen_ball
  have hN : DifferentiableOn ℂ (fun q : P × ℂ => h q * diffCoeff b A i q.1 q.2)
      (U ×ˢ ball (0 : ℂ) R) :=
    hh.mul ((differentiableOn_diffCoeff b hA i).mono fun q hq => ⟨hq.1, mem_univ _⟩)
  have hD : DifferentiableOn ℂ (fun q : P × ℂ => polyEval b A q.1 q.2) (U ×ˢ ball (0 : ℂ) R) :=
    (differentiableOn_polyEval b hA).mono fun q hq => ⟨hq.1, mem_univ _⟩
  intro z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  exact (differentiableAt_circleIntegral_div hO₀ hN hD hρ.le fun ζ hζ =>
    ⟨⟨hz, sphere_subset_ball hρR hζ⟩, hW z hz ζ hζ⟩).const_mul _

/-- The remainder is holomorphic on `U × ℂ`. -/
theorem differentiableOn_divRem (hU : IsOpen U) (hA : ∀ k, DifferentiableOn ℂ (A k) U)
    (hρ : 0 < ρ) (hρR : ρ < R) (hh : DifferentiableOn ℂ h (U ×ˢ ball 0 R))
    (hW : ∀ z ∈ U, ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0) :
    DifferentiableOn ℂ (divRem b A h ρ) (U ×ˢ univ) :=
  DifferentiableOn.fun_sum fun i _ =>
    ((differentiableOn_remCoeff hU hA hρ hρR hh hW i).comp differentiableOn_fst
      fun _ hx => hx.1).mul (differentiableOn_snd.pow i)

end Holomorphy

/-! ## Uniform bounds -/

section Bounds

/-- Bound for the remainder coefficients, uniform in everything but the bounds of `h`, `W`
and the coefficients on the circle. -/
theorem norm_remCoeff_le (hρ : 0 < ρ) (i : ℕ) (z : P) {M B m : ℝ} (hm : 0 < m)
    (hM : ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖h (z, ζ)‖ ≤ M)
    (hB : ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖diffCoeff b A i z ζ‖ ≤ B)
    (hmW : ∀ ζ ∈ sphere (0 : ℂ) ρ, m ≤ ‖polyEval b A z ζ‖) :
    ‖remCoeff b A h ρ i z‖ ≤ ρ * (M * B / m) := by
  unfold remCoeff
  rw [← smul_eq_mul]
  refine circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ.le fun ζ hζ => ?_
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ζ hζ)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB ζ hζ)
  have hWpos : 0 < ‖polyEval b A z ζ‖ := hm.trans_le (hmW ζ hζ)
  rw [norm_div, norm_mul]
  calc ‖h (z, ζ)‖ * ‖diffCoeff b A i z ζ‖ / ‖polyEval b A z ζ‖
      ≤ M * B / ‖polyEval b A z ζ‖ := by
        gcongr
        · exact hM ζ hζ
        · exact hB ζ hζ
    _ ≤ M * B / m := by
        gcongr
        exact hmW ζ hζ

/-- Bound for the quotient on `|w| < ρ`. -/
theorem norm_divQuot_le (hρ : 0 < ρ) (z : P) {w : ℂ} (hw : ‖w‖ < ρ) {M m : ℝ} (hm : 0 < m)
    (hM : ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖h (z, ζ)‖ ≤ M)
    (hmW : ∀ ζ ∈ sphere (0 : ℂ) ρ, m ≤ ‖polyEval b A z ζ‖) :
    ‖divQuot b A h ρ (z, w)‖ ≤ ρ * (M / (m * (ρ - ‖w‖))) := by
  unfold divQuot
  rw [← smul_eq_mul]
  refine circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hρ.le fun ζ hζ => ?_
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM ζ hζ)
  have hζn : ‖ζ‖ = ρ := mem_sphere_zero_iff_norm.mp hζ
  have hgap : ρ - ‖w‖ ≤ ‖ζ - w‖ := by
    have := norm_sub_norm_le ζ w
    rw [hζn] at this
    exact this
  have hgap0 : 0 < ρ - ‖w‖ := sub_pos.mpr hw
  simp only
  rw [norm_div, norm_mul]
  calc ‖h (z, ζ)‖ / (‖polyEval b A z ζ‖ * ‖ζ - w‖) ≤ M / (‖polyEval b A z ζ‖ * ‖ζ - w‖) := by
        gcongr
        exact hM ζ hζ
    _ ≤ M / (m * (ρ - ‖w‖)) := by
        gcongr
        exact hmW ζ hζ

end Bounds

/-! ## Uniqueness -/

section Uniqueness

private theorem eq_zero_aux {ρ : ℝ} (n : ℕ) :
    ∀ (W r : ℂ[X]) (q : ℂ → ℂ), W.Monic → W.natDegree = n →
      (∀ α, W.IsRoot α → α ∈ ball (0 : ℂ) ρ) → (r = 0 ∨ r.natDegree < n) →
      ContinuousOn q (ball 0 ρ) → (∀ w ∈ ball (0 : ℂ) ρ, q w * W.eval w = r.eval w) → r = 0 := by
  induction n with
  | zero =>
    intro W r q _ _ _ hr _ _
    rcases hr with hr | hr
    · exact hr
    · exact absurd hr (Nat.not_lt_zero _)
  | succ n ih =>
    intro W r q hW hdeg hroots hr hq heq
    by_cases hr0 : r = 0
    · exact hr0
    have hr' : r.natDegree < n + 1 := hr.resolve_left hr0
    have hpos : 0 < W.degree := by
      rw [Polynomial.degree_eq_natDegree hW.ne_zero, hdeg]
      exact_mod_cast Nat.succ_pos n
    obtain ⟨α, hα⟩ := Complex.exists_root hpos
    have hαb := hroots α hα
    have hrα : r.IsRoot α := by
      change r.eval α = 0
      rw [← heq α hαb, hα.eq_zero, mul_zero]
    set W' := W /ₘ (X - C α) with hW'def
    set r' := r /ₘ (X - C α) with hr'def
    have hWfac : (X - C α) * W' = W := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hα
    have hrfac : (X - C α) * r' = r := Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hrα
    have hW'm : W'.Monic := (Polynomial.monic_X_sub_C α).of_mul_monic_left (hWfac ▸ hW)
    have hW'deg : W'.natDegree = n := by
      have := (Polynomial.monic_X_sub_C α).natDegree_mul hW'm
      rw [hWfac, hdeg, Polynomial.natDegree_X_sub_C] at this
      omega
    have hr'0 : r' ≠ 0 := by
      rintro h0
      rw [h0, mul_zero] at hrfac
      exact hr0 hrfac.symm
    have hr'deg : r'.natDegree < n := by
      have := Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero α) hr'0
      rw [hrfac, Polynomial.natDegree_X_sub_C] at this
      omega
    have hroots' : ∀ β, W'.IsRoot β → β ∈ ball (0 : ℂ) ρ := by
      intro β hβ
      refine hroots β ?_
      change W.eval β = 0
      rw [← hWfac, Polynomial.eval_mul, hβ.eq_zero, mul_zero]
    -- the reduced equation, first off `α`, then everywhere by continuity
    have hoff : EqOn (fun w => q w * W'.eval w) (fun w => r'.eval w) (ball 0 ρ ∩ {α}ᶜ) := by
      intro w ⟨hw, hwα⟩
      have hwα' : w - α ≠ 0 := sub_ne_zero.mpr hwα
      have h1 := heq w hw
      rw [← hWfac, ← hrfac, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C] at h1
      apply mul_left_cancel₀ hwα'
      linear_combination h1
    have hred : EqOn (fun w => q w * W'.eval w) (fun w => r'.eval w) (ball 0 ρ) :=
      hoff.of_subset_closure (hq.mul (Polynomial.continuous _).continuousOn)
        (Polynomial.continuous _).continuousOn inter_subset_left
        ((dense_compl_singleton α).open_subset_closure_inter isOpen_ball)
    exact absurd (ih W' r' q hW'm hW'deg hroots' (Or.inr hr'deg) hq fun w hw => hred hw) hr'0

/-- **Uniqueness of the remainder.** If `W` is monic with all its roots in `D(0,ρ)`, `q` is
continuous on `D(0,ρ)`, `r` is a polynomial of smaller degree and `q W = r` on `D(0,ρ)`,
then `r = 0`. -/
theorem eq_zero_of_mul_eval_eq {ρ : ℝ} (W r : ℂ[X]) (hW : W.Monic)
    (hroots : ∀ α, W.IsRoot α → α ∈ ball (0 : ℂ) ρ) (hr : r.natDegree < W.natDegree ∨ r = 0)
    (q : ℂ → ℂ) (hq : ContinuousOn q (ball 0 ρ))
    (heq : ∀ w ∈ ball (0 : ℂ) ρ, q w * W.eval w = r.eval w) : r = 0 :=
  eq_zero_aux W.natDegree W r q hW rfl hroots hr.symm hq heq

/-- **Uniqueness of the division.** If `W` is monic of degree `b` with all its roots in
`D(0,ρ)` and `q₁ W + ∑_{i<b} c₁ᵢ wⁱ = q₂ W + ∑_{i<b} c₂ᵢ wⁱ` on `D(0,ρ)` with `q₁, q₂`
continuous there, then the remainders and the quotients agree. -/
theorem division_unique {ρ : ℝ} (W : ℂ[X]) (hW : W.Monic) {b : ℕ} (hdeg : W.natDegree = b)
    (hroots : ∀ α, W.IsRoot α → α ∈ ball (0 : ℂ) ρ) (q₁ q₂ : ℂ → ℂ)
    (hq₁ : ContinuousOn q₁ (ball 0 ρ)) (hq₂ : ContinuousOn q₂ (ball 0 ρ)) (c₁ c₂ : ℕ → ℂ)
    (heq : ∀ w ∈ ball (0 : ℂ) ρ, q₁ w * W.eval w + ∑ i ∈ Finset.range b, c₁ i * w ^ i =
      q₂ w * W.eval w + ∑ i ∈ Finset.range b, c₂ i * w ^ i) :
    (∀ i < b, c₁ i = c₂ i) ∧ EqOn q₁ q₂ (ball 0 ρ) := by
  set r : ℂ[X] := ∑ i ∈ Finset.range b, C (c₂ i - c₁ i) * X ^ i with hrdef
  have hreval : ∀ w, r.eval w = ∑ i ∈ Finset.range b, c₂ i * w ^ i -
      ∑ i ∈ Finset.range b, c₁ i * w ^ i := by
    intro w
    rw [hrdef, Polynomial.eval_finsetSum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]; ring
  have hrcoeff : ∀ i, r.coeff i = if i < b then c₂ i - c₁ i else 0 := by
    intro i
    rw [hrdef, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  have hrdeg : r.natDegree < W.natDegree ∨ r = 0 := by
    by_cases hr0 : r = 0
    · exact Or.inr hr0
    left
    rw [hdeg]
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb
      exfalso
      apply hr0
      ext i
      rw [hrcoeff, Polynomial.coeff_zero]
      simp
    · rw [Polynomial.natDegree_lt_iff_degree_lt hr0, Polynomial.degree_lt_iff_coeff_zero]
      intro i hi
      rw [hrcoeff, if_neg]
      exact_mod_cast not_lt.mpr hi
  have hr0 : r = 0 := eq_zero_of_mul_eval_eq W r hW hroots hrdeg (fun w => q₁ w - q₂ w)
    (hq₁.sub hq₂) fun w hw => by
      rw [hreval]
      linear_combination heq w hw
  have hc : ∀ i < b, c₁ i = c₂ i := by
    intro i hi
    have := hrcoeff i
    rw [hr0, Polynomial.coeff_zero, if_pos hi] at this
    linear_combination this
  refine ⟨hc, ?_⟩
  have hsum : ∀ w, ∑ i ∈ Finset.range b, c₁ i * w ^ i = ∑ i ∈ Finset.range b, c₂ i * w ^ i :=
    fun w => Finset.sum_congr rfl fun i hi => by rw [hc i (Finset.mem_range.mp hi)]
  have hfin : (W.rootSet ℂ).Finite := Polynomial.rootSet_finite W ℂ
  have hoff : EqOn q₁ q₂ (ball 0 ρ ∩ (W.rootSet ℂ)ᶜ) := by
    intro w ⟨hw, hwr⟩
    have hWw : W.eval w ≠ 0 := by
      intro h0
      apply hwr
      rw [Polynomial.mem_rootSet]
      exact ⟨hW.ne_zero, by simpa [Polynomial.aeval_def] using h0⟩
    have h1 := heq w hw
    rw [hsum w, add_left_inj] at h1
    exact mul_right_cancel₀ hWw h1
  exact hoff.of_subset_closure hq₁ hq₂ inter_subset_left
    ((Set.Countable.dense_compl ℂ (Set.Finite.countable hfin)).open_subset_closure_inter isOpen_ball)

/-- The monic polynomial `X^b + ∑_{k<b} A_k(z) X^k`. -/
def toPoly (b : ℕ) (A : ℕ → P → ℂ) (z : P) : ℂ[X] :=
  X ^ b + ∑ k ∈ Finset.range b, C (A k z) * X ^ k

theorem toPoly_low_degree (b : ℕ) (A : ℕ → P → ℂ) (z : P) :
    (∑ k ∈ Finset.range b, C (A k z) * X ^ k).degree < (b : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro i hi
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  rw [if_neg]
  exact_mod_cast not_lt.mpr hi

theorem toPoly_monic (b : ℕ) (A : ℕ → P → ℂ) (z : P) : (toPoly b A z).Monic :=
  Polynomial.monic_X_pow_add (toPoly_low_degree b A z)

theorem toPoly_natDegree (b : ℕ) (A : ℕ → P → ℂ) (z : P) : (toPoly b A z).natDegree = b := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [toPoly, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
  rw [Polynomial.degree_X_pow]
  exact toPoly_low_degree b A z

theorem eval_toPoly {b : ℕ} {A : ℕ → P → ℂ} {z : P} (hmon : A b z = 1) (w : ℂ) :
    (toPoly b A z).eval w = polyEval b A z w := by
  rw [toPoly, polyEval, Finset.sum_range_succ, hmon, one_mul, add_comm, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_finsetSum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-- **Uniqueness of the Weierstrass data.** If `W(z,·)` is monic of degree `b` with all its
roots in `D(0,ρ)`, every division `h(z,·) = W(z,·) q + ∑_{i<b} cᵢ wⁱ` on `D(0,ρ)` with `q`
continuous is the Cauchy division: `cᵢ = remCoeff i z` and `q = divQuot (z,·)`. -/
theorem eq_divQuot_remCoeff [NormedAddCommGroup P] [NormedSpace ℂ P] {b : ℕ} {A : ℕ → P → ℂ}
    {h : P × ℂ → ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ < R) (z : P)
    (hh : DifferentiableOn ℂ (fun ζ => h (z, ζ)) (ball 0 R)) (hmon : A b z = 1)
    (hroots : ∀ α, polyEval b A z α = 0 → α ∈ ball (0 : ℂ) ρ)
    (q : ℂ → ℂ) (hq : ContinuousOn q (ball 0 ρ)) (c : ℕ → ℂ)
    (hdiv : ∀ w ∈ ball (0 : ℂ) ρ, h (z, w) = polyEval b A z w * q w +
      ∑ i ∈ Finset.range b, c i * w ^ i) :
    (∀ i < b, c i = remCoeff b A h ρ i z) ∧ EqOn q (fun w => divQuot b A h ρ (z, w)) (ball 0 ρ) := by
  have hW : ∀ ζ ∈ sphere (0 : ℂ) ρ, polyEval b A z ζ ≠ 0 := by
    intro ζ hζ h0
    have := hroots ζ h0
    rw [mem_ball_zero_iff, mem_sphere_zero_iff_norm.mp hζ] at this
    exact lt_irrefl _ this
  have hq₀ : ContinuousOn (fun w => divQuot b A h ρ (z, w)) (ball 0 ρ) :=
    (differentiableOn_divQuot_slice hρ hρR z hh hW).continuousOn
  have hroots' : ∀ α, (toPoly b A z).IsRoot α → α ∈ ball (0 : ℂ) ρ := by
    intro α hα
    apply hroots α
    rw [← eval_toPoly hmon]
    exact hα
  refine division_unique (toPoly b A z) (toPoly_monic b A z) (toPoly_natDegree b A z) hroots'
    q _ hq hq₀ c (fun i => remCoeff b A h ρ i z) fun w hw => ?_
  rw [eval_toPoly hmon, mul_comm (q w), mul_comm (divQuot b A h ρ (z, w)), ← hdiv w hw]
  exact division_eq hρ hρR z hh hW hw

end Uniqueness

end
end Hironaka.HironakaG10FlatDiscWeierstrassDivision
