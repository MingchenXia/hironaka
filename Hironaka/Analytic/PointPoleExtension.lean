import Hironaka.Analytic.OTWeakDbar
import Hironaka.Analytic.OTChenExtension
import Hironaka.Analytic.WeakDbarWeyl
import Hironaka.Analytic.HormanderL2Theorem
import Hironaka.Analytic.WeightedL2ExtensionLimit
import Hironaka.Analytic.PotentialTheory.LogLevi
import Hironaka.Manifold.HolomorphicContDiff

set_option autoImplicit false

/-!
# `L²` extension from a point with a logarithmic pole

This is the analytic core of Step 2 of Copy-4 `lem:regularization`, the `O(1/m)` comparison of
Bergman-kernel overlaps: an `L²`-extension *from a point* obtained from Hörmander's estimate with
a logarithmic pole weight (Demailly, *Complex Analytic and Differential Geometry*, Ch. VIII §6;
Hörmander, *An introduction to complex analysis in several variables*, §4.4).

Fix `x` in a bounded convex open `D ⊆ {‖z‖ < R}` of `ComplexModel d`, a smooth cut-off `θ`
with `0 ≤ θ ≤ 1`, compact support in `D` and `θ ≡ 1` on `Metric.ball x r`, and `f` holomorphic
near `tsupport θ`.  The `(0,1)`-form `v_j = f · ∂̄_j θ` is smooth, `∂̄`-closed and supported in
`tsupport θ \ ball x r`.  Solving `∂̄ u = v` with Hörmander's estimate for the weight

  `Φ_δ = ϕ + d · log (‖z - x‖² + δ²) + ‖z‖²`

(`poleWeight`) produces `u_δ` with `∫ |u_δ|² e^{-Φ_δ} ≤ (1+t) ∫ ‖v‖² e^{-Φ_δ}`, and since
`‖z - x‖ ≥ r` on the support of `v` the right-hand side is bounded by
`(1+t) M_θ² r^{-2d} ∫_{tsupport θ} |f|² e^{-ϕ}`, uniformly in `δ`.  Then `F_δ = θ f - u_δ` is
holomorphic (Weyl's lemma) and `F_δ (x) → f (x)` as `δ → 0` because a nonzero value of
`θ f - F` at `x` would make `‖z - x‖^{-2d}` integrable near `x`.

## Main contents

* `polePotential`, `poleWeight`: the regularized logarithmic pole and the Hörmander weight,
  with `leviForm_poleWeight_ge`: the Levi form of `Φ_δ` dominates `‖ξ‖²`;
* `poleForm`: the `∂̄`-closed datum `v_j = f · ∂̄_j θ`;
* `exists_holomorphic_poleSolution`: one application of Hörmander's estimate at a fixed `δ`,
  in the shape of `Hironaka.OTChen.exists_holomorphic_minimal_solution`.
-/

open Set Filter MeasureTheory Complex Metric
open scoped Topology ContDiff ComplexConjugate ENNReal

namespace Hironaka.PointPole

noncomputable section

open CauchyGreen Hormander OTChen

variable {d : ℕ} {p : ℕ}

/-! ### The regularized logarithmic pole -/

/-- The regularized logarithmic pole at `x`: `log (‖z - x‖² + δ²)`. -/
def polePotential (x : ComplexModel d) (δ : ℝ) (z : ComplexModel d) : ℝ :=
  Real.log (‖z - x‖ ^ 2 + δ ^ 2)

theorem polePotential_eq (x : ComplexModel d) (δ : ℝ) (z : ComplexModel d) :
    polePotential x δ z = regularizedLogNormSq (δ ^ 2) (z - x) := rfl

theorem contDiff_polePotential {δ : ℝ} (hδ : 0 < δ) (x : ComplexModel d) {n : ℕ∞ω} :
    ContDiff ℝ n (polePotential x δ) :=
  (contDiff_regularizedLogNormSq (H := ComplexModel d) (by positivity)).comp
    (contDiff_id.sub contDiff_const)

/-- The Levi form is invariant under translation of the argument. -/
theorem leviForm_comp_sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] {u : E → ℝ} (hu : ContDiff ℝ 2 u) (c z v : E) :
    leviForm (fun y ↦ u (y - c)) z v = leviForm u (z - c) v := by
  have key : ∀ a b : E, realHessian (fun y ↦ u (y - c)) z a b = realHessian u (z - c) a b := by
    intro a b
    have h := realHessian_comp_affine hu (ContinuousLinearMap.id ℝ E) (-c) z a b
    simpa only [ContinuousLinearMap.coe_id', id_eq, neg_add_eq_sub] using h
  simp only [leviForm, key]

theorem leviForm_polePotential_nonneg {δ : ℝ} (hδ : 0 < δ) (x z v : ComplexModel d) :
    0 ≤ leviForm (polePotential x δ) z v := by
  have hc : ContDiff ℝ 2 (regularizedLogNormSq (E := ComplexModel d) (δ ^ 2)) :=
    contDiff_regularizedLogNormSq (by positivity)
  have : leviForm (polePotential x δ) z v =
      leviForm (regularizedLogNormSq (E := ComplexModel d) (δ ^ 2)) (z - x) v :=
    leviForm_comp_sub hc x z v
  rw [this]
  exact leviForm_regularizedLogNormSq_nonneg (by positivity) _ _

/-! ### The Hörmander weight with a logarithmic pole -/

/-- The Hörmander weight `Φ_δ = ϕ + d · log (‖z - x‖² + δ²) + ‖z‖²`. -/
def poleWeight (p : ℕ) (ϕ : ComplexModel d → ℝ) (x : ComplexModel d) (δ : ℝ)
    (z : ComplexModel d) : ℝ :=
  ϕ z + (p : ℝ) * polePotential x δ z + ‖z‖ ^ 2

theorem contDiffOn_poleWeight {D : Set (ComplexModel d)} {ϕ : ComplexModel d → ℝ}
    (hϕ : ContDiffOn ℝ ∞ ϕ D) {δ : ℝ} (hδ : 0 < δ) (x : ComplexModel d) :
    ContDiffOn ℝ ∞ (poleWeight p ϕ x δ) D :=
  (hϕ.add (contDiff_const.mul (contDiff_polePotential hδ x)).contDiffOn).add
    (contDiff_norm_sq ℝ).contDiffOn

/-- **The Levi form of the pole weight dominates the Euclidean one.** -/
theorem leviForm_poleWeight_ge {D : Set (ComplexModel d)} (hDo : IsOpen D)
    {ϕ : ComplexModel d → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) {δ : ℝ} (hδ : 0 < δ) (x : ComplexModel d)
    {z : ComplexModel d} (hz : z ∈ D) (ξ : ComplexModel d) :
    ‖ξ‖ ^ 2 ≤ leviForm (poleWeight p ϕ x δ) z ξ := by
  have h1 : ContDiffAt ℝ 2 ϕ z :=
    ((hϕ z hz).contDiffAt (hDo.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top)
  have h2 : ContDiffAt ℝ 2 (fun y ↦ (p : ℝ) * polePotential x δ y) z :=
    (contDiff_const.mul (contDiff_polePotential hδ x)).contDiffAt
  have h3 : ContDiffAt ℝ 2 (fun y : ComplexModel d ↦ ‖y‖ ^ 2) z :=
    (contDiff_norm_sq ℝ).contDiffAt
  have hsum : leviForm (poleWeight p ϕ x δ) z ξ =
      (leviForm ϕ z ξ + leviForm (fun y ↦ (p : ℝ) * polePotential x δ y) z ξ) +
        leviForm (fun y : ComplexModel d ↦ ‖y‖ ^ 2) z ξ := by
    have e1 : leviForm ((ϕ + fun y ↦ (p : ℝ) * polePotential x δ y) +
        fun y : ComplexModel d ↦ ‖y‖ ^ 2) z ξ =
        leviForm (ϕ + fun y ↦ (p : ℝ) * polePotential x δ y) z ξ +
          leviForm (fun y : ComplexModel d ↦ ‖y‖ ^ 2) z ξ := leviForm_add (h1.add h2) h3 ξ
    have e2 : leviForm (ϕ + fun y ↦ (p : ℝ) * polePotential x δ y) z ξ =
        leviForm ϕ z ξ + leviForm (fun y ↦ (p : ℝ) * polePotential x δ y) z ξ :=
      leviForm_add h1 h2 ξ
    rw [show poleWeight p ϕ x δ =
      (ϕ + fun y ↦ (p : ℝ) * polePotential x δ y) + fun y : ComplexModel d ↦ ‖y‖ ^ 2 from rfl,
      e1, e2]
  rw [hsum, leviForm_norm_sq]
  have hd : leviForm (fun y ↦ (p : ℝ) * polePotential x δ y) z ξ =
      (p : ℝ) * leviForm (polePotential x δ) z ξ :=
    leviForm_smul (contDiff_polePotential hδ x).contDiffAt (p : ℝ) ξ
  have := hϕL z hz ξ
  have hpp := leviForm_polePotential_nonneg hδ x z ξ
  have hdn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [hd]
  nlinarith

/-! ### Elementary bounds on `e^{-Φ_δ}` -/

theorem exp_neg_poleWeight (ϕ : ComplexModel d → ℝ) (x : ComplexModel d) {δ : ℝ} (hδ : 0 < δ)
    (z : ComplexModel d) :
    Real.exp (-poleWeight p ϕ x δ z) =
      Real.exp (-ϕ z) * ((‖z - x‖ ^ 2 + δ ^ 2) ^ p)⁻¹ * Real.exp (-‖z‖ ^ 2) := by
  have hA : (0 : ℝ) < ‖z - x‖ ^ 2 + δ ^ 2 := by positivity
  have hlog : (p : ℝ) * polePotential x δ z = Real.log ((‖z - x‖ ^ 2 + δ ^ 2) ^ p) := by
    rw [polePotential, Real.log_pow]
  rw [poleWeight, hlog, show -(ϕ z + Real.log ((‖z - x‖ ^ 2 + δ ^ 2) ^ p) + ‖z‖ ^ 2) =
    -ϕ z + -Real.log ((‖z - x‖ ^ 2 + δ ^ 2) ^ p) + -‖z‖ ^ 2 by ring, Real.exp_add, Real.exp_add,
    Real.exp_neg (Real.log ((‖z - x‖ ^ 2 + δ ^ 2) ^ p)), Real.exp_log (by positivity)]

/-- On `D` the weight `e^{-Φ_δ-l}` is bounded by `e^{B_ϕ} δ^{-2d}`, for every `l ≥ 0`. -/
theorem exp_neg_poleWeight_add_le_of_bddBelow {ϕ : ComplexModel d → ℝ} {Bϕ : ℝ}
    (x : ComplexModel d) {δ : ℝ} (hδ : 0 < δ) {z : ComplexModel d} (hBϕ : -Bϕ ≤ ϕ z)
    {l : ℝ} (hl : 0 ≤ l) :
    Real.exp (-(poleWeight p ϕ x δ z + l)) ≤ Real.exp Bϕ * ((δ ^ 2) ^ p)⁻¹ := by
  have hd2 : (0 : ℝ) < δ ^ 2 := by positivity
  have e1 : Real.exp (-(poleWeight p ϕ x δ z + l)) =
      Real.exp (-poleWeight p ϕ x δ z) * Real.exp (-l) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, exp_neg_poleWeight ϕ x hδ z]
  have b1 : Real.exp (-ϕ z) ≤ Real.exp Bϕ := Real.exp_le_exp.mpr (by linarith)
  have hδle : (δ : ℝ) ^ 2 ≤ ‖z - x‖ ^ 2 + δ ^ 2 := by nlinarith [sq_nonneg ‖z - x‖]
  have b2 : ((‖z - x‖ ^ 2 + δ ^ 2) ^ p)⁻¹ ≤ ((δ ^ 2) ^ p)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ hd2.le hδle p)
  have s1 : Real.exp (-ϕ z) * ((‖z - x‖ ^ 2 + δ ^ 2) ^ p)⁻¹ ≤
      Real.exp Bϕ * ((δ ^ 2) ^ p)⁻¹ :=
    mul_le_mul b1 b2 (by positivity) (Real.exp_pos _).le
  have s2 : Real.exp (-‖z‖ ^ 2) * Real.exp (-l) ≤ 1 := by
    have b3 : Real.exp (-‖z‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
    have b4 : Real.exp (-l) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [Real.exp_pos (-‖z‖ ^ 2), Real.exp_pos (-l)]
  calc Real.exp (-ϕ z) * ((‖z - x‖ ^ 2 + δ ^ 2) ^ p)⁻¹ * Real.exp (-‖z‖ ^ 2) * Real.exp (-l)
      = Real.exp (-ϕ z) * ((‖z - x‖ ^ 2 + δ ^ 2) ^ p)⁻¹ *
          (Real.exp (-‖z‖ ^ 2) * Real.exp (-l)) := by ring
    _ ≤ Real.exp Bϕ * ((δ ^ 2) ^ p)⁻¹ * 1 :=
        mul_le_mul s1 s2 (by positivity) (by positivity)
    _ = Real.exp Bϕ * ((δ ^ 2) ^ p)⁻¹ := by ring

/-! ### The `∂̄`-closed datum `v_j = f · ∂̄_j θ` -/

section Dbar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- `∂̄_v` is bounded by the full derivative. -/
theorem norm_dbarDir_le (F : E → ℂ) (z v : E) : ‖dbarDir v F z‖ ≤ ‖fderiv ℝ F z‖ * ‖v‖ := by
  have h1 : ‖fderiv ℝ F z v‖ ≤ ‖fderiv ℝ F z‖ * ‖v‖ := (fderiv ℝ F z).le_opNorm v
  have h2 : ‖fderiv ℝ F z (Complex.I • v)‖ ≤ ‖fderiv ℝ F z‖ * ‖v‖ := by
    refine ((fderiv ℝ F z).le_opNorm _).trans_eq ?_
    rw [norm_smul, Complex.norm_I, one_mul]
  have h3 : ‖Complex.I * fderiv ℝ F z (Complex.I • v)‖ = ‖fderiv ℝ F z (Complex.I • v)‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  rw [dbarDir, norm_div, Complex.norm_ofNat]
  have := norm_add_le (fderiv ℝ F z v) (Complex.I * fderiv ℝ F z (Complex.I • v))
  rw [h3] at this
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  linarith

omit [FiniteDimensional ℂ E] in
/-- The real-to-complex coercion does not increase the derivative norm. -/
theorem norm_fderiv_ofReal_le {θ : E → ℝ} {z : E} (h : DifferentiableAt ℝ θ z) :
    ‖fderiv ℝ (fun y ↦ ((θ y : ℝ) : ℂ)) z‖ ≤ ‖fderiv ℝ θ z‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w ↦ ?_
  rw [fderiv_ofReal_comp_apply h w, Complex.norm_real]
  exact (fderiv ℝ θ z).le_opNorm w

omit [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
theorem support_ofReal_comp (θ : E → ℝ) :
    Function.support (fun y ↦ ((θ y : ℝ) : ℂ)) = Function.support θ := by
  ext y; simp [Function.mem_support]

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
theorem tsupport_ofReal_comp (θ : E → ℝ) :
    tsupport (fun y ↦ ((θ y : ℝ) : ℂ)) = tsupport θ := by
  rw [tsupport, tsupport, support_ofReal_comp]

end Dbar

/-- A product `a h` with `a` continuous on an open set containing `tsupport h` is continuous;
the version of `Hironaka.OTChen.continuous_mul_of_tsupport_subset` for any target. -/
theorem continuous_mul_of_tsupport_subset' {X : Type*} [TopologicalSpace X] {M : Type*}
    [TopologicalSpace M] [MulZeroClass M] [ContinuousMul M] {W : Set X} (hW : IsOpen W)
    {a h : X → M} (ha : ContinuousOn a W) (hh : Continuous h) (hts : tsupport h ⊆ W) :
    Continuous fun y ↦ a y * h y := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hy : y ∈ W
  · exact ((ha y hy).continuousAt (hW.mem_nhds hy)).mul hh.continuousAt
  · have hny : y ∉ tsupport h := fun h' ↦ hy (hts h')
    refine (continuousAt_const (y := (0 : M))).congr ?_
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hny] with z hz
    simp [hz]

/-- Outside `tsupport θ` the derivative of `θ` vanishes. -/
theorem fderiv_eq_zero_of_notMem_tsupport {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {θ : E → ℝ} {z : E} (hz : z ∉ tsupport θ) : fderiv ℝ θ z = 0 := by
  have hev : θ =ᶠ[𝓝 z] fun _ ↦ 0 := notMem_tsupport_iff_eventuallyEq.mp hz
  rw [hev.fderiv_eq]
  simp

theorem tsupport_normSq_fderiv_subset {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : E → ℝ) : tsupport (fun z ↦ ‖fderiv ℝ θ z‖ ^ 2) ⊆ tsupport θ := by
  refine closure_minimal (fun z hz ↦ ?_) (isClosed_tsupport θ)
  by_contra hnz
  exact hz (by simp [fderiv_eq_zero_of_notMem_tsupport hnz])

/-- The cut-off product `θ f`, extended by zero off the support of `θ`. -/
def cutProd (θ : ComplexModel d → ℝ) (f : ComplexModel d → ℂ) (z : ComplexModel d) : ℂ :=
  ((θ z : ℝ) : ℂ) * f z

/-- The components of the `(0,1)`-form `∂̄ (θ f) = f ∂̄ θ`. -/
def poleForm (θ : ComplexModel d → ℝ) (f : ComplexModel d → ℂ) (j : Fin d)
    (z : ComplexModel d) : ℂ :=
  f z * dbarDir (coordVec j) (fun y ↦ ((θ y : ℝ) : ℂ)) z

/-- The Levi majorant `‖f‖² ‖dθ‖²` of the datum `v = f ∂̄ θ`. -/
def poleMajorant (θ : ComplexModel d → ℝ) (f : ComplexModel d → ℂ) (z : ComplexModel d) : ℝ :=
  ‖f z‖ ^ 2 * ‖fderiv ℝ θ z‖ ^ 2

theorem poleMajorant_nonneg (θ : ComplexModel d → ℝ) (f : ComplexModel d → ℂ)
    (z : ComplexModel d) : 0 ≤ poleMajorant θ f z := by
  unfold poleMajorant; positivity

theorem poleMajorant_eq_zero_of_notMem_tsupport {θ : ComplexModel d → ℝ}
    {f : ComplexModel d → ℂ} {z : ComplexModel d} (hz : z ∉ tsupport θ) :
    poleMajorant θ f z = 0 := by
  simp [poleMajorant, fderiv_eq_zero_of_notMem_tsupport hz]

theorem poleMajorant_le {θ : ComplexModel d → ℝ} {f : ComplexModel d → ℂ} {Mθ : ℝ}
    (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ) (z : ComplexModel d) :
    poleMajorant θ f z ≤ Mθ ^ 2 * ‖f z‖ ^ 2 := by
  have h : ‖fderiv ℝ θ z‖ ^ 2 ≤ Mθ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hMθ z) 2
  have : (0 : ℝ) ≤ ‖f z‖ ^ 2 := by positivity
  simp only [poleMajorant]
  nlinarith

theorem poleMajorant_le_const {θ : ComplexModel d → ℝ} {f : ComplexModel d → ℂ} {Mθ Mf : ℝ}
    (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ) (hMf : ∀ z ∈ tsupport θ, ‖f z‖ ≤ Mf) (z : ComplexModel d) :
    poleMajorant θ f z ≤ Mθ ^ 2 * Mf ^ 2 := by
  have hMθ0 : 0 ≤ Mθ := (norm_nonneg _).trans (hMθ z)
  by_cases hz : z ∈ tsupport θ
  · have h1 := hMf z hz
    have hMf0 : 0 ≤ Mf := (norm_nonneg _).trans h1
    refine (poleMajorant_le hMθ z).trans ?_
    have : ‖f z‖ ^ 2 ≤ Mf ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith
  · rw [poleMajorant_eq_zero_of_notMem_tsupport hz]
    positivity

section CutOff

variable {W : Set (ComplexModel d)} {θ : ComplexModel d → ℝ} {f : ComplexModel d → ℂ}

theorem contDiff_ofReal_theta (hθ : ContDiff ℝ ∞ θ) :
    ContDiff ℝ ∞ fun y ↦ ((θ y : ℝ) : ℂ) :=
  Complex.ofRealCLM.contDiff.comp hθ

theorem tsupport_ofReal_theta_subset (hts : tsupport θ ⊆ W) :
    tsupport (fun y ↦ ((θ y : ℝ) : ℂ)) ⊆ W := by
  rw [tsupport_ofReal_comp]; exact hts

/-- `θ f` is globally smooth: `f` is smooth on `W` and `θ` vanishes near every point off `W`. -/
theorem contDiff_cutProd (hW : IsOpen W) (hθ : ContDiff ℝ ∞ θ)
    (hf : DifferentiableOn ℂ f W) (hts : tsupport θ ⊆ W) : ContDiff ℝ ∞ (cutProd θ f) := by
  have h := contDiff_mul_of_tsupport_subset (k := (∞ : WithTop ℕ∞)) hW
    (contDiffOn_real_of_differentiableOn_complex hf hW) (contDiff_ofReal_theta hθ)
    (tsupport_ofReal_theta_subset hts)
  have e : cutProd θ f = fun y ↦ f y * ((θ y : ℝ) : ℂ) := funext fun y ↦ mul_comm _ _
  rw [e]; exact h

theorem dbarDir_ofReal_theta_eq_zero_of_notMem {z : ComplexModel d} (hz : z ∉ tsupport θ)
    (j : Fin d) : dbarDir (coordVec j) (fun y ↦ ((θ y : ℝ) : ℂ)) z = 0 := by
  have hev : (fun y ↦ ((θ y : ℝ) : ℂ)) =ᶠ[𝓝 z] fun _ ↦ (0 : ℂ) := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with y hy
    simp [hy]
  rw [dbarDir_congr hev, dbarDir_const]

/-- **`∂̄ (θ f) = f ∂̄ θ`.** -/
theorem dbarDir_cutProd (hW : IsOpen W) (hθ : ContDiff ℝ ∞ θ)
    (hf : DifferentiableOn ℂ f W) (hts : tsupport θ ⊆ W) (j : Fin d) (z : ComplexModel d) :
    dbarDir (coordVec j) (cutProd θ f) z = poleForm θ f j z := by
  by_cases hz : z ∈ W
  · have hfd : DifferentiableAt ℂ f z := hf.differentiableAt (hW.mem_nhds hz)
    have hθd : DifferentiableAt ℝ θ z := (hθ.differentiable (by simp)) z
    show dbarDir (coordVec j) (fun y ↦ ((θ y : ℝ) : ℂ) * f y) z = _
    rw [dbarDir_ofReal_mul hθd (hfd.restrictScalars ℝ),
      dbarDir_eq_zero_of_differentiableAt hfd, mul_zero, add_zero]
    exact mul_comm _ _
  · have hnz : z ∉ tsupport θ := fun h ↦ hz (hts h)
    have hev : cutProd θ f =ᶠ[𝓝 z] fun _ ↦ (0 : ℂ) := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hnz] with y hy
      simp [cutProd, hy]
    show dbarDir (coordVec j) (fun y ↦ ((θ y : ℝ) : ℂ) * f y) z = _
    rw [dbarDir_congr (show (fun y ↦ ((θ y : ℝ) : ℂ) * f y) =ᶠ[𝓝 z] fun _ ↦ (0 : ℂ) from hev),
      dbarDir_const, poleForm, dbarDir_ofReal_theta_eq_zero_of_notMem hnz, mul_zero]

theorem continuous_poleForm (hW : IsOpen W) (hθ : ContDiff ℝ ∞ θ)
    (hf : DifferentiableOn ℂ f W) (hts : tsupport θ ⊆ W) (j : Fin d) :
    Continuous (poleForm θ f j) := by
  have e : poleForm θ f j = dbarDir (coordVec j) (cutProd θ f) :=
    (funext fun z ↦ dbarDir_cutProd hW hθ hf hts j z).symm
  rw [e]
  exact continuous_dbarDir'
    ((contDiff_cutProd hW hθ hf hts).of_le (WithTop.coe_le_coe.mpr le_top))

/-- `v_j` vanishes wherever `θ` is locally constant, in particular on `ball x r`. -/
theorem poleForm_eq_zero_of_eventuallyEq_one {z : ComplexModel d}
    (hz : θ =ᶠ[𝓝 z] fun _ ↦ (1 : ℝ)) (j : Fin d) : poleForm θ f j z = 0 := by
  have hev : (fun y ↦ ((θ y : ℝ) : ℂ)) =ᶠ[𝓝 z] fun _ ↦ (1 : ℂ) := by
    filter_upwards [hz] with y hy; simp [hy]
  rw [poleForm, dbarDir_congr hev, dbarDir_const, mul_zero]

theorem tsupport_poleForm_subset (j : Fin d) : tsupport (poleForm θ f j) ⊆ tsupport θ := by
  refine closure_minimal (fun z hz ↦ ?_) (isClosed_tsupport θ)
  by_contra hnz
  exact hz (by simp [poleForm, dbarDir_ofReal_theta_eq_zero_of_notMem hnz])

theorem norm_poleForm_sq_le (hθd : ∀ z, DifferentiableAt ℝ θ z) (j : Fin d)
    (z : ComplexModel d) : ‖poleForm θ f j z‖ ^ 2 ≤ poleMajorant θ f z := by
  have h1 : ‖dbarDir (coordVec j) (fun y ↦ ((θ y : ℝ) : ℂ)) z‖ ≤ ‖fderiv ℝ θ z‖ := by
    refine (norm_dbarDir_le _ z (coordVec j)).trans ?_
    rw [PiLp.norm_single, norm_one, mul_one]
    exact norm_fderiv_ofReal_le (hθd z)
  have h2 : ‖poleForm θ f j z‖ ≤ ‖f z‖ * ‖fderiv ℝ θ z‖ := by
    rw [poleForm, norm_mul]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  calc ‖poleForm θ f j z‖ ^ 2 ≤ (‖f z‖ * ‖fderiv ℝ θ z‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = poleMajorant θ f z := by rw [poleMajorant, mul_pow]

/-- **The Levi majorant bound for `v = f ∂̄ θ`.** -/
theorem norm_sum_conj_mul_poleForm_sq_le (hθd : ∀ z, DifferentiableAt ℝ θ z)
    (z : ComplexModel d) (ξ : Fin d → ℂ) :
    ‖∑ j, conj (ξ j) * poleForm θ f j z‖ ^ 2 ≤
      poleMajorant θ f z * ‖(∑ j, ξ j • coordVec j : ComplexModel d)‖ ^ 2 := by
  set w : ComplexModel d := ∑ j, ξ j • coordVec j with hw
  have hsum : ∑ j, conj (ξ j) * poleForm θ f j z =
      f z * dbarDir w (fun y ↦ ((θ y : ℝ) : ℂ)) z := by
    rw [hw, dbarDir_sum_dir, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [poleForm]; ring
  have h1 : ‖dbarDir w (fun y ↦ ((θ y : ℝ) : ℂ)) z‖ ≤ ‖fderiv ℝ θ z‖ * ‖w‖ :=
    (norm_dbarDir_le _ z w).trans
      (mul_le_mul_of_nonneg_right (norm_fderiv_ofReal_le (hθd z)) (norm_nonneg _))
  have h2 : ‖∑ j, conj (ξ j) * poleForm θ f j z‖ ≤ ‖f z‖ * (‖fderiv ℝ θ z‖ * ‖w‖) := by
    rw [hsum, norm_mul]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  calc ‖∑ j, conj (ξ j) * poleForm θ f j z‖ ^ 2
      ≤ (‖f z‖ * (‖fderiv ℝ θ z‖ * ‖w‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ = poleMajorant θ f z * ‖w‖ ^ 2 := by rw [poleMajorant]; ring

theorem continuous_poleMajorant (hW : IsOpen W) (hθ : ContDiff ℝ ∞ θ)
    (hf : DifferentiableOn ℂ f W) (hts : tsupport θ ⊆ W) : Continuous (poleMajorant θ f) := by
  have h1 : ContinuousOn (fun z ↦ ‖f z‖ ^ 2) W :=
    (hf.continuousOn.norm.pow 2)
  have h2 : Continuous fun z : ComplexModel d ↦ ‖fderiv ℝ θ z‖ ^ 2 :=
    ((hθ.continuous_fderiv (by simp)).norm.pow 2)
  exact continuous_mul_of_tsupport_subset' hW h1 h2
    ((tsupport_normSq_fderiv_subset θ).trans hts)

end CutOff

/-- The Hörmander right-hand side `‖v‖² e^{-Φ_δ-lam₁}` is integrable on a bounded `D'`. -/
theorem integrable_poleMajorant_weight
    {D D' : Set (ComplexModel d)} (hD'o : IsOpen D') (hD'D : D' ⊆ D)
    (hD'b : Bornology.IsBounded D') {δ : ℝ} (hδ : 0 < δ)
    {ϕ : ComplexModel d → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    (x : ComplexModel d) {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {W : Set (ComplexModel d)} (hW : IsOpen W) (hts : tsupport θ ⊆ W)
    {f : ComplexModel d → ℂ} (hf : DifferentiableOn ℂ f W)
    {Mθ Mf : ℝ} (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ) (hMf : ∀ z ∈ tsupport θ, ‖f z‖ ≤ Mf)
    {lam₁ : ComplexModel d → ℝ} (hl₁c : ContinuousOn lam₁ D') (hl₁ : ∀ z ∈ D', 0 ≤ lam₁ z) :
    Integrable (fun z ↦ poleMajorant θ f z *
      Real.exp (-(poleWeight p ϕ x δ z + lam₁ z))) (volume.restrict D') := by
  have hΦc : ContinuousOn (poleWeight p ϕ x δ) D' :=
    ((contDiffOn_poleWeight hϕ hδ x).continuousOn).mono hD'D
  have hgc : Continuous (poleMajorant θ f) := continuous_poleMajorant hW hθ hf hts
  have hMθ0 : 0 ≤ Mθ := (norm_nonneg _).trans (hMθ 0)
  refine integrable_restrict_of_continuousOn_bound hD'o hD'b
    (hgc.continuousOn.mul (hΦc.add hl₁c).neg.rexp)
    (M := Mθ ^ 2 * Mf ^ 2 * (Real.exp Bϕ * ((δ ^ 2) ^ p)⁻¹)) fun z hz ↦ ?_
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (poleMajorant_nonneg _ _ _) (Real.exp_pos _).le)]
  exact mul_le_mul (poleMajorant_le_const hMθ hMf z)
    (exp_neg_poleWeight_add_le_of_bddBelow x hδ (hBϕ z (hD'D hz)) (hl₁ z hz))
    (Real.exp_pos _).le (by positivity)

/-! ### Step one: Hörmander's solution for the weight `Φ_δ` -/

/-- **Step one.**  Hörmander's minimal solution of `∂̄ u = ∂̄ (θ f)` for the weight `Φ_δ + lam₁`,
corrected by Weyl's lemma so that `θ f - u = G` is holomorphic, together with the `L²`
estimate.  This is the analogue of
`Hironaka.OTChen.exists_holomorphic_minimal_solution` for the point pole. -/
theorem exists_holomorphic_poleSolution
    {D D' : Set (ComplexModel d)} (hDo : IsOpen D) (hD'o : IsOpen D')
    (hD'D : D' ⊆ D) (hD'b : Bornology.IsBounded D') {δ : ℝ} (hδ : 0 < δ)
    {ϕ : ComplexModel d → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    (x : ComplexModel d) {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ)
    {W : Set (ComplexModel d)} (hW : IsOpen W) (hts : tsupport θ ⊆ W)
    {f : ComplexModel d → ℂ} (hf : DifferentiableOn ℂ f W)
    {Mθ Mf : ℝ} (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ) (hMf : ∀ z ∈ tsupport θ, ‖f z‖ ≤ Mf)
    {lam₁ lam₂ : ComplexModel d → ℝ} (hl₁ : ContinuousOn lam₁ D')
    (hl₂ : ContinuousOn lam₂ D') (hl : ∀ z ∈ D', 0 ≤ lam₁ z ∧ lam₁ z ≤ lam₂ z) {t : ℝ}
    (hest : HormanderClause D D' lam₁ lam₂ t) :
    ∃ G : ComplexModel d → ℂ, DifferentiableOn ℂ G D' ∧
      Integrable (fun z ↦ ‖cutProd θ f z - G z‖ ^ 2 *
        Real.exp (-(poleWeight p ϕ x δ z + lam₁ z))) (volume.restrict D') ∧
      ∫ z in D', ‖cutProd θ f z - G z‖ ^ 2 *
          Real.exp (-(poleWeight p ϕ x δ z + lam₁ z)) ≤
        (1 + t) * ∫ z in D', poleMajorant θ f z *
          Real.exp (-(poleWeight p ϕ x δ z + lam₁ z)) := by
  set a := cutProd θ f with ha_def
  set v : Fin d → ComplexModel d → ℂ := poleForm θ f with hv_def
  set Φ := poleWeight p ϕ x δ with hΦ_def
  set g := poleMajorant θ f with hg_def
  have hθd : ∀ z, DifferentiableAt ℝ θ z := fun z ↦ (hθ.differentiable (by simp)) z
  have hD'm : MeasurableSet D' := hD'o.measurableSet
  have ha : ContDiff ℝ ∞ a := contDiff_cutProd hW hθ hf hts
  have ha1 : ContDiff ℝ 1 a := ha.of_le (WithTop.coe_le_coe.mpr le_top)
  have hvdef : (fun j ↦ dbarDir (coordVec j) a) = v :=
    funext fun j ↦ funext fun z ↦ dbarDir_cutProd hW hθ hf hts j z
  have hΦs : ContDiffOn ℝ ∞ Φ D := contDiffOn_poleWeight hϕ hδ x
  have hΦc : ContinuousOn Φ D' := (hΦs.continuousOn).mono hD'D
  have hΦL : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm Φ z ξ := fun z hz ξ ↦
    le_trans (by positivity) (leviForm_poleWeight_ge hDo hϕ hϕL hδ x hz ξ)
  -- A uniform bound for the weight on `D'`.
  have hwt : ∀ z ∈ D', ∀ l : ℝ, 0 ≤ l →
      Real.exp (-(Φ z + l)) ≤ Real.exp Bϕ * ((δ ^ 2) ^ p)⁻¹ := fun z hz l hl0 ↦
    exp_neg_poleWeight_add_le_of_bddBelow x hδ (hBϕ z (hD'D hz)) hl0
  -- The Levi majorant.
  have hg0 : ∀ z, 0 ≤ g z := fun z ↦ poleMajorant_nonneg θ f z
  have hgle : ∀ z, g z ≤ Mθ ^ 2 * Mf ^ 2 := poleMajorant_le_const hMθ hMf
  have hgc : Continuous g := continuous_poleMajorant hW hθ hf hts
  have hglevi : ∀ z ∈ D', ∀ ξ : Fin d → ℂ,
      ‖∑ j, conj (ξ j) * v j z‖ ^ 2 ≤ g z * leviForm Φ z (∑ j, ξ j • coordVec j) := by
    intro z hz ξ
    refine (norm_sum_conj_mul_poleForm_sq_le hθd z ξ).trans ?_
    exact mul_le_mul_of_nonneg_left
      (leviForm_poleWeight_ge hDo hϕ hϕL hδ x (hD'D hz) _) (hg0 z)
  have hgint : Integrable (fun z ↦ g z * Real.exp (-(Φ z + lam₁ z))) (volume.restrict D') :=
    integrable_poleMajorant_weight hD'o hD'D hD'b hδ hϕ hBϕ x hθ hW hts hf hMθ hMf hl₁
      fun z hz ↦ (hl z hz).1
  -- The datum `v` lies in the weighted `L²` space.
  have hvcont : ∀ j, Continuous (v j) := fun j ↦ continuous_poleForm hW hθ hf hts j
  have hvsq : ∀ j, ∀ z, ‖v j z‖ ^ 2 ≤ Mθ ^ 2 * Mf ^ 2 := fun j z ↦
    (norm_poleForm_sq_le hθd j z).trans (hgle z)
  have hvmem : ∀ j, MemLp (v j) 2 (weightedVolume D' fun z ↦ Φ z + lam₂ z) := by
    intro j
    rw [memLp_weightedVolume_iff (w := fun z ↦ Φ z + lam₂ z)
      ((hΦc.add hl₂).aemeasurable hD'm) ((hvcont j).continuousOn.aestronglyMeasurable hD'm)]
    refine integrable_restrict_of_continuousOn_bound hD'o hD'b
      (((hvcont j).continuousOn.norm.pow 2).mul (hΦc.add hl₂).neg.rexp)
      (M := Mθ ^ 2 * Mf ^ 2 * (Real.exp Bϕ * ((δ ^ 2) ^ p)⁻¹)) fun z hz ↦ ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hMθ0 : 0 ≤ Mθ := (norm_nonneg _).trans (hMθ z)
    exact mul_le_mul (hvsq j z) (hwt z hz (lam₂ z) ((hl z hz).1.trans (hl z hz).2))
      (Real.exp_pos _).le (by positivity)
  have hvclosed : WeakDbarClosed D' v := by
    rw [← hvdef]; exact weakDbarClosed_of_contDiffOn hD'o ha1.contDiffOn
  -- Hörmander's estimate.
  obtain ⟨⟨u₀, hu₀mem, hu₀eq, hu₀orth⟩, hu₀est⟩ :=
    hest Φ hΦs hΦL v hvmem hvclosed g (fun z _ ↦ hg0 z) hglevi hgint
  -- Weyl's lemma turns `a - u₀` into a holomorphic function.
  have hwc : ContinuousOn (fun z ↦ Φ z + lam₁ z) D' := hΦc.add hl₁
  have hu₀loc : LocallyIntegrableOn u₀ D' :=
    locallyIntegrableOn_of_memLp_weightedVolume hD'o hwc hu₀mem
  have haloc : LocallyIntegrableOn a D' :=
    ha.continuous.continuousOn.locallyIntegrableOn hD'm
  have hFloc : LocallyIntegrableOn (fun z ↦ a z - u₀ z) D' := haloc.sub hu₀loc
  have hcoord : ∀ h, IsTestFunctionOn D' h → ∀ j,
      ∫ z, (a z - u₀ z) * dbarDir (coordVec j) h z = 0 := by
    intro h hh j
    have hdc : Continuous (dbarDir (coordVec j) h) :=
      continuous_dbarDir' (hh.1.of_le (WithTop.coe_le_coe.mpr le_top))
    have hdcs := hasCompactSupport_dbarDir (v := coordVec j) hh.2.1
    have hdts := (tsupport_dbarDir_subset (coordVec j) h).trans hh.2.2
    have i1 := integrable_mul_of_locallyIntegrableOn haloc hdc hdcs hdts
    have i2 := integrable_mul_of_locallyIntegrableOn hu₀loc hdc hdcs hdts
    simp only [sub_mul]
    rw [integral_sub i1 i2, hu₀eq h hh j]
    have := weakDbarEq_of_contDiffOn hD'o ha1.contDiffOn h hh j
    rw [show (fun j ↦ dbarDir (coordVec j) a) j = v j from congrFun hvdef j] at this
    rw [this]
    ring
  obtain ⟨G, hG, hGae⟩ := exists_differentiableOn_ae_eq_of_weak_dbar hD'o hFloc
    (integral_mul_dbarDir_eq_zero_of_coord hFloc hcoord)
  have hae : (fun z ↦ a z - G z) =ᵐ[volume.restrict D'] u₀ := by
    filter_upwards [hGae] with z hz
    rw [← hz]; ring
  have hmem : MemLp (fun z ↦ a z - G z) 2 (weightedVolume D' fun z ↦ Φ z + lam₁ z) :=
    hu₀mem.ae_eq ((withDensity_absolutelyContinuous _ _).ae_eq hae.symm)
  have hw₁m : AEMeasurable (fun z ↦ Φ z + lam₁ z) (volume.restrict D') :=
    (hΦc.add hl₁).aemeasurable hD'm
  refine ⟨G, hG, integrable_of_memLp_weightedVolume hw₁m hmem, ?_⟩
  have horth : ∀ h : ComplexModel d → ℂ,
      MemLp h 2 (weightedVolume D' fun z ↦ Φ z + lam₁ z) → WeakDbarEq D' h 0 →
      ∫ z in D', conj (h z) * u₀ z * Real.exp (-(Φ z + lam₁ z)) = 0 := hu₀orth
  have hfinal := hu₀est u₀ hu₀mem hu₀eq horth
  have heq : ∫ z in D', ‖a z - G z‖ ^ 2 * Real.exp (-(Φ z + lam₁ z)) =
      ∫ z in D', ‖u₀ z‖ ^ 2 * Real.exp (-(Φ z + lam₁ z)) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with z hz
    rw [hz]
  exact heq.le.trans hfinal

/-! ### The right-hand side: `‖z - x‖ ≥ r` on the support of the datum -/

theorem poleMajorant_eq_zero_of_mem_ball {θ : ComplexModel d → ℝ} {f : ComplexModel d → ℂ}
    {x : ComplexModel d} {r : ℝ} (hθ1 : ∀ z ∈ ball x r, θ z = 1) {z : ComplexModel d}
    (hz : z ∈ ball x r) : poleMajorant θ f z = 0 := by
  have hev : θ =ᶠ[𝓝 z] fun _ ↦ (1 : ℝ) :=
    Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) hθ1
  have hz0 : fderiv ℝ θ z = 0 := by rw [hev.fderiv_eq]; simp
  simp [poleMajorant, hz0]

/-- Away from the pole the weight is bounded by `e^{-ϕ} r^{-2d}`. -/
theorem exp_neg_poleWeight_add_le (ϕ : ComplexModel d → ℝ) (x : ComplexModel d) {δ r : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) {z : ComplexModel d} (hz : r ≤ ‖z - x‖) {l : ℝ} (hl : 0 ≤ l) :
    Real.exp (-(poleWeight p ϕ x δ z + l)) ≤ Real.exp (-ϕ z) * ((r ^ 2) ^ p)⁻¹ := by
  have e1 : Real.exp (-(poleWeight p ϕ x δ z + l)) =
      Real.exp (-poleWeight p ϕ x δ z) * Real.exp (-l) := by
    rw [← Real.exp_add]; ring_nf
  rw [e1, exp_neg_poleWeight ϕ x hδ z]
  have hr2 : (r : ℝ) ^ 2 ≤ ‖z - x‖ ^ 2 + δ ^ 2 := by nlinarith [norm_nonneg (z - x)]
  have b2 : ((‖z - x‖ ^ 2 + δ ^ 2) ^ p)⁻¹ ≤ ((r ^ 2) ^ p)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) hr2 p)
  calc Real.exp (-ϕ z) * ((‖z - x‖ ^ 2 + δ ^ 2) ^ p)⁻¹ * Real.exp (-‖z‖ ^ 2) * Real.exp (-l)
      = Real.exp (-ϕ z) * ((‖z - x‖ ^ 2 + δ ^ 2) ^ p)⁻¹ *
          (Real.exp (-‖z‖ ^ 2) * Real.exp (-l)) := by ring
    _ ≤ Real.exp (-ϕ z) * ((r ^ 2) ^ p)⁻¹ * 1 := by
        refine mul_le_mul ?_ ?_ (by positivity) (by positivity)
        · exact mul_le_mul_of_nonneg_left b2 (Real.exp_pos _).le
        · have b3 : Real.exp (-‖z‖ ^ 2) ≤ 1 :=
            Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
          have b4 : Real.exp (-l) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          nlinarith [Real.exp_pos (-‖z‖ ^ 2), Real.exp_pos (-l)]
    _ = Real.exp (-ϕ z) * ((r ^ 2) ^ p)⁻¹ := by ring

/-- **The Hörmander right-hand side is `≤ M_θ² r^{-2d} ∫_{tsupport θ} |f|² e^{-ϕ}`.** -/
theorem integral_poleMajorant_le
    {D D' : Set (ComplexModel d)} (hD'o : IsOpen D') (_hD'D : D' ⊆ D) {δ r : ℝ} (hδ : 0 < δ)
    (hr : 0 < r) {ϕ : ComplexModel d → ℝ} (hϕ : ContinuousOn ϕ D) (x : ComplexModel d)
    {θ : ComplexModel d → ℝ} (hθcs : HasCompactSupport θ) (hθ1 : ∀ z ∈ ball x r, θ z = 1)
    {W : Set (ComplexModel d)} (hts : tsupport θ ⊆ W) (htsD : tsupport θ ⊆ D)
    {f : ComplexModel d → ℂ} (hfc : ContinuousOn f W) {Mθ : ℝ}
    (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ) {lam₁ : ComplexModel d → ℝ} (hl₁ : ∀ z ∈ D', 0 ≤ lam₁ z)
    (hgint : Integrable (fun z ↦ poleMajorant θ f z *
      Real.exp (-(poleWeight p ϕ x δ z + lam₁ z))) (volume.restrict D')) :
    ∫ z in D', poleMajorant θ f z * Real.exp (-(poleWeight p ϕ x δ z + lam₁ z)) ≤
      Mθ ^ 2 * ((r ^ 2) ^ p)⁻¹ * ∫ z in tsupport θ, ‖f z‖ ^ 2 * Real.exp (-ϕ z) := by
  set T := tsupport θ with hT
  set G : ComplexModel d → ℝ := fun z ↦ poleMajorant θ f z *
    Real.exp (-(poleWeight p ϕ x δ z + lam₁ z)) with hG
  set K : ℝ := Mθ ^ 2 * ((r ^ 2) ^ p)⁻¹ with hK
  set h : ComplexModel d → ℝ := fun z ↦ K * (‖f z‖ ^ 2 * Real.exp (-ϕ z)) with hh
  have hD'm : MeasurableSet D' := hD'o.measurableSet
  have hTm : MeasurableSet T := (isClosed_tsupport θ).measurableSet
  have hMθ0 : 0 ≤ Mθ := (norm_nonneg _).trans (hMθ 0)
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hh0 : ∀ z, 0 ≤ h z := fun z ↦ mul_nonneg hK0 (by positivity)
  have hhcont : ContinuousOn h T :=
    continuousOn_const.mul (((hfc.mono hts).norm.pow 2).mul ((hϕ.mono htsD).neg.rexp))
  have hhint : IntegrableOn h T := hhcont.integrableOn_compact hθcs
  have hzero : ∀ z ∈ D' \ T, G z = 0 := fun z hz ↦ by
    simp [hG, poleMajorant_eq_zero_of_notMem_tsupport hz.2]
  have hstep : ∀ z ∈ D' ∩ T, G z ≤ h z := by
    intro z hz
    by_cases hb : z ∈ ball x r
    · rw [hG]
      simp only [poleMajorant_eq_zero_of_mem_ball hθ1 hb, zero_mul]
      exact hh0 z
    · have hrz : r ≤ ‖z - x‖ := by
        rw [mem_ball, dist_eq_norm] at hb
        exact not_lt.mp hb
      calc G z ≤ Mθ ^ 2 * ‖f z‖ ^ 2 * (Real.exp (-ϕ z) * ((r ^ 2) ^ p)⁻¹) :=
            mul_le_mul (poleMajorant_le hMθ z)
              (exp_neg_poleWeight_add_le ϕ x hδ hr hrz (hl₁ z hz.1)) (Real.exp_pos _).le
              (by positivity)
        _ = h z := by rw [hh, hK]; ring
  have e1 : ∫ z in D', G z = ∫ z in D' ∩ T, G z := by
    have hint := integral_inter_add_sdiff hTm hgint
    rw [setIntegral_eq_zero_of_forall_eq_zero hzero, add_zero] at hint
    exact hint.symm
  rw [e1]
  calc ∫ z in D' ∩ T, G z
      ≤ ∫ z in D' ∩ T, h z :=
        setIntegral_mono_on (IntegrableOn.mono_set hgint inter_subset_left)
          (hhint.mono_set inter_subset_right) (hD'm.inter hTm) hstep
    _ ≤ ∫ z in T, h z :=
        setIntegral_mono_set hhint
          ((ae_restrict_iff' hTm).mpr (Eventually.of_forall fun z _ ↦ hh0 z))
          (LE.le.eventuallyLE inter_subset_right)
    _ = K * ∫ z in T, ‖f z‖ ^ 2 * Real.exp (-ϕ z) := integral_const_mul _ _

/-! ### Vanishing at the pole -/

section Pole

variable [MeasurableSpace (ComplexModel d)] [BorelSpace (ComplexModel d)]

theorem finrank_real_complexModel (d : ℕ) : Module.finrank ℝ (ComplexModel d) = 2 * d := by
  rw [← Module.finrank_mul_finrank ℝ ℂ (ComplexModel d), Complex.finrank_real_complex,
    finrank_euclideanSpace_fin]

/-- **Vanishing at the pole.**  If `u` is holomorphic near `x` and the integrals of `|u|²`
against the regularized poles `(‖z - x‖² + η²)^{-(d+1)}` are bounded *uniformly in `η > 0`*,
then `u x = 0`.  Indeed on `ball x η` the pole factor is at least `(2η²)^{-(d+1)}`, and the
mean-value inequality bounds `∫_{ball x η} |u|²` from below by `c η^{2d} |u x|²`, so the
integral is at least a constant multiple of `|u x|² / η²`, which blows up as `η → 0`. -/
theorem eq_zero_of_lintegral_pole_bounded {u : ComplexModel d → ℂ} {x : ComplexModel d}
    {U : Set (ComplexModel d)} (hd : 0 < d) (hU : IsOpen U) (hx : x ∈ U)
    (hu : DifferentiableOn ℂ u U) {c : ℝ} (hc : 0 < c) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (hb : ∀ η : ℝ, 0 < η → ∫⁻ z in U, ENNReal.ofReal (c * ‖u z‖ ^ 2) *
        ENNReal.ofReal (((‖z - x‖ ^ 2 + η ^ 2) ^ (d + 1))⁻¹) ≤ A) :
    u x = 0 := by
  by_contra hux
  obtain ⟨s₀, hs₀, hball⟩ := Metric.isOpen_iff.mp hU x hx
  have : Nontrivial (ComplexModel d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_real_complexModel]; omega)
  set V1 := volume (ball (0 : ComplexModel d) 1) with hV1
  have hV1ne : V1 ≠ 0 := (measure_ball_pos volume _ one_pos).ne'
  have hV1top : V1 ≠ ⊤ := measure_ball_lt_top.ne
  have hux2 : 0 < ‖u x‖ ^ 2 := by positivity
  set B : ℝ := c * ‖u x‖ ^ 2 / 2 ^ (d + 1) with hB
  have hB0 : 0 < B := by rw [hB]; positivity
  -- The lower bound for every small radius.
  have key : ∀ s : ℝ, 0 < s → s ≤ s₀ / 2 → ENNReal.ofReal (B / s ^ 2) * V1 ≤ A := by
    intro s hs hss
    have hcb : closedBall x s ⊆ U := (closedBall_subset_ball (by linarith)).trans hball
    have hbs : ball x s ⊆ U := ball_subset_closedBall.trans hcb
    set C : ℝ≥0∞ := ENNReal.ofReal c * ENNReal.ofReal (((2 * s ^ 2) ^ (d + 1))⁻¹) with hC
    have hCtop : C ≠ ⊤ := by
      rw [hC]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have hpt : ∀ z ∈ ball x s, C * ENNReal.ofReal (‖u z‖ ^ 2) ≤
        ENNReal.ofReal (c * ‖u z‖ ^ 2) *
          ENNReal.ofReal (((‖z - x‖ ^ 2 + s ^ 2) ^ (d + 1)) ⁻¹) := by
      intro z hz
      have hzs : ‖z - x‖ ≤ s := by
        rw [mem_ball, dist_eq_norm] at hz; exact hz.le
      have hle : (‖z - x‖ ^ 2 + s ^ 2) ^ (d + 1) ≤ (2 * s ^ 2) ^ (d + 1) := by
        refine pow_le_pow_left₀ (by positivity) ?_ _
        nlinarith [norm_nonneg (z - x)]
      have hinv : ((2 * s ^ 2) ^ (d + 1))⁻¹ ≤ ((‖z - x‖ ^ 2 + s ^ 2) ^ (d + 1))⁻¹ :=
        inv_anti₀ (by positivity) hle
      rw [ENNReal.ofReal_mul hc.le, hC,
        show ENNReal.ofReal c * ENNReal.ofReal (((2 * s ^ 2) ^ (d + 1))⁻¹) *
            ENNReal.ofReal (‖u z‖ ^ 2) =
          ENNReal.ofReal c * ENNReal.ofReal (‖u z‖ ^ 2) *
            ENNReal.ofReal (((2 * s ^ 2) ^ (d + 1))⁻¹) by ring]
      gcongr
    calc ENNReal.ofReal (B / s ^ 2) * V1
        = C * (volume (ball x s) * ENNReal.ofReal (‖u x‖ ^ 2)) := by
          have hvol : volume (ball x s) = ENNReal.ofReal (s ^ (2 * d)) * V1 := by
            rw [Measure.addHaar_ball _ _ hs.le, finrank_real_complexModel]
          have hsne : s ≠ 0 := hs.ne'
          have hprod : ENNReal.ofReal (B / s ^ 2) =
              ENNReal.ofReal c * ENNReal.ofReal (((2 * s ^ 2) ^ (d + 1))⁻¹) *
                ENNReal.ofReal (s ^ (2 * d)) * ENNReal.ofReal (‖u x‖ ^ 2) := by
            rw [← ENNReal.ofReal_mul hc.le, ← ENNReal.ofReal_mul (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1
            rw [hB, mul_pow, ← pow_mul, show 2 * (d + 1) = 2 * d + 2 by ring, pow_add]
            field_simp
            ring
          rw [hvol, hC, hprod]
          ring
      _ ≤ C * ∫⁻ z in ball x s, ENNReal.ofReal (‖u z‖ ^ 2) := by
          gcongr
          exact lintegral_ball_normSq_ge hU hu hs hcb
      _ = ∫⁻ z in ball x s, C * ENNReal.ofReal (‖u z‖ ^ 2) :=
          (lintegral_const_mul' _ _ hCtop).symm
      _ ≤ ∫⁻ z in ball x s, ENNReal.ofReal (c * ‖u z‖ ^ 2) *
            ENNReal.ofReal (((‖z - x‖ ^ 2 + s ^ 2) ^ (d + 1))⁻¹) :=
          setLIntegral_mono' measurableSet_ball hpt
      _ ≤ ∫⁻ z in U, ENNReal.ofReal (c * ‖u z‖ ^ 2) *
            ENNReal.ofReal (((‖z - x‖ ^ 2 + s ^ 2) ^ (d + 1))⁻¹) := lintegral_mono_set hbs
      _ ≤ A := hb s hs
  -- Letting the radius tend to `0` contradicts finiteness.
  set A' : ℝ≥0∞ := A / V1 with hA'
  have hA'top : A' ≠ ⊤ := ENNReal.div_ne_top hA hV1ne
  have hMle : ∀ s : ℝ, 0 < s → s ≤ s₀ / 2 → B / s ^ 2 ≤ A'.toReal := by
    intro s hs hss
    refine (ENNReal.ofReal_le_iff_le_toReal hA'top).mp ?_
    rw [hA', ENNReal.le_div_iff_mul_le (Or.inl hV1ne) (Or.inl hV1top)]
    exact key s hs hss
  have hM0 : 0 ≤ A'.toReal := ENNReal.toReal_nonneg
  set s : ℝ := min (s₀ / 2) (Real.sqrt (B / (A'.toReal + 1))) with hsdef
  have hsq : 0 < Real.sqrt (B / (A'.toReal + 1)) := Real.sqrt_pos.mpr (by positivity)
  have hs : 0 < s := lt_min (by linarith) hsq
  have hss : s ≤ s₀ / 2 := min_le_left _ _
  have hs2 : s ^ 2 ≤ B / (A'.toReal + 1) := by
    have h1 : s ≤ Real.sqrt (B / (A'.toReal + 1)) := min_le_right _ _
    have h2 : s ^ 2 ≤ (Real.sqrt (B / (A'.toReal + 1))) ^ 2 :=
      pow_le_pow_left₀ hs.le h1 2
    rwa [Real.sq_sqrt (by positivity)] at h2
  have hfinal := hMle s hs hss
  have hs2pos : 0 < s ^ 2 := by positivity
  rw [div_le_iff₀ hs2pos] at hfinal
  have hkey2 : B ≤ A'.toReal * (B / (A'.toReal + 1)) :=
    hfinal.trans (mul_le_mul_of_nonneg_left hs2 hM0)
  rw [mul_div_assoc'] at hkey2
  rw [le_div_iff₀ (by positivity)] at hkey2
  nlinarith

end Pole

/-! ### One value of `δ`, on a relatively compact subset -/

/-- **One value of `δ`.**  For every open `K` with compact closure inside `D` there is a `G`
holomorphic on `K` with
`∫_K |θ f - G|² e^{-Φ_δ} ≤ 2 M_θ² r^{-2d} ∫_{tsupport θ} |f|² e^{-ϕ}`, a bound independent
of `δ`. -/
theorem exists_poleExtension_delta (hH : HormanderL2Estimate d)
    {D : Set (ComplexModel d)} (hDo : IsOpen D) (hDc : Convex ℝ D)
    (hDb : Bornology.IsBounded D) {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r)
    {ϕ : ComplexModel d → ℝ} (hϕ : ContDiffOn ℝ ∞ ϕ D)
    (hϕL : ∀ z ∈ D, ∀ ξ, 0 ≤ leviForm ϕ z ξ) {Bϕ : ℝ} (hBϕ : ∀ z ∈ D, -Bϕ ≤ ϕ z)
    (x : ComplexModel d) {θ : ComplexModel d → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθcs : HasCompactSupport θ) (hθ1 : ∀ z ∈ ball x r, θ z = 1)
    {W : Set (ComplexModel d)} (hW : IsOpen W) (hts : tsupport θ ⊆ W) (htsD : tsupport θ ⊆ D)
    {f : ComplexModel d → ℂ} (hf : DifferentiableOn ℂ f W)
    {Mθ : ℝ} (hMθ : ∀ z, ‖fderiv ℝ θ z‖ ≤ Mθ)
    {K Kc : Set (ComplexModel d)} (hKo : IsOpen K) (hKKc : K ⊆ Kc) (hKc : IsCompact Kc)
    (hKcD : Kc ⊆ D) :
    ∃ G : ComplexModel d → ℂ, DifferentiableOn ℂ G K ∧
      ∫⁻ z in K, ENNReal.ofReal (‖cutProd θ f z - G z‖ ^ 2 *
          Real.exp (-poleWeight p ϕ x δ z)) ≤
        ENNReal.ofReal (2 * (Mθ ^ 2 * ((r ^ 2) ^ p)⁻¹) *
          ∫ z in tsupport θ, ‖f z‖ ^ 2 * Real.exp (-ϕ z)) := by
  obtain ⟨D', U₀, lam₁, lam₂, hD'o, -, hD'D, -, hKcU₀, hU₀D', hl₁, hl₂, hl, hl0, hest⟩ :=
    hH D hDo hDc hDb Kc hKc hKcD 1 one_pos
  have hD'sub : D' ⊆ D := subset_closure.trans hD'D
  have hD'b : Bornology.IsBounded D' := hDb.subset hD'sub
  obtain ⟨Mf, hMf⟩ : ∃ C : ℝ, ∀ z ∈ tsupport θ, ‖f z‖ ≤ C := by
    rcases (tsupport θ).eq_empty_or_nonempty with he | hne
    · exact ⟨0, by simp [he]⟩
    · obtain ⟨z₀, -, hmax⟩ := hθcs.exists_isMaxOn hne ((hf.continuousOn.mono hts).norm)
      exact ⟨‖f z₀‖, fun z hz ↦ hmax hz⟩
  obtain ⟨G, hG, hint, hbound⟩ := exists_holomorphic_poleSolution (p := p) hDo hD'o hD'sub hD'b
    hδ hϕ hϕL hBϕ x hθ hW hts hf hMθ hMf hl₁ hl₂ hl hest
  have hgint := integrable_poleMajorant_weight (p := p) hD'o hD'sub hD'b hδ hϕ hBϕ x hθ hW hts
    hf hMθ hMf hl₁ fun z hz ↦ (hl z hz).1
  have hrhs := integral_poleMajorant_le (p := p) hD'o hD'sub hδ hr hϕ.continuousOn x hθcs hθ1
    hts htsD hf.continuousOn hMθ (fun z hz ↦ (hl z hz).1) hgint
  have hKD' : K ⊆ D' := hKKc.trans (hKcU₀.trans hU₀D')
  refine ⟨G, hG.mono hKD', ?_⟩
  have hY0 : ∀ z, 0 ≤ ‖cutProd θ f z - G z‖ ^ 2 *
      Real.exp (-(poleWeight p ϕ x δ z + lam₁ z)) := fun z ↦ by positivity
  calc ∫⁻ z in K, ENNReal.ofReal (‖cutProd θ f z - G z‖ ^ 2 *
          Real.exp (-poleWeight p ϕ x δ z))
      ≤ ∫⁻ z in D', ENNReal.ofReal (‖cutProd θ f z - G z‖ ^ 2 *
          Real.exp (-(poleWeight p ϕ x δ z + lam₁ z))) := by
        refine (setLIntegral_mono' hKo.measurableSet fun z hz ↦ le_of_eq ?_).trans
          (lintegral_mono_set hKD')
        rw [(hl0 z (hKcU₀ (hKKc hz))).1, add_zero]
    _ = ENNReal.ofReal (∫ z in D', ‖cutProd θ f z - G z‖ ^ 2 *
          Real.exp (-(poleWeight p ϕ x δ z + lam₁ z))) :=
        (ofReal_integral_eq_lintegral_ofReal hint
          (Eventually.of_forall fun z ↦ hY0 z)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h2 := hbound
        have h3 := hrhs
        linarith

end

end Hironaka.PointPole
