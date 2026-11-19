import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false

/-!
# The symmetric `N`-ary regularized maximum

Demailly's regularized maximum (Demailly, *Complex analytic and differential geometry*,
Chapter I, Lemma 5.18; recalled in Copy-4 before `lem:regularization`,
`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:828-850`) is

  `M_δ(t_1, …, t_N) = ∫_{ℝ^N} max_i (t_i + τ_i) ∏_i δ⁻¹ ϑ(τ_i / δ) dτ`.

This file builds it for an arbitrary finite set `S` of indices of a finite type `ι`, as the
real function `rmax δ S : (ι → ℝ) → ℝ`, and proves the properties the gluing step of Demailly's
regularization uses:

* `contDiff_rmax`: `M_δ` is `C^∞`;
* `convexOn_rmax`, `rmax_mono`: convex and nondecreasing in each variable;
* `rmax_add_const`: `M_δ(t + c𝟙) = M_δ(t) + c`;
* `smax_le_rmax`, `rmax_le_smax_add`: `max_S t ≤ M_δ(t) ≤ max_S t + δ`;
* `rmax_eq_of_dominated`, `rmax_erase`, `rmax_erase_of_gap`: **exact independence** -- the
  variables `t_i` with `t_i + δ ≤ t_j` for some other `j ∈ S` do not contribute at all, and
  `M_δ` coincides there with the regularized maximum of the remaining variables
  (`rmax_erase_of_gap` is Copy-4's form of the condition);
* `rmax_congr`: `M_δ` over `S` only depends on the coordinates in `S`;
* `rmax_mono_set`: enlarging `S` increases `M_δ`;
* `exists_subgradient`: at every point there is an affine minorant
  `M_δ(a) + ∑ λ_i (t_i - a_i)` with `λ ≥ 0` supported in `S` and `∑ λ_i = 1` -- the
  device that makes `M_δ` of plurisubharmonic functions plurisubharmonic
  (`Hironaka.SymmetricRegularizedMaxPsh`).

## How this differs from the source

The kernel used here is supported in the cube `[0, δ]^ι` instead of `[-δ, δ]^ι`
(`kernel`, a normed `ContDiffBump` on `ι → ℝ` centred at `(δ/2, …, δ/2)` with outer radius
`δ/2` for the sup norm).  For a kernel symmetric about the centre of the cube this is
Demailly's construction with parameter `δ/2`, translated by `δ/2`.  The translation buys
simpler constants: `max ≤ M_δ ≤ max + δ` (Copy-4 records `max + Nδ`), and the independence
condition is `t_i + δ ≤ t_j` (Copy-4: `t_i + δ < max_{j ≠ i}(t_j - δ)`, which implies it).
No evenness of the kernel is used anywhere.

The symmetric (unordered) form is what the gluing of local Bergman branches over the active
set `{j : z ∈ V_j}` needs; the right-nested binary recursions elsewhere in the tree
(`FiniteScaledSmoothMax`) only eliminate their head or tail.
-/

open MeasureTheory Set Function
open scoped ContDiff

namespace Hironaka.SymmetricRegularizedMax

noncomputable section

variable {ι : Type*}

/-! ### The maximum over a finite set -/

/-- The maximum of `t` over `S` (`0` for the empty set; every statement below that
needs it assumes `S` nonempty). -/
def smax (S : Finset ι) (t : ι → ℝ) : ℝ :=
  if h : S.Nonempty then S.sup' h t else 0

theorem smax_of_nonempty {S : Finset ι} (h : S.Nonempty) (t : ι → ℝ) :
    smax S t = S.sup' h t :=
  dif_pos h

theorem le_smax {S : Finset ι} {t : ι → ℝ} {i : ι} (hi : i ∈ S) : t i ≤ smax S t := by
  rw [smax_of_nonempty ⟨i, hi⟩]
  exact Finset.le_sup' t hi

theorem smax_le {S : Finset ι} (h : S.Nonempty) {t : ι → ℝ} {c : ℝ}
    (hc : ∀ i ∈ S, t i ≤ c) : smax S t ≤ c := by
  rw [smax_of_nonempty h]
  exact Finset.sup'_le h t hc

theorem exists_smax_eq {S : Finset ι} (h : S.Nonempty) (t : ι → ℝ) :
    ∃ i ∈ S, smax S t = t i := by
  rw [smax_of_nonempty h]
  exact Finset.exists_mem_eq_sup' h t

theorem smax_mono {S : Finset ι} {t t' : ι → ℝ} (h : ∀ i ∈ S, t i ≤ t' i) :
    smax S t ≤ smax S t' := by
  by_cases hS : S.Nonempty
  · exact smax_le hS fun i hi => (h i hi).trans (le_smax hi)
  · simp only [smax, dif_neg hS, le_refl]

theorem smax_congr {S : Finset ι} {t t' : ι → ℝ} (h : ∀ i ∈ S, t i = t' i) :
    smax S t = smax S t' :=
  le_antisymm (smax_mono fun i hi => (h i hi).le) (smax_mono fun i hi => (h i hi).ge)

theorem smax_add_const {S : Finset ι} (h : S.Nonempty) (t : ι → ℝ) (c : ℝ) :
    smax S (fun i => t i + c) = smax S t + c := by
  refine le_antisymm (smax_le h fun i hi => ?_) ?_
  · have := le_smax (t := t) hi
    linarith
  · obtain ⟨i, hi, he⟩ := exists_smax_eq h t
    rw [he]
    exact le_smax (t := fun i => t i + c) hi

theorem smax_mono_set {S T : Finset ι} (hST : S ⊆ T) (hS : S.Nonempty) (t : ι → ℝ) :
    smax S t ≤ smax T t :=
  smax_le hS fun _ hi => le_smax (hST hi)

theorem continuous_smax (S : Finset ι) : Continuous (smax (ι := ι) S) := by
  by_cases hS : S.Nonempty
  · have heq : smax (ι := ι) S = fun t => S.sup' hS fun i => t i :=
      funext fun t => smax_of_nonempty hS t
    rw [heq]
    exact Continuous.finset_sup'_apply hS fun i _ => continuous_apply i
  · have heq : smax (ι := ι) S = fun _ => 0 := funext fun t => dif_neg hS
    rw [heq]
    exact continuous_const

theorem continuous_smax_add (S : Finset ι) (t : ι → ℝ) :
    Continuous fun τ : ι → ℝ => smax S (t + τ) :=
  (continuous_smax S).comp (continuous_const.add continuous_id)

theorem smax_convexComb (S : Finset ι) (a b : ι → ℝ) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    smax S (fun i => α * a i + β * b i) ≤ α * smax S a + β * smax S b := by
  by_cases hS : S.Nonempty
  · refine smax_le hS fun i hi => ?_
    have h1 := mul_le_mul_of_nonneg_left (le_smax (t := a) hi) hα
    have h2 := mul_le_mul_of_nonneg_left (le_smax (t := b) hi) hβ
    linarith
  · simp only [smax, dif_neg hS, mul_zero, add_zero, le_refl]

variable [Fintype ι]

/-! ### The kernel -/

/-- The bump on `ι → ℝ` centred at `(δ/2, …, δ/2)` with outer radius `δ/2` for the sup
norm: its support is the open cube `(0, δ)^ι`. -/
def kernelBump {δ : ℝ} (hδ : 0 < δ) : ContDiffBump (fun _ : ι => δ / 2) where
  rIn := δ / 4
  rOut := δ / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- **The mollifier**: smooth, nonnegative, of integral one and supported in `[0, δ]^ι`
when `0 < δ` (and `0` otherwise). -/
def kernel (δ : ℝ) : (ι → ℝ) → ℝ :=
  if hδ : 0 < δ then (kernelBump (ι := ι) hδ).normed volume else 0

theorem kernel_of_pos {δ : ℝ} (hδ : 0 < δ) :
    kernel (ι := ι) δ = (kernelBump (ι := ι) hδ).normed volume := by
  simp only [kernel, dif_pos hδ]

theorem kernel_nonneg (δ : ℝ) (τ : ι → ℝ) : 0 ≤ kernel δ τ := by
  unfold kernel
  split_ifs with hδ
  · exact (kernelBump hδ).nonneg_normed τ
  · exact le_rfl

theorem contDiff_kernel (δ : ℝ) : ContDiff ℝ ∞ (kernel (ι := ι) δ) := by
  unfold kernel
  split_ifs with hδ
  · exact (kernelBump hδ).contDiff_normed
  · exact contDiff_const

theorem hasCompactSupport_kernel (δ : ℝ) : HasCompactSupport (kernel (ι := ι) δ) := by
  unfold kernel
  split_ifs with hδ
  · exact (kernelBump hδ).hasCompactSupport_normed
  · exact HasCompactSupport.zero

theorem continuous_kernel (δ : ℝ) : Continuous (kernel (ι := ι) δ) :=
  (contDiff_kernel δ).continuous

theorem integral_kernel {δ : ℝ} (hδ : 0 < δ) : ∫ τ, kernel (ι := ι) δ τ = 1 := by
  rw [kernel_of_pos hδ]
  exact (kernelBump hδ).integral_normed

/-- Where the kernel does not vanish, every coordinate lies in `(0, δ)`. -/
theorem mem_Ioo_of_kernel_ne_zero {δ : ℝ} {τ : ι → ℝ} (h : kernel δ τ ≠ 0) (i : ι) :
    0 < τ i ∧ τ i < δ := by
  by_cases hδ : 0 < δ
  · rw [kernel_of_pos hδ] at h
    have hmem : τ ∈ Metric.ball (fun _ : ι => δ / 2) (kernelBump (ι := ι) hδ).rOut := by
      rw [← (kernelBump hδ).support_normed_eq (μ := volume)]
      exact h
    have hi := (dist_pi_lt_iff (show (0 : ℝ) < δ / 2 by positivity)).1 hmem i
    rw [Real.dist_eq, abs_sub_lt_iff] at hi
    constructor <;> linarith [hi.1, hi.2]
  · exact absurd (by simp [kernel, dif_neg hδ]) h

/-! ### The regularized maximum -/

/-- **Demailly's regularized maximum** of the coordinates of `t` indexed by `S`:
`M_δ(t) = ∫ K_δ(τ) max_{i ∈ S}(t_i + τ_i) dτ`. -/
def rmax (δ : ℝ) (S : Finset ι) (t : ι → ℝ) : ℝ :=
  ∫ τ, kernel δ τ * smax S (t + τ)

theorem integrable_kernel_mul (δ : ℝ) {g : (ι → ℝ) → ℝ} (hg : Continuous g) :
    Integrable fun τ => kernel δ τ * g τ :=
  ((continuous_kernel δ).mul hg).integrable_of_hasCompactSupport
    (hasCompactSupport_kernel δ).mul_right

theorem integral_kernel_mul_congr {δ : ℝ} {f g : (ι → ℝ) → ℝ}
    (h : ∀ τ, kernel δ τ ≠ 0 → f τ = g τ) :
    ∫ τ, kernel δ τ * f τ = ∫ τ, kernel δ τ * g τ := by
  congr 1
  funext τ
  by_cases hk : kernel δ τ = 0
  · rw [hk, zero_mul, zero_mul]
  · rw [h τ hk]

theorem integral_kernel_mul_mono {δ : ℝ} {f g : (ι → ℝ) → ℝ} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ τ, kernel δ τ ≠ 0 → f τ ≤ g τ) :
    ∫ τ, kernel δ τ * f τ ≤ ∫ τ, kernel δ τ * g τ := by
  refine integral_mono (integrable_kernel_mul δ hf) (integrable_kernel_mul δ hg) fun τ => ?_
  by_cases hk : kernel δ τ = 0
  · simp only [hk, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (h τ hk) (kernel_nonneg δ τ)

theorem integral_kernel_mul_const {δ : ℝ} (hδ : 0 < δ) (c : ℝ) :
    ∫ τ, kernel (ι := ι) δ τ * c = c := by
  rw [integral_mul_const, integral_kernel hδ, one_mul]

/-- On the support of the kernel, `max_S t ≤ max_S (t + τ) ≤ max_S t + δ`. -/
theorem smax_add_mem {δ : ℝ} {S : Finset ι} (hS : S.Nonempty) (t : ι → ℝ) {τ : ι → ℝ}
    (hτ : kernel δ τ ≠ 0) : smax S t ≤ smax S (t + τ) ∧ smax S (t + τ) ≤ smax S t + δ := by
  constructor
  · refine smax_mono fun i _ => ?_
    have := (mem_Ioo_of_kernel_ne_zero hτ i).1
    simp only [Pi.add_apply]
    linarith
  · refine smax_le hS fun i hi => ?_
    have h1 := (mem_Ioo_of_kernel_ne_zero hτ i).2
    have h2 := le_smax (t := t) hi
    simp only [Pi.add_apply]
    linarith

/-- `max_S t ≤ M_δ(t)`. -/
theorem smax_le_rmax {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} (hS : S.Nonempty) (t : ι → ℝ) :
    smax S t ≤ rmax δ S t :=
  calc smax S t = ∫ τ, kernel δ τ * smax S t := (integral_kernel_mul_const hδ _).symm
    _ ≤ rmax δ S t := integral_kernel_mul_mono continuous_const (continuous_smax_add S t)
        fun _ hτ => (smax_add_mem hS t hτ).1

/-- `M_δ(t) ≤ max_S t + δ`. -/
theorem rmax_le_smax_add {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} (hS : S.Nonempty)
    (t : ι → ℝ) : rmax δ S t ≤ smax S t + δ :=
  calc rmax δ S t ≤ ∫ τ, kernel δ τ * (smax S t + δ) :=
        integral_kernel_mul_mono (continuous_smax_add S t) continuous_const
          fun _ hτ => (smax_add_mem hS t hτ).2
    _ = smax S t + δ := integral_kernel_mul_const hδ _

/-- **`M_δ` dominates each of its entries.** -/
theorem le_rmax {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} {i : ι} (hi : i ∈ S) (t : ι → ℝ) :
    t i ≤ rmax δ S t :=
  (le_smax hi).trans (smax_le_rmax hδ ⟨i, hi⟩ t)

theorem rmax_le {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} (hS : S.Nonempty) {t : ι → ℝ} {c : ℝ}
    (hc : ∀ i ∈ S, t i ≤ c) : rmax δ S t ≤ c + δ :=
  (rmax_le_smax_add hδ hS t).trans (by linarith [smax_le hS hc])

/-- **`M_δ` is nondecreasing in each variable.** -/
theorem rmax_mono {δ : ℝ} {S : Finset ι} {t t' : ι → ℝ} (h : ∀ i ∈ S, t i ≤ t' i) :
    rmax δ S t ≤ rmax δ S t' :=
  integral_kernel_mul_mono (continuous_smax_add S t) (continuous_smax_add S t')
    fun τ _ => smax_mono fun i hi => by simp only [Pi.add_apply]; linarith [h i hi]

/-- **`M_δ` over `S` only sees the coordinates in `S`.** -/
theorem rmax_congr {δ : ℝ} {S : Finset ι} {t t' : ι → ℝ} (h : ∀ i ∈ S, t i = t' i) :
    rmax δ S t = rmax δ S t' :=
  integral_kernel_mul_congr fun τ _ => smax_congr fun i hi => by simp only [Pi.add_apply, h i hi]

/-- **Translation equivariance**: `M_δ(t + c𝟙) = M_δ(t) + c`. -/
theorem rmax_add_const {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} (hS : S.Nonempty) (t : ι → ℝ)
    (c : ℝ) : rmax δ S (fun i => t i + c) = rmax δ S t + c := by
  have hpt : ∀ τ : ι → ℝ, kernel δ τ * smax S ((fun i => t i + c) + τ)
      = kernel δ τ * smax S (t + τ) + kernel δ τ * c := by
    intro τ
    have : ((fun i => t i + c) + τ) = fun i => (t + τ) i + c := by
      funext i
      simp only [Pi.add_apply]
      ring
    rw [this, smax_add_const hS, mul_add]
  unfold rmax
  simp_rw [hpt]
  rw [integral_add (integrable_kernel_mul δ (continuous_smax_add S t))
    (integrable_kernel_mul δ continuous_const), integral_kernel_mul_const hδ]

/-- **Enlarging the index set increases `M_δ`.** -/
theorem rmax_mono_set {δ : ℝ} {S T : Finset ι} (hST : S ⊆ T) (hS : S.Nonempty)
    (t : ι → ℝ) : rmax δ S t ≤ rmax δ T t :=
  integral_kernel_mul_mono (continuous_smax_add S t) (continuous_smax_add T t)
    fun _ _ => smax_mono_set hST hS _

/-- **Exact independence.**  If every index of `T` outside `F ⊆ T` is beaten by at least `δ`
by some index of `F`, then the regularized maximum over `T` *equals* the one over `F`. -/
theorem rmax_eq_of_dominated {δ : ℝ} {F T : Finset ι} (hFT : F ⊆ T) (hF : F.Nonempty)
    {t : ι → ℝ} (hdom : ∀ i ∈ T, i ∉ F → ∃ j ∈ F, t i + δ ≤ t j) :
    rmax δ T t = rmax δ F t := by
  refine integral_kernel_mul_congr fun τ hτ => le_antisymm ?_ (smax_mono_set hFT hF _)
  obtain ⟨j₀, hj₀⟩ := hF
  refine smax_le ⟨j₀, hFT hj₀⟩ fun i hi => ?_
  by_cases hiF : i ∈ F
  · exact le_smax hiF
  · obtain ⟨j, hj, hij⟩ := hdom i hi hiF
    have h1 := (mem_Ioo_of_kernel_ne_zero hτ i).2
    have h2 := (mem_Ioo_of_kernel_ne_zero hτ j).1
    have h3 := le_smax (t := t + τ) hj
    simp only [Pi.add_apply] at h3 ⊢
    linarith

/-- **Exact independence, one variable at a time.**  If `t_i + δ ≤ t_j` for another index
`j ∈ S`, then `M_δ` over `S` does not depend on `t_i` and equals `M_δ` over `S \ {i}`. -/
theorem rmax_erase [DecidableEq ι] {δ : ℝ} {S : Finset ι} {i j : ι} (hj : j ∈ S) (hji : j ≠ i)
    {t : ι → ℝ} (h : t i + δ ≤ t j) : rmax δ S t = rmax δ (S.erase i) t := by
  have hjS : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hji, hj⟩
  refine rmax_eq_of_dominated (S.erase_subset i) ⟨j, hjS⟩ fun k hk hkF => ?_
  have hki : k = i := by
    by_contra hne
    exact hkF (Finset.mem_erase.mpr ⟨hne, hk⟩)
  subst hki
  exact ⟨j, hjS, h⟩

/-- **Copy-4's independence property**: `M_δ(t)` does not depend on `t_i` on the set where
`t_i + δ < max_{j ≠ i}(t_j - δ)`, where it coincides with the regularized maximum of the
remaining variables. -/
theorem rmax_erase_of_gap [DecidableEq ι] {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} {i j : ι} (hj : j ∈ S)
    (hji : j ≠ i) {t : ι → ℝ} (h : t i + δ < t j - δ) : rmax δ S t = rmax δ (S.erase i) t :=
  rmax_erase hj hji (by linarith)

/-- **`M_δ` is convex.** -/
theorem convexOn_rmax (δ : ℝ) (S : Finset ι) : ConvexOn ℝ univ (rmax (ι := ι) δ S) := by
  refine ⟨convex_univ, fun a _ b _ α β hα hβ hαβ => ?_⟩
  simp only [smul_eq_mul]
  unfold rmax
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_kernel_mul δ (continuous_smax_add S a)).const_mul α)
      ((integrable_kernel_mul δ (continuous_smax_add S b)).const_mul β)]
  refine integral_mono (integrable_kernel_mul δ (continuous_smax_add S _))
    (((integrable_kernel_mul δ (continuous_smax_add S a)).const_mul α).add
      ((integrable_kernel_mul δ (continuous_smax_add S b)).const_mul β)) fun τ => ?_
  have hcomb : α • a + β • b + τ = fun i => α * (a + τ) i + β * (b + τ) i := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have : τ i = (α + β) * τ i := by rw [hαβ, one_mul]
    linarith [this]
  rw [hcomb]
  have := mul_le_mul_of_nonneg_left (smax_convexComb S (a + τ) (b + τ) hα hβ)
    (kernel_nonneg δ τ)
  simp only
  linarith

/-- `M_δ` as a convolution (with the reflected kernel). -/
theorem rmax_eq_convolution (δ : ℝ) (S : Finset ι) :
    rmax (ι := ι) δ S = convolution (smax S) (fun x => kernel δ (-x))
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) volume := by
  funext t
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  rw [← integral_add_right_eq_self (μ := volume) (fun s => smax S s * kernel δ (-(t - s))) t]
  unfold rmax
  congr 1
  funext τ
  rw [show -(t - (τ + t)) = τ by abel, add_comm τ t, mul_comm]

/-- **`M_δ` is `C^∞`.** -/
theorem contDiff_rmax (δ : ℝ) (S : Finset ι) : ContDiff ℝ ∞ (rmax (ι := ι) δ S) := by
  rw [rmax_eq_convolution]
  have hK : HasCompactSupport fun x : ι → ℝ => kernel δ (-x) :=
    (hasCompactSupport_kernel δ).comp_homeomorph (Homeomorph.neg _)
  exact hK.contDiff_convolution_right _ (continuous_smax S).locallyIntegrable
    ((contDiff_kernel δ).comp contDiff_neg)

/-! ### The affine minorant -/

/-- The derivative of `M_δ` at `a` in the direction `t - a`, expanded in coordinates. -/
theorem fderiv_rmax_sub (δ : ℝ) (S : Finset ι) [DecidableEq ι] (a t : ι → ℝ) :
    fderiv ℝ (rmax δ S) a (t - a) =
      ∑ i, fderiv ℝ (rmax δ S) a (fun j => if i = j then 1 else 0) * (t i - a i) := by
  conv_lhs => rw [pi_eq_sum_univ (t - a)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

/-- **The tangent inequality**: `M_δ(a) + DM_δ(a)(t - a) ≤ M_δ(t)`. -/
theorem rmax_add_fderiv_le (δ : ℝ) (S : Finset ι) (a t : ι → ℝ) :
    rmax δ S a + fderiv ℝ (rmax δ S) a (t - a) ≤ rmax δ S t := by
  set L : ℝ →ᵃ[ℝ] (ι → ℝ) := AffineMap.lineMap a t with hLdef
  have hD : HasFDerivAt (rmax δ S) (fderiv ℝ (rmax δ S) a) (L 0) := by
    rw [hLdef, AffineMap.lineMap_apply_zero]
    exact ((contDiff_rmax δ S).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hg : HasDerivAt (rmax δ S ∘ L) (fderiv ℝ (rmax δ S) a (t - a)) (0 : ℝ) :=
    hD.comp_hasDerivAt (0 : ℝ) AffineMap.hasDerivAt_lineMap
  have hconv : ConvexOn ℝ univ (rmax δ S ∘ L) := by
    have := (convexOn_rmax δ S).comp_affineMap L
    rwa [preimage_univ] at this
  have hslope := hconv.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1) zero_lt_one hg
  rw [slope_def_field] at hslope
  simp only [comp_apply, hLdef, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero,
    sub_zero, div_one] at hslope
  linarith

/-- **The affine minorant of `M_δ` at a point.**  There are weights `λ_i ≥ 0`, vanishing
off `S` and summing to `1`, with `M_δ(a) + ∑ λ_i (t_i - a_i) ≤ M_δ(t)` for every `t`. -/
theorem exists_subgradient {δ : ℝ} (hδ : 0 < δ) {S : Finset ι} (hS : S.Nonempty)
    (a : ι → ℝ) :
    ∃ lam : ι → ℝ, (∀ i, 0 ≤ lam i) ∧ (∀ i, i ∉ S → lam i = 0) ∧ ∑ i, lam i = 1 ∧
      ∀ t : ι → ℝ, rmax δ S a + ∑ i, lam i * (t i - a i) ≤ rmax δ S t := by
  classical
  set D := fderiv ℝ (rmax δ S) a with hDdef
  set e : ι → ι → ℝ := fun i j => if i = j then 1 else 0 with hedef
  refine ⟨fun i => D (e i), ?_, ?_, ?_, fun t => ?_⟩
  · -- nonnegativity from monotonicity
    intro i
    have h := rmax_add_fderiv_le δ S a (a - e i)
    rw [show a - e i - a = -e i by abel, map_neg] at h
    have hmono : rmax δ S (a - e i) ≤ rmax δ S a :=
      rmax_mono fun k _ => by simp only [Pi.sub_apply, hedef]; split_ifs <;> linarith
    linarith
  · -- vanishing off `S`
    intro i hi
    have hcongr : ∀ s : ℝ, rmax δ S (a + s • e i) = rmax δ S a := fun s =>
      rmax_congr fun k hk => by
        have hik : i ≠ k := fun h => hi (h ▸ hk)
        simp only [Pi.add_apply, Pi.smul_apply, hedef, if_neg hik, smul_zero, add_zero]
    have h1 := rmax_add_fderiv_le δ S a (a + (1 : ℝ) • e i)
    have h2 := rmax_add_fderiv_le δ S a (a + (-1 : ℝ) • e i)
    rw [add_sub_cancel_left, map_smul, smul_eq_mul, one_mul, hcongr] at h1
    rw [add_sub_cancel_left, map_smul, smul_eq_mul, hcongr] at h2
    simp only
    linarith
  · -- total mass one from translation equivariance
    have hsum : ∀ c : ℝ, D (fun _ => c) = c * ∑ i, D (e i) := by
      intro c
      have := fderiv_rmax_sub δ S a (fun i => a i + c)
      rw [← hDdef] at this
      have hsub : (fun i => a i + c) - a = fun _ => c := by
        funext i
        simp only [Pi.sub_apply]
        ring
      rw [hsub] at this
      rw [this, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [add_sub_cancel_left]
      ring
    have h1 := rmax_add_fderiv_le δ S a (fun i => a i + 1)
    have h2 := rmax_add_fderiv_le δ S a (fun i => a i + (-1))
    have hs1 : (fun i => a i + 1) - a = fun _ => (1 : ℝ) := by
      funext i; simp only [Pi.sub_apply]; ring
    have hs2 : (fun i => a i + (-1)) - a = fun _ => (-1 : ℝ) := by
      funext i; simp only [Pi.sub_apply]; ring
    rw [hs1, ← hDdef, hsum, rmax_add_const hδ hS] at h1
    rw [hs2, ← hDdef, hsum, rmax_add_const hδ hS] at h2
    simp only
    linarith
  · have h := rmax_add_fderiv_le δ S a t
    rw [fderiv_rmax_sub δ S a t] at h
    exact h

end

end Hironaka.SymmetricRegularizedMax
