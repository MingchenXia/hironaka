import Hironaka.Analytic.PshThreeCircles
import Hironaka.Analytic.OTSliceVanishing
import Hironaka.Analytic.SingularLocus

set_option autoImplicit false

/-!
# The slice bound along a coordinate hyperplane

Blueprint `pc:divisorial-slice-bound` (Copy-4 `lem:domination`, Step 1; the Siu-type bound of
Boucksom--Favre--Jonsson's valuative description, in the project's normalization of Lelong numbers,
`ν(log ‖z‖, 0) = 1`).

Let `E = {z_{m+1} = 0}` in `ℂ^{m+1}` and let `u` be plurisubharmonic near a point `p ∈ E`.  If every
point `q` of `E` near `p` admits a logarithmic exponent `γ_q > γ`, i.e. `u ≤ γ_q log ‖· - q‖ + C_q` on
a punctured neighbourhood of `q` (in particular if `ν(u, q) > γ`), then on a smaller ball around `p`

  `u(z) ≤ γ log |z_{m+1}| + (K - γ log r)`,

with `K` an upper bound of `u` on `closedBall p (2r)`; the constant does not depend on the point.

The proof is Hadamard's three-circle inequality (`PshThreeCircles.le_log_interpolation`) about the
foot `q` of `z` on `E`, between a small sphere, where the exponent `γ_q` controls `u`, and the
sphere of radius `r`, where `K` does; the inner radius is taken so small that the interpolated
bound is at most `γ log |z_{m+1}| + K - γ log r`.  No maximum principle along the slice and no
removable-singularity argument is needed beyond the three-circle inequality.

* `hyperplaneFoot`, `norm_sub_hyperplaneFoot`, `norm_hyperplaneFoot_sub_le`, `norm_last_le`:
  the orthogonal projection onto `E`.
* `le_log_last_add_of_admissible`: the slice bound from admissible exponents.
* `exists_admissible_of_lt_lelongNumber`: an exponent below the Lelong number is exceeded by an
  admissible one (Lelong numbers of `ℂ^{m+1}` are computed in the identity chart).
* `le_log_last_add_of_lt_lelongNumber`: the slice bound from a lower bound on Lelong numbers along
  `E`.

Sorry-free.
-/

open Set Filter Metric
open scoped Topology ENNReal NNReal

namespace Hironaka.DivisorialSliceBound

open Hironaka.PshThreeCircles

noncomputable section

variable {m : ℕ}

/-! ### The foot of a point on the hyperplane `{z_{m+1} = 0}` -/

/-- The orthogonal projection of `z ∈ ℂ^{m+1}` onto the hyperplane `{z_{m+1} = 0}`. -/
def hyperplaneFoot (z : ComplexModel (m + 1)) : ComplexModel (m + 1) :=
  sliceMap m 0 (initCoords z)

@[simp] theorem hyperplaneFoot_last (z : ComplexModel (m + 1)) :
    hyperplaneFoot z (Fin.last m) = 0 := by
  simp [hyperplaneFoot]

theorem initCoords_hyperplaneFoot (z : ComplexModel (m + 1)) :
    initCoords (hyperplaneFoot z) = initCoords z := by
  simp [hyperplaneFoot, initCoords_sliceMap]

theorem norm_sub_hyperplaneFoot (z : ComplexModel (m + 1)) :
    ‖z - hyperplaneFoot z‖ = ‖z (Fin.last m)‖ := by
  have h := OTChen.norm_sq_eq_initCoords (z - hyperplaneFoot z)
  rw [OTChen.initCoords_sub, initCoords_hyperplaneFoot, sub_self, norm_zero] at h
  simp only [PiLp.sub_apply, hyperplaneFoot_last, sub_zero] at h
  have h2 : ‖z - hyperplaneFoot z‖ ^ 2 = ‖z (Fin.last m)‖ ^ 2 := by simpa using h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h2

/-- For `p` on the hyperplane, `|z_{m+1}| ≤ ‖z - p‖`. -/
theorem norm_last_le {p : ComplexModel (m + 1)} (hp : p (Fin.last m) = 0)
    (z : ComplexModel (m + 1)) : ‖z (Fin.last m)‖ ≤ ‖z - p‖ := by
  have h := PiLp.norm_apply_le (z - p) (Fin.last m)
  simpa [hp] using h

/-- For `p` on the hyperplane, the foot of `z` is at least as close to `p` as `z`. -/
theorem norm_hyperplaneFoot_sub_le {p : ComplexModel (m + 1)} (hp : p (Fin.last m) = 0)
    (z : ComplexModel (m + 1)) : ‖hyperplaneFoot z - p‖ ≤ ‖z - p‖ := by
  have h1 := OTChen.norm_sq_eq_initCoords (hyperplaneFoot z - p)
  have h2 := OTChen.norm_sq_eq_initCoords (z - p)
  rw [OTChen.initCoords_sub, initCoords_hyperplaneFoot] at h1
  rw [OTChen.initCoords_sub] at h2
  simp only [PiLp.sub_apply, hyperplaneFoot_last, hp, sub_zero, norm_zero] at h1 h2
  have hsq : ‖hyperplaneFoot z - p‖ ^ 2 ≤ ‖z - p‖ ^ 2 := by
    rw [h1, h2]
    have : (0 : ℝ) ≤ ‖z (Fin.last m)‖ ^ 2 := by positivity
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq

/-! ### The slice bound -/

/-- The elementary inequality behind the slice bound: the logarithmic interpolation between
`γ' log r₁ + C` at radius `r₁` and `K` at radius `r` is at most `γ log t + K - γ log r` at every
radius `t ∈ (r₁, r]`, provided `γ < γ'` and `log r₁ ≤ (K - C - γ log r) / (γ' - γ)`. -/
theorem log_interpolation_le {γ γ' C K L₁ L L₃ : ℝ} (hγ : γ < γ') (h1 : L₁ < L) (h3 : L ≤ L₃)
    (hL₁ : L₁ ≤ (K - C - γ * L₃) / (γ' - γ)) :
    (γ' * L₁ + C) + (L - L₁) * (K - (γ' * L₁ + C)) / (L₃ - L₁) ≤ γ * L + (K - γ * L₃) := by
  have hD : 0 < L₃ - L₁ := by linarith
  have hγ' : 0 < γ' - γ := by linarith
  have hb : (γ' - γ) * L₁ + C - K + γ * L₃ ≤ 0 := by
    have := (le_div_iff₀ hγ').mp hL₁
    linarith
  rw [← sub_nonpos]
  have e : (γ' * L₁ + C) + (L - L₁) * (K - (γ' * L₁ + C)) / (L₃ - L₁) - (γ * L + (K - γ * L₃)) =
      (L₃ - L) * ((γ' - γ) * L₁ + C - K + γ * L₃) / (L₃ - L₁) := by
    field_simp
    ring
  rw [e]
  exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith) hb) hD.le

/-- **Slice bound along a coordinate hyperplane** (`pc:divisorial-slice-bound`).  Let `u` be
plurisubharmonic on `Ω ⊇ closedBall p (2r)`, `p` on the hyperplane `{z_{m+1} = 0}`, `u ≤ K` on
`closedBall p (2r)`, and suppose every point `q` of the hyperplane in `ball p r` admits an exponent
`γ_q > γ`.  Then `u(z) ≤ γ log |z_{m+1}| + (K - γ log r)` on `ball p r` off the hyperplane. -/
theorem le_log_last_add_of_admissible {u : ComplexModel (m + 1) → EReal}
    {Ω : Set (ComplexModel (m + 1))} (hu : PlurisubharmonicOn u Ω)
    {p : ComplexModel (m + 1)} (hp : p (Fin.last m) = 0) {r : ℝ}
    (hΩ : closedBall p (2 * r) ⊆ Ω) {K : ℝ} (hK : ∀ z ∈ closedBall p (2 * r), u z ≤ (K : EReal))
    {γ : ℝ}
    (hadm : ∀ q ∈ ball p r, q (Fin.last m) = 0 → ∃ γ' > γ, ∃ C : ℝ,
      ∀ᶠ z in 𝓝[≠] q, u z ≤ ((γ' * Real.log ‖z - q‖ + C : ℝ) : EReal))
    {z : ComplexModel (m + 1)} (hz : z ∈ ball p r) (hz0 : z (Fin.last m) ≠ 0) :
    u z ≤ ((γ * Real.log ‖z (Fin.last m)‖ + (K - γ * Real.log r) : ℝ) : EReal) := by
  set q := hyperplaneFoot z with hqdef
  have hzp : ‖z - p‖ < r := by rw [← dist_eq_norm]; exact mem_ball.mp hz
  have hqp : ‖q - p‖ < r := (norm_hyperplaneFoot_sub_le hp z).trans_lt hzp
  have hqball : q ∈ ball p r := by rw [mem_ball, dist_eq_norm]; exact hqp
  set t := ‖z (Fin.last m)‖ with ht
  have htpos : 0 < t := norm_pos_iff.mpr hz0
  have htr : t < r := (norm_last_le hp z).trans_lt hzp
  have hzq : ‖z - q‖ = t := norm_sub_hyperplaneFoot z
  obtain ⟨γ', hγγ', C, hC⟩ := hadm q hqball (hyperplaneFoot_last z)
  -- the punctured neighbourhood on which `γ'` is admissible
  obtain ⟨δ, hδ, hδC⟩ := Metric.mem_nhdsWithin_iff.mp hC
  set L := (K - C - γ * Real.log r) / (γ' - γ) with hL
  set r₁ := min (min (δ / 2) (t / 2)) (Real.exp L) with hr₁
  have hr₁pos : 0 < r₁ := lt_min (lt_min (by linarith) (by linarith)) (Real.exp_pos _)
  have hr₁t : r₁ < t := (min_le_left _ _).trans_lt ((min_le_right _ _).trans_lt (by linarith))
  have hr₁δ : r₁ < δ := (min_le_left _ _).trans_lt ((min_le_left _ _).trans_lt (by linarith))
  have hr₁r : r₁ < r := hr₁t.trans htr
  have hlogr₁ : Real.log r₁ ≤ L := by
    rw [Real.log_le_iff_le_exp hr₁pos]
    exact min_le_right _ _
  -- the closed ball about the foot lies in `Ω`, and `u ≤ K` there
  have hqsub : closedBall q r ⊆ closedBall p (2 * r) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw ⊢
    calc ‖w - p‖ = ‖(w - q) + (q - p)‖ := by congr 1; abel
      _ ≤ ‖w - q‖ + ‖q - p‖ := norm_add_le _ _
      _ ≤ 2 * r := by linarith
  -- inner sphere
  have h1 : ∀ w, ‖w - q‖ = r₁ → u w ≤ ((γ' * Real.log r₁ + C : ℝ) : EReal) := by
    intro w hw
    have hwmem : w ∈ ball q δ ∩ {q}ᶜ := by
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_eq_norm, hw]; exact hr₁δ
      · intro hwq
        rw [mem_singleton_iff] at hwq
        rw [hwq, sub_self, norm_zero] at hw
        exact hr₁pos.ne hw
    have := hδC hwmem
    simpa [hw] using this
  -- outer sphere
  have h3 : ∀ w, ‖w - q‖ = r → u w ≤ (K : EReal) := by
    intro w hw
    refine hK w (hqsub ?_)
    rw [mem_closedBall, dist_eq_norm, hw]
  have hinterp := le_log_interpolation hu hr₁pos hr₁r (hqsub.trans hΩ) h1 h3
    (by rw [hzq]; exact hr₁t.le) (by rw [hzq]; exact htr.le)
  rw [hzq] at hinterp
  refine hinterp.trans (EReal.coe_le_coe_iff.mpr ?_)
  exact log_interpolation_le hγγ' (Real.log_lt_log hr₁pos hr₁t) (Real.log_le_log htpos htr.le)
    hlogr₁

/-! ### From Lelong numbers to admissible exponents -/

/-- On `ℂ^{m+1}` (its own chart), an exponent `γ` below the Lelong number `ν(u, q)` is exceeded by
an admissible exponent: `u ≤ γ' log ‖· - q‖ + C` on a punctured neighbourhood of `q`, `γ' > γ`. -/
theorem exists_admissible_of_lt_lelongNumber {u : ComplexModel (m + 1) → EReal}
    {q : ComplexModel (m + 1)} {γ : ℝ≥0} (h : (γ : ℝ≥0∞) < lelongNumber (n := m + 1) u q) :
    ∃ γ' > (γ : ℝ), ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] q, u z ≤ ((γ' * Real.log ‖z - q‖ + C : ℝ) : EReal) := by
  unfold lelongNumber at h
  obtain ⟨γ', hγ'⟩ := lt_iSup_iff.mp h
  obtain ⟨hadm, hlt⟩ := lt_iSup_iff.mp hγ'
  obtain ⟨C, hC⟩ := hadm
  refine ⟨γ', by exact_mod_cast ENNReal.coe_lt_coe.mp hlt, C, ?_⟩
  simpa [complexChartAt, chartAt_self_eq] using hC

/-- **Slice bound from Lelong numbers along the hyperplane.**  If `ν(u, q) > γ` at every point `q`
of the hyperplane in `ball p r`, then `u(z) ≤ γ log |z_{m+1}| + (K - γ log r)` on `ball p r` off the
hyperplane. -/
theorem le_log_last_add_of_lt_lelongNumber {u : ComplexModel (m + 1) → EReal}
    {Ω : Set (ComplexModel (m + 1))} (hu : PlurisubharmonicOn u Ω)
    {p : ComplexModel (m + 1)} (hp : p (Fin.last m) = 0) {r : ℝ}
    (hΩ : closedBall p (2 * r) ⊆ Ω) {K : ℝ} (hK : ∀ z ∈ closedBall p (2 * r), u z ≤ (K : EReal))
    {γ : ℝ≥0}
    (hν : ∀ q ∈ ball p r, q (Fin.last m) = 0 → (γ : ℝ≥0∞) < lelongNumber (n := m + 1) u q)
    {z : ComplexModel (m + 1)} (hz : z ∈ ball p r) (hz0 : z (Fin.last m) ≠ 0) :
    u z ≤ (((γ : ℝ) * Real.log ‖z (Fin.last m)‖ + (K - (γ : ℝ) * Real.log r) : ℝ) : EReal) :=
  le_log_last_add_of_admissible hu hp hΩ hK
    (fun q hq hq0 => exists_admissible_of_lt_lelongNumber (hν q hq hq0)) hz hz0

end

end Hironaka.DivisorialSliceBound
