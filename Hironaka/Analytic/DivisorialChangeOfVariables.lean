import Hironaka.Analytic.DivisorialMultiplierOrder
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Complex

set_option autoImplicit false

/-!
# Weighted `L²` integrals along a holomorphic map, and the divisorial estimate in coordinates

Blueprint `pc:divisorial-multiplier-order` and `pc:demailly-divisorial-lelong` (Copy-4
`lem:domination`, Step 1), in coordinates: the divisor is the hyperplane `E₀ = {z_N = 0}` of
`ℂ^N` (`N = m + 1`) and `F` is the holomorphic map `ρ` read in coordinates.

* `det_restrictScalars_eq_normSq`, `complexJacobian`: the real Jacobian determinant of a
  `ℂ`-linear map is the squared modulus of its complex determinant.
* `lintegral_multiplierDensity_comp_le` — **change of variables**: if `F` is holomorphic on an
  open `U` and injective off a null set, then
  `∫_U |g ∘ F|² |J_F|² e^{-c w ∘ F} ≤ ∫_{F(U)} |g|² e^{-c w}`.
* `exists_eq_last_pow_mul_of_lintegral_image` — the vanishing order along `E₀` of `g ∘ F` for a
  germ `g` with `|g|² e^{-c w}` integrable near `F p` (`DivisorialMultiplierOrder` after the change
  of variables): `g ∘ F = z_N^a H` near `p` for every `a` with `a + k < c ν / 2`, where
  `J_F = z_N^k J'` with `J'` not identically zero on `E₀` near `p`.
* `exists_sum_normSq_le_of_lintegral_image` — for finitely many such germs,
  `∑ |gᵢ ∘ F|² ≤ C |z_N|^{2a}` near `p`.

Sorry-free.
-/

open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal

namespace Hironaka.DivisorialChangeOfVariables

open DivisorialMultiplierOrder

noncomputable section

variable {N : ℕ}

/-! ### The real Jacobian of a holomorphic map -/

/-- The complex Jacobian determinant of a map `ℂ^N → ℂ^N`. -/
def complexJacobian (F : ComplexModel N → ComplexModel N) (z : ComplexModel N) : ℂ :=
  (fderiv ℂ F z).det

/-- The real determinant of a `ℂ`-linear map of `ℂ^N` is the squared modulus of its complex
determinant. -/
theorem det_restrictScalars_eq_normSq (L : ComplexModel N →L[ℂ] ComplexModel N) :
    (L.restrictScalars ℝ).det = Complex.normSq L.det := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars, Algebra.norm_complex_apply]

/-- **Change of variables for weighted `L²` densities along a holomorphic map** that is injective
off a null set: `∫_U |g ∘ F|² |J_F|² e^{-c w ∘ F} ≤ ∫_{F(U)} |g|² e^{-c w}`. -/
theorem lintegral_multiplierDensity_comp_le {F : ComplexModel N → ComplexModel N}
    {U : Set (ComplexModel N)} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {S : Set (ComplexModel N)} (hS : volume S = 0) (hinj : InjOn F (U \ S))
    (w : ComplexModel N → EReal) (c : ℝ) (g : ComplexModel N → ℂ) :
    ∫⁻ z in U, multiplierDensity (fun z => w (F z)) c
        (fun z => g (F z) * complexJacobian F z) z ≤
      ∫⁻ y in F '' U, multiplierDensity w c g y := by
  set S' := toMeasurable volume S with hS'
  have hS'0 : volume S' = 0 := by rw [hS', measure_toMeasurable]; exact hS
  set s := U \ S' with hs
  have hsm : MeasurableSet s := hU.measurableSet.diff (measurableSet_toMeasurable _ _)
  have hinj' : InjOn F s := hinj.mono (sdiff_subset_sdiff_right (subset_toMeasurable _ _))
  have hderiv : ∀ x ∈ s, HasFDerivWithinAt F ((fderiv ℂ F x).restrictScalars ℝ) s x :=
    fun x hx => ((hF.differentiableAt (hU.mem_nhds hx.1)).hasFDerivAt.restrictScalars ℝ)
      |>.hasFDerivWithinAt
  have hcov := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsm hderiv hinj'
    (multiplierDensity w c g)
  calc ∫⁻ z in U, multiplierDensity (fun z => w (F z)) c
          (fun z => g (F z) * complexJacobian F z) z
        = ∫⁻ z in s, multiplierDensity (fun z => w (F z)) c
          (fun z => g (F z) * complexJacobian F z) z :=
          (setLIntegral_congr (sdiff_null_ae_eq_self hS'0)).symm
      _ = ∫⁻ x in s, ENNReal.ofReal |((fderiv ℂ F x).restrictScalars ℝ).det| *
            multiplierDensity w c g (F x) := by
          refine setLIntegral_congr_fun hsm fun z _ => ?_
          rw [det_restrictScalars_eq_normSq, abs_of_nonneg (Complex.normSq_nonneg _)]
          simp only [multiplierDensity, complexJacobian, norm_mul, mul_pow]
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
            Complex.normSq_eq_norm_sq, mul_comm (‖(fderiv ℂ F z).det‖ ^ 2)]
      _ = ∫⁻ y in F '' s, multiplierDensity w c g y := hcov.symm
      _ ≤ ∫⁻ y in F '' U, multiplierDensity w c g y :=
          lintegral_mono_set (image_mono sdiff_subset)

/-! ### The divisorial estimate in coordinates -/

/-- **Vanishing order along `E₀` of `g ∘ F`** (`pc:divisorial-multiplier-order` in coordinates).
Let `F` be holomorphic on an open `D ∋ p`, `p ∈ E₀`, injective off a null set; `|g|² e^{-c w}`
integrable on a neighbourhood `W` of `F p`, `g ∘ F` holomorphic near `p`; the slice bound
`w ∘ F ≤ γ log |z_N| + C` near `p` for every `γ < ν`; and `J_F = z_N^k J'` near `p` with `J'`
holomorphic and not identically zero on `E₀` near `p`.  Then `g ∘ F = z_N^a H` near `p` for every
`a` with `a = 0` or `a + k < c ν / 2`. -/
theorem exists_eq_last_pow_mul_of_lintegral_image {m : ℕ} {p : ComplexModel (m + 1)}
    (hp : p (Fin.last m) = 0) {F : ComplexModel (m + 1) → ComplexModel (m + 1)}
    {D : Set (ComplexModel (m + 1))} (hD : IsOpen D) (hpD : p ∈ D)
    (hF : DifferentiableOn ℂ F D) {S : Set (ComplexModel (m + 1))} (hS : volume S = 0)
    (hinj : InjOn F (D \ S)) {w : ComplexModel (m + 1) → EReal} {c ν : ℝ} (hc : 0 < c)
    {g : ComplexModel (m + 1) → ℂ} {W : Set (ComplexModel (m + 1))} (hW : IsOpen W)
    (hpW : F p ∈ W) (hgW : ∫⁻ y in W, multiplierDensity w c g y ≠ ⊤)
    (hgF : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (fun z => g (F z)) z)
    (hslice : ∀ γ < ν, ∃ U ∈ 𝓝 p, ∃ C : ℝ, ∀ z ∈ U, z (Fin.last m) ≠ 0 →
      w (F z) ≤ ((γ * Real.log ‖z (Fin.last m)‖ + C : ℝ) : EReal))
    {k : ℕ} {J' : ComplexModel (m + 1) → ℂ}
    (hJ' : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ J' z)
    (hJ : complexJacobian F =ᶠ[𝓝 p] fun z => z (Fin.last m) ^ k * J' z)
    (hJne : ∃ᶠ z in 𝓝 p, z (Fin.last m) = 0 ∧ J' z ≠ 0) :
    ∀ a : ℕ, (a = 0 ∨ (a : ℝ) + k < c * ν / 2) →
      ∃ H : ComplexModel (m + 1) → ℂ, (∀ᶠ z in 𝓝 p, DifferentiableAt ℂ H z) ∧
        (fun z => g (F z)) =ᶠ[𝓝 p] fun z => z (Fin.last m) ^ a * H z := by
  set U := D ∩ F ⁻¹' W with hUdef
  have hU : IsOpen U := hF.continuousOn.isOpen_inter_preimage hD hW
  have hpU : p ∈ U := ⟨hpD, hpW⟩
  have hint : ∃ U ∈ 𝓝 p, ∫⁻ z in U, multiplierDensity (fun z => w (F z)) c
      (fun z => g (F z) * complexJacobian F z) z ≠ ⊤ := by
    refine ⟨U, hU.mem_nhds hpU, ne_top_of_le_ne_top hgW ?_⟩
    refine (lintegral_multiplierDensity_comp_le hU (hF.mono inter_subset_left) hS
      (hinj.mono (sdiff_subset_sdiff_left inter_subset_left)) w c g).trans ?_
    exact lintegral_mono_set (image_subset_iff.mpr fun z hz => hz.2)
  exact exists_eq_last_pow_mul_of_lintegral_ne_top hp hc hslice hgF hJ' hJ hJne hint

/-- **Finitely many germs at once**: under the hypotheses of
`exists_eq_last_pow_mul_of_lintegral_image` for each `gᵢ`, `∑ᵢ |gᵢ ∘ F|² ≤ C |z_N|^{2a}` near `p`
for every `a` with `a = 0` or `a + k < c ν / 2`. -/
theorem exists_sum_normSq_le_of_lintegral_image {m : ℕ} {p : ComplexModel (m + 1)}
    (hp : p (Fin.last m) = 0) {F : ComplexModel (m + 1) → ComplexModel (m + 1)}
    {D : Set (ComplexModel (m + 1))} (hD : IsOpen D) (hpD : p ∈ D)
    (hF : DifferentiableOn ℂ F D) {S : Set (ComplexModel (m + 1))} (hS : volume S = 0)
    (hinj : InjOn F (D \ S)) {w : ComplexModel (m + 1) → EReal} {c ν : ℝ} (hc : 0 < c)
    {ι : Type*} [Fintype ι] {g : ι → ComplexModel (m + 1) → ℂ}
    (hgW : ∀ i, ∃ W : Set (ComplexModel (m + 1)), IsOpen W ∧ F p ∈ W ∧
      ∫⁻ y in W, multiplierDensity w c (g i) y ≠ ⊤)
    (hgF : ∀ i, ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (fun z => g i (F z)) z)
    (hslice : ∀ γ < ν, ∃ U ∈ 𝓝 p, ∃ C : ℝ, ∀ z ∈ U, z (Fin.last m) ≠ 0 →
      w (F z) ≤ ((γ * Real.log ‖z (Fin.last m)‖ + C : ℝ) : EReal))
    {k : ℕ} {J' : ComplexModel (m + 1) → ℂ}
    (hJ' : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ J' z)
    (hJ : complexJacobian F =ᶠ[𝓝 p] fun z => z (Fin.last m) ^ k * J' z)
    (hJne : ∃ᶠ z in 𝓝 p, z (Fin.last m) = 0 ∧ J' z ≠ 0)
    (a : ℕ) (ha : a = 0 ∨ (a : ℝ) + k < c * ν / 2) :
    ∃ C : ℝ, ∀ᶠ z in 𝓝 p, ∑ i, ‖g i (F z)‖ ^ 2 ≤ C * ‖z (Fin.last m)‖ ^ (2 * a) := by
  have hfac : ∀ i, ∃ H : ComplexModel (m + 1) → ℂ, (∀ᶠ z in 𝓝 p, DifferentiableAt ℂ H z) ∧
      (fun z => g i (F z)) =ᶠ[𝓝 p] fun z => z (Fin.last m) ^ a * H z := fun i => by
    obtain ⟨W, hW, hpW, hgi⟩ := hgW i
    exact exists_eq_last_pow_mul_of_lintegral_image hp hD hpD hF hS hinj hc hW hpW hgi (hgF i)
      hslice hJ' hJ hJne a ha
  choose H hHd hgH using hfac
  -- each `H i` is bounded near `p`
  have hbd : ∀ i, ∃ B : ℝ, ∀ᶠ z in 𝓝 p, ‖H i z‖ ^ 2 ≤ B := fun i => by
    have hc : ContinuousAt (fun z => ‖H i z‖ ^ 2) p :=
      ((hHd i).self_of_nhds.continuousAt.norm).pow 2
    exact ⟨‖H i p‖ ^ 2 + 1,
      hc.eventually (gt_mem_nhds (lt_add_one _)) |>.mono fun z hz => hz.le⟩
  choose B hB using hbd
  refine ⟨∑ i, B i, ?_⟩
  have hall : ∀ᶠ z in 𝓝 p, ∀ i, g i (F z) = z (Fin.last m) ^ a * H i z ∧ ‖H i z‖ ^ 2 ≤ B i :=
    eventually_all.2 fun i => (hgH i).and (hB i)
  filter_upwards [hall] with z hz
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [(hz i).1, norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm, mul_comm a 2]
  exact mul_le_mul_of_nonneg_right (hz i).2 (by positivity)

end

end Hironaka.DivisorialChangeOfVariables
