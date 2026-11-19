import Hironaka.Analytic.HormanderL2Spaces
import Mathlib.Algebra.QuadraticDiscriminant

set_option autoImplicit false

/-!
# The pairing bound in Hörmander's method

Let `D ⊆ ℂⁿ` be open, `Φ` plurisubharmonic and `χ`, `ψ₀` smooth on `D`, with weights
`w₁ = Φ + χ - 2ψ₀`, `w₂ = Φ + χ - ψ₀`, `w₃ = Φ + χ`.  If `f ∈ L²_{(0,1)}(e^{-w₂})` satisfies the
pointwise Levi bound `|⟨f, ξ⟩|² ≤ g · Levi_Φ(ξ)`, then for every test form `α`

  `|(α, f)_{w₂}|² ≤ (1 + t) (∫_D g e^{-w₁}) (‖T* α‖²_{w₁} + ∫ |∂̄ α|² e^{-w₃})`.

The proof is Cauchy--Schwarz, `|(α, f)| ≤ (∫ g e^{-w₁})^{1/2} (∫ Levi_Φ(α) e^{-w₃})^{1/2}`, followed
by the a priori estimate `apriori_global`, transferred to weights which are only smooth on `D`
(`apriori_on`).  This is Hörmander, *An introduction to complex analysis in several variables*,
proof of Theorem 4.2.1.
-/

open MeasureTheory Set Filter Complex
open scoped ComplexConjugate ContDiff Topology

namespace Hironaka.Hormander

noncomputable section

open CauchyGreen

variable {n : ℕ}

theorem fderiv_congr_of_eqOn {O : Set (ComplexModel n)} (hO : IsOpen O) {F G : ComplexModel n → ℝ}
    (hEq : EqOn F G O) {x : ComplexModel n} (hx : x ∈ O) : fderiv ℝ F x = fderiv ℝ G x := by
  have hev : F =ᶠ[𝓝 x] G := eventually_of_mem (hO.mem_nhds hx) fun y hy ↦ hEq hy
  exact hev.fderiv_eq

theorem leviForm_congr_of_eqOn {O : Set (ComplexModel n)} (hO : IsOpen O)
    {F G : ComplexModel n → ℝ} (hEq : EqOn F G O) {x : ComplexModel n} (hx : x ∈ O)
    (ξ : ComplexModel n) : leviForm F x ξ = leviForm G x ξ := by
  have hev : F =ᶠ[𝓝 x] G := eventually_of_mem (hO.mem_nhds hx) fun y hy ↦ hEq hy
  simp only [leviForm, realHessian_eq_fderiv, hev.fderiv.fderiv_eq]

/-- **The a priori estimate on `D`**, for weights smooth on `D`: the Levi integrand is integrable
on `D` and `∫_D Levi_Φ(α) e^{-w₃} ≤ (1 + t) ‖T* α‖²_{w₁} + ∫ |∂̄ α|² e^{-w₃}`. -/
theorem apriori_on {D : Set (ComplexModel n)} (hD : IsOpen D)
    {Φ χ ψ₀ : ComplexModel n → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ D) (hχ : ContDiffOn ℝ ∞ χ D)
    (hψ : ContDiffOn ℝ ∞ ψ₀ D) {t : ℝ} (ht : 0 < t)
    (hLevi : ∀ x ∈ D, ∀ ξ, (1 + 1 / t) * n * ‖fderiv ℝ ψ₀ x‖ ^ 2 * ‖ξ‖ ^ 2 ≤ leviForm χ x ξ)
    {α : Fin n → ComplexModel n → ℂ} (hα : α ∈ testForms D) :
    IntegrableOn (fun x ↦ leviForm Φ x (∑ j, α j x • coordVec j) * Real.exp (-(Φ x + χ x))) D ∧
    ∫ x in D, leviForm Φ x (∑ j, α j x • coordVec j) * Real.exp (-(Φ x + χ x)) ≤
      (1 + t) * (∫ x, ‖tstarForm (fun x ↦ Φ x + χ x - ψ₀ x) ψ₀ α x‖ ^ 2
            ∂(weightedVolume D fun x ↦ Φ x + χ x - 2 * ψ₀ x)) +
          ∫ x, (∑ p, ‖dbarForm α p x‖ ^ 2) * Real.exp (-(Φ x + χ x)) := by
  classical
  set K : Set (ComplexModel n) := ⋃ j, tsupport (α j) with hKdef
  have hK : IsCompact K := isCompact_iUnion fun j ↦ (hα j).2.1
  have hKD : K ⊆ D := iUnion_subset fun j ↦ (hα j).2.2
  obtain ⟨Φ', O₁, hΦ', hO₁, hKO₁, -, hEΦ⟩ := exists_global_weight hD hΦ hK hKD
  obtain ⟨χ', O₂, hχ', hO₂, hKO₂, -, hEχ⟩ := exists_global_weight hD hχ hK hKD
  obtain ⟨ψ', O₃, hψ', hO₃, hKO₃, hO₃D, hEψ⟩ := exists_global_weight hD hψ hK hKD
  set O := O₁ ∩ O₂ ∩ O₃ with hOdef
  have hO : IsOpen O := (hO₁.inter hO₂).inter hO₃
  have hKO : K ⊆ O := subset_inter (subset_inter hKO₁ hKO₂) hKO₃
  have hOD : O ⊆ D := inter_subset_right.trans hO₃D
  have hαO : ∀ j, tsupport (α j) ⊆ O := fun j ↦ (subset_iUnion (fun j ↦ tsupport (α j)) j).trans hKO
  have hout : ∀ x ∉ K, ∀ j, x ∉ tsupport (α j) := fun x hx j h ↦ hx (mem_iUnion.mpr ⟨j, h⟩)
  have hξ0 : ∀ x ∉ K, ∑ j, α j x • (coordVec j : ComplexModel n) = 0 := fun x hx ↦
    Finset.sum_eq_zero fun j _ ↦ by rw [eq_zero_of_notMem_tsupport' (hout x hx j), zero_smul]
  have hΦ2 : ContDiff ℝ 2 Φ' := hΦ'.of_le (by norm_cast)
  have hχ2 : ContDiff ℝ 2 χ' := hχ'.of_le (by norm_cast)
  have hψ2 : ContDiff ℝ 2 ψ' := hψ'.of_le (by norm_cast)
  have hα2 : ∀ j, ContDiff ℝ 2 (α j) := fun j ↦ (hα j).1.of_le (by norm_cast)
  have hw₁c : ContinuousOn (fun x ↦ Φ x + χ x - 2 * ψ₀ x) D :=
    (hΦ.continuousOn.add hχ.continuousOn).sub (continuousOn_const.mul hψ.continuousOn)
  have hEw₂ : EqOn (fun y ↦ Φ' y + χ' y - ψ' y) (fun y ↦ Φ y + χ y - ψ₀ y) O := fun y hy ↦ by
    simp only [hEΦ hy.1.1, hEχ hy.1.2, hEψ hy.2]
  have key := apriori_global hΦ2 hχ2 hψ2 ht hα2 (fun j ↦ (hα j).2.1) (by
    rintro x ⟨j, hj⟩ ξ
    have hxO : x ∈ O := hαO j hj
    rw [fderiv_congr_of_eqOn hO₃ hEψ hxO.2, leviForm_congr_of_eqOn hO₂ hEχ hxO.1.2]
    exact hLevi x (hOD hxO) ξ)
  -- the Levi integrand
  have hLeq : ∀ x, leviForm Φ' x (∑ j, α j x • coordVec j) * Real.exp (-(Φ' x + χ' x)) =
      D.indicator (fun x ↦ leviForm Φ x (∑ j, α j x • coordVec j) * Real.exp (-(Φ x + χ x))) x := by
    intro x
    by_cases hxO : x ∈ O
    · rw [indicator_of_mem (hOD hxO), leviForm_congr_of_eqOn hO₁ hEΦ hxO.1.1, hEΦ hxO.1.1,
        hEχ hxO.1.2]
    · have hxK : x ∉ K := fun h ↦ hxO (hKO h)
      by_cases hxD : x ∈ D
      · simp [indicator_of_mem hxD, hξ0 x hxK]
      · simp [indicator_of_notMem hxD, hξ0 x hxK]
  have iL : Integrable fun x ↦ leviForm Φ' x (∑ j, α j x • coordVec j) *
      Real.exp (-(Φ' x + χ' x)) := by
    have hexp : Continuous fun x ↦ Real.exp (-(Φ' x + χ' x)) := by
      have := hΦ'.continuous; have := hχ'.continuous; fun_prop
    have hξc : Continuous fun x ↦ ∑ j, α j x • (coordVec j : ComplexModel n) := by
      have := fun j ↦ (hα2 j).continuous; fun_prop
    refine integrable_of_continuous_of_eq_zero_off hK
      ((continuous_leviForm_comp hΦ2 hξc).mul hexp) fun x hx ↦ ?_
    simp [hξ0 x hx]
  have hLint : ∫ x, leviForm Φ' x (∑ j, α j x • coordVec j) * Real.exp (-(Φ' x + χ' x)) =
      ∫ x in D, leviForm Φ x (∑ j, α j x • coordVec j) * Real.exp (-(Φ x + χ x)) := by
    simp_rw [hLeq]
    exact integral_indicator hD.measurableSet
  refine ⟨?_, ?_⟩
  · rw [← integrable_indicator_iff hD.measurableSet]
    exact iL.congr (Eventually.of_forall hLeq)
  -- the adjoint term
  have hT : ∫ x, ‖tstarForm (fun y ↦ Φ' y + χ' y - ψ' y) ψ' α x‖ ^ 2 *
      Real.exp (-(Φ' x + χ' x - 2 * ψ' x)) =
      ∫ x, ‖tstarForm (fun x ↦ Φ x + χ x - ψ₀ x) ψ₀ α x‖ ^ 2
        ∂(weightedVolume D fun x ↦ Φ x + χ x - 2 * ψ₀ x) := by
    rw [integral_weightedVolume hD hw₁c, ← integral_indicator hD.measurableSet]
    congr 1
    funext x
    by_cases hxO : x ∈ O
    · rw [indicator_of_mem (hOD hxO), smul_eq_mul, mul_comm]
      simp only [tstarForm, hEΦ hxO.1.1, hEχ hxO.1.2, hEψ hxO.2]
      congr 4
      exact Finset.sum_congr rfl fun j _ ↦ deltaDir_congr_weight hO hEw₂ (hαO j) _ x
    · have hxK : x ∉ K := fun h ↦ hxO (hKO h)
      have h0 : ∀ (W ψ : ComplexModel n → ℝ), tstarForm W ψ α x = 0 := fun W ψ ↦ by
        simp [tstarForm, deltaDir_eq_zero_of_notMem_tsupport (hout x hxK _)]
      by_cases hxD : x ∈ D
      · simp [indicator_of_mem hxD, h0]
      · simp [indicator_of_notMem hxD, h0]
  -- the `∂̄` term
  have hS : ∫ x, (∑ p, ‖dbarForm α p x‖ ^ 2) * Real.exp (-(Φ' x + χ' x)) =
      ∫ x, (∑ p, ‖dbarForm α p x‖ ^ 2) * Real.exp (-(Φ x + χ x)) := by
    congr 1
    funext x
    by_cases hxO : x ∈ O
    · rw [hEΦ hxO.1.1, hEχ hxO.1.2]
    · have hxK : x ∉ K := fun h ↦ hxO (hKO h)
      simp [dbarForm, dbarDir_eq_zero_of_notMem_tsupport (hout x hxK _)]
  rw [← hLint, ← hT, ← hS]
  exact key

theorem two_mul_le_add_of_sq_le {a X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y) (h : a ^ 2 ≤ X * Y) :
    2 * a ≤ X + Y := by
  by_cases ha : a ≤ 0
  · linarith
  push Not at ha
  have h2 : (2 * a) ^ 2 ≤ (X + Y) ^ 2 := by nlinarith [sq_nonneg (X - Y)]
  exact (pow_le_pow_iff_left₀ (by linarith) (by linarith) two_ne_zero).mp h2

/-- **The pairing bound.** For `f` in `L²_{(0,1)}(D, e^{-w₂})` with pointwise Levi bound
`|⟨f, ξ⟩|² ≤ g · Levi_Φ(ξ)` and every test form `α`,
`|(α, f)_{w₂}|² ≤ (1 + t) (∫_D g e^{-w₁}) (‖T* α‖²_{w₁} + ∫ |∂̄ α|² e^{-w₃})`. -/
theorem norm_sq_pairing_le {n : ℕ} {D : Set (ComplexModel n)} (hD : IsOpen D)
    {Φ χ ψ₀ : ComplexModel n → ℝ} (hΦ : ContDiffOn ℝ ∞ Φ D) (hχ : ContDiffOn ℝ ∞ χ D)
    (hψ : ContDiffOn ℝ ∞ ψ₀ D) (hpsh : ∀ x ∈ D, ∀ ξ, 0 ≤ leviForm Φ x ξ)
    {t : ℝ} (ht : 0 < t)
    (hLevi : ∀ x ∈ D, ∀ ξ, (1 + 1 / t) * n * ‖fderiv ℝ ψ₀ x‖ ^ 2 * ‖ξ‖ ^ 2 ≤ leviForm χ x ξ)
    {f : Fin n → ComplexModel n → ℂ}
    (hf : ∀ j, MemLp (f j) 2 (weightedVolume D fun x ↦ Φ x + χ x - ψ₀ x))
    {g : ComplexModel n → ℝ} (hg0 : ∀ x ∈ D, 0 ≤ g x)
    (hfg : ∀ x ∈ D, ∀ ξ : Fin n → ℂ,
      ‖∑ j, conj (ξ j) * f j x‖ ^ 2 ≤ g x * leviForm Φ x (∑ j, ξ j • coordVec j))
    (hgi : Integrable (fun x ↦ g x * Real.exp (-(Φ x + χ x - 2 * ψ₀ x))) (volume.restrict D))
    {α : Fin n → ComplexModel n → ℂ} (hα : α ∈ testForms D) :
    ‖∑ j, ∫ x, conj (α j x) * f j x ∂(weightedVolume D fun x ↦ Φ x + χ x - ψ₀ x)‖ ^ 2 ≤
      (1 + t) * (∫ x in D, g x * Real.exp (-(Φ x + χ x - 2 * ψ₀ x))) *
        ((∫ x, ‖tstarForm (fun x ↦ Φ x + χ x - ψ₀ x) ψ₀ α x‖ ^ 2
            ∂(weightedVolume D fun x ↦ Φ x + χ x - 2 * ψ₀ x)) +
          ∫ x, (∑ p, ‖dbarForm α p x‖ ^ 2) * Real.exp (-(Φ x + χ x))) := by
  obtain ⟨iL, hap⟩ := apriori_on hD hΦ hχ hψ ht hLevi (Φ := Φ) hα
  have hw₂c : ContinuousOn (fun x ↦ Φ x + χ x - ψ₀ x) D :=
    (hΦ.continuousOn.add hχ.continuousOn).sub hψ.continuousOn
  set I := ∑ j, ∫ x, conj (α j x) * f j x ∂(weightedVolume D fun x ↦ Φ x + χ x - ψ₀ x) with hIdef
  set G := ∫ x in D, g x * Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) with hGdef
  set Λ := ∫ x in D, leviForm Φ x (∑ j, α j x • coordVec j) * Real.exp (-(Φ x + χ x)) with hΛdef
  set A := ∫ x, ‖tstarForm (fun x ↦ Φ x + χ x - ψ₀ x) ψ₀ α x‖ ^ 2
    ∂(weightedVolume D fun x ↦ Φ x + χ x - 2 * ψ₀ x) with hAdef
  set B := ∫ x, (∑ p, ‖dbarForm α p x‖ ^ 2) * Real.exp (-(Φ x + χ x)) with hBdef
  have hαm : ∀ j, MemLp (fun x ↦ conj (α j x)) 2
      (weightedVolume D fun x ↦ Φ x + χ x - ψ₀ x) := fun j ↦ by
    have h := (hα j).conj
    exact memLp_weightedVolume_of_continuous hD hw₂c h.1.continuous h.2.1 h.2.2 2
  have hI : I = ∫ x in D, Real.exp (-(Φ x + χ x - ψ₀ x)) • ∑ j, conj (α j x) * f j x := by
    rw [hIdef, ← integral_finsetSum _ fun j _ ↦ integrable_mul_of_memLp_two (hαm j) (hf j)]
    exact integral_weightedVolume hD hw₂c _
  have hnormI : ‖I‖ ≤ ∫ x in D, Real.exp (-(Φ x + χ x - ψ₀ x)) * ‖∑ j, conj (α j x) * f j x‖ := by
    rw [hI]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext x
    rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hG0 : 0 ≤ G := setIntegral_nonneg hD.measurableSet fun x hx ↦
    mul_nonneg (hg0 x hx) (Real.exp_pos _).le
  have hΛ0 : 0 ≤ Λ := setIntegral_nonneg hD.measurableSet fun x hx ↦
    mul_nonneg (hpsh x hx _) (Real.exp_pos _).le
  have hA0 : 0 ≤ A := integral_nonneg fun x ↦ sq_nonneg _
  have hB0 : 0 ≤ B := integral_nonneg fun x ↦
    mul_nonneg (Finset.sum_nonneg fun p _ ↦ sq_nonneg _) (Real.exp_pos _).le
  -- Cauchy--Schwarz in the form `2 s ‖I‖ ≤ s² G + Λ`
  have hquad : ∀ s : ℝ, 0 ≤ G * (s * s) + (-2 * ‖I‖) * s + Λ := by
    intro s
    by_cases hs : s ≤ 0
    · nlinarith [norm_nonneg I, mul_nonneg hG0 (mul_self_nonneg s)]
    push Not at hs
    have hpt : ∀ᵐ x ∂(volume.restrict D),
        (2 * s) * (Real.exp (-(Φ x + χ x - ψ₀ x)) * ‖∑ j, conj (α j x) * f j x‖) ≤
          s * s * (g x * Real.exp (-(Φ x + χ x - 2 * ψ₀ x))) +
            leviForm Φ x (∑ j, α j x • coordVec j) * Real.exp (-(Φ x + χ x)) := by
      filter_upwards [ae_restrict_mem hD.measurableSet] with x hx
      have hS2 := hfg x hx fun j ↦ α j x
      have hL0 := hpsh x hx (∑ j, α j x • coordVec j)
      have hE : Real.exp (-(Φ x + χ x - ψ₀ x)) ^ 2 =
          Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) * Real.exp (-(Φ x + χ x)) := by
        rw [sq, ← Real.exp_add, ← Real.exp_add]; ring_nf
      have hX : 0 ≤ s * s * (g x * Real.exp (-(Φ x + χ x - 2 * ψ₀ x))) :=
        mul_nonneg (mul_self_nonneg s) (mul_nonneg (hg0 x hx) (Real.exp_pos _).le)
      have hY : 0 ≤ leviForm Φ x (∑ j, α j x • coordVec j) * Real.exp (-(Φ x + χ x)) :=
        mul_nonneg hL0 (Real.exp_pos _).le
      have h := two_mul_le_add_of_sq_le hX hY
        (a := s * (Real.exp (-(Φ x + χ x - ψ₀ x)) * ‖∑ j, conj (α j x) * f j x‖)) (by
          have e : (s * (Real.exp (-(Φ x + χ x - ψ₀ x)) * ‖∑ j, conj (α j x) * f j x‖)) ^ 2 =
              s * s * Real.exp (-(Φ x + χ x - ψ₀ x)) ^ 2 * ‖∑ j, conj (α j x) * f j x‖ ^ 2 := by
            ring
          rw [e, hE]
          have hE13 : 0 ≤ s * s * (Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) * Real.exp (-(Φ x + χ x))) :=
            mul_nonneg (mul_self_nonneg s) (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          calc s * s * (Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) * Real.exp (-(Φ x + χ x))) *
                ‖∑ j, conj (α j x) * f j x‖ ^ 2
              ≤ s * s * (Real.exp (-(Φ x + χ x - 2 * ψ₀ x)) * Real.exp (-(Φ x + χ x))) *
                (g x * leviForm Φ x (∑ j, α j x • coordVec j)) :=
                mul_le_mul_of_nonneg_left hS2 hE13
            _ = _ := by ring)
      linarith
    have hmono := integral_mono_of_nonneg
      (Eventually.of_forall fun x ↦ mul_nonneg (by linarith)
        (mul_nonneg (Real.exp_pos _).le (norm_nonneg _)))
      ((hgi.const_mul (s * s)).add iL) hpt
    simp only [Pi.add_apply] at hmono
    rw [integral_const_mul, integral_add (hgi.const_mul (s * s)) iL, integral_const_mul] at hmono
    nlinarith
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  have hIG : ‖I‖ ^ 2 ≤ G * Λ := by nlinarith
  calc ‖I‖ ^ 2 ≤ G * Λ := hIG
    _ ≤ G * ((1 + t) * A + B) := mul_le_mul_of_nonneg_left hap hG0
    _ ≤ (1 + t) * G * (A + B) := by nlinarith [mul_nonneg hG0 hB0]

end

end Hironaka.Hormander
