import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod

set_option autoImplicit false

/-! # Actual finite Tonelli products for multiplier densities -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.FiniteMultiplierProductIntegral

noncomputable section

/-- Actual finite Tonelli factorization, with no finite-integral assumptions. -/
theorem lintegral_fin_prod_eq_prod {n : ℕ} {X : Fin n → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : Fin n) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → X i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x : (i : Fin n) → X i, ∏ i, f i (x i) ∂Measure.pi μ) =
      ∏ i, ∫⁻ x, f i x ∂μ i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hm : Measurable (fun x : (i : Fin (n + 1)) → X i => ∏ i, f i (x i)) :=
      by fun_prop
    have ht : Measurable (fun x : (i : Fin n) → X i.succ => ∏ i, f i.succ (x i)) :=
      by fun_prop
    calc
      _ = ∫⁻ x : X 0 × ((i : Fin n) → X i.succ),
          f 0 x.1 * ∏ i : Fin n, f i.succ (x.2 i)
          ∂((μ 0).prod (Measure.pi (fun i : Fin n => μ i.succ))) := by
        rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp hm]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero]
        simp only [Fin.zero_succAbove]
        rfl
      _ = (∫⁻ x, f 0 x ∂μ 0) *
          ∫⁻ x : (i : Fin n) → X i.succ, ∏ i, f i.succ (x i)
            ∂Measure.pi (fun i : Fin n => μ i.succ) :=
        lintegral_prod_mul (hf 0).aemeasurable ht.aemeasurable
      _ = ∏ i, ∫⁻ x, f i x ∂μ i := by
        rw [ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf i.succ),
          Fin.prod_univ_succ]

/-- Pointwise nonzero densities in nonzero measures internally give the finite-product criterion. -/
theorem lintegral_fin_prod_lt_top_iff {n : ℕ} {X : Fin n → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : (i : Fin n) → Measure (X i))
    [∀ i, SigmaFinite (μ i)] (f : (i : Fin n) → X i → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hμ : ∀ i, μ i ≠ 0)
    (hpos : ∀ i, ∀ᵐ x ∂μ i, f i x ≠ 0) :
    (∫⁻ x : (i : Fin n) → X i, ∏ i, f i (x i) ∂Measure.pi μ) < ⊤ ↔
      ∀ i, (∫⁻ x, f i x ∂μ i) < ⊤ := by
  classical
  have hI : ∀ i, (∫⁻ x, f i x ∂μ i) ≠ 0 := by
    intro i hzero
    let : NeZero (μ i) := ⟨hμ i⟩
    have heq := (lintegral_eq_zero_iff' (hf i).aemeasurable).mp hzero
    obtain ⟨x, hx, hx0⟩ := ((hpos i).and heq).exists
    exact hx hx0
  rw [lintegral_fin_prod_eq_prod μ f hf]
  constructor
  · intro hfinite i
    by_contra hnot
    have hi : (∫⁻ x, f i x ∂μ i) = ⊤ := ENNReal.not_lt_top.mp hnot
    exact hfinite.ne (WithTop.prod_eq_top (Finset.mem_univ i) hi (fun j _ => hI j))
  · intro hfinite
    exact ENNReal.prod_lt_top (fun i _ => hfinite i)

end
end Hironaka.FiniteMultiplierProductIntegral
