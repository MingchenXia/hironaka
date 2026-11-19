import Hironaka.Analytic.LocalBergmanThetaBranch

set_option autoImplicit false

/-!
# Lower comparison for a local Bergman branch

The finite-generator domination retained in a `LocalBergmanPatch` yields the
Demailly lower estimate for the original potential.  The proof enlarges the
nonnegative domination constant by one before taking logarithms, so no
cancellation at a zero generator sum or a polar value is used.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Hironaka.BergmanBranchLowerComparison


open DemaillyAnalyticType
open QuasiEquisingularBergmanAtlas
open QuasiEquisingularBergmanBranch

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The finite Bergman-generator domination on a patch gives a local Demailly
lower estimate for the original potential.  The conclusion is an
extended-real inequality; it does not assign a finite value at a pole. -/
theorem LocalBergmanPatch.exists_original_le_bergmanBranch_add
    {θ : SmoothRealForm n M 2} {u : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (hm : 0 < m) :
    ∃ C : ℝ, ∀ x ∈ D.source, u x ≤ bergmanBranch D x + (C : EReal) := by
  obtain ⟨K, hKtop, hdom⟩ := D.domination
  set Kplus : ℝ≥0∞ := K + 1 with hKplus
  have hKplus_top : Kplus ≠ ⊤ := by
    rw [hKplus, ENNReal.add_ne_top]
    exact ⟨hKtop, ENNReal.one_ne_top⟩
  have hKplus_pos : 0 < Kplus := by
    rw [hKplus]
    exact lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_left bot_le)
  have hKplus_zero : Kplus ≠ 0 := ne_of_gt hKplus_pos
  have hKplus_toReal_pos : 0 < Kplus.toReal :=
    ENNReal.toReal_pos hKplus_zero hKplus_top
  let a : EReal := (((m : ℝ)⁻¹ : ℝ) : EReal)
  set R : ℝ := (m : ℝ)⁻¹ * Real.log Kplus.toReal with hR
  refine ⟨R, fun x hx => ?_⟩
  have hy : D.chart.val x ∈ D.domain := hx.2
  have hKle : K ≤ Kplus := by
    rw [hKplus]
    exact le_add_of_nonneg_right bot_le
  have hdomplus : EReal.exp ((m : EReal) *
      (chartFunction u D.chart (D.chart.val x) + (D.potential (D.chart.val x) : EReal))) ≤
      Kplus * ∑ l, ENNReal.ofReal (‖D.generator l (D.chart.val x)‖ ^ 2) :=
    (hdom _ hy).trans (mul_le_mul_of_nonneg_right hKle bot_le)
  have hsum_eq : ENNReal.ofReal (∑ l, ‖D.generator l (D.chart.val x)‖ ^ 2) =
      ∑ l, ENNReal.ofReal (‖D.generator l (D.chart.val x)‖ ^ 2) := by
    simpa using (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ)
      (f := fun l => ‖D.generator l (D.chart.val x)‖ ^ 2)
      (fun l _ => sq_nonneg _))
  have hlog : (m : EReal) *
      (chartFunction u D.chart (D.chart.val x) + (D.potential (D.chart.val x) : EReal)) ≤
      Kplus.log + generatorLog D.generator (D.chart.val x) := by
    rw [generatorLog_eq_log_sum, hsum_eq]
    simpa only [EReal.log_exp, ENNReal.log_mul_add] using ENNReal.log_le_log hdomplus
  have hKplus_log : Kplus.log = (Real.log Kplus.toReal : EReal) := by
    calc
      Kplus.log = (ENNReal.ofReal Kplus.toReal).log := by
        rw [ENNReal.ofReal_toReal hKplus_top]
      _ = (Real.log Kplus.toReal : EReal) :=
        ENNReal.log_ofReal_of_pos hKplus_toReal_pos
  rw [hKplus_log] at hlog
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact_mod_cast inv_nonneg.mpr (by positivity : 0 ≤ (m : ℝ))
  have ha_ne_top : a ≠ ⊤ := by
    dsimp [a]
    exact EReal.coe_ne_top _
  have hacancel : a * (m : EReal) = 1 := by
    dsimp [a]
    norm_cast
    field_simp
  have hscaled :
      chartFunction u D.chart (D.chart.val x) + (D.potential (D.chart.val x) : EReal) ≤
        a * (Real.log Kplus.toReal : EReal) +
          a * generatorLog D.generator (D.chart.val x) := by
    calc
      chartFunction u D.chart (D.chart.val x) + (D.potential (D.chart.val x) : EReal) =
          (a * (m : EReal)) *
            (chartFunction u D.chart (D.chart.val x) + (D.potential (D.chart.val x) : EReal)) := by
        rw [hacancel, one_mul]
      _ = a * ((m : EReal) *
            (chartFunction u D.chart (D.chart.val x) + (D.potential (D.chart.val x) : EReal))) := by
        rw [mul_assoc]
      _ ≤ a * ((Real.log Kplus.toReal : EReal) +
            generatorLog D.generator (D.chart.val x)) :=
        mul_le_mul_of_nonneg_left hlog ha_nonneg
      _ = a * (Real.log Kplus.toReal : EReal) +
            a * generatorLog D.generator (D.chart.val x) :=
        EReal.left_distrib_of_nonneg_of_ne_top ha_nonneg ha_ne_top _ _
  have hsum_upper : u x + (D.potential (D.chart.val x) : EReal) ≤
      a * generatorLog D.generator (D.chart.val x) +
        a * (Real.log Kplus.toReal : EReal) := by
    simpa only [chartFunction, D.chart.val.left_inv hx.1, add_comm] using hscaled
  have hsub : u x ≤
      (a * generatorLog D.generator (D.chart.val x) +
        a * (Real.log Kplus.toReal : EReal)) -
          (D.potential (D.chart.val x) : EReal) :=
    (EReal.le_sub_iff_add_le
      (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))).mpr hsum_upper
  have hRcoe : (R : EReal) = a * (Real.log Kplus.toReal : EReal) := by
    rw [hR, EReal.coe_mul]
  have hrearr :
      (a * generatorLog D.generator (D.chart.val x) -
          (D.potential (D.chart.val x) : EReal)) +
        a * (Real.log Kplus.toReal : EReal) =
      (a * generatorLog D.generator (D.chart.val x) +
        a * (Real.log Kplus.toReal : EReal)) -
          (D.potential (D.chart.val x) : EReal) := by
    calc
      (a * generatorLog D.generator (D.chart.val x) -
          (D.potential (D.chart.val x) : EReal)) +
        a * (Real.log Kplus.toReal : EReal) =
        a * (Real.log Kplus.toReal : EReal) +
          (a * generatorLog D.generator (D.chart.val x) -
            (D.potential (D.chart.val x) : EReal)) := add_comm _ _
      _ = (a * (Real.log Kplus.toReal : EReal) +
          a * generatorLog D.generator (D.chart.val x)) -
            (D.potential (D.chart.val x) : EReal) := (add_sub_assoc _ _ _).symm
      _ = (a * generatorLog D.generator (D.chart.val x) +
          a * (Real.log Kplus.toReal : EReal)) -
            (D.potential (D.chart.val x) : EReal) := by
        rw [add_comm]
  rw [bergmanBranch]
  split
  · rw [hRcoe]
    exact hsub.trans_eq hrearr.symm
  · rename_i hnot_source
    exact (hnot_source hx).elim

/-- Any branch bounded above by the original potential up to a real constant
also satisfies the corresponding lower comparison with the Bergman branch. -/
theorem LocalBergmanPatch.exists_le_bergmanBranch_add_of_le_original_add
    {θ : SmoothRealForm n M 2} {u g : M → EReal} {m : ℕ}
    (D : LocalBergmanPatch θ u m) (hm : 0 < m) {B : ℝ}
    (hg : ∀ x ∈ D.source, g x ≤ u x + (B : EReal)) :
    ∃ C : ℝ, ∀ x ∈ D.source, g x ≤ bergmanBranch D x + (C : EReal) := by
  obtain ⟨C, hC⟩ := LocalBergmanPatch.exists_original_le_bergmanBranch_add D hm
  refine ⟨C + B, fun x hx => ?_⟩
  calc
    g x ≤ u x + (B : EReal) := hg x hx
    _ ≤ (bergmanBranch D x + (C : EReal)) + (B : EReal) := by
      simpa only [add_comm] using add_le_add_left (hC x hx) (B : EReal)
    _ = bergmanBranch D x + ((C + B : ℝ) : EReal) := by
      rw [EReal.coe_add]
      ac_rfl

end

end Hironaka.BergmanBranchLowerComparison
