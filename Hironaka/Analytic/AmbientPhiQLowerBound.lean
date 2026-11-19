import Hironaka.Analytic.AmbientConvexCurrent
import Hironaka.Analytic.CollarWeightComparison

set_option autoImplicit false

/-!
# The source-free `eq:phiQ-lower` calculation

Copy-4's ambient calculation has two logically separate parts.  The lower
bound for `Phi_R` uses Rückert's Nullstellensatz, while the passage from the
two displayed lower bounds for `U_M` and `Phi_R` to the lower bound for their
convex combination is elementary `EReal` arithmetic.  This module contains
only the latter part, so consumers which already provide the two lower bounds
do not acquire a dependency on the Nullstellensatz source interface.

Source: Copy-4, `sec:ambient`, equation `eq:phiQ-lower`
(`source/main-Nulllocus.tex:1721-1745`).
-/

open Set

namespace Hironaka.AmbientPhiQLowerBound


open Hironaka.CollarWeightComparison
open Hironaka.ThetaPshConvexCombination

noncomputable section

/-! ### An `EReal` multiple is a natural multiple -/

/-- `N • x = N x` on `EReal`, with the real coefficient.  Both sides are `0`
at `N = 0`, including at `x = ⊥`. -/
theorem nsmul_eq_coe_mul : ∀ (N : ℕ) (x : EReal), N • x = ((N : ℝ) : EReal) * x
  | 0, x => by simp
  | (k + 1), x => by
      have h1 : (((k + 1 : ℕ) : ℝ) : EReal) = ((k : ℝ) : EReal) + ((1 : ℝ) : EReal) := by
        rw [← EReal.coe_add]
        norm_num
      rw [succ_nsmul, nsmul_eq_coe_mul k x, h1,
        EReal.right_distrib_of_nonneg
          (EReal.coe_nonneg.mpr (by positivity)) (EReal.coe_nonneg.mpr zero_le_one)]
      norm_num

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- **`eq:phiQ-lower`** (Copy-4, `sec:ambient`).  The lower bounds
`U_M ≥ M⁻¹ ψ_{B_M} + O(1)` and
`Phi_R ≥ A_R (ψ_{I_V} + ψ_j) + O(1)` combine to the displayed lower bound for
`(1-L/M) U_M + (L/M) Phi_R`.  This is independent of how either input lower
bound was obtained. -/
theorem moreSingularOn_phiQ_lower
    {UM ΦR ψBM ψIV ψj : M → EReal} {L lev A : ℝ}
    (hL : 0 < L) (hLlev : L < lev)
    (hU : MoreSingularOn (fun x => ((1 / lev : ℝ) : EReal) * ψBM x) UM univ)
    (hΦ : MoreSingularOn (fun x => (A : EReal) * (ψIV x + ψj x)) ΦR univ) :
    MoreSingularOn
      (fun x => (((1 - L / lev) / lev : ℝ) : EReal) * ψBM x
        + ((L * A / lev : ℝ) : EReal) * (ψIV x + ψj x))
      (convexComb (1 - L / lev) UM ΦR) univ := by
  have hlev : 0 < lev := lt_trans hL hLlev
  have hratio0 : 0 < L / lev := by positivity
  have hratio1 : L / lev < 1 := (div_lt_one hlev).mpr hLlev
  set t : ℝ := 1 - L / lev with ht
  have ht0 : 0 < t := by simp only [ht]; linarith
  have ht1 : t < 1 := by simp only [ht]; linarith
  obtain ⟨C₁, hC₁⟩ := hU
  obtain ⟨C₂, hC₂⟩ := hΦ
  refine ⟨t * C₁ + (1 - t) * C₂, fun x hx => ?_⟩
  have hcomb := AmbientConvexCurrent.convexComb_lower_bound (M := M) ht0 ht1 hC₁ hC₂ x hx
  refine le_trans (le_of_eq ?_) hcomb
  have e1 : t / lev = t * (1 / lev) := by ring
  have e2 : L * A / lev = (1 - t) * A := by rw [ht]; ring
  simp only [convexComb_apply, e1, e2, EReal.coe_mul, mul_assoc]

end

end Hironaka.AmbientPhiQLowerBound
