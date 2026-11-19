import Hironaka.Analytic.PullbackNonvanishing
import Hironaka.Analytic.MeteredDivisorPositivity
import Hironaka.Analytic.CollarWeightComparison

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Nonnegative rational multiples of a metered effective `ℚ`-divisor

Source: Copy-4, `eq:def-DLY` and Step 2 of `prop:principalization`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1875-1893`),
where the two divisors the proof runs on are

  `H = H^fix_m + P^mov + P^F`,
  `D = (1/M) G̃_M + ((C-1)/M) P^mov + (C/M) P^F + τ E_rel`.

`Pending/MeteredDivisorOperations` has the sum; the rational multiple was
missing, and `D` is not expressible without it.  `smul` supplies it: the weight
is multiplied by the coefficient, the curvature is the real multiple of the
curvature, and the local presentation is the old one with every exponent `aᵢ`
scaled and the smooth remainder `h` scaled.

The two weight identities `weight_smul` and `weight_add` are *definitional*, so
the hypotheses `hD` and `hH` of
`CollarWeightComparison.moreSingularOn_exceptionalWeightSum` hold on the nose for
divisors built this way — no `O(1)` is spent on them.  `weight_qcomb4` records
`eq:def-DLY` in that form.

The module closes with `exists_forall_weight_le`: on a compact manifold the
weight of a metered divisor is bounded above, because it is quasi-psh
(`MeteredDivisorPositivity.thetaPlurisubharmonic_weight`).  That discharges the
five boundedness hypotheses of `moreSingularOn_exceptionalWeightSum`.

Everything here is sorry-free.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MeteredDivisorScaling

open Hironaka.HolomorphicIdealSheaves
open Hironaka.MeteredDivisorOperations

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- A finite nonnegative real coefficient distributes over a finite `EReal` sum.
No hypothesis on the summands: the coefficient is finite and nonnegative, which
is all `EReal.left_distrib_of_nonneg_of_ne_top` needs. -/
theorem coe_mul_finsetSum {ι : Type*} (s : Finset ι) {c : ℝ} (hc : 0 ≤ c)
    (f : ι → EReal) :
    (c : EReal) * (∑ i ∈ s, f i) = ∑ i ∈ s, (c : EReal) * f i := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.sum_insert hi,
    EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hc)
      (EReal.coe_ne_top c), ih]

/-- **The nonnegative rational multiple `c E` of a metered effective
`ℚ`-divisor.**  Its weight is `c ψ_E` and its curvature `c Θ_E`. -/
def smul {c : ℚ} (hc : 0 ≤ c) (E : MeteredEffectiveQDivisor n M) :
    MeteredEffectiveQDivisor n M where
  weight := fun y => ((c : ℝ) : EReal) * E.weight y
  curvature := (c : ℝ) • E.curvature
  local_presentation := fun x => by
    obtain ⟨U, hU, hxU, N, a, g, h, ha, hg, hne, hh, hw, hcurv⟩ := E.local_presentation x
    have hcR : (0 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
    refine ⟨U, hU, hxU, N, fun i => c * a i, g, fun y => (c : ℝ) • h y,
      fun i => mul_nonneg hc (ha i), hg, hne, fun e => (hh e).const_smul (c : ℝ), ?_, ?_⟩
    · intro y hy
      show ((c : ℝ) : EReal) * E.weight y = _
      rw [hw y hy, EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.mpr hcR)
        (EReal.coe_ne_top _), coe_mul_finsetSum _ hcR]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← mul_assoc, ← EReal.coe_mul]
        norm_cast
    · intro e z hz hzU
      rw [ClosedRealOneOneForm.coeff_smul, hcurv e z hz hzU,
        smoothDDC_smul (e.val.isOpen_inter_preimage_symm hU) (hh e) (c : ℝ) ⟨hz, hzU⟩]
      simp

@[simp] theorem weight_smul {c : ℚ} (hc : 0 ≤ c) (E : MeteredEffectiveQDivisor n M)
    (y : M) : (smul hc E).weight y = ((c : ℝ) : EReal) * E.weight y := rfl

@[simp] theorem curvature_smul {c : ℚ} (hc : 0 ≤ c) (E : MeteredEffectiveQDivisor n M) :
    (smul hc E).curvature = (c : ℝ) • E.curvature := rfl

@[simp] theorem weight_add (E E' : MeteredEffectiveQDivisor n M) (y : M) :
    (add E E').weight y = E.weight y + E'.weight y := rfl

/-- The support of a positive multiple is the support of the divisor. -/
theorem smul_support {c : ℚ} (hc : 0 ≤ c) (hc0 : c ≠ 0)
    (E : MeteredEffectiveQDivisor n M) : (smul hc E).support = E.support := by
  have hpos : (0 : ℝ) < (c : ℝ) := by
    have : (0 : ℚ) < c := lt_of_le_of_ne hc (Ne.symm hc0)
    exact_mod_cast this
  ext y
  constructor
  · intro hy
    have hy' : ((c : ℝ) : EReal) * E.weight y = ⊥ := hy
    rcases (EReal.mul_eq_bot _ _).mp hy' with ⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · exact absurd h (EReal.coe_ne_bot _)
    · exact h
    · exact absurd h (EReal.coe_ne_top _)
    · exact absurd h (not_lt.mpr (EReal.coe_nonneg.mpr hpos.le))
  · intro hy
    have hy' : E.weight y = ⊥ := hy
    show ((c : ℝ) : EReal) * E.weight y = ⊥
    rw [hy', EReal.coe_mul_bot_of_pos hpos]

/-! ### `eq:def-DLY` and the boundedness hypotheses of Step 5 -/

variable (n M) in
/-- A nonnegative rational combination of four metered effective `ℚ`-divisors.
This is the shape of Copy-4 `eq:def-DLY`,
`D = (1/M) G̃_M + ((C-1)/M) P^mov + (C/M) P^F + τ E_rel`. -/
def qcomb4 {c₁ c₂ c₃ c₄ : ℚ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (h₃ : 0 ≤ c₃) (h₄ : 0 ≤ c₄)
    (E₁ E₂ E₃ E₄ : MeteredEffectiveQDivisor n M) : MeteredEffectiveQDivisor n M :=
  add (add (add (smul h₁ E₁) (smul h₂ E₂)) (smul h₃ E₃)) (smul h₄ E₄)

/-- **`eq:def-DLY`, weight form** — an exact identity, not an `O(1)` one. -/
@[simp] theorem weight_qcomb4 {c₁ c₂ c₃ c₄ : ℚ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (h₃ : 0 ≤ c₃) (h₄ : 0 ≤ c₄) (E₁ E₂ E₃ E₄ : MeteredEffectiveQDivisor n M) (y : M) :
    (qcomb4 n M h₁ h₂ h₃ h₄ E₁ E₂ E₃ E₄).weight y
      = ((c₁ : ℝ) : EReal) * E₁.weight y + ((c₂ : ℝ) : EReal) * E₂.weight y
        + ((c₃ : ℝ) : EReal) * E₃.weight y + ((c₄ : ℝ) : EReal) * E₄.weight y := rfl

/-- **The weight of a metered effective `ℚ`-divisor is bounded above on a compact
manifold.**  It is quasi-psh, hence upper semicontinuous and never `⊤`.  This
discharges each of the five boundedness hypotheses of Copy-4 Step 5. -/
theorem exists_forall_weight_le [CompactSpace M] (E : MeteredEffectiveQDivisor n M) :
    ∃ K : ℝ, ∀ y : M, E.weight y ≤ (K : EReal) :=
  CollarWeightComparison.ManifoldQuasiPlurisubharmonic.exists_forall_le_coe
    (MeteredDivisorPositivity.thetaPlurisubharmonic_weight E).quasiPlurisubharmonic

end

end Hironaka.MeteredDivisorScaling
