import Hironaka.Analytic.MeteredDivisorScaling

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Two remaining inputs of Copy-4 Step 5

Source: Copy-4, Step 5 of `prop:principalization`
(`references/transcendental-nakamaye-copy4-20260911/source/main-Nulllocus.tex:1908-1935`).

`Pending/CollarWeightComparison` reduces `eq:collar` to three hypotheses, `hD`,
`hχ` and `hH`.  `Pending/MeteredDivisorScaling` discharges `hD` and `hH` on the
nose (`weight_qcomb4`, `weight_add`).  This module supplies the last one.

* `moreSingularOn_weight_add_left` — **a larger effective divisor has a more
  singular weight**: if `E = E' + R` with `R` effective then
  `ψ_E ≤ ψ_{E'} + O(1)`, because `ψ_R` is bounded above on a compact manifold.
  This is the manuscript's passage from `G̃_m ≥ H^fix_m` (`eq:def-Gm-tilde`) to
  `ψ_{G̃_m} ≤ ψ_{H^fix_m} + O(1)`, which is the *only* place the inequality
  between those two divisors is used.

* `moreSingularOn_chi` — **`hχ` itself**: with `χ = ((C-1)/M) Ψ_m∘π` and
  `Ψ_m = ψ_𝔧 + ψ_{𝔅_m} + O(1)` (`eq:def-Psi`), the manuscript's
  `χ ≤ ((C-1)/M)(ψ_𝔧∘π + ψ_{H^fix_m}) + O(1)` is the previous item scaled by the
  (nonnegative) coefficient.

Everything here is sorry-free.
-/

open Set

universe u

namespace Hironaka.ExceptionalWeightBounds

open Hironaka.HolomorphicIdealSheaves
open Hironaka.CollarWeightComparison
open Hironaka.MeteredDivisorOperations
open Hironaka.MeteredDivisorScaling

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **A larger effective divisor has a more singular weight.**  `ψ_{E + R} ≤ ψ_E
+ O(1)` on a compact manifold, the constant being an upper bound for `ψ_R`. -/
theorem moreSingularOn_weight_add_left [CompactSpace M]
    (E R : MeteredEffectiveQDivisor n M) :
    MoreSingularOn (add E R).weight E.weight univ := by
  obtain ⟨K, hK⟩ := exists_forall_weight_le R
  exact ⟨K, fun y _ => add_le_add le_rfl (hK y)⟩

/-- The same with an extra nonnegative coefficient, in the form Step 5 uses. -/
theorem moreSingularOn_smul_weight_add_left [CompactSpace M] {c : ℝ} (hc : 0 ≤ c)
    (E R : MeteredEffectiveQDivisor n M) :
    MoreSingularOn (fun y => (c : EReal) * (add E R).weight y)
      (fun y => (c : EReal) * E.weight y) univ :=
  moreSingularOn_smul hc (moreSingularOn_weight_add_left E R)

/-- **Copy-4 Step 5, the hypothesis `hχ`.**  With `χ = c Ψ` for a nonnegative `c`,
`Ψ ≤ ψ_𝔧 + ψ_{G̃_m} + O(1)` and `ψ_{G̃_m} ≤ ψ_{H^fix_m} + O(1)`, one gets
`χ ≤ c(ψ_𝔧 + ψ_{H^fix_m}) + O(1)` — which is exactly the `hχ` of
`CollarWeightComparison.moreSingularOn_exceptionalWeightSum`. -/
theorem moreSingularOn_chi {Z : Type*} {ψj ψGm ψHfix Ψ χ : Z → EReal} {c : ℝ}
    (hc : 0 ≤ c) (hχdef : ∀ y, χ y = (c : EReal) * Ψ y)
    (hΨ : MoreSingularOn Ψ (fun y => ψj y + ψGm y) univ)
    (hGm : MoreSingularOn ψGm ψHfix univ) :
    MoreSingularOn χ (fun y => (c : EReal) * (ψj y + ψHfix y)) univ := by
  have h1 : MoreSingularOn Ψ (fun y => ψj y + ψHfix y) univ :=
    hΨ.trans (moreSingularOn_add (MoreSingularOn.refl _ _) hGm)
  exact (MoreSingularOn.of_le fun y _ => le_of_eq (hχdef y)).trans
    (moreSingularOn_smul hc h1)

end

end Hironaka.ExceptionalWeightBounds
