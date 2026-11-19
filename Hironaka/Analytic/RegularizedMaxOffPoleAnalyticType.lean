import Hironaka.Analytic.DemaillyAnalyticType
import Hironaka.Analytic.RegularizedMaxSmoothAnalyticType

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The regularized maximum in the `I-0489` convention: NO alignment is needed

`Hironaka.RegularizedMaxSmoothAnalyticType` proves that `M_δ(u,v)` inherits the
STRONG CT22 convention (`SmoothLogarithmicTypeAt`, remainder smooth ACROSS the
poles) only when the two branches are presented with the *same* generator
family; at a common pole nothing weaker suffices, because
`M_δ(c·L + b₁, c·L + b₂) = c·L + M_δ(b₁,b₂)` needs the logarithm `L` to be
literally shared.  That is the source of
`Hironaka.FiniteRegularizedMaxCoreCover.PolewiseAlignedBranches`.

The human decision `I-0489` fixed a weaker convention for CT22 analytic
singularities: a remainder that is BOUNDED near the point and `C^∞` only OFF
the pole set (`Hironaka.BoundedSmoothOffPoleLogarithmicTypeAt`).  **In that
convention the alignment obligation disappears.**  Two branches with the same
positive coefficient `c` and arbitrary generator families `f`, `g` combine
under `M_δ` with the CONCATENATED family `Fin.append f g`:

* the remainder is bounded because `max(u,v)` already is
  (`Hironaka.DemaillyAnalyticType.LogarithmicTypeAt.max_of_generators`) and
  `M_δ` differs from `max` by at most `δ`;
* off the pole set of the concatenated family there is no common pole, so the
  three-case analysis of `hasSmoothAnalyticSingularitiesAt_eregularizedMax`
  runs with its *second* and *third* cases only — exactly the two cases whose
  proofs never mention a common family.

The technical device is the **canonical remainder**: any bounded-remainder
presentation of `w` by `(c, h)` can be replaced by the single explicit function
`y ↦ (w y).toReal - c·log ‖h(y)‖²` (and `0` on the pole set).  Boundedness is
then inherited from *any* presentation, while smoothness is proved once for a
concrete formula instead of for an opaque existential.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.RegularizedMaxOffPoleAnalyticType

open Hironaka
open Hironaka
open Hironaka.AdmissibleCurrentFormPositivity
open Hironaka.DemaillyAnalyticType
open Hironaka.RegularizedMaxEReal
open Hironaka.RegularizedMaxSmoothAnalyticType

noncomputable section

/-! ### The canonical remainder of a logarithmic presentation -/

/-- The remainder a presentation by `(c, h)` is *forced* to have off the pole
set: there `w` is finite and `c · log ‖h‖²` is a real number, so the remainder
is their difference.  On the pole set the value is irrelevant — both sides of
the presentation are `⊥` — and is normalised to `0`. -/
def canonicalRemainder {X : Type*} (c : ℝ) {k : ℕ} (h : Fin k → X → ℂ)
    (w : X → EReal) : X → ℝ :=
  fun y => if generatorNormSq h y = 0 then 0 else
    (w y).toReal - c * Real.log (generatorNormSq h y)

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- On the non-polar locus the generator logarithm is the ordinary logarithm of
the norm square. -/
theorem generatorLog_eq_coe_log {k : ℕ} (h : Fin k → X → ℂ) {y : X}
    (hy : generatorNormSq h y ≠ 0) :
    generatorLog h y = (Real.log (generatorNormSq h y) : EReal) := by
  refine generatorLog_of_nonzero ?_
  by_contra hcon
  push Not at hcon
  exact hy (by simp [generatorNormSq, hcon])

/-- On the polar locus the generator logarithm is `⊥`. -/
theorem generatorLog_eq_bot_of_normSq_eq_zero {k : ℕ} (h : Fin k → X → ℂ) {y : X}
    (hy : generatorNormSq h y = 0) : generatorLog h y = ⊥ := by
  rw [generatorLog_eq_bot_iff]
  intro j
  have hsum : ∀ j' ∈ Finset.univ, (0 : ℝ) ≤ ‖h j' y‖ ^ 2 := fun _ _ => sq_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg hsum).mp hy j (Finset.mem_univ j)
  simpa using this

/-- **Normalisation of a bounded presentation.**  Every `LogarithmicTypeAt`
witness can be rewritten with the canonical remainder, which is therefore
bounded as well.  This is what lets the smoothness clause be checked on one
concrete function. -/
theorem LogarithmicTypeAt.canonical {w : X → EReal} {c : ℝ} {k : ℕ}
    {h : Fin k → X → ℂ} {z : X} (hw : LogarithmicTypeAt w c h z) :
    BoundedRealGermAt (canonicalRemainder c h w) z ∧
      w =ᶠ[𝓝 z] fun y =>
        (c : EReal) * generatorLog h y + (canonicalRemainder c h w y : EReal) := by
  obtain ⟨hc, -, b, ⟨C, hC0, hCb⟩, heq⟩ := hw
  have hkey : ∀ᶠ y in 𝓝 z, canonicalRemainder c h w y =
      (if generatorNormSq h y = 0 then 0 else b y) := by
    filter_upwards [heq] with y hy
    by_cases hQ : generatorNormSq h y = 0
    · simp [canonicalRemainder, hQ]
    · have hlog : generatorLog h y = (Real.log (generatorNormSq h y) : EReal) :=
        generatorLog_eq_coe_log h hQ
      have hwy : w y = ((c * Real.log (generatorNormSq h y) + b y : ℝ) : EReal) := by
        rw [hy, hlog, ← EReal.coe_mul, ← EReal.coe_add]
      simp only [canonicalRemainder, if_neg hQ, hwy, EReal.toReal_coe]
      ring
  refine ⟨⟨C, hC0, ?_⟩, ?_⟩
  · filter_upwards [hkey, hCb] with y hy hyb
    rw [hy]
    by_cases hQ : generatorNormSq h y = 0
    · simpa [hQ] using hC0
    · simpa [hQ] using hyb
  · filter_upwards [heq, hkey] with y hy hycan
    by_cases hQ : generatorNormSq h y = 0
    · have hlog : generatorLog h y = ⊥ := generatorLog_eq_bot_of_normSq_eq_zero h hQ
      rw [hy, hlog, EReal.mul_bot_of_pos (EReal.coe_pos.mpr hc), EReal.bot_add,
        EReal.bot_add]
    · rw [hycan, if_neg hQ, hy]

/-! ### A bounded perturbation keeps a bounded presentation -/

/-- If `w` is squeezed between `u` and `u + δ` near `z`, it inherits `u`'s
logarithmic presentation.  Only the remainder changes, by at most `δ`. -/
theorem LogarithmicTypeAt.of_sandwich {u w : X → EReal} {c δ : ℝ} (hδ : 0 ≤ δ)
    {k : ℕ} {h : Fin k → X → ℂ} {z : X} (hu : LogarithmicTypeAt u c h z)
    (hsand : ∀ᶠ y in 𝓝 z, u y ≤ w y ∧ w y ≤ u y + (δ : EReal)) :
    LogarithmicTypeAt w c h z := by
  obtain ⟨hc, hh, b, ⟨C, hC0, hCb⟩, heq⟩ := hu
  refine ⟨hc, hh, fun y => if generatorNormSq h y = 0 then 0 else
    b y + ((w y).toReal - (u y).toReal), ⟨C + δ, by linarith, ?_⟩, ?_⟩
  · filter_upwards [heq, hCb, hsand] with y hy hyb ⟨hle, hlt⟩
    by_cases hQ : generatorNormSq h y = 0
    · simpa [hQ] using by linarith
    · have hlog : generatorLog h y = (Real.log (generatorNormSq h y) : EReal) :=
        generatorLog_eq_coe_log h hQ
      have huy : u y = ((c * Real.log (generatorNormSq h y) + b y : ℝ) : EReal) := by
        rw [hy, hlog, ← EReal.coe_mul, ← EReal.coe_add]
      set a : ℝ := c * Real.log (generatorNormSq h y) + b y with ha
      have hwtop : w y ≠ ⊤ := by
        intro hcon
        rw [hcon, huy] at hlt
        exact absurd (top_le_iff.mp hlt) (by rw [← EReal.coe_add]; exact EReal.coe_ne_top _)
      have hwbot : w y ≠ ⊥ := by
        intro hcon
        rw [hcon, huy] at hle
        exact absurd (le_bot_iff.mp hle) (by simp)
      have hwreal : w y = ((w y).toReal : EReal) := (EReal.coe_toReal hwtop hwbot).symm
      have h1 : a ≤ (w y).toReal := by
        have := hle
        rw [huy, hwreal] at this
        exact_mod_cast this
      have h2 : (w y).toReal ≤ a + δ := by
        have := hlt
        rw [huy, hwreal, ← EReal.coe_add] at this
        exact_mod_cast this
      rw [if_neg hQ, huy, EReal.toReal_coe]
      rw [abs_le]
      constructor
      · have : |b y| ≤ C := hyb
        rw [abs_le] at this
        linarith
      · have : |b y| ≤ C := hyb
        rw [abs_le] at this
        linarith
  · filter_upwards [heq, hsand] with y hy ⟨hle, hlt⟩
    by_cases hQ : generatorNormSq h y = 0
    · have hlog : generatorLog h y = ⊥ := generatorLog_eq_bot_of_normSq_eq_zero h hQ
      have huy : u y = ⊥ := by
        rw [hy, hlog, EReal.mul_bot_of_pos (EReal.coe_pos.mpr hc), EReal.bot_add]
      have hwy : w y = ⊥ := by
        refine le_bot_iff.mp ?_
        simpa [huy] using hlt
      rw [hwy, hlog, EReal.mul_bot_of_pos (EReal.coe_pos.mpr hc), EReal.bot_add]
    · have hlog : generatorLog h y = (Real.log (generatorNormSq h y) : EReal) :=
        generatorLog_eq_coe_log h hQ
      have huy : u y = ((c * Real.log (generatorNormSq h y) + b y : ℝ) : EReal) := by
        rw [hy, hlog, ← EReal.coe_mul, ← EReal.coe_add]
      have hwtop : w y ≠ ⊤ := by
        intro hcon
        rw [hcon, huy] at hlt
        exact absurd (top_le_iff.mp hlt) (by rw [← EReal.coe_add]; exact EReal.coe_ne_top _)
      have hwbot : w y ≠ ⊥ := by
        intro hcon
        rw [hcon, huy] at hle
        exact absurd (le_bot_iff.mp hle) (EReal.coe_ne_bot _)
      have hwreal : w y = ((w y).toReal : EReal) := (EReal.coe_toReal hwtop hwbot).symm
      rw [if_neg hQ, hlog, huy, EReal.toReal_coe]
      conv_lhs => rw [hwreal]
      congr 1
      ring

end

end Hironaka.RegularizedMaxOffPoleAnalyticType
