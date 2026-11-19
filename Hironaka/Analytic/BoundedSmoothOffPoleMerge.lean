import Hironaka.Analytic.SmoothOffPole
import Hironaka.Analytic.RegularizedMaxOffPoleAppend

set_option autoImplicit false

/-!
# Merging two `I-0489` presentations of the *same* function

`Hironaka.RegularizedMaxOffPoleAppend` concatenates the generator families of two
*different* branches under the regularized maximum.  The Demailly frame data
needs the other combination: at one point of a manifold several overlapping
Bergman charts present the *same* potential, and the presentation carried to the
next chart must be the concatenation of all of them.

The mechanism is a general upgrade lemma.  A bounded-remainder presentation
(`Hironaka.LogarithmicTypeAt`) of a function which *is* of `I-0489` type
automatically has the off-pole smoothness clause:

* off the pole set of the family the presented function is finite, hence a
  smooth real germ there by
  `Hironaka.AdmissibleCurrentFormPositivity.exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt`;
* the logarithm of the family's norm square is smooth wherever it is positive;
* so the remainder, which is their difference as a germ, is smooth there.

Hence merging reduces to the bounded-remainder statement already proved for the
ordinary maximum (`Hironaka.DemaillyAnalyticType.LogarithmicTypeAt.max_of_generators`)
applied with `max u u = u`.  No alignment of the two families and no relation
between their pole sets is needed.
-/

open Set Filter
open scoped Topology ContDiff

namespace Hironaka.BoundedSmoothOffPoleMerge

open Hironaka
open Hironaka
open Hironaka.AdmissibleCurrentFormPositivity
open Hironaka.DemaillyAnalyticType
open Hironaka.RegularizedMaxOffPoleAppend

noncomputable section

variable {n : ℕ}

/-- The norm square of a holomorphic generator family is `C^∞` on the open set
where the family is holomorphic. -/
theorem contDiffOn_generatorNormSq {k : ℕ} {f : Fin k → ComplexModel n → ℂ}
    {U : Set (ComplexModel n)} (hU : IsOpen U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) :
    ContDiffOn ℝ ∞ (generatorNormSq f) U := by
  unfold generatorNormSq
  refine ContDiffOn.sum fun j _ => ?_
  have hj : ContDiffOn ℝ ∞ (f j) U :=
    contDiffOn_real_of_differentiableOn_complex (hf j) hU
  exact (contDiff_norm_sq ℝ).comp_contDiffOn hj

/-- Where the norm square is positive the generator logarithm is the ordinary
real logarithm. -/
theorem generatorLog_eq_coe_log {k : ℕ} (f : Fin k → ComplexModel n → ℂ)
    {y : ComplexModel n} (hy : 0 < generatorNormSq f y) :
    generatorLog f y = (Real.log (generatorNormSq f y) : EReal) := by
  rw [generatorLog, logNormSq, generatorVector_norm_sq, ENNReal.log_ofReal_of_pos hy]

/-- **A bounded-remainder presentation of a function of `I-0489` type is itself an
`I-0489` presentation.**

The hypothesis is only that the presented function has *some* `I-0489`
presentation at every nearby point — not that it has one with this coefficient or
this family.  Off the pole set of `f` the function is finite, so it is a smooth
real germ there, and the remainder is that germ minus the smooth real logarithm
of `generatorNormSq f`. -/
theorem LogarithmicTypeAt.boundedSmoothOffPole_of_eventually
    {u : ComplexModel n → EReal} {c : ℝ} {k : ℕ}
    {f : Fin k → ComplexModel n → ℂ} {z : ComplexModel n}
    (hL : LogarithmicTypeAt u c f z)
    (hu : ∀ᶠ y in 𝓝 z, HasAnalyticSingularitiesSmoothOffPoleAt u y) :
    BoundedSmoothOffPoleLogarithmicTypeAt u c f z := by
  obtain ⟨hc, hfhol, b, hb, heq⟩ := hL
  obtain ⟨U, hUopen, hzU, hf⟩ := hfhol
  have hsq : ContDiffOn ℝ ∞ (generatorNormSq f) U := contDiffOn_generatorNormSq hUopen hf
  refine ⟨hc, ⟨U, hUopen, hzU, hf⟩, b, hb, ?_, heq⟩
  have heq' : ∀ᶠ y in 𝓝 z,
      u =ᶠ[𝓝 y] fun w => (c : EReal) * generatorLog f w + (b w : EReal) :=
    eventually_eventually_nhds.mpr heq
  filter_upwards [hu, heq', hUopen.mem_nhds hzU] with y hy hyeq hyU
  intro hne
  have hpos : 0 < generatorNormSq f y :=
    lt_of_le_of_ne (generatorNormSq_nonneg f y) (Ne.symm hne)
  have hufin : u y ≠ ⊥ := by
    rw [hyeq.eq_of_nhds, generatorLog_eq_coe_log f hpos, ← EReal.coe_mul, ← EReal.coe_add]
    exact EReal.coe_ne_bot _
  obtain ⟨g, hg, hug⟩ :=
    exists_smooth_eventuallyEq_of_hasAnalyticSingularitiesSmoothOffPoleAt hy hufin
  have hposNear : ∀ᶠ w in 𝓝 y, 0 < generatorNormSq f w :=
    (hsq.continuousOn.continuousAt (hUopen.mem_nhds hyU)).eventually (lt_mem_nhds hpos)
  have hbeq : b =ᶠ[𝓝 y] fun w => g w - c * Real.log (generatorNormSq f w) := by
    filter_upwards [hyeq, hug, hposNear] with w hw hwg hwp
    have hcoe : ((g w : ℝ) : EReal)
        = ((c * Real.log (generatorNormSq f w) + b w : ℝ) : EReal) := by
      rw [← hwg, hw, generatorLog_eq_coe_log f hwp, ← EReal.coe_mul, ← EReal.coe_add]
    have hreal := EReal.coe_eq_coe_iff.mp hcoe
    linarith [hreal]
  have hlogsm : ContDiffAt ℝ ∞ (fun w => c * Real.log (generatorNormSq f w)) y :=
    contDiffAt_const.mul ((hsq.contDiffAt (hUopen.mem_nhds hyU)).log hpos.ne')
  exact (hg.self_of_nhds.sub hlogsm).congr_of_eventuallyEq hbeq

/-- The pointwise form of the upgrade lemma: an `I-0489` presentation at the
centre already localizes to a neighbourhood, so one witness suffices. -/
theorem LogarithmicTypeAt.boundedSmoothOffPole
    {u : ComplexModel n → EReal} {c : ℝ} {k : ℕ}
    {f : Fin k → ComplexModel n → ℂ} {z : ComplexModel n}
    (hL : LogarithmicTypeAt u c f z)
    (hu : HasAnalyticSingularitiesSmoothOffPoleAt u z) :
    BoundedSmoothOffPoleLogarithmicTypeAt u c f z := by
  obtain ⟨c', k', f', hu'⟩ := hu
  exact LogarithmicTypeAt.boundedSmoothOffPole_of_eventually hL
    ((BoundedSmoothOffPoleLogarithmicTypeAt.eventually hu').mono
      fun y hy => ⟨c', k', f', hy⟩)

/-- **Two `I-0489` presentations of the SAME function, with the same coefficient,
merge into one presented by the CONCATENATED family.**

This is the companion of
`Hironaka.RegularizedMaxOffPoleAppend.boundedSmoothOffPoleLogarithmicTypeAt_eregularizedMax_append`,
which concatenates the families of two branches of a regularized maximum.  Here
nothing is combined on the function side: `max u u = u`, so the bounded-remainder
concatenation theorem for the ordinary maximum already gives the presentation,
and the upgrade lemma supplies the off-pole clause. -/
theorem BoundedSmoothOffPoleLogarithmicTypeAt.append_same
    {u : ComplexModel n → EReal} {c : ℝ} {k l : ℕ}
    {f : Fin k → ComplexModel n → ℂ} {g : Fin l → ComplexModel n → ℂ}
    {z : ComplexModel n}
    (hf : BoundedSmoothOffPoleLogarithmicTypeAt u c f z)
    (hg : BoundedSmoothOffPoleLogarithmicTypeAt u c g z) :
    BoundedSmoothOffPoleLogarithmicTypeAt u c (Fin.append f g) z := by
  have hmax := LogarithmicTypeAt.max_of_generators hf.logarithmicTypeAt hg.logarithmicTypeAt
  simp only [max_self] at hmax
  exact LogarithmicTypeAt.boundedSmoothOffPole hmax ⟨c, k, f, hf⟩

end

end Hironaka.BoundedSmoothOffPoleMerge
