import Hironaka.Analytic.IEnvelope
import Hironaka.Analytic.ThetaPshEnvelopes

set_option autoImplicit false

/-!
# Nonemptiness of the I-envelope competitor class

Subtracting a finite real constant from a potential multiplies every
multiplier density by the finite nonzero constant `exp(c C)`, so it preserves
all local multiplier germs.  Consequently the normalized translate of a genuine
theta-PSH potential on a compact manifold is an I-envelope competitor, and the
regularized supremum defining `P_θ[φ]_I` is a genuine theta-PSH potential.
-/

open Set MeasureTheory

namespace Hironaka

noncomputable section


open Hironaka.IEnvelope
open Hironaka.QuasiEquisingularApproximation

/-- A finite translation rescales the extended multiplier weight, including
at both infinite values. -/
theorem multiplierWeight_sub_coe (c : ℝ) (a : EReal) (C : ℝ) :
    multiplierWeight c (a - (C : EReal)) =
      multiplierWeight c a * ENNReal.ofReal (Real.exp (c * C)) := by
  induction a using EReal.rec with
  | bot =>
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · simp [multiplierWeight, EReal.coe_mul_bot_of_neg hc]
    · simp [multiplierWeight]
    · simp [multiplierWeight, EReal.coe_mul_bot_of_pos hc, Real.exp_pos]
  | top =>
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · simp [multiplierWeight, EReal.coe_mul_top_of_neg hc, Real.exp_pos]
    · simp [multiplierWeight]
    · simp [multiplierWeight, EReal.coe_mul_top_of_pos hc]
  | coe a =>
    rw [← EReal.coe_sub, multiplierWeight_coe, multiplierWeight_coe,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring

section LocalL2

variable {E : Type*} {_ : MeasurableSpace E}

theorem weightedL2On_sub_const {φ : E → EReal} {c : ℝ} {f : E → ℂ} {U : Set E}
    {μ : Measure E} (h : WeightedL2On φ c f U μ) (C : ℝ) :
    WeightedL2On (fun y => φ y - (C : EReal)) c f U μ := by
  have hdens : multiplierDensity (fun y => φ y - (C : EReal)) c f =
      fun y => multiplierDensity φ c f y * ENNReal.ofReal (Real.exp (c * C)) := by
    funext y
    simp only [multiplierDensity, multiplierWeight_sub_coe, mul_assoc]
  unfold WeightedL2On at h ⊢
  rw [hdens]
  refine ⟨h.1.mul_const _, ?_⟩
  rw [lintegral_mul_const'' _ h.1]
  exact ENNReal.mul_lt_top h.2 ENNReal.ofReal_lt_top

theorem weightedL2On_sub_const_iff {φ : E → EReal} {c : ℝ} {f : E → ℂ}
    {U : Set E} {μ : Measure E} (C : ℝ) :
    WeightedL2On (fun y => φ y - (C : EReal)) c f U μ ↔ WeightedL2On φ c f U μ := by
  refine ⟨fun h => ?_, fun h => weightedL2On_sub_const h C⟩
  have hφ : (fun y => (φ y - (C : EReal)) - ((-C : ℝ) : EReal)) = φ := by
    funext y
    induction φ y using EReal.rec with
    | bot => simp
    | top => simp
    | coe a => rw [← EReal.coe_sub, ← EReal.coe_sub]; congr 1; ring
  simpa only [hφ] using weightedL2On_sub_const h (-C)

end LocalL2

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M]

/-- Finite translation does not change any positive-level multiplier germ. -/
theorem iEquivalentOnManifold_sub_const (φ : M → EReal) (C : ℝ) :
    IEquivalentOnManifold (n := n) (fun x => φ x - (C : EReal)) φ := by
  constructor
  · intro c _ e z _ f _ hmem
    obtain ⟨hc, U, hU, hzU, hhol, hint⟩ := hmem
    exact ⟨hc, U, hU, hzU, hhol, (weightedL2On_sub_const_iff C).mp hint⟩
  · intro c _ e z _ f _ hmem
    obtain ⟨hc, U, hU, hzU, hhol, hint⟩ := hmem
    exact ⟨hc, U, hU, hzU, hhol, (weightedL2On_sub_const_iff C).mpr hint⟩

variable [IsComplexManifold n M]

/-- On a compact nonempty manifold, the normalized translate of a genuine
theta-PSH potential is an I-envelope competitor. -/
theorem iSingularityCompetitors_nonempty [CompactSpace M] [Nonempty M]
    {θ : SmoothRealForm n M 2} {φ : M → EReal} (hφ : IsThetaPshPotential θ φ) :
    (iSingularityCompetitors θ φ).Nonempty := by
  obtain ⟨C, hC⟩ := hφ.exists_normalized_sub_const
  exact ⟨_, hC, iEquivalentOnManifold_sub_const φ C⟩

/-- The multiplier-ideal envelope of a genuine theta-PSH potential on a
compact nonempty manifold is a genuine theta-PSH potential. -/
theorem iSingularityEnvelope_isThetaPshPotential_of_potential
    [CompactSpace M] [Nonempty M] {θ : SmoothRealForm n M 2}
    (hlocal : HasSmoothLocalPotentials θ) {φ : M → EReal}
    (hφ : IsThetaPshPotential θ φ) :
    IsThetaPshPotential θ (iSingularityEnvelope θ φ) := by
  have hcomp := iSingularityCompetitors_nonempty hφ
  refine ⟨?_, iSingularityEnvelope_locallyNondegenerate hcomp⟩
  simpa only [iSingularityEnvelope, iSingularitySupremum] using
    thetaPlurisubharmonic_uscRegularization_sSup hlocal hcomp
      (fun _ hu ↦ hu.1.1) (fun _ hu ↦ hu.1.2)

end

end Hironaka
