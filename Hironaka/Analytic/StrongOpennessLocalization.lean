import Hironaka.Analytic.StrongOpennessEnvelope
import Hironaka.Analytic.IncreasingPshBallSubmean

set_option autoImplicit false

/-!
# Localizing strong openness for increasing sequences to one ball

`IncreasingStrongOpenness n` (`Hironaka.StrongOpennessEnvelope`; Xia, Theorem
1.4.4, `xia-sgpt:page-0043`) is a germ statement on an arbitrary open set.  This
module reduces it, sorry-free, to statements on a single ball carrying one real
upper bound for the whole increasing family:

* `BallIncreasingStrongOpenness n` — weight the usc regularization of the limit;
  `increasingStrongOpenness_of_ball` shows it implies `IncreasingStrongOpenness n`.
* `BallIncreasingStrongOpennessLimit n` — weight the pointwise limit;
  `ballIncreasingStrongOpenness_of_limit` shows it implies the former, because the
  two weights agree Lebesgue-a.e. (`ae_uscRegularization_iSup_eq_on_ball`).

Neither ball statement is proved here.  `Hironaka.HiepStrongOpenness` derives the
first from Hiep's strong effective openness theorem.
-/

open Set Filter MeasureTheory Metric
open scoped Topology ENNReal

namespace Hironaka

noncomputable section

open Hironaka

/-- The localized form of Guan--Zhou strong openness: one ball, one real upper
bound for the whole increasing family, one holomorphic representative, and a
finite weighted mass on the whole ball.  This is the statement the L² extension
argument is run against; `IncreasingStrongOpenness` follows from it by
localization alone (`increasingStrongOpenness_of_ball`). -/
def BallIncreasingStrongOpenness (n : ℕ) : Prop := by
  letI : MeasurableSpace (ComplexModel n) := borel _
  letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
  exact ∀ (z : ComplexModel n) (r : ℝ) (v : ℕ → ComplexModel n → EReal) (C : ℝ),
    0 < r →
    (∀ j, PlurisubharmonicOn (v j) (ball z r)) →
    (∀ y ∈ ball z r, Monotone fun j => v j y) →
    (∀ j, ∀ y ∈ ball z r, v j y ≤ (C : EReal)) →
    ∀ c : ℝ, 0 < c → ∀ f : ComplexModel n → ℂ, DifferentiableOn ℂ f (ball z r) →
      WeightedL2On (uscRegularization (⨆ j, v j)) c f (ball z r) volume →
      ∃ j, MultiplierIntegrableAt (v j) c f z volume

/-- Localization: the ball form of strong openness implies the germ form that
`Hironaka.StrongOpennessEnvelope` consumes.  The only content is choosing a
ball inside the intersection of the domain, the neighbourhood carrying a
uniform upper bound for the family, and the neighbourhood on which the germ
`f` has a holomorphic representative of finite weighted mass. -/
theorem increasingStrongOpenness_of_ball (n : ℕ)
    (h : BallIncreasingStrongOpenness n) : IncreasingStrongOpenness n := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  let _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro W v hW hpsh hmono hbdd z hz c hc f _ hmem
  obtain ⟨hc', U, hUopen, hzU, hfhol, hL2⟩ := hmem
  obtain ⟨U₀, hU₀, C, hC⟩ := hbdd z hz
  rw [hW.nhdsWithin_eq hz] at hU₀
  obtain ⟨r, hr, hball⟩ :=
    Metric.mem_nhds_iff.mp (Filter.inter_mem (Filter.inter_mem (hUopen.mem_nhds hzU) hU₀)
      (hW.mem_nhds hz))
  have hballW : ball z r ⊆ W := fun y hy => (hball hy).2
  have hballU : ball z r ⊆ U := fun y hy => (hball hy).1.1
  refine h z r v C hr (fun j y hy => hpsh j y (hballW hy))
    (fun y hy => hmono y (hballW hy)) (fun j y hy => ?_) c hc f
    (hfhol.mono hballU) (hL2.mono hballU)
  exact hC (v j) ⟨j, rfl⟩ y ⟨(hball hy).1.2, hballW hy⟩

/-- The localized statement with the weight given by the **pointwise**
increasing limit rather than by its upper semicontinuous regularization.  This
is the form the L² argument is actually run against: no regularization occurs
in it. -/
def BallIncreasingStrongOpennessLimit (n : ℕ) : Prop := by
  letI : MeasurableSpace (ComplexModel n) := borel _
  letI : BorelSpace (ComplexModel n) := ⟨rfl⟩
  exact ∀ (z : ComplexModel n) (r : ℝ) (v : ℕ → ComplexModel n → EReal) (C : ℝ),
    0 < r →
    (∀ j, PlurisubharmonicOn (v j) (ball z r)) →
    (∀ y ∈ ball z r, Monotone fun j => v j y) →
    (∀ j, ∀ y ∈ ball z r, v j y ≤ (C : EReal)) →
    ∀ c : ℝ, 0 < c → ∀ f : ComplexModel n → ℂ, DifferentiableOn ℂ f (ball z r) →
      WeightedL2On (fun y => ⨆ j, v j y) c f (ball z r) volume →
      ∃ j, MultiplierIntegrableAt (v j) c f z volume

/-- Removing the regularization from the hypothesis.  The two weights differ
only on a Lebesgue null set (`ae_uscRegularization_iSup_eq_on_ball`), so the
weighted masses agree; halving the radius is the only cost, and the conclusion
is a germ statement at the centre. -/
theorem ballIncreasingStrongOpenness_of_limit (n : ℕ)
    (h : BallIncreasingStrongOpennessLimit n) : BallIncreasingStrongOpenness n := by
  let _ : MeasurableSpace (ComplexModel n) := borel _
  let _ : BorelSpace (ComplexModel n) := ⟨rfl⟩
  intro z r v C hr hpsh hmono hbound c hc f hf hL2
  have hhalf : (0 : ℝ) < r / 2 := by linarith
  have hsub : ball z (r / 2) ⊆ ball z r := ball_subset_ball (by linarith)
  have hae : ∀ᵐ x ∂(volume : Measure (ComplexModel n)), x ∈ ball z (r / 2) →
      uscRegularization (fun y => ⨆ j, v j y) x = ⨆ j, v j x :=
    ae_uscRegularization_iSup_eq_on_ball (fun j => (hpsh j).discPshOn) hmono volume z hr
      subset_rfl hbound
  have hweight : multiplierDensity (uscRegularization (⨆ j, v j)) c f
      =ᵐ[(volume : Measure (ComplexModel n)).restrict (ball z (r / 2))]
        multiplierDensity (fun y => ⨆ j, v j y) c f := by
    filter_upwards [ae_restrict_of_ae hae,
      ae_restrict_mem (measurableSet_ball (x := z) (ε := r / 2))] with x hx hxmem
    have hfun : (fun y => ⨆ j, v j y) = (⨆ j, v j) := by
      funext y
      exact iSup_apply.symm
    simp only [multiplierDensity]
    rw [← hfun, hx hxmem]
  have hL2' : WeightedL2On (fun y => ⨆ j, v j y) c f (ball z (r / 2)) volume := by
    obtain ⟨hmeas, hint⟩ := hL2.mono hsub
    exact ⟨hmeas.congr hweight, by rwa [← lintegral_congr_ae hweight]⟩
  exact h z (r / 2) v C hhalf (fun j y hy => hpsh j y (hsub hy))
    (fun y hy => hmono y (hsub hy)) (fun j y hy => hbound j y (hsub hy)) c hc f
    (hf.mono hsub) hL2'

end

end Hironaka
