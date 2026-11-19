import Hironaka.Analytic.HolomorphicAnalytic
import Hironaka.Resolution.HironakaHolomorphicJetMonomialSpan

/-! # Normalized actual Taylor series for Banach-valued holomorphic germs -/
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor
open Hironaka Hironaka

/-- A function holomorphic near the origin has the actual normalized
  iterated-derivative power series there, for any complex Banach target. -/
theorem has_normalized_powerSeriesAt
    {X B : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (f : X → B) (hf : ∀ᶠ z in 𝓝 (0 : X), DifferentiableAt ℂ f z) :
    HasFPowerSeriesAt f (fun n => (Nat.factorial n : ℂ)⁻¹ • iteratedFDeriv ℂ n f 0) 0 := by
  obtain ⟨U,hUf,hU,h0⟩ := _root_.eventually_nhds_iff.mp hf
  have hcont : ContinuousAt (fun z => ‖f z‖) 0 :=
    continuous_norm.continuousAt.comp ((hUf 0 h0).continuousAt)
  have hev : ∀ᶠ z in 𝓝 (0 : X), z ∈ U ∧ ‖f z‖ < ‖f 0‖ + 1 :=
    (hU.eventually_mem h0).and (hcont.eventually (gt_mem_nhds (lt_add_one _)))
  obtain ⟨R,hR,hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  exact (HolomorphicAnalytic.hasFPowerSeriesOnBall_of_differentiableOn hR
    (fun z hz => (hUf z (hball z hz).1).differentiableWithinAt)
    (fun z hz => (hball z hz).2.le)).hasFPowerSeriesAt

end Hironaka.Analytic.Unibranch.HironakaG10NormalizedBanachTaylor
