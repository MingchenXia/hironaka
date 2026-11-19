import Hironaka.Resolution.HironakaG8OddCuspGeometricSource
import Hironaka.Resolution.HironakaG8CompactNativeFirstStep

/-! Actual historical native states for the literal geometric odd cusps. -/
set_option autoImplicit false
open Set TopologicalSpace
namespace Hironaka.HironakaG8OddCuspHistoricalNative
noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals ResolutionInvariantSpec HironakaHolomorphicJetChartInvariance
  HironakaG11PresLineState HironakaG8CompactNativeFirstStep
  HironakaActualVanishingIntrinsicHSTransport HironakaG8OddCuspVanishingStalk
  HironakaG8OddCuspGeometricSource

/-- Every prescribed ambient neighbourhood of the actual odd cusp origin
contains a history-ready native chart. The exact common numerical profile is
independent of the odd exponent once that exponent exceeds two. -/
theorem exists_odd_cusp_historical_native_near_zero (p : ℕ) (hp : Odd p) (hp2 : 2 < p)
    (U : Opens (ComplexModel 3)) (hU : (0 : ComplexModel 3) ∈ U) :
    ∃ (D : Opens (ComplexModel 3)) (hD : (0 : ComplexModel 3) ∈ D),
      (D : Set (ComplexModel 3)) ⊆ U ∧
      ∃ Q : MarkedIdeal 3 (CMfd.of (n := 3) D), IsInvDomain 3 Q ∧ Q.E = [] ∧
        NativeHSState Q ((Subtype.val : D → ComplexModel 3) ⁻¹' embeddedCuspSet p)
          (fun l => Nat.choose (2+l) 2 - (if 2 ≤ l then Nat.choose (2+(l-2)) 2 else 0)) ∧
        (⟨0, hD⟩ : D) ∈ Q.cosupp := by
  obtain ⟨D, hD, hIncl, Q, hQ, hE, hState⟩ :=
    exists_native_state_on_ambient_open (X := CMfd.of (n := 3) (ComplexModel 3))
      (embeddedCuspSet p) (embedded_cusp_isAnalytic p) 0
      (embedded_odd_cusp_singular_at_zero p hp hp2) U hU
  have hProfile : (fun l => hilbertSamuelAt (vanishingIdeal (n := 3) (embeddedCuspSet p)) 0 l) =
      (fun l => Nat.choose (2+l) 2 - (if 2 ≤ l then Nat.choose (2+(l-2)) 2 else 0)) :=
    funext (embedded_odd_cusp_geometric_profile p hp hp2)
  refine ⟨D, hD, hIncl, Q, hQ, hE, hProfile ▸ hState, ?_⟩
  rw [hState.cosupp_eq]
  intro l
  exact hilbertSamuelAt_vanishing_actual_open_any D (embeddedCuspSet p) ⟨0,hD⟩ l

end
end Hironaka.HironakaG8OddCuspHistoricalNative
