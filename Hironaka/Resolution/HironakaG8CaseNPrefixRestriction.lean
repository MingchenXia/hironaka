import Hironaka.Resolution.HironakaG8CaseNPrefix
import Hironaka.Resolution.HironakaG8CaseNRestriction

/-!
# Restriction of a retained local class relation along an actual tower

The ordered old-boundary identity and native P1 restriction combine to compare
orders at a point avoiding the original strict members. The actual test tower,
its stage domain data, and the avoiding point are inputs to this bounded lemma.
-/

set_option autoImplicit false
open Set
universe u

namespace Hironaka.HironakaG8CaseNPrefixRestriction

noncomputable section
open Hironaka.BlowupSequences BlowupTowers HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG8LocalHistory
open ResolutionInvariantSpec (IsInvDomain)
open HironakaG11InvBMClass (SameCarrierDim)
open HironakaSharpOriginalProductTraceOrder (ordinaryTraceOrder)

/-- At an actual test-tower stage, the local equivalence drops precisely the
strict old prefix on a neighborhood of a point avoiding it. Native P1 then
compares orders on the full native boundary, including its born members. -/
theorem normalized_order_eq_at_stage_off_original_prefix
    {n kA kB : ℕ} {X Y : CMfd.{u} n}
    (A B : MarkedIdeal n X) (F : List (Set X)) (hClosed : ∀ H ∈ F, IsClosed H)
    (h : LocWPEquiv ({ A with E := F ++ A.E } : MarkedIdeal n X)
      ({ B with E := F ++ B.E } : MarkedIdeal n X))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower ({ A with E := F ++ A.E } : MarkedIdeal n X) T)
    (hA : IsInvDomain kA (geoTransformAlong A T))
    (hB : IsInvDomain kB (geoTransformAlong B T))
    (hE : (geoTransformAlong B T).E = (geoTransformAlong A T).E)
    (hdim : SameCarrierDim (geoTransformAlong A T) (geoTransformAlong B T))
    {y : Y} (hyA : y ∈ (geoTransformAlong A T).cosupp)
    (hyOff : ∀ H ∈ F, y ∉ strictAlong T H) :
    (geoTransformAlong B T).d * ordinaryTraceOrder (geoTransformAlong A T).N
      (geoTransformAlong A T).ideal y =
    (geoTransformAlong A T).d * ordinaryTraceOrder (geoTransformAlong B T).N
      (geoTransformAlong B T).ideal y := by
  have hStage := LocEquiv.geoTransformAlong h T hT
  rw [HironakaG8CaseNPrefix.geoTransformAlong_prefix A F T,
    HironakaG8CaseNPrefix.geoTransformAlong_prefix B F T] at hStage
  have hClosedStage : ∀ H ∈ F.map (strictAlong T), IsClosed H := by
    intro H hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact MemberInterTowerAlong.isClosed_strictAlong T (hClosed H₀ hH₀)
  have hyOffStage : ∀ H ∈ F.map (strictAlong T), y ∉ H := by
    intro H hH
    obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
    exact hyOff H₀ hH₀
  exact HironakaG8CaseNRestriction.normalized_order_eq_off_finite_original_prefix
    (geoTransformAlong A T) (geoTransformAlong B T) hA hB hE hdim
    (F.map (strictAlong T)) hClosedStage hStage hyA hyOffStage

end
end Hironaka.HironakaG8CaseNPrefixRestriction
