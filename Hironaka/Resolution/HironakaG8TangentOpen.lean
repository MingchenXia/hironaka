import Hironaka.Resolution.HironakaG11IntrinsicTangentTransfer
import Hironaka.Resolution.HironakaG8CaseNOpenTransport
/-! # Intrinsic tangent containment on an open subset -/
set_option autoImplicit false
set_option maxHeartbeats 200000
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG8TangentOpen
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers BlowupSpaceTangent
  HironakaG11IntrinsicTangentTransfer HironakaG8CaseNOpenTransport

/-- At an incident regular point, containment of intrinsic tangent spaces is
unchanged by restricting both sets to an actual open neighbourhood. -/
theorem tangent_le_preimage_val_iff
    {n : ℕ} {X : CMfd.{u} n} (O : Opens X) {P H : Set X} (p : O) {k : ℕ}
    (hP : RegularAtDim (n := n) P p.val k) (hpH : p.val ∈ H) :
    tangentSpace n ((Subtype.val : O → X) ⁻¹' P) p ≤
        tangentSpace n ((Subtype.val : O → X) ⁻¹' H) p ↔
      tangentSpace n P p.val ≤ tangentSpace n H p.val := by
  have hPO : RegularAtDim (n := n) ((Subtype.val : O → X) ⁻¹' P) p k :=
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hP
  calc
    tangentSpace n ((Subtype.val : O → X) ⁻¹' P) p ≤
        tangentSpace n ((Subtype.val : O → X) ⁻¹' H) p ↔
      p ∈ GermIdealOrder.cosupport n ((Subtype.val : O → X) ⁻¹' P)
        (vanishingIdeal (n := n) ((Subtype.val : O → X) ⁻¹' H)) 2 :=
      (cosupport_vanishing_two_iff_tangent_le (X := CMfd.of (n := n) O) hPO hpH).symm
    _ ↔ p.val ∈ GermIdealOrder.cosupport n P (vanishingIdeal (n := n) H) 2 :=
      cosupport_vanishingIdeal_pullback_val P H O p
    _ ↔ tangentSpace n P p.val ≤ tangentSpace n H p.val :=
      cosupport_vanishing_two_iff_tangent_le (X := X) hP hpH

end
end Hironaka.HironakaG8TangentOpen
