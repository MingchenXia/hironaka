import Hironaka.Resolution.FactorizationFromResolution
import Hironaka.Resolution.HironakaSharpActualCompositeTotalResidual

set_option autoImplicit false

/-! A centre may miss one old member while that member still meets the carrier
elsewhere. Reuse the exact native disjoint-centre whole ideal pullback law.
Blueprint: hironaka-g4-disjoint-old-strict-trace.tex. -/

open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4DisjointOldStrictTrace

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold MarkedIdeals MarkedIdeals.MarkedIdeal
  RestrictedIdealExtension HironakaSharpActualCompositeTotalResidual
  HironakaSharpOriginalFirstMemberExceptionalFactor

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The normalized WHOLE old strict trace is the actual mark-zero transform
when the real centre misses this member, without global carrier transversality. -/
theorem actual_disjoint_old_zero_mark_trace {N H C : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsClosedSubmanifold n H)
    {E : List (Set X)} {π : Y → X} (hπ : IsBlowupAlong n C π)
    (hCN : C ⊆ N) (hDisj : Disjoint C H) :
    ((⟨N, E, restrictOn n N (vanishingIdeal (n := n) H), 0⟩ : MarkedIdeal n X).geoTransform C π).ideal =
      restrictOn n (geoStrictTransform π C N)
        (vanishingIdeal (n := n) (geoStrictTransform π C H)) := by
  let N' := geoStrictTransform π C N
  have hN' := BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hπ hN hCN
  have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal hH
  have hNorm := actual_normalized_pullback_restrictOn hN hN'.1 hcH hπ.contMDiff
    (fun y hy => geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hy)
  rw [geoTransform_zeroMark_ideal_eq_restricted_total
    (⟨N, E, restrictOn n N (vanishingIdeal (n := n) H), 0⟩ : MarkedIdeal n X) rfl C π]
  change restrictOn n N' (GermIdeal.pullback (m := n) π (restrictOn n N (vanishingIdeal (n := n) H))) = _
  rw [hNorm, FactorizationFromResolution.pullback_vanishingIdeal_eq_of_disjoint hπ hH.1 hDisj]
  have hStrict : geoStrictTransform π C H = π ⁻¹' H := by
    change closure (π ⁻¹' (H \ C)) = π ⁻¹' H
    rw [sdiff_eq_left.mpr hDisj.symm, (hH.1.preimage hπ.contMDiff.continuous).closure_eq]
  rw [hStrict]

end
end Hironaka.HironakaG4DisjointOldStrictTrace
