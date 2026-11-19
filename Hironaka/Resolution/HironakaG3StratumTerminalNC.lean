import Hironaka.Resolution.HironakaG3EndpointNC

/-! Terminal normal crossings for a constructed finite containing-stratum
history, conditional on the corresponding intrinsic endpoint property. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3StratumTerminalNC
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  SubmanifoldChartedSpace HironakaDisjointFiniteControlledHistory
  HironakaG3ControlledHistorySubsetTransport HironakaG3EndpointNC

/-- A given finite intrinsic test tower whose strict target is normal crossing
has an ambient lift with the same full-boundary endpoint property. -/
theorem exists_full_boundary_history_with_terminal_nc
    {d t : ℕ} {X : CMfd.{0} (d+t)} {N : Set X} (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d) (ht : 0 < t)
    {E B : List (Set X)} (hE : IsSNCDivisor (d+t) E) (hBsub : B.Sublist E)
    (hOmitted : ∀ H ∈ E, H ∉ B → N ⊆ H)
    (hTrans : IsTransverse (d+t) N B)
    {W : Set X} (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    let V : Set N := (Subtype.val : N → X) ⁻¹' W
    let L := fullMarked (B.map fun H => (Subtype.val : N → X) ⁻¹' H)
      (vanishingIdeal (n := d) V)
    ∀ {Q : CMfd.{0} d} (T : BlowupTower (CMfd.of N) Q), IsGeoTestTower L T →
      HasNormalCrossings d (strictAlong T V) (geoTransformAlong L T).E →
      ∃ (Y : CMfd.{0} (d+t)) (U : BlowupTower X Y) (η : Q → Y),
        IsGeoTestTower (fullMarked E (vanishingIdeal (n := d+t) W)) U ∧
        U.length = T.length ∧
        CoupledHistory N B (vanishingIdeal (n := d+t) W)
          (Subtype.val : N → X) L T U η ∧
        HasNormalCrossings (d+t) (strictAlong U W)
          (geoTransformAlong (fullMarked E (vanishingIdeal (n := d+t) W)) U).E ∧
        U.proj '' strictAlong U W =
          (Subtype.val : N → X) '' (T.proj '' strictAlong T V) := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  dsimp only
  intro Q T hTest hD
  obtain ⟨Y,U,η,hTestU,hLength,hHist,hEnd,hCentres,hSNC,hSub,hMissing,
    hTarget,hProj,hNonempty⟩ :=
      HironakaG3ContainingStratumHistory.exists_full_boundary_history_for_analytic_subset
        hNc hN ht hE hBsub hOmitted hTrans hWa hWN T hTest
  have hNC := endpoint_full_boundary_nc hEnd (by omega) hSNC hSub hMissing
    (strictAlong T ((Subtype.val : N → X) ⁻¹' W)) hD
  rw [hTarget] at hNC
  exact ⟨Y,U,η,hTestU,hLength,hHist,hNC,hProj⟩

end
end Hironaka.HironakaG3StratumTerminalNC
