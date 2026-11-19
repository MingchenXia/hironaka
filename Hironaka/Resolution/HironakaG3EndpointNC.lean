import Hironaka.Resolution.HironakaG3ContainingStratumHistory
import Hironaka.Resolution.HironakaDisjointEmbeddedBoundaryLift

/-! The terminal normal-crossings transfer for a coupled finite history.
The lower normal-crossings conclusion is an input; no resolution is claimed. -/
set_option autoImplicit false
open Set Filter Function TopologicalSpace Topology
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3EndpointNC
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsInvariance
  SubmanifoldChartedSpace HironakaDisjointFiniteControlledHistory
  HironakaG3ControlledHistorySubsetTransport

/-- Intrinsic normal crossings at the actual lower endpoint lift to the full
ambient boundary, including all omitted members containing the contact. -/
theorem endpoint_full_boundary_nc
    {d t : ℕ} {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)}
    {N : Set X} {B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeal d P} {T : BlowupTower P Q}
    {U : BlowupTower X Y} {η : Q → Y}
    (hEnd : Endpoint N B J ι M T U η) (hn : 0 < d+t)
    {E : List (Set Y)}
    (hE : IsSNCDivisor (d+t) E)
    (hSub : ∀ H ∈ (geoTransformAlong (fullMarked B J) U).E, H ∈ E)
    (hMissing : ∀ H ∈ E, H ∉ (geoTransformAlong (fullMarked B J) U).E →
      strictAlong U N ⊆ H)
    (D : Set Q) (hD : HasNormalCrossings d D (geoTransformAlong M T).E) :
    HasNormalCrossings (d+t) (η '' D) E := by
  obtain ⟨hc, hr, hI, hNormal, hSNC, hTrans, F, hFη, hSquare, hIdeal, hBoundary⟩ := hEnd
  let S := contactAlong N U
  let A := geoTransformAlong (fullMarked B J) U
  let := chartedSpace (Nat.le_add_right d t) hr
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hr
  have hPull := (MarkedIdealTowerTransport.hasNormalCrossings_preimage_iff F.symm).2 hD
  have hSets : (geoTransformAlong M T).E.map (fun H => F.symm ⁻¹' H) =
      A.E.map (fun H => (Subtype.val : S → Y) ⁻¹' H) := by
    rw [← hBoundary, List.map_map]
    apply List.map_congr_left
    intro H hH
    ext s
    change η (F.symm s) ∈ H ↔ s.val ∈ H
    rw [← congrFun hFη (F.symm s), F.apply_symm_apply]
  have hNC : HasNormalCrossings d (F.symm ⁻¹' D)
      (A.E.map fun H => (Subtype.val : S → Y) ⁻¹' H) := by
    rw [← hSets]
    exact hPull
  have hLift := HironakaDisjointEmbeddedBoundaryLift.hasNormalCrossings_native_image
    hr hn hSNC hTrans (F.symm ⁻¹' D) hNC
  have hImage : (Subtype.val : S → Y) '' (F.symm ⁻¹' D) = η '' D := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨F.symm s, hs, ?_⟩
      rw [← congrFun hFη (F.symm s), F.apply_symm_apply]
    · rintro ⟨q, hq, rfl⟩
      refine ⟨F q, ?_, ?_⟩
      · simpa using hq
      · exact congrFun hFη q
  rw [hImage] at hLift
  apply (NormalCrossingsComparison.hasNormalCrossings_iff_of_forall_mem hE hSub ?_).mp hLift
  intro H hH hHnot y hy
  obtain ⟨q, hq, rfl⟩ := hy
  apply hMissing H hH hHnot
  rw [← contactAlong_eq_strictAlong]
  rw [← congrFun hFη q]
  exact (F q).property

end
end Hironaka.HironakaG3EndpointNC
