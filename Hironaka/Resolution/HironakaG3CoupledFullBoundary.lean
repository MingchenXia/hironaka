import Hironaka.Resolution.HironakaG3ContainingStratumHistory
import Hironaka.Resolution.HironakaG3StoppedCoupledGeometry
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3CoupledFullBoundary
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison HironakaDisjointFiniteControlledHistory
  HironakaG3ControlledHistorySubsetTransport CoefficientIdealRestriction

/-- On the same actual coupled tower, restore every original SNC boundary
member containing the contact, including its strict transform. -/
theorem restore_containing_boundary {d t : ℕ}
    {X : CMfd.{0} (d+t)} {P Q : CMfd.{0} d} {Y : CMfd.{0} (d+t)}
    {N W : Set X} {E B : List (Set X)} {J : GermIdeal (d+t) X}
    {ι : P → X} {M : MarkedIdeal d P} {T : BlowupTower P Q} {A : BlowupTower X Y}
    {η : Q → Y} (h : CoupledHistory N B J ι M T A η)
    (hJ : J.IsCoherent) (hE : IsSNCDivisor (d+t) E) (hBsub : B.Sublist E)
    (hOmitted : ∀ H ∈ E, H ∉ B → N ⊆ H) (hWN : W ⊆ N)
    (hTest : IsGeoTestTower (fullMarked B J) A)
    (hNC : HasNormalCrossings (d+t) (strictAlong A W) (geoTransformAlong (fullMarked B J) A).E) :
    IsGeoTestTower (fullMarked E J) A ∧
      IsSNCDivisor (d+t) (geoTransformAlong (fullMarked E J) A).E ∧
      HasNormalCrossings (d+t) (strictAlong A W) (geoTransformAlong (fullMarked E J) A).E := by
  have hFull : (fullMarked E J).IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,hJ,hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hCentres := centresIn_of_coupledHistory h
  obtain ⟨hIff,hMembers,hMissing⟩ :=
    DropMembers.isGeoTestTower_withE_iff_of_centresIn (fullMarked E J) hFull
      (E' := B) (S := N) (fun _ hH => hBsub.subset hH) hOmitted A hCentres
  have hTestFull : IsGeoTestTower (fullMarked E J) A := hIff.mp hTest
  have hSNC := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hFull A hTestFull).isSNCDivisor
  have hSub : strictAlong A W ⊆ strictAlong A N := MemberInterTowerAlong.strictAlong_mono A hWN
  refine ⟨hTestFull,hSNC,(hasNormalCrossings_iff_of_forall_mem hSNC hMembers ?_).mp hNC⟩
  intro H hH hNot
  exact hSub.trans (hMissing H hH hNot)
end
end Hironaka.HironakaG3CoupledFullBoundary
