import Hironaka.Resolution.HironakaG4OrderedProcessedMaskHistory

/-! A label containing an absent original row has a reflexive phase. -/

set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4EmptyOldMaskPhase

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison HomogenizedGlueingTower GermIdealOrder InvertibleIdealQuotient
  MonomialPartAlong RestrictedIdealExtension HironakaActualProcessedMaskControlledSum
  HironakaActualProcessedMaskFiniteBlock HironakaG4PreparedCentreCoordinates
  HironakaG4RecordedTowerResidualCompatibility HironakaSharpActualFiniteChronologicalHistory
  HironakaG34ProcessedMaskEquivariance
  CanonicalCentres
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- A mask containing one empty original old row has empty cosupport on
the actual current carrier. -/
theorem processed_mask_cosupp_eq_empty_of_empty_old_row (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {P : Finset (Fin E.length)} {i : Fin E.length} (hi : i ∈ P)
    (hEmpty : E.get i = ∅) : (processedMaskMarked W E T P).cosupp = ∅ := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let H := strictAlong T (E.get i)
  let I := restrictOn n A.N (vanishingIdeal (n := n) H)
  have hGeom := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hBorn := isSNCDivisor_of_sublist hGeom.2.1 (List.sublist_append_right _ _)
  have hH : H = ∅ := by
    unfold H
    rw [hEmpty,StepOneEmptyPrefix.strictAlong_empty]
  have hCoherentH : (vanishingIdeal (n := n) H).IsCoherent :=
    isCoherent_vanishingIdeal_of_mem hn hGeom.2.1
      (List.mem_append_left _ (List.mem_map_of_mem (List.get_mem E i)))
  have hCoherentI : I.IsCoherent := (hGeom.2.2.2.2 i).1
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hUnitH : (vanishingIdeal (n := n) H).mem x (fun _ => (1 : ℂ)) := by
    refine ⟨holomorphicAt_const 1,?_⟩
    rw [hH]
    exact Eventually.of_forall fun _ hy => (notMem_empty _ hy).elim
  have hUnitI : I.mem x (fun _ => (1 : ℂ)) :=
    le_restrictOn hCoherentH x _ hUnitH
  have hUnitFactor : (oldFactor W E T i).mem x (fun _ => (1 : ℂ)) :=
    le_monomialPartAlong hn hBorn hGeom.2.2.1 hCoherentI x _ hUnitI
  have hUnit : (processedMaskMarked W E T P).ideal.mem x (fun _ => (1 : ℂ)) :=
    isInSpanAt_self (S := fun f => ∃ j ∈ P,(oldFactor W E T j).mem x f)
      ⟨i,hi,hUnitFactor⟩ (holomorphicAt_const 1)
  exact one_ne_zero ((vanishesToOrderOn_one_iff hx.1 (holomorphicAt_const 1)).mp (hx.2 _ hUnit))

/-- An absent-row label can remain in the schedule with the actual identity
history, including its original-family canonical certificate. -/
theorem canonical_processed_identity_of_empty_old_row (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {P : Finset (Fin E.length)} {i : Fin E.length} (hi : i ∈ P)
    (hEmpty : E.get i = ∅) :
    let M := processedMaskMarked W E T P
    IsCanonical M ((invFamily hn (n+1)).inv M) (.refl : BlowupTower Y Y) ∧
      IsGeoResolution M (.refl : BlowupTower Y Y) := by
  intro M
  exact ⟨trivial,trivial,
    processed_mask_cosupp_eq_empty_of_empty_old_row hn hW hE hdense T hT hFull hi hEmpty⟩

end
end Hironaka.HironakaG4EmptyOldMaskPhase
