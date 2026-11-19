import Hironaka.Resolution.HironakaG4OriginalMixedTailProtection
import Hironaka.Resolution.HironakaG4RetainedPreparedDefectRerun

/-! Protection of native prepared retained rows along the same actual equivariant lower tail. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedEquivariantTailProtection

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaG34MaskFoldEquivariance HironakaG34EquivariantLiftAction HironakaG34LowerCleanupLift
  HironakaG4PreparedCentreCoordinates HironakaG4OriginalUnitStepProtection
  HironakaG4OriginalMixedTailProtection HironakaG4RetainedPreparedLocalSupport
  HironakaG4RetainedPreparedOverlapStep HironakaG4RetainedPreparedDefectRerun
  HironakaG4OrderedRetainedDefectTrace HironakaActualRetainedBornResidualHistory
  HironakaActualProtectedOtherRowLocalStep HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualCurveGlobalBoundaryCoordinates HironakaSharpOriginalProductTraceOrder
  RestrictEmptyTower

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Each actual step of the retained tail carries its selected row's
incident protected window at the true source support. -/
def RetainedProtectedTail (N : Set X) (old born : List (Set X)) (i : Fin old.length) :
    {Y : CMfd.{u} n} → BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step R C _ _ =>
    RetainedProtectedTail N old born i R ∧
      ∀ x ∈ C ∩ retainedRowSupport N old born i R,
        ProtectedWindowAt (geoTransformAlong (geometricTemplate N born) R).N
          (retainedRowSupport N old born i R) (retainedRowBoundary N old born i R) C x

private theorem remaining_boundary_along (N : Set X) (old born : List (Set X))
    (i : Fin old.length) (R : BlowupTower X Y) :
    (old.eraseIdx i.val ++ born).map (strictAlong R) ++
      (geoTransformAlong (geometricTemplate N []) R).E =
        retainedRowBoundary N old born i R := by
  unfold retainedRowBoundary
  rw [boundary_geoTransformAlong_decomposition
      (geometricTemplate N born) (geometricTemplate N []) rfl R]
  simp only [List.map_append, List.eraseIdx_map, List.append_assoc]
  rfl

set_option maxHeartbeats 800000 in
/-- The same lower test tower, equivariant for the literal retained
boundary and any prescribed extra labels, preserves each already
prepared retained row with its exact strict-transform support. -/
theorem retained_mixed_tail_protects_prepared_row_with_window (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (i j : Fin old.length) (hne : j ≠ i)
    (hPrep : RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    (P : MarkedIdeal n X) (hPclosed : IsClosed P.N)
    (hPcarrier : P.N = N ∩ (oldResidualPart N old born j).zeroLocus)
    (V : Opens X) (extra : List (Set X)) (hExtra : ∀ K ∈ extra, (V : Set X) ⊆ K) :
    ∀ {Y : CMfd.{u} n} (R : BlowupTower X Y),
      IsGeoTestTower P R →
      CentresOver (V : Set X) R →
      IsEquivariant P.N (extra ++ (old ++ born)) R →
      IsGeoTestTower (geometricTemplate N born) R →
      IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) R →
      RetainedRowPrepared N old born i R ∧
      retainedRowSupport N old born i R =
        strictAlong R (retainedRowSupport N old born i (.refl : BlowupTower X X)) ∧
      RetainedProtectedTail N old born i R := by
  have hPN : P.N ⊆ N := by rw [hPcarrier]; exact inter_subset_left
  let S := N ∩ (oldResidualPart N old born i).zeroLocus
  have hOrd : ∀ x ∈ N, ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ 1 := hPrep.1
  have hClosed : IsClosed S :=
    (native_row_globally_reduced hn g.carrier g.full g.born_transverse g.dense i hOrd).1.1
  obtain ⟨hNC,hDenseS⟩ := prepared_refl_nc_dense i hPrep
  intro Y R
  induction R with
  | refl =>
    intro _ _ _ _ _
    exact ⟨hPrep,rfl,trivial⟩
  | @step Y Z R C π hπ ih =>
    intro hTest hOver hEq hUpper hAmbient
    obtain ⟨hPrev,hSupport,hTail⟩ := ih hTest.1 hOver.1 (IsEquivariant.of_step hEq) hUpper.1 hAmbient.1
    let A := geoTransformAlong (geometricTemplate N born) R
    let O := old.map (strictAlong R)
    let k : Fin O.length := Fin.cast (List.length_map _).symm i
    have hCurrent := retained_preparation_current_readback hn g i R hUpper.1 hAmbient.1
    have hPrepCurrent : RetainedRowPrepared A.N O A.E k (.refl : BlowupTower Y Y) :=
      hCurrent.1.mp hPrev
    obtain ⟨hN,hFull,hTr,hDense,_⟩ :=
      actual_retained_born_recorded_residual_dictionary hn g.carrier g.full g.born_transverse g.dense
        R hUpper.1 hAmbient.1
    have hCarrier : A.N = strictAlong R N := N_geoTransformAlong (geometricTemplate N born) R
    have hBoundary := remaining_boundary_along N old born i R
    have hCert (x : Y) (hx : x ∈ C ∩ retainedRowSupport N old born i R) :
        ProtectedWindowAt A.N (retainedRowSupport N old born i R)
          (retainedRowBoundary N old born i R) C x := by
      have hxS : x ∈ strictAlong R S := hSupport ▸ hx.2
      have hxBase := MemberInterTowerAlong.strictAlong_subset_preimage R hClosed hxS
      have hc : ProtectedWindowAt (strictAlong R N) (strictAlong R S)
          ((old.eraseIdx i.val ++ born).map (strictAlong R) ++
            (geoTransformAlong (geometricTemplate N []) R).E) C x := by
        by_cases hUnit : (oldMonomialPart N old born i).mem (R.proj x) 1
        · exact native_prepared_row_unit_step_certificate hn g.carrier g.full g.born_transverse g.dense
            i hOrd hNC hDenseS P (geometricTemplate (univ : Set X) (old ++ born)) hPN rfl
            R C π hπ hTest hAmbient x hxBase hUnit
        · exact native_prepared_row_nonunit_step_certificate_with_window hn g.carrier g.full
            g.born_transverse g.dense i j hne hOrd hNC hDenseS P hPclosed hPcarrier R C π hπ hTest
            V extra hExtra hEq x hx.1 (hOver.2 hx.1) hxBase hUnit
      rw [←hCarrier,hBoundary] at hc
      change retainedRowSupport N old born i R = strictAlong R S at hSupport
      rwa [←hSupport] at hc
    let T : BlowupTower Y Z := .step .refl C π hπ
    have hCN : C ⊆ A.N := hUpper.2.subset_N
    have hCertCurrent (x : Y) (hx : x ∈ C ∩ retainedRowSupport A.N O A.E k (.refl : BlowupTower Y Y)) :
        ProtectedWindowAt A.N (retainedRowSupport A.N O A.E k (.refl : BlowupTower Y Y))
          (O.eraseIdx k.val ++ A.E) C x := by
      rw [←hCurrent.2] at hx ⊢
      exact hCert x hx
    obtain ⟨hPrepNext,hSupportNext⟩ :=
      retained_prepared_row_step_of_incident_protected_windows hn hN hFull hTr hDense
        k hPrepCurrent hπ hCN hCertCurrent
    have hNext := retained_preparation_append_readback hn g i R hUpper.1 hAmbient.1 T
    refine ⟨hNext.1.mpr hPrepNext,?_,hTail,hCert⟩
    change retainedRowSupport N old born i (R.append T) =
      geoStrictTransform π C (strictAlong R S)
    rw [hNext.2,hSupportNext,←hCurrent.2,hSupport]
    rfl


/-- A single actual equivariant lower tail preserves the specified family
of earlier prepared native rows and gives each exact support readback. -/
theorem retained_mixed_tail_protects_prepared_rows_with_window (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (rows : Finset (Fin old.length)) (j : Fin old.length) (hj : j ∉ rows)
    (hPrep : ∀ i ∈ rows, RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    (P : MarkedIdeal n X) (hPclosed : IsClosed P.N)
    (hPcarrier : P.N = N ∩ (oldResidualPart N old born j).zeroLocus)
    (V : Opens X) (extra : List (Set X)) (hExtra : ∀ K ∈ extra, (V : Set X) ⊆ K)
    (R : BlowupTower X Y) (hTest : IsGeoTestTower P R) (hOver : CentresOver (V : Set X) R)
    (hEq : IsEquivariant P.N (extra ++ (old ++ born)) R)
    (hUpper : IsGeoTestTower (geometricTemplate N born) R)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) R) :
    ∀ i ∈ rows,
      RetainedRowPrepared N old born i R ∧
      retainedRowSupport N old born i R =
        strictAlong R (retainedRowSupport N old born i (.refl : BlowupTower X X)) ∧
      RetainedProtectedTail N old born i R := by
  intro i hi
  have hne : j ≠ i := fun he => hj (he.symm ▸ hi)
  exact retained_mixed_tail_protects_prepared_row_with_window hn g i j hne (hPrep i hi)
    P hPclosed hPcarrier V extra hExtra R hTest hOver hEq hUpper hFull


end
end Hironaka.HironakaG4RetainedEquivariantTailProtection
