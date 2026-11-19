import Hironaka.Resolution.HironakaG4RetainedTraceOverlap
import Hironaka.Resolution.HironakaG4RetainedPreparedLocalSupport
import Hironaka.Resolution.HironakaActualProcessedAllMasksDrop

/-! An actual compact-relative defect rerun preserves disjoint prepared supports. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4ProtectedRetainedDefectExit
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals.MarkedIdeal
  MarkedIdealTowerTransport HomogenizedGlueingTower
  NormalCrossings NormalCrossingsComparison RestrictEmptyTower
  HironakaActualProcessedAllMasksDrop HironakaG3CentresOverGenericFactor
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaG4PreparedCentreCoordinates HironakaActualRetainedBornResidualHistory
  HironakaActualRetainedBoundaryMaskBlock HironakaG4RetainedRankTowerIso HironakaG4RetainedCurrentStamp
  HironakaG4RetainedDefectRelativeDecrease HironakaG4OrderedRetainedDefectTrace
  HironakaG4RetainedDefectRelativeExit HironakaG4RetainedPreparedLocalSupport
  HironakaG4CompactWholeMonomialMaskPhase

variable {n : ℕ} {X Y : CMfd.{u} n}

set_option maxHeartbeats 700000 in
/-- Every actual centre of an ordered retained trace is over the initial
true retained distinct germ defect. The proof follows the whole actual
trace, including literal restrictions and transports. -/
theorem ordered_retained_trace_centresOver_defect {hn : 0 < n} {N : Set X}
    {old born : List (Set X)} {μ : WithTop RetainedStampRank} {T : BlowupTower X Y}
    (R : OrderedRetainedDefectTrace hn N old born μ T) :
    NativeRetainedGeometry N old born →
      CentresOver (actualFamilyDistinctDefect N (oldResidualPart N old born)) T := by
  induction R with
  | done _ => exact fun _ => trivial
  | @phase A B C N old born μ Q S P _hBound hQ hFull _tail ih =>
    intro g
    let D := actualFamilyDistinctDefect N (oldResidualPart N old born)
    let Bnow := geoTransformAlong (geometricTemplate N born) Q
    let O := old.map (strictAlong Q)
    let Dnow := actualFamilyDistinctDefect Bnow.N (oldResidualPart Bnow.N O Bnow.E)
    have hP : P.footprint ⊆ D := fun x hx => ((P.footprint_iff x).mp hx).1
    have hActual := actual_retained_defect_and_rank_current_tuple hn g.carrier g.full
      g.born_transverse g.dense Q hQ hFull
    have hMap : Dnow ⊆ Q.proj ⁻¹' D := by
      intro y hy
      by_cases hyP : Q.proj y ∈ P.footprint
      · exact hP hyP
      · have hd : y ∈ retainedDistinctDefect N old born Q := hActual.1 ▸ hy
        exact (actual_retained_defect_unchanged_off_closed_footprint hn g.carrier g.full
          g.born_transverse g.dense Q hQ hFull P.isClosed_footprint P.centresOver y hyP).mp hd
    have hG := actual_retained_born_recorded_residual_dictionary hn g.carrier g.full
      g.born_transverse g.dense Q hQ hFull
    have hS : CentresOver Dnow S := ih ⟨hG.1,hG.2.1,hG.2.2.1,hG.2.2.2.1⟩
    exact (centresOver_append_iff D Q S).mpr
      ⟨centresOver_mono_local hP Q P.centresOver,centresOver_mono_local hMap S hS⟩
  | @restrictOpen A B N old born μ Q U g _tail ih =>
    intro _gU
    rw [(actual_retained_defect_and_rank_open hn g.carrier g.full g.born_transverse g.dense U).1]
    exact centresOver_restrict U _ Q (ih g)
  | @rebase A A' B N old born μ Q φ g _tail ih =>
    intro _gNew
    rw [(actual_retained_defect_and_rank_biholomorph hn g.carrier g.full g.born_transverse g.dense φ).1]
    exact centresOver_of_isTowerIso (transport_isTowerIso φ Q) _ (ih g)

set_option maxHeartbeats 700000 in
/-- An actual finite retained-defect rerun near a compact enclosure,
retaining every prepared row whose support misses the source defect. -/
theorem exists_protected_ordered_retained_defect_exit_near_compact (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (P : Finset (Fin old.length))
    (hP : ∀ i ∈ P,RetainedRowPrepared N old born i (.refl : BlowupTower X X))
    (hDisjoint : ∀ i ∈ P,Disjoint (actualFamilyDistinctDefect N (oldResidualPart N old born))
      (retainedRowSupport N old born i (.refl : BlowupTower X X)))
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      let u := (Subtype.val : U → X)
      let NU := u ⁻¹' N
      let OU := old.map (u ⁻¹' ·)
      let BU := born.map (u ⁻¹' ·)
      let A := geoTransformAlong (geometricTemplate NU BU) T
      IsGeoTestTower (geometricTemplate NU BU) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) T ∧
      CurrentSharpCentres NU (OU ++ BU) T ∧
      CentresOver (u ⁻¹' actualFamilyDistinctDefect N (oldResidualPart N old born)) T ∧
      actualFamilyDistinctDefect A.N (oldResidualPart A.N (OU.map (strictAlong T)) A.E) = ∅ ∧
      Nonempty (OrderedRetainedDefectTrace hn NU OU BU ⊤ T) ∧
      ∀ i ∈ P,
        let iU : Fin OU.length := Fin.cast (List.length_map _).symm i
        RetainedRowPrepared NU OU BU iU T ∧
          retainedRowSupport NU OU BU iU T =
            (u ∘ T.proj) ⁻¹' retainedRowSupport N old born i (.refl : BlowupTower X X) := by
  obtain ⟨U,hKU,Y,T,hT,hFull,hSharp,hEnd,⟨R⟩⟩ :=
    exists_ordered_retained_defect_exit_near_compact hn g.carrier g.full g.born_transverse g.dense hK
  let XU := CMfd.of (n := n) U
  let u := (Subtype.val : U → X)
  let NU := u ⁻¹' N
  let OU := old.map (u ⁻¹' ·)
  let BU := born.map (u ⁻¹' ·)
  let D := actualFamilyDistinctDefect N (oldResidualPart N old born)
  have gU : NativeRetainedGeometry (X := XU) NU OU BU := g.restrict U
  have hD := (actual_retained_defect_and_rank_open hn g.carrier g.full g.born_transverse g.dense U).1
  have hOver := ordered_retained_trace_centresOver_defect R gU
  rw [hD] at hOver
  refine ⟨U,hKU,Y,T,hT,hFull,hSharp,hOver,hEnd,⟨R⟩,?_⟩
  intro i hi iU
  obtain ⟨hPrepU,hSuppU⟩ := retained_prepared_row_restrict_open hn g.carrier g.full
    g.born_transverse g.dense i (hP i hi) U
  have hSep : Disjoint (u ⁻¹' D) (retainedRowSupport (X := XU) NU OU BU iU .refl) := by
    rw [hSuppU]
    exact (hDisjoint i hi).preimage u
  obtain ⟨hPT,hSuppT⟩ := retained_prepared_row_of_disjoint_footprint hn gU.carrier gU.full
    gU.born_transverse gU.dense iU hPrepU hSep T hT hOver
  exact ⟨hPT,hSuppT.trans (congrArg (fun S : Set U => T.proj ⁻¹' S) hSuppU)⟩

end
end Hironaka.HironakaG4ProtectedRetainedDefectExit
