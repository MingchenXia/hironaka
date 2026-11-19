import Hironaka.Resolution.HironakaG4RetainedEquivariantRowService
import Hironaka.Resolution.HironakaActualOriginalProcessedJointPreparedness

/-! Compact-relative full sharp existence by dimension, with the processed finish as input. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4CompactRelativeSharpDimension
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport MaxLocusLocal
  MarkedIdeals MarkedIdeals.MarkedIdeal HomogenizedGlueingTower NormalCrossings
  NormalCrossingsComparison NormalCrossingsInvariance
  HironakaG4RetainedEquivariantRowService HironakaG4RetainedPreparedFold
  HironakaG4RetainedPreparedContinuation HironakaG4OrderedRetainedDefectTrace
  HironakaG4RetainedPreparedDefectRerun HironakaG4RetainedPreparedLocalSupport
  HironakaG4PreparedCentreCoordinates HironakaG4RetainedDefectRelativeExit
  HironakaG4SharpTerminalAtlas HironakaG34MaskFoldEquivariance HironakaG4MonomialFamilyInvariant
  HironakaG4RetainedDefectTraceEquivariance HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4RetainedPreparationTrace HironakaG4RetainedPreparationLowerHistory
  HironakaSharpActualFiniteChronologicalHistory HironakaActualRetainedBornResidualSeed
  HironakaActualRetainedBornResidualHistory HironakaSharpOriginalProductTraceOrder
  HironakaActualProcessedAllMasksDrop HironakaActualProcessedMaskFiniteBlock
  HironakaActualOriginalProcessedJointPreparedness
  RegularPointDimension AnalyticIrreducibleComponents

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- The processed finish for a strictly equivariant sharp prefix on an
arbitrary compact enclosure. The input retains the exact original rows. -/
def CompactRelativeEquivariantProcessedFinish (n : ℕ) : Prop :=
  ∀ (X Y : CMfd.{u} n) (W : Set X) (E : List (Set X)),
    IsClosedSubmanifold n W → IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E,H) →
    ∀ T : BlowupTower X Y, At W E E.length T → IsEquivariant W E T →
      ∀ K : Set X, IsCompact K → ∃ O : Opens X, K ⊆ O ∧
        ∃ (Z : CMfd.{u} n) (S : BlowupTower (CMfd.of (n := n) O) Z),
          let u := (Subtype.val : O → X)
          IsSharpTerminalTower (u ⁻¹' W) (E.map (u ⁻¹' ·)) S ∧
          IsEquivariant (u ⁻¹' W) (E.map (u ⁻¹' ·)) S

/-- Original row positions are read from the length of the retained ordered list. -/
def originalRetainedPreparationPhases (length : ℕ) : List RetainedPreparationPhase :=
  retainedPreparationPhases (((Finset.univ : Finset (Fin length)).sort (· ≤ ·)).map Fin.val)

/-- The processed finish consumes the exact prepared tape and returns a
certificate on the same actual terminal tower. -/
def CompactRelativeEquivariantProcessedFinishUsing (hn : 0 < n)
    (lower result : SharpHistoryPredicate.{u} n) : Prop :=
  ∀ (X Y : CMfd.{u} n) (W : Set X) (E : List (Set X)),
    IsClosedSubmanifold n W → IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E,H) →
    ∀ T : BlowupTower X Y, At W E E.length T → IsEquivariant W E T →
      ∀ tape : RetainedPreparationTrace hn W E [] (originalRetainedPreparationPhases E.length) T,
        usesLowerHistory lower tape →
        ∀ K : Set X, IsCompact K → ∃ O : Opens X, K ⊆ O ∧
          ∃ (Z : CMfd.{u} n) (S : BlowupTower (CMfd.of (n := n) O) Z),
            let u := (Subtype.val : O → X)
            IsSharpTerminalTower (u ⁻¹' W) (E.map (u ⁻¹' ·)) S ∧
            IsEquivariant (u ⁻¹' W) (E.map (u ⁻¹' ·)) S ∧
            result (u ⁻¹' W) (E.map (u ⁻¹' ·)) S

/-- The property survives actual rebasing by a biholomorphism. -/
def SharpHistoryRebase (history : SharpHistoryPredicate.{u} n) : Prop :=
  ∀ {X X' Y : CMfd.{u} n} {W : Set X} {E : List (Set X)}
    (φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) (T : BlowupTower X Y),
    history W E T → history (φ ⁻¹' W) (E.map (φ ⁻¹' ·)) (transport φ T).tower

set_option maxHeartbeats 600000 in
/-- All prepared retained rows on an original prefix give the exact
processed state used by the existing monomial finish. -/
theorem original_processed_at_of_all_retained_rows (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hPrep : ∀ i : Fin E.length, RetainedRowPrepared W E [] i T) :
    At W E E.length T := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let OY := E.map (strictAlong T)
  have g : NativeRetainedGeometry W E [] :=
    ⟨hW,by simpa using hE,isTransverse_nil_of_isClosedSubmanifold hW,by simpa using hDense⟩
  have hEach (i : Fin E.length) :
      (∀ x ∈ A.N,ordinaryTraceOrder A.N (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1) ∧
      HasNormalCrossings n (residualSupport W E T i) (OY.eraseIdx i.val ++ A.E) ∧
      residualSupport W E T i ⊆ closure (residualSupport W E T i \ ⋃ H ∈ OY.eraseIdx i.val ++ A.E,H) := by
    let j : Fin OY.length := Fin.cast (List.length_map _).symm i
    let J := retainedResidualMarked A.N OY A.E j
    let M := chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T
    have hJ : J = M := retained_seed_eq_original_chronological hn hW hE hDense T hT hFull i
    have h := (retained_preparation_current_readback hn g i T hT (by simpa using hFull)).1.mp (hPrep i)
    let L := A.N ∩ J.ideal.zeroLocus
    change (∀ x ∈ A.N,ordinaryTraceOrder A.N J.ideal x ≤ 1) ∧
      HasNormalCrossings n L ((OY.map id).eraseIdx j.val ++ A.E) ∧
      L ⊆ closure (L \ ⋃ H ∈ (OY.map id).eraseIdx j.val ++ A.E,H) at h
    have hSupport : L = residualSupport W E T i := by
      unfold L
      rw [hJ]
      rfl
    rw [hSupport,hJ,List.map_id] at h
    exact h
  have hOrd : ∀ x ∈ A.N,∀ i : Fin E.length,
      ordinaryTraceOrder A.N (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1 :=
    fun x hx i => (hEach i).1 x hx
  have hNC : ∀ i : Fin E.length,
      HasNormalCrossings n (residualSupport W E T i) (OY.eraseIdx i.val ++ A.E) :=
    fun i => (hEach i).2.1
  have hDenseS : ∀ i : Fin E.length,
      residualSupport W E T i ⊆ closure (residualSupport W E T i \ ⋃ H ∈ OY.eraseIdx i.val ++ A.E,H) :=
    fun i => (hEach i).2.2
  have hJoint := actual_original_processed_joint_preparedness hn hW hE hDense T hT hFull hOrd hNC hDenseS
  refine ⟨hT,hFull,hSharp,hOrd,hNC,hDenseS,hJoint,?_⟩
  intro x _hx
  simpa only [tauD,Fintype.card_fin] using Finset.card_le_univ (properRows (factorMatrix W E T x))

set_option maxHeartbeats 700000 in
private theorem terminal_equivariant_flatten_using (history : SharpHistoryPredicate.{u} n)
    (hRebase : SharpHistoryRebase history) (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (g : NativeRetainedGeometry W E []) {K : Set X}
    (U : Opens X) (hKU : K ⊆ U)
    (V : Opens (CMfd.of (n := n) U)) (hKV : (Subtype.val : U → X) ⁻¹' K ⊆ V)
    (S : BlowupTower (CMfd.of (n := n) V) Y) :
    let ν := (Subtype.val : U → X)
    let v := (Subtype.val : V → U)
    let NV := v ⁻¹' (ν ⁻¹' W)
    let EV := (E.map (ν ⁻¹' ·)).map (v ⁻¹' ·)
    IsSharpTerminalTower NV EV S → IsEquivariant NV EV S → history NV EV S →
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) O) Z),
      let o := (Subtype.val : O → X)
      IsSharpTerminalTower (o ⁻¹' W) (E.map (o ⁻¹' ·)) T ∧ IsEquivariant (o ⁻¹' W) (E.map (o ⁻¹' ·)) T ∧
      history (o ⁻¹' W) (E.map (o ⁻¹' ·)) T := by
  intro ν v NV EV hTerminal hEq hHistory
  obtain ⟨O,hKO,hVO,hOU,hRT,hRF,hRS,_gS,hRN,hRO,hRB⟩ :=
    exists_flattened_retained_history_native hn g U hKU V hKV S
      (by simpa only [List.map_nil] using hTerminal.carrierTest)
      (by simpa only [List.map_nil,List.append_nil] using hTerminal.boundaryTest)
      (by simpa only [List.map_nil,List.append_nil] using hTerminal.sharp)
  let XV := CMfd.of (n := n) V
  let XO := CMfd.of (n := n) O
  let φ := (nestedDiffeo (n := n) U V O hVO hOU).symm
  let R := transport φ S
  let o := (Subtype.val : O → X)
  let NO := o ⁻¹' W
  let EO := E.map (o ⁻¹' ·)
  let AV := geoTransformAlong (geometricTemplate (X := XV) NV []) S
  let AR := geoTransformAlong (geometricTemplate (X := XO) NO []) R.tower
  let b := R.back
  have hFullV := retained_born_full_boundary_ordered_dictionary NV EV [] S
  have hFullO := retained_born_full_boundary_ordered_dictionary NO EO [] R.tower
  simp only [List.append_nil] at hFullV hFullO
  have hEquivariant := isEquivariant_of_actualIso (transport_isTowerIso φ S) hEq
  have hN : φ ⁻¹' NV = NO := rfl
  have hE : EV.map (φ ⁻¹' ·) = EO := by
    simp only [EV,EO,List.map_map]
    rfl
  have hRebased := hRebase φ S hHistory
  rw [hN,hE] at hEquivariant hRebased
  refine ⟨O,hKO,R.target,R.tower,⟨?_,?_,?_,?_⟩,hEquivariant,hRebased⟩
  · simpa only [List.map_nil] using hRT
  · simpa only [List.map_nil,List.append_nil] using hRF
  · simpa only [List.map_nil,List.append_nil] using hRS
  · change AR.N = b ⁻¹' AV.N at hRN
    change EO.map (strictAlong R.tower) = (EV.map (strictAlong S)).map (b ⁻¹' ·) at hRO
    change AR.E = AV.E.map (b ⁻¹' ·) at hRB
    have hnc : HasNormalCrossings n AV.N (EV.map (strictAlong S) ++ AV.E) := by
      rw [show AV.N = strictAlong S NV from N_geoTransformAlong _ S,←hFullV]
      exact hTerminal.normalCrossings
    rw [←show AR.N = strictAlong R.tower NO from N_geoTransformAlong _ _,hFullO,hRN,hRO,hRB,
      ←List.map_append]
    exact hasNormalCrossings_preimage (pullsBackCoordinates b) hnc

set_option maxHeartbeats 1000000 in
/-- The actual finite prepared fold and a strict compact-relative processed
finish give full sharp existence in every local carrier dimension. -/
theorem compactRelativeEquivariantSharpCleanupsExist_using (hn : 0 < n)
    (history : ℕ → SharpHistoryPredicate.{u} n)
    (hBase : ∀ (X : CMfd.{u} n) (W : Set X) (E : List (Set X)),
      IsClosedSubmanifold n W → IsSharpTerminalTower W E (.refl : BlowupTower X X) →
      history 0 W E (.refl : BlowupTower X X))
    (hRebase : ∀ d, SharpHistoryRebase (history d))
    (hFinish : ∀ d, CompactRelativeEquivariantProcessedFinishUsing hn (history d) (history (d+1)))
    (d : ℕ) : CompactRelativeEquivariantSharpCleanupsExistUsing (history d) d := by
  induction d with
  | zero => exact compactRelativeEquivariantSharpCleanupsExist_zero_using (history 0) hBase
  | succ d ih =>
      intro X W E hW hE hDense hDim K hK
      have g : NativeRetainedGeometry W E [] :=
        ⟨hW,by simpa using hE,isTransverse_nil_of_isClosedSubmanifold hW,by simpa using hDense⟩
      have hRow := compactRelativeRetainedRowServicesExist_of_equivariant_lower_using (history d) hn d ih
      obtain ⟨U,hKU,Y,T,hT,hFull,hSharp,_hEnd,hPrep,hCert⟩ :=
        exists_all_prepared_retained_rows_near_compact_using (history d) hn (d+1) hRow g hDim hK
      let XU := CMfd.of (n := n) U
      let u := (Subtype.val : U → X)
      let NU := u ⁻¹' W
      let EU := E.map (u ⁻¹' ·)
      let e : Fin E.length ≃ Fin EU.length := finCongr (List.length_map _).symm
      have gU : NativeRetainedGeometry (X := XU) NU EU [] := g.restrict U
      have hTU : IsGeoTestTower (geometricTemplate NU []) T := by simpa only [List.map_nil] using hT
      have hFullU : IsGeoTestTower (geometricTemplate (univ : Set XU) EU) T := by
        simpa only [List.map_nil,List.append_nil] using hFull
      have hSharpU : CurrentSharpCentres NU EU T := by
        simpa only [List.map_nil,List.append_nil] using hSharp
      have hPrepU : ∀ j : Fin EU.length,RetainedRowPrepared NU EU [] j T := by
        intro j
        have hRowPrep := hPrep (e.symm j) (Finset.mem_univ _)
        change RetainedRowPrepared NU EU [] (e (e.symm j)) T at hRowPrep
        exact e.apply_symm_apply j ▸ hRowPrep
      have hEqU : IsEquivariant NU EU T := by
        simpa only [List.map_nil,List.append_nil] using (hCert rfl).1
      have hAt := original_processed_at_of_all_retained_rows hn gU.carrier (by simpa using gU.full)
        (by simpa using gU.dense) T hTU hFullU hSharpU hPrepU
      let KU := u ⁻¹' K
      have hKUcomp : IsCompact KU :=
        (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
          (fun x hx => ⟨⟨x,hKU hx⟩,rfl⟩)).mpr hK
      have hCertifiedTape : ∃ tape : RetainedPreparationTrace hn NU EU []
          (originalRetainedPreparationPhases EU.length) T, usesLowerHistory (history d) tape := by
        have hTape := (hCert rfl).2 hn
        have hPhase : originalRetainedPreparationPhases EU.length = originalRetainedPreparationPhases E.length :=
          congrArg originalRetainedPreparationPhases (List.length_map _)
        rw [hPhase]
        exact hTape
      obtain ⟨tape,hLowerTape⟩ := hCertifiedTape
      obtain ⟨V,hKV,Z,S,hTerminal,hEq,hChosen⟩ :=
        hFinish d XU Y NU EU gU.carrier (by simpa using gU.full) (by simpa using gU.dense)
          T hAt hEqU tape hLowerTape KU hKUcomp
      exact terminal_equivariant_flatten_using (history (d+1)) (hRebase (d+1))
        hn g U hKU V hKV S hTerminal hEq hChosen

/-- The finite sharp service with unrestricted lower histories. -/
theorem compactRelativeEquivariantSharpCleanupsExist_of_processed_finish (hn : 0 < n)
    (hFinish : CompactRelativeEquivariantProcessedFinish.{u} n) (d : ℕ) :
    CompactRelativeEquivariantSharpCleanupsExist.{u} n d := by
  let trivialHistory : ℕ → SharpHistoryPredicate.{u} n := fun _ {_ _} _ _ _ => True
  have hF (k : ℕ) : CompactRelativeEquivariantProcessedFinishUsing hn
      (trivialHistory k) (trivialHistory (k+1)) := by
    intro A B W E hW hE hDense T hAt hEq _tape _hTape K hK
    obtain ⟨O,hKO,Z,S,hEnd,hFinalEq⟩ := hFinish A B W E hW hE hDense T hAt hEq K hK
    exact ⟨O,hKO,Z,S,hEnd,hFinalEq,trivial⟩
  exact (compactRelativeEquivariantSharpCleanupsExist_using hn trivialHistory
    (fun _ _ _ _ _ => trivial) (fun _ => by intro A B C W E φ T h; trivial) hF d).forget

/-- The dimension bound can be taken to be the ambient dimension, including
when the carrier is mixed-dimensional. -/
theorem exists_compact_relative_equivariant_sharp_cleanup_of_processed_finish
    (hFinish : CompactRelativeEquivariantProcessedFinish.{u} n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {K : Set X} (hK : IsCompact K) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) O) Z),
      let o := (Subtype.val : O → X)
      IsSharpTerminalTower (o ⁻¹' W) (E.map (o ⁻¹' ·)) T ∧ IsEquivariant (o ⁻¹' W) (E.map (o ⁻¹' ·)) T := by
  have hAll : CompactRelativeEquivariantSharpCleanupsExist.{u} n n := by
    by_cases hn : 0 < n
    · exact compactRelativeEquivariantSharpCleanupsExist_of_processed_finish hn hFinish n
    · obtain rfl : n = 0 := by omega
      exact compactRelativeEquivariantSharpCleanupsExist_zero 0
  exact hAll X W E hW hE hDense (fun x hx => by
    obtain ⟨k,hk⟩ := hW.2 x hx
    exact ⟨k,hk.1,hk⟩) K hK

end
end Hironaka.HironakaG4CompactRelativeSharpDimension
