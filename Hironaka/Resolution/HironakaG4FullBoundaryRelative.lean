import Hironaka.Resolution.HironakaG4FullBoundaryCompactCleanup
import Hironaka.Resolution.HironakaG4SharpTerminalOpen

/-! Reduce finite full-boundary sharp cleanup around compact sets to
compact-relative dense-complement cleanup on the original containment pieces. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4FullBoundaryRelative

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpOriginalDynamicGoodPrefixes
  HironakaG4CompactWholeMonomialMaskPhase HironakaSharpActualFiniteChronologicalHistory
  HironakaActualFullBoundaryContainmentPatterns HironakaActualFullBoundaryMixedPatterns
  HironakaG4FullBoundaryCompactCleanup HironakaG4SharpTerminalAtlas HironakaG4SharpTerminalOpen
  HironakaG4SharpBadFootprint HironakaG34NonPureLowDim HironakaActualProcessedAllMasksDrop
  RestrictEmptyTower SimultaneousNormalCrossings

/-- Input from the dense cleanup construction on an arbitrary compact
ambient task. The output carries the full literal boundary supplied to it. -/
def DenseSharpService (n : ℕ) : Prop :=
  ∀ {X : CMfd.{u} n} {W : Set X}, IsClosedSubmanifold n W →
    ∀ (E : List (Set X)), IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E, H) →
    ∀ (K : Set X), IsCompact K → ∃ O : Opens X, K ⊆ O ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
      IsSharpTerminalTower ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) T

theorem full_piece_on_window {n : ℕ} {X : CMfd.{0} n}
    {W A : Set X} {E F : List (Set X)} (hA : IsClosedSubmanifold n A)
    (hE : IsSNCDivisor n E) (hFE : F.Sublist E) (hContains : ∀ H ∈ E, H ∉ F → A ⊆ H)
    (hBad : originalSharpBadLocus (n := n) A F ⊆ originalSharpBadLocus (n := n) W E ∩ A)
    (O : Opens X) {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) O) Y)
    (hT : IsSharpTerminalTower ((Subtype.val : O → X) ⁻¹' A) (F.map ((Subtype.val : O → X) ⁻¹' ·)) T) :
    CentresOver (originalSharpBadLocus (n := n) ((Subtype.val : O → X) ⁻¹' W)
      (E.map ((Subtype.val : O → X) ⁻¹' ·)) ∩ (Subtype.val : O → X) ⁻¹' A) T ∧
      IsSharpTerminalTower ((Subtype.val : O → X) ⁻¹' A) (E.map ((Subtype.val : O → X) ⁻¹' ·)) T := by
  let XO := CMfd.of (n := n) O
  let v := (Subtype.val : O → X)
  let AO := v ⁻¹' A
  let EO := E.map (v ⁻¹' ·)
  let FO := F.map (v ⁻¹' ·)
  have hAO : IsClosedSubmanifold n AO := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hA O
  have hEO : IsSNCDivisor n EO :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
  have hFOE : FO.Sublist EO := hFE.map _
  have hContainsO : ∀ H ∈ EO, H ∉ FO → AO ⊆ H := by
    rintro J hJ hJF x hx
    obtain ⟨H, hH, rfl⟩ := List.mem_map.mp hJ
    exact hContains H hH (fun h => hJF (List.mem_map_of_mem h)) hx
  have hFoot := (sharpTerminal_full_geometry hAO (isSNCDivisor_of_sublist hEO hFOE) T hT).1
  have hFootSub : originalSharpBadLocus (n := n) AO FO ⊆
      originalSharpBadLocus (n := n) (v ⁻¹' W) EO ∩ AO := by
    rw [full_sharp_bad_preimage_val O A F, full_sharp_bad_preimage_val O W E, ← preimage_inter]
    exact preimage_mono hBad
  obtain ⟨hFull, hSharp, hNC⟩ := retain_full_boundary_on_sharp_piece (X := XO)
    hEO hFOE hContainsO T hT.carrierTest hT.boundaryTest hT.sharp hT.normalCrossings
  exact ⟨centresOver_mono_local hFootSub T hFoot, hT.carrierTest, hFull, hSharp, hNC⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2500000 in
/-- The finitely many original containment patterns reduce arbitrary
containment to dense-complement cleanup on one common actual source open. -/
theorem exists_full_sharp_terminal_near_compact {n : ℕ} (hService : DenseSharpService.{0} n)
    {X : CMfd.{0} n} {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{0} n) (Q : BlowupTower (CMfd.of (n := n) O) Z),
      IsSharpTerminalTower ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) Q := by
  classical
  let ι := Fin (n + 1) × Finset (Fin E.length)
  let D : Fin (n + 1) → Set X := fun d => dimPiece W d.val
  let A : ι → Set X := fun P => patternPiece (D P.1) E P.2
  let F : ι → List (Set X) := fun P => remainingBoundary E P.2
  obtain ⟨hDgerm, hDreg, hD, hA, hCover, V, hAV, hSep⟩ := mixed_dimension_containment_patterns hW hE
  have hPattern (P : ι) := (actual_full_boundary_containment_patterns (hD P.1) hE (hDreg P.1)).2.2 P.2
  have hF (P : ι) : (F P).Sublist E := (hPattern P).2.2.2.2.2.1
  have hContains (P : ι) : ∀ H ∈ E, H ∉ F P → A P ⊆ H := (hPattern P).2.2.2.2.2.2.2.1
  have hDense (P : ι) : A P ⊆ closure (A P \ ⋃ H ∈ F P, H) := (hPattern P).2.2.2.2.2.2.2.2
  have hBad (P : ι) : originalSharpBadLocus (n := n) (A P) (F P) ⊆
      originalSharpBadLocus (n := n) W E ∩ A P := by
    obtain ⟨hAD, _, _, hGerm, _, _, _, _, _⟩ := hPattern P
    have hAW : A P ⊆ W := hAD.trans (dimPiece_subset W P.1.val)
    have hGermW (x : X) (hx : x ∈ A P) : ∀ᶠ y in 𝓝 x, y ∈ A P ↔ y ∈ W := by
      filter_upwards [hGerm x hx, hDgerm P.1 x (hAD hx)] with y hy hz
      exact hy.trans hz
    exact sharpBad_subset_full_of_carrier_germs hW.1 hE (hF P) hAW hGermW
  have hServiceP (P : ι) := hService (hA P) (F P) (isSNCDivisor_of_sublist hE (hF P)) (hDense P) K hK
  choose U hKU Y T hT using hServiceP
  let O : Opens X := ⟨⋂ P, (U P : Set X), isOpen_iInter_of_finite fun P => (U P).isOpen⟩
  have hKO : K ⊆ O := fun x hx => mem_iInter.mpr fun P => hKU P hx
  have hOU (P : ι) : O ≤ U P := fun _ hx => mem_iInter.mp hx P
  let XO := CMfd.of (n := n) O
  let v := (Subtype.val : O → X)
  let WO := v ⁻¹' W
  let EO := E.map (v ⁻¹' ·)
  let AO : ι → Set O := fun P => v ⁻¹' A P
  let VO : ι → Opens O := fun P => ⟨v ⁻¹' V P, (V P).isOpen.preimage continuous_subtype_val⟩
  have hWO : IsClosedSubmanifold n WO := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O
  have hEO : IsSNCDivisor n EO :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
  have hAO (P : ι) : IsClosedSubmanifold n (AO P) :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val (hA P) O
  have hCoverO : (⋃ P, AO P) = WO := by
    change (⋃ P, v ⁻¹' A P) = v ⁻¹' W
    rw [← preimage_iUnion, hCover]
  have hAVO (P : ι) : AO P ⊆ VO P := fun _ hx => hAV P hx
  have hSepO (P R : ι) (hPR : P ≠ R) : Disjoint (VO P : Set O) (AO R) :=
    disjoint_left.mpr fun _ hx hxR => disjoint_left.mp (hSep P R hPR) hx hxR
  have hPiece (P : ι) : ∃ (Z : CMfd.{0} n) (S : BlowupTower XO Z),
      CentresOver (originalSharpBadLocus (n := n) WO EO ∩ AO P) S ∧
        IsSharpTerminalTower (AO P) EO S := by
    obtain ⟨Z, S, hS⟩ := sharpTerminal_on_smaller_open (hA P) (F P) (U P) O (hOU P) (T P) (hT P)
    exact ⟨Z, S, full_piece_on_window (hA P) hE (hF P) (hContains P) (hBad P) O S hS⟩
  choose Z S hOver hEnd using hPiece
  obtain ⟨Y₀, Q, hC, hF, hSharp, _, _, _, hNC, _, _⟩ :=
    exists_full_sharp_cleanup_of_disjoint_pieces (X := XO) (W := WO) (E := EO) hWO hEO
      AO VO hAO hCoverO hAVO hSepO Z S hOver
      (fun P => (hEnd P).carrierTest) (fun P => (hEnd P).boundaryTest)
      (fun P => (hEnd P).sharp) (fun P => (hEnd P).normalCrossings)
  rw [N_geoTransformAlong] at hNC
  exact ⟨O, hKO, Y₀, Q, hC, hF, hSharp, hNC⟩

/-- A literal compact-enclosed open carries an actual finite sharp tower
with its full initial ordered boundary, exact permitted footprint and good isomorphism. -/
theorem exists_full_sharp_cleanup_on_compact_enclosed_open {n : ℕ} (hService : DenseSharpService.{0} n)
    {X : CMfd.{0} n} {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ (Z : CMfd.{0} n) (Q : BlowupTower (CMfd.of (n := n) U) Z),
      let WU := (Subtype.val : U → X) ⁻¹' W
      let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
      let BU := (Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E
      IsSharpTerminalTower WU EU Q ∧ CentresOver BU Q ∧ IsClosedSubmanifold n (strictAlong Q WU) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set U) EU) Q).E ∧
      IsProperMap Q.proj ∧ IsIsomorphismOver n Q.proj BUᶜ := by
  obtain ⟨O, hKO, Y, T, hT⟩ := exists_full_sharp_terminal_near_compact hService hW hE K hK
  obtain ⟨Z, Q, hQ⟩ := sharpTerminal_on_smaller_open hW E O U (hUK.trans hKO) T hT
  have hWU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U
  have hEU := isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hGeom := sharpTerminal_full_geometry hWU hEU Q hQ
  rw [full_sharp_bad_preimage_val U W E] at hGeom
  exact ⟨Z, Q, hQ, hGeom⟩

end
end Hironaka.HironakaG4FullBoundaryRelative
