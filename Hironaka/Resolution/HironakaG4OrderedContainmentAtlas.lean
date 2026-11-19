import Hironaka.Resolution.HironakaG4FullBoundaryRelative
import Hironaka.Resolution.HironakaG4OrderedPieceClass
import Hironaka.Resolution.HironakaG4OrderedPieceMergeConstruction
import Hironaka.Resolution.HironakaG4SharpTerminalAtlas

/-! The arbitrary-containment atlas from compatible dense-complement classes. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG4OrderedContainmentAtlas

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  HironakaG3RTowerClass G3UniversePhysicalClassComparisons MaxLocusLocal RestrictEmptyTower
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpNormalCrossingsOpenLocus
  HironakaActualFullBoundaryContainmentPatterns HironakaActualFullBoundaryMixedPatterns
  HironakaG4FullBoundaryCompactCleanup HironakaG4FullBoundaryRelative HironakaG4SharpTerminalAtlas
  HironakaG4OrderedPieceClass HironakaG4OrderedPieceMergeConstruction HironakaG4OrderedPieceMerge
  HironakaG3FiniteDisjointTowerMerge HironakaG34NonPureLowDim

/-- Dense-complement input consists of compatible terminal histories on
all prescribed compact-enclosed opens of the same ambient. -/
def DenseSharpAtlasService (n : ℕ) : Prop :=
  ∀ {X : CMfd.{0} n} {W : Set X}, IsClosedSubmanifold n W →
    ∀ (E : List (Set X)), IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E, H) →
    ∃ C : LocalTowerClass X, SharpTerminalClass W E C ∧ HasPhysicalComparisons C ∧
      ∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), C U Y T

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2700000 in
/-- Fixed original pattern order and the supplied compatible dense charts
produce a complete class with arbitrary initial boundary containment. -/
theorem exists_full_sharp_class_of_dense {n : ℕ} (hService : DenseSharpAtlasService n)
    {X : CMfd.{0} n} {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) :
    ∃ C : LocalTowerClass X, SharpTerminalClass W E C ∧ HasPhysicalComparisons C ∧
      ∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) U) Y), C U Y T := by
  classical
  let ι := Fin (n + 1) × Finset (Fin E.length)
  let D : Fin (n + 1) → Set X := fun d => dimPiece W d.val
  let A : ι → Set X := fun P => patternPiece (D P.1) E P.2
  let F : ι → List (Set X) := fun P => remainingBoundary E P.2
  let Bad := originalSharpBadLocus (n := n) W E
  let B : ι → Set X := fun P => Bad ∩ A P
  let order := (Finset.univ : Finset ι).toList
  obtain ⟨hDgerm, hDreg, hD, hA, hCover, V, hAV, hSep⟩ := mixed_dimension_containment_patterns hW hE
  have hPattern (P : ι) := (actual_full_boundary_containment_patterns (hD P.1) hE (hDreg P.1)).2.2 P.2
  have hF (P : ι) : (F P).Sublist E := (hPattern P).2.2.2.2.2.1
  have hContains (P : ι) : ∀ H ∈ E, H ∉ F P → A P ⊆ H := (hPattern P).2.2.2.2.2.2.2.1
  have hDense (P : ι) : A P ⊆ closure (A P \ ⋃ H ∈ F P, H) := (hPattern P).2.2.2.2.2.2.2.2
  have hBad (P : ι) : originalSharpBadLocus (n := n) (A P) (F P) ⊆ B P := by
    obtain ⟨hAD, _, _, hGerm, _, _, _, _, _⟩ := hPattern P
    have hAW : A P ⊆ W := hAD.trans (dimPiece_subset W P.1.val)
    have hGermW (x : X) (hx : x ∈ A P) : ∀ᶠ y in 𝓝 x, y ∈ A P ↔ y ∈ W := by
      filter_upwards [hGerm x hx, hDgerm P.1 x (hAD hx)] with y hy hz
      exact hy.trans hz
    exact sharpBad_subset_full_of_carrier_germs hW.1 hE (hF P) hAW hGermW
  have hSepB (P R : ι) (hPR : P ≠ R) : Disjoint (V P : Set X) (B R) :=
    (hSep P R hPR).mono_right inter_subset_right
  have hBV (P : ι) : B P ⊆ V P := inter_subset_right.trans (hAV P)
  have hPart (P : ι) := hService (hA P) (F P) (isSNCDivisor_of_sublist hE (hF P)) (hDense P)
  choose C hTerminal hCmp hLocal using hPart
  let K : LocalTowerClass X := fun U Y T =>
    orderedPieceClass B V C order U Y T ∧
      IsSharpTerminalTower ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) T
  have hAllCmp := orderedPieceClass_physical B V hBV C hCmp order
  refine ⟨K, fun _ _ _ h => h.2, ?_, ?_⟩
  · intro U₁ U₂ Y₁ Y₂ T₁ T₂ h₁ h₂
    exact hAllCmp U₁ U₂ Y₁ Y₂ T₁ T₂ h₁.1 h₂.1
  intro U L hL hUL
  let XU := CMfd.of (n := n) U
  let v := (Subtype.val : U → X)
  let WU := v ⁻¹' W
  let EU := E.map (v ⁻¹' ·)
  let AU : ι → Set U := fun P => v ⁻¹' A P
  let BU : ι → Set U := fun P => v ⁻¹' B P
  let VU : ι → Opens U := fun P => nestedOpens U (V P)
  have hWU : IsClosedSubmanifold n WU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U
  have hEU : IsSNCDivisor n EU :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hAU (P : ι) : IsClosedSubmanifold n (AU P) :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val (hA P) U
  have hBU (P : ι) : IsClosed (BU P) :=
    ((isClosed_originalSharpBadLocus hW.1 hE.1).inter (hA P).1).preimage continuous_subtype_val
  have hCoverU : (⋃ P, AU P) = WU := by
    change (⋃ P, v ⁻¹' A P) = v ⁻¹' W
    rw [← preimage_iUnion, hCover]
  have hAVU (P : ι) : AU P ⊆ VU P := fun _ hz => hAV P hz
  have hBVU (P : ι) : BU P ⊆ VU P := fun _ hz => hBV P hz
  have hSepU (P R : ι) (hPR : P ≠ R) : Disjoint (VU P : Set U) (AU R) :=
    disjoint_left.mpr fun _ hz hy => disjoint_left.mp (hSep P R hPR) hz hy
  have hSepBU (P R : ι) (hPR : P ≠ R) : Disjoint (VU P : Set U) (BU R) :=
    disjoint_left.mpr fun _ hz hy => disjoint_left.mp (hSepB P R hPR) hz hy
  choose Y T hMember using fun P => hLocal P U L hL hUL
  have hSupportEq : (fun P => originalSharpBadLocus (n := n) WU EU ∩ AU P) = BU := by
    funext P
    dsimp only [WU, EU]
    rw [full_sharp_bad_preimage_val U W E]
    rfl
  have hPiece (P : ι) : CentresOver (BU P) (T P) ∧ IsSharpTerminalTower (AU P) EU (T P) := by
    have h := full_piece_on_window (hA P) hE (hF P) (hContains P) (hBad P) U (T P)
      (hTerminal P U (Y P) (T P) (hMember P))
    change CentresOver ((fun P => originalSharpBadLocus (n := n) WU EU ∩ AU P) P) (T P) ∧ _ at h
    rwa [hSupportEq] at h
  have hOrder : order.reverse.Nodup := List.nodup_reverse.mpr (Finset.nodup_toList _)
  obtain ⟨Z, Q, hMerge, hPhysical⟩ :=
    exists_ordered_piece_merge (X := XU) BU hBU VU hBVU hSepBU Y T (fun P => (hPiece P).1) order.reverse hOrder
  have hSupport := orderedPieceMerge_centresOver hMerge
  have hSuppEq : (⋃ P ∈ order.reverse, BU P) = finiteSupport (X := XU) BU (Finset.univ : Finset ι) := by
    ext z
    simp [order, finiteSupport]
  rw [hSuppEq, ← hSupportEq] at hSupport
  obtain ⟨hC, hM, hSharp, _, _, _, hNC, _, _⟩ :=
    full_sharp_cleanup_of_piece_comparisons (X := XU) hWU hEU AU VU hAU hCoverU hAVU hSepU
      Y T (fun P => (hPiece P).2.carrierTest) (fun P => (hPiece P).2.boundaryTest)
      (fun P => (hPiece P).2.sharp) (fun P => (hPiece P).2.normalCrossings)
      Q hSupport (fun P => hPhysical P (by simp [order]))
  rw [N_geoTransformAlong] at hNC
  exact ⟨Z, Q, ⟨Y, T, hMember, hMerge⟩, hC, hM, hSharp, hNC⟩

/-- Compatible dense-complement chart classes give one proper full sharp
cleanup map with actual finite factorizations over the prescribed opens. -/
theorem exists_glued_full_sharp_cleanup_of_dense {n : ℕ} (hService : DenseSharpAtlasService n)
    {X : CMfd.{0} n} {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) :
    ∃ (C : LocalTowerClass X) (Z : CMfd.{0} n) (P : Z → X),
      IsGluedSharpCleanup C W E Z P ∧
      ∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ c : TowerChart C Z P, c.U = U := by
  obtain ⟨C, hTerm, hCmp, hLocal⟩ := exists_full_sharp_class_of_dense hService hW hE
  obtain ⟨Z, P, hP, hCharts⟩ := glue_compatible_sharp_terminal_histories hW hE hTerm hCmp hLocal
  exact ⟨C, Z, P, hP, hCharts⟩

end
end Hironaka.HironakaG4OrderedContainmentAtlas
