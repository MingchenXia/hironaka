import Hironaka.Resolution.HironakaG8LocalPureEmbeddedResolution
import Hironaka.Resolution.HironakaG3BoundaryRestrictInitialList

/-! Literal restriction of the full embedded endpoint, including a finite
actual history on a prescribed compact-enclosed source open. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8DenseBoundaryRestriction

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings NormalCrossingsInvariance
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaEmbeddedBoundary
  HironakaAdmissibleSequence HironakaAdmissibleCalculus MarkedIdealTowerTransport MaxLocusLocal
  HironakaG8UniverseBMTransport HironakaG8UniverseDenseBoundary HironakaG8LocalPureFinish
  HironakaG8LocalPureEmbeddedResolution HironakaActualSmoothBoundaryCleanup
  HironakaG3BoundaryRestrictInitialList HironakaG3CentresOverGenericFactor
  HironakaCoherentTransformExtension HironakaSharpActualFiniteChronologicalHistory
  HironakaMixedDimensionalBoundaryFiniteResolution HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaResolutionSpaceLocal

/-- Every literal restricted centre still has either of the full two
centre positions, with the whole restricted chronological boundary. -/
theorem bm_stages_restrict {n : ℕ} {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) (O : Opens X) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), BMStages W E T →
      BMStages ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) (restrict O T)
  | _, .refl, _ => trivial
  | _, @BlowupTower.step _ _ Y Z T C π hπ, h => by
    let G := geometricTemplate (univ : Set X) E
    let GO := geometricTemplate (univ : Set (CMfd.of (n := n) O)) (E.map ((Subtype.val : O → X) ⁻¹' ·))
    let q : openPreimage T O → _ := Subtype.val
    refine ⟨bm_stages_restrict W E O T h.1, ?_⟩
    change BMPosition (strictTransform n (restrict O T).proj ((Subtype.val : O → X) ⁻¹' W))
      (geoTransformAlong GO (restrict O T)).E (q ⁻¹' C)
    rw [strictTransform_restricted_tower O T W, boundary_restrict_of_initial_eq G O GO rfl T]
    apply bm_position_of_preimage (X := Y) (Y := CMfd.of (n := n) (openPreimage T O)) q h.2
    · exact singularSet_preimage_val (openPreimage T O)
    · exact fun hA => BlowupRestrictOpen.isClosedSubmanifold_preimage_val hA _
    · exact hasNormalCrossings_preimage (pullsBackCoordinates_val (openPreimage T O)) h.2.2

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2500000 in
/-- The same finite tower restricted to any source open gives the full
embedded endpoint for the literal traces of the carrier and boundary. -/
theorem dense_boundary_resolution_restrict {n : ℕ} {X Y : CMfd.{0} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (T : BlowupTower X Y)
    (h : DenseBoundaryResolution W E T) (O : Opens X) :
    DenseBoundaryResolution ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·))
      (restrict O T) := by
  obtain ⟨hAdm, hStages, hSmooth, hSNC, hNC, _, _, _, _, _, _, _, _⟩ := h
  let R := restrict O T
  let W₀ := (Subtype.val : O → X) ⁻¹' W
  let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let M := actualSmoothBoundaryMarked W E
  let M₀ := actualSmoothBoundaryMarked (X := CMfd.of (n := n) O) W₀ E₀
  let G := geometricTemplate (univ : Set (CMfd.of (n := n) O)) E₀
  let F := singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H)
  let F₀ := singularSet (n := n) W₀ ∪ (W₀ ∩ ⋃ H ∈ E₀, H)
  let q : openPreimage T O → Y := Subtype.val
  have hF₀ : F₀ = (Subtype.val : O → X) ⁻¹' F := by
    dsimp only [F₀, F, W₀, E₀]
    rw [singularSet_preimage_val, ← preimage_biUnion_list, preimage_union, preimage_inter]
  have hOver : CentresOver F T := by
    apply centresOver_of_exceptionalDivisor_support_subset F T
    rw [HironakaPrincipalizationBoundary.support_exceptionalDivisor_eq_biUnion_drop M hE.1 T]
    exact (IsAdmissibleBlowupSequence.exceptionalLocus_subset_drop hAdm).2
  have hStages₀ : BMStages W₀ E₀ R := bm_stages_restrict W E O T hStages
  have hAdm₀ : IsAdmissibleBlowupSequence n (CMfd.of (n := n) O) E₀ F₀
      (CMfd.of (n := n) (openPreimage T O)) R.proj (geoTransformAlong M₀ R).E := by
    have h := isAdmissibleBlowupSequence_proj G F₀ R (bm_stage_test W₀ E₀ R hStages₀)
      (hF₀.symm ▸ centresOver_restrict O F T hOver)
    rw [geoTransformAlong_E_eq_of_E_eq (𝔍 := G) (𝔪 := M₀) rfl R] at h
    exact h
  have hStrict : strictTransform n R.proj W₀ = q ⁻¹' strictTransform n T.proj W :=
    strictTransform_restricted_tower O T W
  have hBoundary : (geoTransformAlong M₀ R).E = (geoTransformAlong M T).E.map (q ⁻¹' ·) :=
    boundary_restrict_of_initial_eq M O M₀ rfl T
  have hSmooth₀ : IsClosedSubmanifold n (strictTransform n R.proj W₀) := hStrict.symm ▸
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hSmooth (openPreimage T O)
  have hSNC₀ : IsSNCDivisor n (geoTransformAlong M₀ R).E := hBoundary.symm ▸
    isSNCDivisor_map_preimage (pullsBackCoordinates_val (openPreimage T O)) continuous_subtype_val hSNC
  have hNC₀ : HasNormalCrossings n (strictTransform n R.proj W₀) (geoTransformAlong M₀ R).E := by
    rw [hStrict, hBoundary]
    exact hasNormalCrossings_preimage (pullsBackCoordinates_val (openPreimage T O)) hNC
  have hW₀ : IsComplexAnalyticSubset (n := n) W₀ := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O
  have hE₀ : IsSNCDivisor n E₀ :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
  have hDense₀ : W₀ ⊆ closure (W₀ \ ⋃ H ∈ E₀, H) := dense_complement_restrict W E hDense O
  exact dense_boundary_resolution_of_final_normalCrossings (X := CMfd.of (n := n) O)
    (Y := CMfd.of (n := n) (openPreimage T O)) (W := W₀) hW₀ E₀ hE₀ hDense₀ R
    hStages₀ hAdm₀ hSmooth₀ hSNC₀ hNC₀


/-- A resolution on an ambient open restricts to the finer literal open
with its full history and terminal geometry. -/
theorem dense_boundary_resolution_on_smaller_open {n : ℕ} {X Y : CMfd.{0} n} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (O U : Opens X) (hUO : U ≤ O)
    (T : BlowupTower (CMfd.of (n := n) O) Y)
    (hT : DenseBoundaryResolution ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) T) :
    ∃ (Z : CMfd.{0} n) (R : BlowupTower (CMfd.of (n := n) U) Z),
      DenseBoundaryResolution ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) R := by
  let V := nestedOpens O U
  let e := (nestedOpensDiffeo (n := n) hUO).symm
  let R := transport e (restrict V T)
  let WO := (Subtype.val : O → X) ⁻¹' W
  let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
  have hWO := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O
  have hEO := isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
  have hDenseO := dense_complement_restrict W E hDense O
  have hV := dense_boundary_resolution_restrict hWO EO hEO hDenseO T hT V
  have hWV := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hWO V
  let EV := EO.map ((Subtype.val : V → O) ⁻¹' ·)
  have hEV := isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hEO
  have hRoot := dense_boundary_resolution_rebase e hWV EV hEV
    (dense_complement_restrict WO EO hDenseO V) (restrict V T) hV
  have hList : EV.map (e ⁻¹' ·) = E.map ((Subtype.val : U → X) ⁻¹' ·) := by
    dsimp only [EV, EO]
    rw [List.map_map, List.map_map]
    rfl
  rw [hList] at hRoot
  exact ⟨R.target, R.tower, hRoot⟩


set_option maxHeartbeats 1000000 in
/-- For any prescribed open enclosed by a compact subset, the actual
finite pure embedded resolution lives on that very open. -/
theorem exists_pure_embedded_resolution_on_compact_enclosed_open
    {m d : ℕ} {X : CMfd.{0} (m + 1)} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (hPure : W ⊆ closure (regularLocus (n := m + 1) W d)) (hd : d < m + 1)
    (E : List (Set X)) (hE : IsSNCDivisor (m + 1) E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ (Z : CMfd.{0} (m + 1)) (T : BlowupTower (CMfd.of (n := m + 1) U) Z),
      DenseBoundaryResolution ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) T := by
  obtain ⟨O, hKO, Y, T, hT⟩ := exists_local_pure_embedded_resolution_of_dense_boundary_complement
    hW hPure hd E hE hDense K hK
  exact dense_boundary_resolution_on_smaller_open hW E hE hDense O U (hUK.trans hKO) T hT

end
end Hironaka.HironakaG8DenseBoundaryRestriction
