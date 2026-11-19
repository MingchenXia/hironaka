import Hironaka.Resolution.HironakaG4RetainedSelectedLowerLift
import Hironaka.Resolution.HironakaG4RetainedLowerCompactWindow
import Hironaka.Resolution.HironakaG4SharpTerminalAtlas
import Hironaka.Resolution.HironakaG34SurfaceSharpCleanup
import Hironaka.Resolution.HironakaG4OrderedRetainedDefectTrace
import Hironaka.Resolution.HironakaG8SpecialLoci
import Hironaka.Resolution.HironakaG4RetainedCurrentStamp

/-! One compact-relative retained row service from a full smaller-dimensional sharp cleanup. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaG4RetainedRelativeLowerService
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4OrderedRetainedDefectTrace HironakaG4PreparedCentreCoordinates
  HironakaG4RetainedPreparedLocalSupport HironakaG4RetainedSelectedLowerLift
  HironakaG4ResidualInductionInputs HironakaActualRetainedBornResidualSeed
  HironakaActualRetainedBornResidualOpen HironakaG4RetainedLowerCompactWindow
  HironakaG4SharpTerminalAtlas HironakaG34LowerTemplateBridge HironakaG34SurfaceSharpCleanup
  HironakaG4SharpBadFootprint HironakaG4CompactWholeMonomialMaskPhase
  NonmonomialOrderLocal HironakaG34NonPureLowDim RestrictEmptyTower
  AnalyticIrreducibleComponents RegularPointDimension HironakaG4RetainedCurrentStamp

/-- Full sharp cleanup on a neighbourhood of every compact enclosure,
for closed carriers of locally varying dimension bounded by `d`. -/
def CompactRelativeSharpCleanupsExist (n d : ℕ) : Prop :=
  ∀ (X : CMfd.{u} n) (W : Set X) (E : List (Set X)),
    IsClosedSubmanifold n W → IsSNCDivisor n E → W ⊆ closure (W \ ⋃ H ∈ E,H) →
    (∀ x ∈ W,∃ e ≤ d,RegularAtDim (n := n) W x e) →
    ∀ (K : Set X), IsCompact K →
      ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        let u := (Subtype.val : U → X)
        IsSharpTerminalTower (u ⁻¹' W) (E.map (u ⁻¹' ·)) T

variable {n : ℕ} {X : CMfd.{u} n}

/-- A bound on the local carrier dimensions persists through any actual
geometric test tower. Each surviving point retains the dimension at
its physical projection in the source. -/
theorem carrier_dim_bound_geoTransformAlong (M : MarkedIdeal n X) (hN : IsClosed M.N) (d : ℕ)
    (hDim : ∀ x ∈ M.N,∃ e ≤ d,RegularAtDim (n := n) M.N x e) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower M T →
      IsClosed (geoTransformAlong M T).N ∧
      ∀ y ∈ (geoTransformAlong M T).N,∃ e ≤ d,RegularAtDim (n := n) (geoTransformAlong M T).N y e
  | _, .refl, _ => ⟨hN,hDim⟩
  | _, .step T C π hπ, hT => by
    obtain ⟨hClosed,hBound⟩ := carrier_dim_bound_geoTransformAlong M hN d hDim T hT.1
    refine ⟨isClosed_closure,?_⟩
    intro y hy
    have hyN : π y ∈ (geoTransformAlong M T).N :=
      BlowupStrictSubmanifold.geoStrictTransform_subset_preimage (C := C)
        hπ.contMDiff.continuous hClosed hy
    obtain ⟨e,he,hreg⟩ := hBound (π y) hyN
    exact ⟨e,he,HironakaG8SpecialLoci.regularAtDim_geoStrictTransform_carrier hπ hClosed
      hT.2.subset_N hy hreg⟩

/-- Native lower geometry of a selected row after the true distinct
defect has been cleared. The lower carrier has local codimension one
inside the upper carrier. -/
theorem retained_selected_lower_geometry (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    (i : Fin old.length) :
    let L := N ∩ (oldResidualPart N old born i).zeroLocus
    let F := remainingBoundary old born i
    IsClosedSubmanifold n L ∧ IsSNCDivisor n F ∧ L ⊆ closure (L \ ⋃ H ∈ F,H) ∧
    ∀ x ∈ L,∃ e,RegularAtDim (n := n) N x (e+1) ∧ RegularAtDim (n := n) L x e := by
  intro L F
  obtain ⟨hOrd,hDistinct⟩ := retained_row_conditions_of_empty_distinct_defect hn g.carrier g.full
    g.born_transverse g.dense hEmpty
  obtain ⟨hL,_hOwn,hPoint⟩ :=
    actual_residual_support_local_geometry hn g.carrier g.full g.born_transverse g.dense hOrd i
  have hLD := residual_support_dense_off_remainingBoundary_of_local_dimension
    hn g.carrier g.full g.born_transverse g.dense hOrd hDistinct i
  have hF : IsSNCDivisor n F := isSNCDivisor_of_sublist g.full
    ((List.eraseIdx_sublist old i.val).append (List.Sublist.refl born))
  exact ⟨hL,hF,hLD,fun x hx => (hPoint x hx).2.2⟩

/-- The literal lower record on an original open is the pullback of the
selected carrier and remaining ordered boundary. -/
theorem retained_selected_lower_tuple_open (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (i : Fin old.length) (U : Opens X) :
    let XU := CMfd.of (n := n) U
    let u := (Subtype.val : U → X)
    let NU := u ⁻¹' N
    let OU := old.map (u ⁻¹' ·)
    let BU := born.map (u ⁻¹' ·)
    let j : Fin OU.length := Fin.cast (List.length_map _).symm i
    NU ∩ (oldResidualPart (X := XU) NU OU BU j).zeroLocus =
        u ⁻¹' (N ∩ (oldResidualPart N old born i).zeroLocus) ∧
    remainingBoundary (X := XU) OU BU j = (remainingBoundary old born i).map (u ⁻¹' ·) := by
  intro XU u NU OU BU j
  let M := retainedResidualMarked N old born i
  let MU := retainedResidualMarked (X := XU) NU OU BU j
  have hM : MarkedIdeal.pullback u M = MU :=
    retainedResidualMarked_pullback_open hn g.carrier g.full g.born_transverse g.dense U i
  have hSeed := (retainedResidualMarked_geometry hn g.carrier g.full g.born_transverse g.dense i).1
  refine ⟨?_,?_⟩
  · change NU ∩ MU.ideal.zeroLocus = u ⁻¹' (N ∩ M.ideal.zeroLocus)
    rw [←hM]
    exact congrArg (fun A => NU ∩ A)
      (BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val hSeed.isCoherent)
  · change OU.eraseIdx i.val ++ BU = (old.eraseIdx i.val ++ born).map (u ⁻¹' ·)
    rw [List.map_append,List.eraseIdx_map]

set_option maxHeartbeats 500000 in
/-- Full sharp terminal data for the native lower record prepare the
selected upper row on the same actual tower. The lower test and original
sharp support are returned for protected continuations. -/
theorem actual_retained_selected_row_of_lower_terminal (hn : 0 < n)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    (i : Fin old.length) (P : Finset (Fin old.length))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    let L := N ∩ (oldResidualPart N old born i).zeroLocus
    let F := remainingBoundary old born i
    let D := originalSharpBadLocus (n := n) L F
    IsSharpTerminalTower L F T →
    (∀ j ∈ P,RetainedRowPrepared N old born j (.refl : BlowupTower X X) ∧
      Disjoint D (retainedRowSupport N old born j (.refl : BlowupTower X X))) →
    IsGeoTestTower (geometricTemplate N born) T ∧
    IsGeoTestTower (geometricTemplate (univ : Set X) (old ++ born)) T ∧
    CurrentSharpCentres N (old ++ born) T ∧
    IsGeoTestTower (geometricTemplate L F) T ∧ CentresOver D T ∧
    RetainedRowPrepared N old born i T ∧ retainedRowSupport N old born i T = strictAlong T L ∧
    (∀ j ∈ P,RetainedRowPrepared N old born j T ∧
      retainedRowSupport N old born j T = T.proj ⁻¹' retainedRowSupport N old born j (.refl : BlowupTower X X)) := by
  intro L F D hTerminal hProtected
  obtain ⟨hL,hF,hDenseL,_hPoint⟩ := retained_selected_lower_geometry hn g hEmpty i
  obtain ⟨hOrder,_hDistinct⟩ := retained_row_conditions_of_empty_distinct_defect hn g.carrier
    g.full g.born_transverse g.dense hEmpty
  have hLow := lowerTemplate_test_of_two_tests L F T hTerminal.carrierTest hTerminal.boundaryTest
  have hOver := (currentSharpCentres_original_footprint hL.1 hF.1 T hTerminal.sharp).2
  have hDensity := (lower_dense_of_two_tests hn hL hF hDenseL T
    hTerminal.carrierTest hTerminal.boundaryTest).2
  have hNC : HasNormalCrossings n (geoTransformAlong (geometricTemplate L []) T).N
      (geoTransformAlong (geometricTemplate (univ : Set X) F) T).E := by
    rw [N_geoTransformAlong]
    exact hTerminal.normalCrossings
  obtain ⟨hNCL,hDL⟩ := lower_nc_dense_of_two_template L F T hNC hDensity
  obtain ⟨hTest,hFull,hSharp,hPrep,hSupport,hPrepP⟩ :=
    actual_retained_prepared_row_of_lower_sharp_cleanup hn g.carrier g.full
      g.born_transverse g.dense hOrder i P T hLow hTerminal.sharp hOver hNCL hDL hProtected
  exact ⟨hTest,hFull,hSharp,hLow,hOver,hPrep,hSupport,hPrepP⟩

set_option maxHeartbeats 900000 in
/-- A full smaller-dimensional sharp cleanup supplies a genuine selected
retained-row service near a compact enclosure. A disjoint prepared support
retains its same pullback support on that actual upper step. -/
theorem exists_retained_selected_row_service_near_compact (hn : 0 < n) (d : ℕ)
    (hLower : CompactRelativeSharpCleanupsExist.{u} n d)
    {N : Set X} {old born : List (Set X)} (g : NativeRetainedGeometry N old born)
    (hDim : ∀ x ∈ N,∃ e ≤ d+1,RegularAtDim (n := n) N x e)
    (hEmpty : actualFamilyDistinctDefect N (oldResidualPart N old born) = ∅)
    (i : Fin old.length) (P : Finset (Fin old.length))
    (hP : ∀ j ∈ P,RetainedRowPrepared N old born j (.refl : BlowupTower X X))
    {K : Set X} (hK : IsCompact K) :
    let L := N ∩ (oldResidualPart N old born i).zeroLocus
    let F := remainingBoundary old born i
    let D := originalSharpBadLocus (n := n) L F
    (∀ j ∈ P,Disjoint D (retainedRowSupport N old born j (.refl : BlowupTower X X))) →
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
      let u := (Subtype.val : U → X)
      let NU := u ⁻¹' N
      let OU := old.map (u ⁻¹' ·)
      let BU := born.map (u ⁻¹' ·)
      let e : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
      IsGeoTestTower (geometricTemplate NU BU) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set U) (OU ++ BU)) T ∧
      CurrentSharpCentres NU (OU ++ BU) T ∧ CentresOver (u ⁻¹' D) T ∧
      RetainedRowPrepared NU OU BU (e i) T ∧
      retainedRowSupport NU OU BU (e i) T = strictAlong T (u ⁻¹' L) ∧
      ∀ j ∈ P,RetainedRowPrepared NU OU BU (e j) T ∧
        retainedRowSupport NU OU BU (e j) T =
          (u ∘ T.proj) ⁻¹' retainedRowSupport N old born j (.refl : BlowupTower X X) := by
  intro L F D hSep
  obtain ⟨hL,hF,hLD,hPoint⟩ := retained_selected_lower_geometry hn g hEmpty i
  have hDimL : ∀ x ∈ L,∃ e ≤ d,RegularAtDim (n := n) L x e := by
    intro x hx
    obtain ⟨e,hNe,hLe⟩ := hPoint x hx
    obtain ⟨f,hf,hNf⟩ := hDim x hx.1
    have he : e+1=f := eq_of_regularAtDim hNe hNf
    exact ⟨e,by omega,hLe⟩
  obtain ⟨U,hKU,Y,T,hTerminal⟩ := hLower X L F hL hF hLD hDimL K hK
  let XU := CMfd.of (n := n) U
  let u := (Subtype.val : U → X)
  let NU := u ⁻¹' N
  let OU := old.map (u ⁻¹' ·)
  let BU := born.map (u ⁻¹' ·)
  let e : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
  let j := e i
  let LU := NU ∩ (oldResidualPart (X := XU) NU OU BU j).zeroLocus
  let FU := remainingBoundary (X := XU) OU BU j
  let Q := P.map e.toEmbedding
  have hGU : NativeRetainedGeometry (X := XU) NU OU BU := g.restrict U
  obtain ⟨hLU,hFU⟩ := retained_selected_lower_tuple_open hn g i U
  change LU = u ⁻¹' L at hLU
  change FU = F.map (u ⁻¹' ·) at hFU
  have hDV : originalSharpBadLocus (n := n) LU FU = u ⁻¹' D := by
    rw [hLU,hFU,full_sharp_bad_preimage_val]
  change IsSharpTerminalTower (u ⁻¹' L) (F.map (u ⁻¹' ·)) T at hTerminal
  rw [←hLU,←hFU] at hTerminal
  have hEmptyU : actualFamilyDistinctDefect NU (oldResidualPart (X := XU) NU OU BU) = ∅ := by
    rw [(actual_retained_defect_and_rank_open hn g.carrier g.full g.born_transverse g.dense U).1,
      hEmpty,Set.preimage_empty]
  have hProtected : ∀ k ∈ Q,RetainedRowPrepared NU OU BU k (.refl : BlowupTower XU XU) ∧
      Disjoint (originalSharpBadLocus (n := n) LU FU) (retainedRowSupport (X := XU) NU OU BU k .refl) := by
    intro k hk
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hk
    obtain ⟨hPrepU,hSuppU⟩ := retained_prepared_row_restrict_open hn g.carrier g.full
      g.born_transverse g.dense l (hP l hl) U
    refine ⟨hPrepU,?_⟩
    change retainedRowSupport (X := XU) NU OU BU (e l) .refl =
      u ⁻¹' retainedRowSupport N old born l .refl at hSuppU
    change Disjoint (originalSharpBadLocus (n := n) LU FU)
      (retainedRowSupport (X := XU) NU OU BU (e l) .refl)
    rw [hDV,hSuppU]
    exact (hSep l hl).preimage u
  obtain ⟨hTest,hFull,hSharp,_hLow,hOver,hPrep,hSupport,hPrepP⟩ :=
    actual_retained_selected_row_of_lower_terminal (X := XU) hn hGU hEmptyU j Q T hTerminal hProtected
  rw [hDV] at hOver
  change retainedRowSupport NU OU BU j T = strictAlong T LU at hSupport
  rw [hLU] at hSupport
  refine ⟨U,hKU,Y,T,hTest,hFull,hSharp,hOver,hPrep,hSupport,?_⟩
  intro l hl
  obtain ⟨hPL,hSL⟩ := hPrepP (e l) (Finset.mem_map.mpr ⟨l,hl,rfl⟩)
  have hU := (retained_prepared_row_restrict_open hn g.carrier g.full
    g.born_transverse g.dense l (hP l hl) U).2
  exact ⟨hPL,hSL.trans (congrArg (fun A : Set U => T.proj ⁻¹' A) hU)⟩

end
end Hironaka.HironakaG4RetainedRelativeLowerService
