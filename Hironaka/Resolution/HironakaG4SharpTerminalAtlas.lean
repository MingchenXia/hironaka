import Hironaka.Resolution.HironakaG3GluedClassFootprint
import Hironaka.Resolution.HironakaG3RPureBoundary
import Hironaka.Resolution.HironakaG3UniversePhysicalClassComparisons
import Hironaka.Resolution.HironakaG3EmptyAwareFullBoundary
import Hironaka.Resolution.HironakaG3OriginalOverlapBoundaryLists
import Hironaka.Resolution.HironakaActualSmoothBoundaryCleanup
import Hironaka.Resolution.HironakaBoundaryContainedSharpBad
import Hironaka.Resolution.HironakaG4SharpBadFootprint
import Hironaka.Resolution.HironakaG34NonPureLowDim

/-!
# The G4 sharp terminal atlas from compatible finite local histories

The terminal map retains the actual chart towers, the original sharp
footprint, and the full transformed chart boundaries on physical overlaps.

Blueprint: `hironaka-g4-sharp-terminal-atlas.tex`.
-/

set_option autoImplicit false

open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4SharpTerminalAtlas

noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  HomogenizedGlueingTower NormalCrossings NormalCrossingsInvariance NormalCrossingsComparison
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  RestrictEmptyTower HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3GluedClassFootprint
  G3UniversePhysicalClassComparisons HironakaG3EmptyAwareHistory
  HironakaG3EmptyAwareFullBoundary HironakaG34NonPureLowDim
  HironakaG3OriginalOverlapBoundaryLists HironakaOriginalTerminalOverlapComparison MaxLocusLocal
  HironakaSharpActualFiniteChronologicalHistory HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpOriginalAllBoundaryCentre
  HironakaBoundaryContainedSharpBad HironakaG4SharpBadFootprint HironakaActualSmoothBoundaryCleanup
  HironakaEmbeddedAnalytic SimultaneousNormalCrossings

variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem ambient_template_wellFormed {E : List (Set X)} (hE : IsSNCDivisor n E) :
    (geometricTemplate (univ : Set X) E).IsWellFormed :=
  ⟨isClosedSubmanifold_univ, IdealWeightPowers.isCoherent_unitIdeal, hE,
    isTransverse_univ_of_isSNCDivisor hE⟩

private theorem carrier_template_wellFormed {W : Set X} (hW : IsClosedSubmanifold n W) :
    (geometricTemplate W []).IsWellFormed :=
  ⟨hW, IdealWeightPowers.isCoherent_unitIdeal, isSNCDivisor_nil,
    isTransverse_nil_of_isClosedSubmanifold hW⟩

/-- The full original ambient test, the carrier test, current sharp centres
and the normal crossings endpoint on one actual finite tower. -/
structure IsSharpTerminalTower (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) : Prop where
  carrierTest : IsGeoTestTower (geometricTemplate W []) T
  boundaryTest : IsGeoTestTower (geometricTemplate (univ : Set X) E) T
  sharp : CurrentSharpCentres W E T
  normalCrossings : HasNormalCrossings n (strictAlong T W)
    (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E

/-- Every member of the proposed local class carries the actual full
sharp terminal contract for the pullback of the original data. -/
def SharpTerminalClass (W : Set X) (E : List (Set X)) (K : LocalTowerClass X) : Prop :=
  ∀ (U : Opens X) (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K U Y T →
    IsSharpTerminalTower ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) T

/-- Restriction to an actual open pulls back the original full sharp bad locus. -/
theorem full_sharp_bad_preimage_val (U : Opens X) (W : Set X) (E : List (Set X)) :
    originalSharpBadLocus (n := n) ((Subtype.val : U → X) ⁻¹' W)
      (E.map ((Subtype.val : U → X) ⁻¹' ·)) =
        (Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E := by
  ext z
  exact and_congr Iff.rfl (not_congr normalCrossingsAt_preimage_val_iff)

/-- The original full good locus is relatively dense in any closed smooth
carrier, including carriers contained in original boundary members. -/
theorem carrier_subset_closure_full_good {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) :
    W ⊆ closure (W ∩ (originalSharpBadLocus (n := n) W E)ᶜ) := by
  intro x hx
  by_contra hBad
  let B := originalSharpBadLocus (n := n) W E
  let O := (closure (W ∩ Bᶜ))ᶜ
  have hO : IsOpen O := isClosed_closure.isOpen_compl
  have hSub : O ∩ W ⊆ B := by
    rintro z ⟨hz, hzW⟩
    by_contra hzB
    exact hz (subset_closure ⟨hzW, hzB⟩)
  have hEmpty := (original_sharp_bad_analytic_and_thin hW hE).2 O hO hSub
  have h : x ∈ O ∩ W := ⟨hBad, hx⟩
  rwa [hEmpty] at h

/-- Current sharp centres cannot erase any relatively open carrier piece.
The actual iterated strict transform agrees with the strict transform of
the terminal projection. -/
theorem sharp_strictAlong_eq_strictTransform {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hSharp : CurrentSharpCentres W E T) :
    strictAlong T W = strictTransform n T.proj W := by
  let B := originalSharpBadLocus (n := n) W E
  let O : Opens X := ⟨Bᶜ, (isClosed_originalSharpBadLocus hW.1 hE.1).isOpen_compl⟩
  have hOver := (currentSharpCentres_original_footprint hW.1 hE.1 T hSharp).2
  exact strictAlong_eq_library_of_avoid W hW.1 O (carrier_subset_closure_full_good hW hE) T
    (centresAvoid_of_centresOver O disjoint_compl_left T hOver)

/-- The actual current-sharp record yields the original full bad footprint
on every chart. -/
theorem class_centresOver_full_bad {W : Set X} {E : List (Set X)} {K : LocalTowerClass X}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hK : SharpTerminalClass W E K)
    (U : Opens X) (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y) (hT : K U Y T) :
    CentresOver ((Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E) T := by
  have hw := hW.1.preimage (continuous_subtype_val : Continuous (Subtype.val : U → X))
  have hE' := (IsWellFormed.pullback_val (ambient_template_wellFormed hE) U).isSNCDivisor
  rw [← full_sharp_bad_preimage_val U W E]
  exact (currentSharpCentres_original_footprint hw hE'.1 T (hK U Y T hT).sharp).2

/-- The full ordered boundary carried by an actual chart of the sharp atlas. -/
def fullChartBoundary {K : LocalTowerClass X} {P : Z → X}
    (c : TowerChart K Z P) (E : List (Set X)) : List (Set Z) :=
  chartBoundary c (geometricTemplate (univ : Set X) E)

theorem full_chart_geometry {W : Set X} {E : List (Set X)} {K : LocalTowerClass X}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hK : SharpTerminalClass W E K) {P : Z → X} (hP : IsGluedFrom K Z P)
    (c : TowerChart K Z P) :
    IsClosedSubmanifold n (chartIncl c ⁻¹' strictTransform n P W) ∧
    IsSNCDivisor n ((fullChartBoundary c E).map ((Subtype.val : c.V → Z) ⁻¹' ·)) ∧
    HasNormalCrossings n ((Subtype.val : c.V → Z) ⁻¹' strictTransform n P W)
      ((fullChartBoundary c E).map ((Subtype.val : c.V → Z) ⁻¹' ·)) := by
  let N := (Subtype.val : c.U → X) ⁻¹' W
  let F := E.map ((Subtype.val : c.U → X) ⁻¹' ·)
  let M := geometricTemplate (univ : Set X) E
  let MU := MarkedIdeal.pullback (Subtype.val : c.U → X) M
  have hN : IsClosedSubmanifold n N := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW c.U
  have hMU := IsWellFormed.pullback_val (ambient_template_wellFormed hE) c.U
  have hF : IsSNCDivisor n F := hMU.isSNCDivisor
  have hT : IsSharpTerminalTower N F c.T := hK c.U c.Y c.T c.mem
  have hStrict : strictAlong c.T N = chartIncl c ⁻¹' strictTransform n P W :=
    (sharp_strictAlong_eq_strictTransform hN hF c.T hT.sharp).trans (strictTransform_chart c hP.1 W)
  have hMUEq : MU = geometricTemplate (X := CMfd.of (n := n) c.U) (univ : Set c.U) F := by
    change MarkedIdeal.pullback (Subtype.val : c.U → X) (geometricTemplate (univ : Set X) E) = _
    rw [template_pullback (Y := CMfd.of (n := n) c.U), preimage_univ]
  have hMUtest : IsGeoTestTower MU c.T := hMUEq.symm ▸ hT.boundaryTest
  have hBdry := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hMU c.T hMUtest).isSNCDivisor
  have hMap : (fullChartBoundary c E).map ((Subtype.val : c.V → Z) ⁻¹' ·) =
      (geoTransformAlong MU c.T).E.map (c.φ.symm ⁻¹' ·) := chartBoundary_map_val c M
  have hPre : (Subtype.val : c.V → Z) ⁻¹' strictTransform n P W =
      c.φ.symm ⁻¹' strictAlong c.T N := by
    rw [hStrict]
    ext v
    change (v : Z) ∈ strictTransform n P W ↔ chartIncl c (c.φ.symm v) ∈ strictTransform n P W
    rw [chartIncl_symm]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hStrict]
    have hSmooth := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (carrier_template_wellFormed hN) c.T hT.carrierTest).isClosedSubmanifold_N
    rw [N_geoTransformAlong] at hSmooth
    exact hSmooth
  · rw [hMap]
    exact (MarkedIdealTowerTransport.isSNCDivisor_map_preimage_iff c.φ.symm).mpr hBdry
  · rw [hMap, hPre, hMUEq]
    exact (MarkedIdealTowerTransport.hasNormalCrossings_preimage_iff c.φ.symm).mpr hT.normalCrossings

/-- Glue compatible finite sharp terminal histories to one proper holomorphic
map with its strict carrier, full chart geometry and original good locus. -/
theorem exists_glued_sharp_terminal_geometry {W : Set X} {E : List (Set X)} {K : LocalTowerClass X}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hTerm : SharpTerminalClass W E K) (hCover : Covers K) (hCmp : HasPhysicalComparisons K) :
    ∃ (Z : CMfd.{u} n) (P : Z → X),
      IsGluedFrom K Z P ∧
      IsIsomorphismOver n P (originalSharpBadLocus (n := n) W E)ᶜ ∧
      P '' strictTransform n P W = W ∧ IsClosedSubmanifold n (strictTransform n P W) ∧
      ∀ c : TowerChart K Z P,
        IsSNCDivisor n ((fullChartBoundary c E).map ((Subtype.val : c.V → Z) ⁻¹' ·)) ∧
        HasNormalCrossings n ((Subtype.val : c.V → Z) ⁻¹' strictTransform n P W)
          ((fullChartBoundary c E).map ((Subtype.val : c.V → Z) ⁻¹' ·)) := by
  let B := originalSharpBadLocus (n := n) W E
  have hB : IsClosed B := isClosed_originalSharpBadLocus hW.1 hE.1
  obtain ⟨Z, P, hP⟩ := exists_isGluedFrom hCover (physical_comparisons_to_comparisons hCmp)
  have hOver := class_centresOver_full_bad hW hE hTerm
  have hExc := glued_exceptional_subset B hB hOver hP
  have hIso := glued_isomorphism_over_compl B hB hOver hP
  refine ⟨Z, P, hP, hIso, ?_, ⟨isClosed_closure, ?_⟩,
    fun c => (full_chart_geometry hW hE hTerm hP c).2⟩
  · apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      exact HironakaAdmissibleCalculus.strictTransform_subset_preimage hP.1.continuous hW.1 hz
    · apply (carrier_subset_closure_full_good hW hE).trans
      apply closure_minimal _ (hP.2.1.isClosedMap _ isClosed_closure)
      rintro x ⟨hxW, hxB⟩
      obtain ⟨z, rfl⟩ := hP.2.2.1 x
      exact ⟨z, subset_closure ⟨hxW, fun hz => hxB (hExc hz)⟩, rfl⟩
  · intro z hz
    obtain ⟨c, hc⟩ := hP.2.2.2 (P z)
    have hzV : z ∈ c.V := c.mem_V hc
    let y := c.φ.symm ⟨z, hzV⟩
    have heq : chartIncl c y = z := chartIncl_symm c ⟨z, hzV⟩
    have hy : y ∈ chartIncl c ⁻¹' strictTransform n P W := by
      change chartIncl c y ∈ strictTransform n P W
      rwa [heq]
    obtain ⟨d, hd⟩ := (full_chart_geometry hW hE hTerm hP c).1.2 y hy
    exact ⟨d, heq ▸ regularAtDim_of_chart c hd⟩


/-- The actual full transformed boundary lists agree on overlaps, preserving
the order of all nonempty original and chronologically born slots. -/
theorem full_chart_boundary_overlap {W : Set X} {E : List (Set X)} {K : LocalTowerClass X}
    (hE : IsSNCDivisor n E) (hTerm : SharpTerminalClass W E K) (hCmp : HasPhysicalComparisons K)
    {P : Z → X} (c₁ c₂ : TowerChart K Z P) :
    ((fullChartBoundary c₁ E).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter
        (fun H => decide H.Nonempty) =
      ((fullChartBoundary c₂ E).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter
        (fun H => decide H.Nonempty) := by
  let O := c₁.U ⊓ c₂.U
  let M := geometricTemplate (univ : Set X) E
  let MU (c : TowerChart K Z P) := MarkedIdeal.pullback (Subtype.val : c.U → X) M
  let MR (c : TowerChart K Z P) :=
    MarkedIdeal.pullback (Subtype.val : nestedOpens c.U O → c.U) (MU c)
  let R (c : TowerChart K Z P) := restrict (nestedOpens c.U O) c.T
  let incl (c : TowerChart K Z P) :
      openPreimage c.T (nestedOpens c.U O) → Z := chartIncl c ∘ Subtype.val
  have hM := ambient_template_wellFormed hE
  have hMU (c : TowerChart K Z P) : (MU c).IsWellFormed := IsWellFormed.pullback_val hM c.U
  have hT (c : TowerChart K Z P) : IsGeoTestTower (MU c) c.T := by
    change IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : c.U → X)
      (geometricTemplate (univ : Set X) E)) c.T
    rw [template_pullback (Y := CMfd.of (n := n) c.U), preimage_univ]
    exact (hTerm c.U c.Y c.T c.mem).boundaryTest
  have hRestr (c : TowerChart K Z P) : (geoTransformAlong (MR c) (R c)).E =
      (geoTransformAlong (MU c) c.T).E.map
        ((Subtype.val : openPreimage c.T (nestedOpens c.U O) → c.Y) ⁻¹' ·) :=
    congrArg MarkedIdeal.E (geoTransformAlong_restrict (nestedOpens c.U O)
      (hMU c).isClosedSubmanifold_N (hMU c).isCoherent c.T (hT c))
  obtain ⟨β, hβ⟩ := hCmp c₁.U c₂.U c₁.Y c₂.Y c₁.T c₂.T c₁.mem c₂.mem
  let α := overlapBaseEquiv (n := n) (inf_le_left : O ≤ c₁.U) (inf_le_right : O ≤ c₂.U)
  have hOriginal (c : TowerChart K Z P) : (MR c).E =
      E.map ((fun p : nestedOpens c.U O => p.val.val) ⁻¹' ·) := by
    simp only [MR, MU, M, MarkedIdeal.pullback, geometricTemplate, List.map_map]
    rfl
  have hOrig : (MR c₁).E = (MR c₂).E.map (α ⁻¹' ·) := by
    rw [hOriginal c₁, hOriginal c₂]
    exact original_overlap_boundary_lists (n := n) c₁.U c₂.U E
  have hBClosed : ∀ H ∈ (MR c₂).E, IsClosed H :=
    (IsWellFormed.pullback_val (hMU c₂) (nestedOpens c₂.U O)).isSNCDivisor.1
  have htrace := full_boundary_transport hβ (MR c₁) (MR c₂) hOrig hBClosed
  have hIncl : ∀ z, incl c₂ (β z) = incl c₁ z :=
    HironakaG3RPureBoundary.incl_comparison c₁ c₂ (inf_le_right : O ≤ c₂.U) β
      (physical_overlap_proj_comm c₁.U c₂.U hβ)
  have hMap (c : TowerChart K Z P) :
      (fullChartBoundary c E).map (· ∩ P ⁻¹' (O : Set X)) =
        (geoTransformAlong (MR c) (R c)).E.map (incl c '' ·) := by
    rw [hRestr]
    unfold fullChartBoundary chartBoundary
    simp only [List.map_map]
    apply List.map_congr_left
    intro H _
    exact HironakaG3RPureBoundary.chartIncl_image_inter_preimage c O H
  rw [hMap c₁, hMap c₂, HironakaG3RGluedBoundary.filter_nonempty_map_image,
    HironakaG3RGluedBoundary.filter_nonempty_map_image]
  change (geoTransformAlong (MR c₁) (R c₁)).E.filter _ =
    ((geoTransformAlong (MR c₂) (R c₂)).E.filter _).map (β ⁻¹' ·) at htrace
  rw [htrace, List.map_map]
  apply List.map_congr_left
  intro H _
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨β a, ha, hIncl a⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨β.symm b, ?_, ?_⟩
    · change β (β.symm b) ∈ H
      rwa [β.apply_symm_apply]
    · have h := hIncl (β.symm b)
      rw [β.apply_symm_apply] at h
      exact h.symm

/-- The full boundary of the glued atlas is the union of the actual
ordered finite chart boundaries. -/
def fullBoundarySupport {K : LocalTowerClass X} {P : Z → X} (E : List (Set X)) : Set Z :=
  {z | ∃ c : TowerChart K Z P, ∃ H ∈ fullChartBoundary c E, z ∈ H}

/-- A chart reads the full boundary support, including all chronological births. -/
theorem full_boundary_support_inter_chart {W : Set X} {E : List (Set X)} {K : LocalTowerClass X}
    (hE : IsSNCDivisor n E) (hTerm : SharpTerminalClass W E K) (hCmp : HasPhysicalComparisons K)
    {P : Z → X} (c : TowerChart K Z P) :
    fullBoundarySupport (K := K) (P := P) E ∩ c.V = ⋃ H ∈ fullChartBoundary c E, H := by
  let M := geometricTemplate (univ : Set X) E
  ext z
  constructor
  · rintro ⟨⟨c', H', hH', hz⟩, hzV⟩
    have hz' : z ∈ (c'.V : Set Z) := chartBoundary_subset_V c' M hH' hz
    have hzV' : z ∈ (c.V : Set Z) := hzV
    rw [c'.V_eq] at hz'
    rw [c.V_eq] at hzV'
    have hPz : P z ∈ ((c'.U ⊓ c.U : Opens X) : Set X) := ⟨hz', hzV'⟩
    have hmem : H' ∩ P ⁻¹' ((c'.U ⊓ c.U : Opens X) : Set X) ∈
        ((fullChartBoundary c' E).map (· ∩ P ⁻¹' ((c'.U ⊓ c.U : Opens X) : Set X))).filter
          (fun H => decide H.Nonempty) :=
      List.mem_filter.mpr ⟨List.mem_map_of_mem hH', decide_eq_true ⟨z, hz, hPz⟩⟩
    rw [full_chart_boundary_overlap hE hTerm hCmp c' c] at hmem
    obtain ⟨H, hH, heq⟩ := List.mem_map.mp (List.mem_filter.mp hmem).1
    have hzH : z ∈ H ∩ P ⁻¹' ((c'.U ⊓ c.U : Opens X) : Set X) := by
      rw [heq]
      exact ⟨hz, hPz⟩
    exact mem_iUnion₂.mpr ⟨H, hH, hzH.1⟩
  · intro hz
    obtain ⟨H, hH, hzH⟩ := mem_iUnion₂.mp hz
    exact ⟨⟨c, H, hH, hzH⟩, chartBoundary_subset_V c M hH hzH⟩

/-- The globally glued full boundary support is closed. -/
theorem isClosed_full_boundary_support {W : Set X} {E : List (Set X)} {K : LocalTowerClass X}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hTerm : SharpTerminalClass W E K) (hCmp : HasPhysicalComparisons K)
    {P : Z → X} (hP : IsGluedFrom K Z P) :
    IsClosed (fullBoundarySupport (K := K) (P := P) E) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨c, hc⟩ := hP.2.2.2 (P z)
  have hzV : z ∈ c.V := c.mem_V hc
  have hsnc := (full_chart_geometry hW hE hTerm hP c).2.1
  let F : Set c.V := (Subtype.val : c.V → Z) ⁻¹' (⋃ H ∈ fullChartBoundary c E, H)
  have hF : IsClosed F := by
    have heq : F = ⋃ H ∈ {H : Set Z | H ∈ fullChartBoundary c E},
        (Subtype.val : c.V → Z) ⁻¹' H := by
      simp only [F, preimage_iUnion₂]
      rfl
    rw [heq]
    exact Set.Finite.isClosed_biUnion (List.finite_toSet _)
      fun H hH => hsnc.1 _ (List.mem_map_of_mem hH)
  refine ⟨Subtype.val '' Fᶜ, ?_, (c.V.isOpen.isOpenMap_subtype_val _ hF.isOpen_compl), ⟨⟨z, hzV⟩, ?_, rfl⟩⟩
  · rintro _ ⟨v, hv, rfl⟩ hvB
    exact hv ((full_boundary_support_inter_chart hE hTerm hCmp c).subset ⟨hvB, v.2⟩)
  · intro hzF
    obtain ⟨H, hH, hzH⟩ := mem_iUnion₂.mp hzF
    exact hz ⟨c, H, hH, hzH⟩

/-- The noncompact sharp-cleanup contract on one actual glued map. -/
structure IsGluedSharpCleanup (K : LocalTowerClass X) (W : Set X) (E : List (Set X))
    (Z : CMfd.{u} n) (P : Z → X) : Prop where
  atlas : IsGluedFrom K Z P
  physicalComparisons : HasPhysicalComparisons K
  comparisons : HasComparisons K
  terminal : SharpTerminalClass W E K
  centresOver : ∀ c : TowerChart K Z P,
    CentresOver ((Subtype.val : c.U → X) ⁻¹' originalSharpBadLocus (n := n) W E) c.T
  goodIso : IsIsomorphismOver n P (originalSharpBadLocus (n := n) W E)ᶜ
  imageCarrier : P '' strictTransform n P W = W
  smoothCarrier : IsClosedSubmanifold n (strictTransform n P W)
  closedBoundary : IsClosed (fullBoundarySupport (K := K) (P := P) E)
  chartBoundary : ∀ c : TowerChart K Z P,
    fullBoundarySupport (K := K) (P := P) E ∩ c.V = ⋃ H ∈ fullChartBoundary c E, H
  chartSNC : ∀ c : TowerChart K Z P,
    IsSNCDivisor n ((fullChartBoundary c E).map ((Subtype.val : c.V → Z) ⁻¹' ·))
  chartNC : ∀ c : TowerChart K Z P,
    HasNormalCrossings n ((Subtype.val : c.V → Z) ⁻¹' strictTransform n P W)
      ((fullChartBoundary c E).map ((Subtype.val : c.V → Z) ⁻¹' ·))
  boundaryComparisons : ∀ c₁ c₂ : TowerChart K Z P,
    ((fullChartBoundary c₁ E).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter
        (fun H => decide H.Nonempty) =
      ((fullChartBoundary c₂ E).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter
        (fun H => decide H.Nonempty)

/-- Finite local coverage and physical overlap comparisons give the
full sharp-cleanup atlas. -/
theorem glue_compatible_sharp_terminal_cover {W : Set X} {E : List (Set X)} {K : LocalTowerClass X}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hTerm : SharpTerminalClass W E K) (hCover : Covers K) (hCmp : HasPhysicalComparisons K) :
    ∃ (Z : CMfd.{u} n) (P : Z → X), IsGluedSharpCleanup K W E Z P := by
  obtain ⟨Z, P, hP, hIso, hImage, hSmooth, hGeom⟩ :=
    exists_glued_sharp_terminal_geometry hW hE hTerm hCover hCmp
  exact ⟨Z, P, hP, hCmp, physical_comparisons_to_comparisons hCmp, hTerm,
    fun c => class_centresOver_full_bad hW hE hTerm c.U c.Y c.T c.mem,
    hIso, hImage, hSmooth, isClosed_full_boundary_support hW hE hTerm hCmp hP,
    full_boundary_support_inter_chart hE hTerm hCmp, fun c => (hGeom c).1, fun c => (hGeom c).2,
    full_chart_boundary_overlap hE hTerm hCmp⟩

/-- A producer of actual terminal towers on every relatively compact open
gives a chart over every such open of the same glued sharp-cleanup map. -/
theorem glue_compatible_sharp_terminal_histories {W : Set X} {E : List (Set X)} {K : LocalTowerClass X}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hTerm : SharpTerminalClass W E K) (hCmp : HasPhysicalComparisons K)
    (hLocal : ∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
      ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y), K U Y T) :
    ∃ (Z : CMfd.{u} n) (P : Z → X), IsGluedSharpCleanup K W E Z P ∧
      ∀ (U : Opens X) (L : Set X), IsCompact L → (U : Set X) ⊆ L →
        ∃ c : TowerChart K Z P, c.U = U := by
  have hCover : Covers K := by
    let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
    intro x
    obtain ⟨L, hL, hxL⟩ := exists_compact_mem_nhds x
    let U : Opens X := ⟨interior L, isOpen_interior⟩
    exact ⟨U, mem_interior_iff_mem_nhds.mpr hxL, hLocal U L hL interior_subset⟩
  obtain ⟨Z, P, hP⟩ := glue_compatible_sharp_terminal_cover hW hE hTerm hCover hCmp
  refine ⟨Z, P, hP, ?_⟩
  intro U L hL hUL
  obtain ⟨Y, T, hT⟩ := hLocal U L hL hUL
  exact ⟨HironakaG3RChartOfMember.chartOfMember hP.comparisons T hT hP.atlas.2.2.2 hP.atlas.1.continuous, rfl⟩

end
end Hironaka.HironakaG4SharpTerminalAtlas
