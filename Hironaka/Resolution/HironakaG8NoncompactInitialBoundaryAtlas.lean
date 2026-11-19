import Hironaka.Resolution.HironakaG8LabelledEmbeddedAtlas
import Hironaka.Resolution.HironakaG8OrderedSmoothSuffix
import Hironaka.Resolution.HironakaG8LocalMixedSmoothCleanup
import Hironaka.Resolution.HironakaG4SharpTerminalAtlas

/-! Noncompact literal local embedded histories preserving an initial ordered SNC list. -/

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff
namespace Hironaka.HironakaG8NoncompactInitialBoundaryAtlas
noncomputable section
attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealRestrictOpen HomogenizedGlueingTower
  RestrictEmptyTower HironakaEmbeddedAnalytic NormalCrossings NormalCrossingsInvariance
  HironakaG3RTowerClass HironakaG3RTowerGluing HironakaG3GenericBornChartOverlap
  HironakaG8LabelledEmbeddedTape HironakaG8LabelledEmbeddedAtlas HironakaG8OrderedSmoothSuffix
  HironakaG8LocalMixedSmoothCleanup HironakaG8LocalMixedPhaseAssembly HironakaG8LocalPureFinish
  HironakaG8UniverseDenseBoundary HironakaG8CompleteEmbeddedAtlas
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaNormalCrossingsSeparationChoiceComparison
  HironakaG3REmbeddedGlobalSNC HironakaResolutionSpaceLocal HironakaBaseChange
  HironakaG8SurfaceLimitEndpoint G3UniversePhysicalClassComparisons
  HironakaG8LocalMixedEmbeddedResolution HironakaOriginalTerminalOverlapComparison
  HironakaG3RPureEmbedded HironakaG3RChartOfMember MaxLocusLocal
  HironakaG3DisjointAtlasCommonGood HironakaEmbeddedBoundary
  HironakaG3EmptyAwareFullBoundary HironakaG3OriginalOverlapBoundaryLists
  HironakaSharpActualFiniteChronologicalHistory HironakaG8UniverseBMTransport
  HironakaG4SharpTerminalAtlas HironakaG34NonPureLowDim

def initialBoundaryClass {n : ℕ} {X : CMfd.{0} n}
    (C : SmoothTailCertificate n) (W : Set X) (E : List (Set X)) : LocalTowerClass X :=
  fun U _ T => LabelledEmbeddedHistory C ((Subtype.val : U → X) ⁻¹' W)
    (E.map ((Subtype.val : U → X) ⁻¹' ·)) univ T

theorem initial_boundary_class_physical {n : ℕ} {X : CMfd.{0} n}
    (hn : 0 < n) {C : SmoothTailCertificate n} (hC : SmoothTailHasComparisons C)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    {E : List (Set X)} (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B)) :
    HasPhysicalComparisons (initialBoundaryClass C W E) := by
  classical
  intro U V Y Z T S hT hS
  let OU := nestedOpens U (U ⊓ V)
  let OV := nestedOpens V (U ⊓ V)
  let e := overlapBaseEquiv (n := n) (show U ⊓ V ≤ U from inf_le_left) (show U ⊓ V ≤ V from inf_le_right)
  let WU := (Subtype.val : U → X) ⁻¹' W
  let WV := (Subtype.val : V → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  let EV := E.map ((Subtype.val : V → X) ⁻¹' ·)
  have hDU := dense_complement_restrict W E hDense U
  have hDV := dense_complement_restrict W E hDense V
  have hTU := hT.restrictOpen (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW U)
    (isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE) hDU OU
  have hSV := hS.restrictOpen (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW V)
    (isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hE) hDV OV
  simp only [preimage_univ] at hTU hSV
  have hCarrier (A : Set X) :
      (Subtype.val : OU → U) ⁻¹' ((Subtype.val : U → X) ⁻¹' A) =
        e ⁻¹' ((Subtype.val : OV → V) ⁻¹' ((Subtype.val : V → X) ⁻¹' A)) := by
    ext x
    change x.val.val ∈ A ↔ (e x).val.val ∈ A
    rw [overlapBaseEquiv_point]
  have hSlots : EU.map ((Subtype.val : OU → U) ⁻¹' ·) =
      (EV.map ((Subtype.val : OV → V) ⁻¹' ·)).map (e ⁻¹' ·) := by
    simp only [EU,EV,List.map_map]
    exact List.map_congr_left (fun A _ => hCarrier A)
  exact labelled_embedded_history_emptyAware hn hC e (hCarrier W)
    (congrArg (List.filter (fun B => decide B.Nonempty)) hSlots)
    (dense_complement_restrict WV EV hDV OV) (dense_complement_restrict WU EU hDU OU) hTU hSV

theorem initial_boundary_class_compact_windows {m : ℕ} {X : CMfd.{0} (m+1)}
    {C : SmoothTailCertificate (m+1)} (hProduce : ProducesLocalSmoothCertificates C)
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m+1) W)
    {E : List (Set X)} (hE : IsSNCDivisor (m+1) E)
    (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B))
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
      ∃ (Y : CMfd.{0} (m+1)) (T : BlowupTower (CMfd.of (n := m+1) U) Y),
        initialBoundaryClass C W E U Y T :=
  exists_labelled_embedded_history_on_compact_enclosed_open C hProduce hW E hE hDense U K hK hUK

abbrev orderedInitialBoundaryClass {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (E : List (Set X)) : LocalTowerClass X :=
  initialBoundaryClass (ascending_smooth_tail_certificate n) W E

/-- Ordered nonempty boundary traces compare between any two physical
charts, with the incoming slots still present in the input lists. -/
theorem initial_boundary_chart_overlap {n : ℕ} {X Z : CMfd.{0} n}
    {C : SmoothTailCertificate n} {W : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (hCmp : HasPhysicalComparisons (initialBoundaryClass C W E))
    {P : Z → X} (c₁ c₂ : TowerChart (initialBoundaryClass C W E) Z P) :
    ((fullChartBoundary c₁ E).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter
        (fun H => decide H.Nonempty) =
      ((fullChartBoundary c₂ E).map (· ∩ P ⁻¹' ((c₁.U ⊓ c₂.U : Opens X) : Set X))).filter
        (fun H => decide H.Nonempty) := by
  classical
  let O := c₁.U ⊓ c₂.U
  let M := geometricTemplate (univ : Set X) E
  let MU (c : TowerChart (initialBoundaryClass C W E) Z P) :=
    MarkedIdeal.pullback (Subtype.val : c.U → X) M
  let MR (c : TowerChart (initialBoundaryClass C W E) Z P) :=
    MarkedIdeal.pullback (Subtype.val : nestedOpens c.U O → c.U) (MU c)
  let R (c : TowerChart (initialBoundaryClass C W E) Z P) := restrict (nestedOpens c.U O) c.T
  let incl (c : TowerChart (initialBoundaryClass C W E) Z P) :
      openPreimage c.T (nestedOpens c.U O) → Z := chartIncl c ∘ Subtype.val
  have hM : M.IsWellFormed := ⟨isClosedSubmanifold_univ, IdealWeightPowers.isCoherent_unitIdeal,
    hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hMU (c : TowerChart (initialBoundaryClass C W E) Z P) : (MU c).IsWellFormed :=
    IsWellFormed.pullback_val hM c.U
  have hT (c : TowerChart (initialBoundaryClass C W E) Z P) : IsGeoTestTower (MU c) c.T := by
    change IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : c.U → X)
      (geometricTemplate (univ : Set X) E)) c.T
    rw [template_pullback (Y := CMfd.of (n := n) c.U), preimage_univ]
    exact bm_stage_test _ _ c.T c.mem.geometry.2.1
  have hRestr (c : TowerChart (initialBoundaryClass C W E) Z P) : (geoTransformAlong (MR c) (R c)).E =
      (geoTransformAlong (MU c) c.T).E.map
        ((Subtype.val : openPreimage c.T (nestedOpens c.U O) → c.Y) ⁻¹' ·) :=
    congrArg MarkedIdeal.E (geoTransformAlong_restrict (nestedOpens c.U O)
      (hMU c).isClosedSubmanifold_N (hMU c).isCoherent c.T (hT c))
  obtain ⟨β, hβ⟩ := hCmp c₁.U c₂.U c₁.Y c₂.Y c₁.T c₂.T c₁.mem c₂.mem
  let α := overlapBaseEquiv (n := n) (inf_le_left : O ≤ c₁.U) (inf_le_right : O ≤ c₂.U)
  have hOriginal (c : TowerChart (initialBoundaryClass C W E) Z P) : (MR c).E =
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
  have hMap (c : TowerChart (initialBoundaryClass C W E) Z P) :
      (fullChartBoundary c E).map (· ∩ P ⁻¹' (O : Set X)) =
        (geoTransformAlong (MR c) (R c)).E.map (incl c '' ·) := by
    rw [hRestr]
    unfold fullChartBoundary HironakaG3RPureEmbedded.chartBoundary
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

/-- The physical local class glues for an arbitrary finite ordered initial SNC
boundary in positive ambient dimension, retaining each prescribed window. -/
theorem exists_locally_finite_initial_boundary_atlas
    {m : ℕ} {X : CMfd.{0} (m+1)} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := m+1) W) {E : List (Set X)}
    (hE : IsSNCDivisor (m+1) E) (hDense : W ⊆ closure (W \ ⋃ B ∈ E, B)) :
    ∃ (Z : CMfd.{0} (m+1)) (P : Z → X),
      IsGluedFrom (orderedInitialBoundaryClass W E) Z P ∧
      (∀ (U : Opens X) (K : Set X), IsCompact K → (U : Set X) ⊆ K →
        ∃ c : TowerChart (orderedInitialBoundaryClass W E) Z P, c.U = U) ∧
      IsClosedSubmanifold (m+1) (strictTransform (m+1) P W) ∧
      IsIsomorphismOver (m+1) P (singularSet (n := m+1) W ∪ (W ∩ ⋃ B ∈ E, B))ᶜ := by
  have hC : SmoothTailHasComparisons (ascending_smooth_tail_certificate (m+1)) := by
    intro A A' Y Y' φ A₀ E E' T T' hB hT' hT
    exact ordered_smooth_suffix_emptyAware φ (ds := List.finRange (m + 2)) hB hT' hT
  have hProduce : ProducesLocalSmoothCertificates (ascending_smooth_tail_certificate (m+1)) := by
    intro A A₀ hSmooth E hE hDense L hL
    exact local_mixed_smooth_boundary_cleanup_ordered hSmooth E hE hDense L hL
  have hP := initial_boundary_class_physical (Nat.succ_pos m) hC hW hE hDense
  have hWindows := initial_boundary_class_compact_windows hProduce hW hE hDense
  have hCover : Covers (orderedInitialBoundaryClass W E) := by
    have : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel (m+1)) X
    let L := CompactExhaustion.choice X
    intro x
    obtain ⟨k,hx⟩ := L.exists_mem x
    let U : Opens X := ⟨interior (L (k+1)),isOpen_interior⟩
    obtain ⟨Y,T,hT⟩ := hWindows U (L (k+1)) (L.isCompact (k+1)) interior_subset
    exact ⟨U,L.subset_interior_succ k hx,Y,T,hT⟩
  obtain ⟨Z,P,hG⟩ := exists_isGluedFrom hCover (physical_comparisons_to_comparisons hP)
  refine ⟨Z,P,hG,?_,⟨isClosed_closure,fun z hz => ?_⟩,?_⟩
  · intro U K hK hUK
    obtain ⟨Y,T,hT⟩ := hWindows U K hK hUK
    exact ⟨chartOfMember (physical_comparisons_to_comparisons hP) T hT hG.2.2.2
      hG.1.continuous,rfl⟩
  · obtain ⟨c,hcz⟩ := hG.2.2.2 (P z)
    let v : c.V := ⟨z,c.mem_V hcz⟩
    let y : c.Y := c.φ.symm v
    have hyz : chartIncl c y = z := chartIncl_symm c v
    have hTrace := strictTransform_chart c hG.1 W
    have hy : y ∈ strictTransform (m+1) c.T.proj ((Subtype.val : c.U → X) ⁻¹' W) := by
      rw [hTrace]
      change chartIncl c y ∈ strictTransform (m+1) P W
      rwa [hyz]
    obtain ⟨d,hd⟩ := c.mem.geometry.2.2.1.2 y hy
    exact ⟨d,hyz ▸ regularAtDim_of_chart c (hTrace ▸ hd)⟩
  · apply glued_isomorphism_over_of_local _ hG
    intro U Y T hT
    have hLocal := hT.geometry.2.2.2.2.2.2.2.2.2.2.2.1
    rwa [singularSet_preimage_val, ← preimage_biUnion_list, ← preimage_inter,
      ← preimage_union, ← preimage_compl] at hLocal

end
end Hironaka.HironakaG8NoncompactInitialBoundaryAtlas
