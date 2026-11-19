import Hironaka.Resolution.HironakaG4ProcessedStateRestriction
import Hironaka.Resolution.HironakaG4NativeFactorTauDictionary
import Hironaka.Resolution.HironakaG4CompactTraceExponentBound
import Hironaka.Resolution.HironakaG4OrderedProcessedMaskHistory

/-! Complete an actual count-one processed prefix on a neighbourhood of any
compact enclosure. A compact closure gives the required uniform exponent
bound even when the physical sharp bad locus itself is noncompact. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4ProcessedCountOneNearCompact

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism NormalCrossings NormalCrossingsInvariance
  HironakaG34NonPureLowDim HironakaG4ProcessedMaskRestriction HironakaG4ProcessedStateRestriction
  HironakaActualProcessedAllMasksDrop HironakaActualProcessedMaskFiniteBlock
  HironakaActualProcessedSharpCleanup HironakaG4NativeFactorTauDictionary
  HironakaG4CompactTraceExponentBound HironakaG4PreparedCentreCoordinates
  HironakaG4MonomialFamilyInvariant HironakaG4ZeroMaskSameGammaHistory
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG4OrderedProcessedMaskHistory
  HironakaLocalPrincipalization HomogenizedGlueingTower DivisorExponentAlong RestrictEmptyTower

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- One compact closure bounds the actual row exponents on its prescribed
literal restriction. This bound concerns the original factor matrix. -/
theorem processed_row_exponents_bounded_on_compact_open (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (O : Opens X) (hCl : IsCompact (closure (O : Set X))) :
    let v := (Subtype.val : O → X)
    let WO := v ⁻¹' W
    let EO := E.map (v ⁻¹' ·)
    let L := restrict O T
    let A₀ := geoTransformAlong (geometricTemplate WO []) L
    ∃ B : ℕ,∀ x ∈ A₀.N,∀ i j,factorMatrix WO EO L x i j ≤ B := by
  intro v WO EO L A₀
  let A := geoTransformAlong (geometricTemplate W []) T
  let u := (Subtype.val : openPreimage T O → Y)
  let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
  have hGeom := HironakaG4RecordedTowerResidualCompatibility.actual_recorded_tower_residual_dictionary
    hn hW hE hdense T hT hFull
  let C := T.proj ⁻¹' closure (O : Set X)
  have hC : IsCompact C := (isProperMap_proj T).isCompact_preimage hCl
  obtain ⟨B,hB⟩ := all_old_rows_bounded_on_compact hn hGeom.1 hGeom.2.1 hGeom.2.2.1
    hGeom.2.2.2.1 C hC
  obtain ⟨c,_hChronology,hEntries⟩ :=
    processed_matrix_entries_restrict hn hW hE hdense T hT hFull O
  have hNOpen : A₀.N = u ⁻¹' A.N := congrArg MarkedIdeal.N (original_carrier_template_restrict hW T hT O)
  refine ⟨B,?_⟩
  intro x hx i j
  let i₀ := e.symm i
  have hxC : x.val ∈ C := subset_closure x.property
  have hxN : x.val ∈ A.N := by
    rw [hNOpen] at hx
    exact hx
  have hEntry := hEntries x i₀ j
  change factorMatrix WO EO L x (e i₀) j = _ at hEntry
  rw [show e i₀ = i from e.apply_symm_apply i] at hEntry
  have hc := hB x.val hxC hxN (oldEquiv E T i₀) (c j)
  have hFactor : oldMonomialPart A.N (E.map (strictAlong T)) A.E (oldEquiv E T i₀) =
      oldFactor W E T i₀ := by
    unfold oldMonomialPart oldTraceIdeal oldFactor
    rw [get_oldEquiv]
  rw [hFactor] at hc
  change factorMatrix W E T x.val i₀ (c j) ≤ B at hc
  exact hEntry.trans_le hc

/-- A fixed mask list still enumerates the full count level after reindexing
the old rows by an equivalence. -/
theorem mask_cover_reindex {r s q : ℕ} (L : List (Finset (Fin r))) (e : Fin r ≃ Fin s)
    (hL : L.toFinset = (Finset.univ : Finset (Fin r)).powersetCard q) :
    (L.map (fun P => P.map e.toEmbedding)).toFinset =
      (Finset.univ : Finset (Fin s)).powersetCard q := by
  have he : (Finset.univ : Finset (Fin r)).map e.toEmbedding = Finset.univ := by simp
  rw [← he,Finset.powersetCard_map,← hL]
  ext P
  simp only [List.mem_toFinset,List.mem_map,Finset.mem_map]
  exact Iff.rfl

set_option maxHeartbeats 650000 in
/-- Finish the actual count-one state on a neighbourhood of a compact
enclosure in the prescribed singleton order. -/
theorem exists_labelled_processed_count_one_cleanup_near_compact (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hAt : At W E 1 T)
    {ι : Type v} (labels : List ι) [DecidableEq ι]
    (mask : ι → Finset (Fin E.length))
    (hLabels : (labels.map mask).toFinset = (Finset.univ : Finset (Fin E.length)).powersetCard 1)
    (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X,K ⊆ O ∧ ∃ (Z : CMfd.{u} n) (Q : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
      let v := (Subtype.val : O → X)
      let WO := v ⁻¹' W
      let EO := E.map (v ⁻¹' ·)
      let L := restrict O T
      let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
      let U := L.append Q
      let A := geoTransformAlong (geometricTemplate WO []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set O) EO) U).E
      OrderedProcessedMaskHistory hn WO EO L (fun i => (mask i).map e.toEmbedding) Q labels.reverse ∧
      IsGeoTestTower (geometricTemplate WO []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set O) EO) U ∧
      CurrentSharpCentres WO EO U ∧
      CentresOver (originalSharpBadLocus (n := n) WO EO) U ∧
      (∀ x ∈ A.N,tauD (factorMatrix WO EO U x)=0) ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) WO EO)ᶜ := by
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace (ComplexModel n) X
  obtain ⟨O₀,hO₀,hKO,hCl⟩ := exists_isOpen_superset_and_isCompact_closure hK
  let O : Opens X := ⟨O₀,hO₀⟩
  let v := (Subtype.val : O → X)
  let WO := v ⁻¹' W
  let EO := E.map (v ⁻¹' ·)
  let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
  let L := restrict O T
  let A₀ := geoTransformAlong (geometricTemplate WO []) L
  let N₀ := strictAlong L WO
  let old₀ := EO.map (strictAlong L)
  let born₀ := A₀.E
  have hWU : IsClosedSubmanifold n WO :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O
  have hEU : IsSNCDivisor n EO :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val (n := n) O) continuous_subtype_val hE
  have hDenseU : WO ⊆ closure (WO \ ⋃ H ∈ EO,H) := open_full_density hdense O
  have hAtU := (processed_at_restrict hn hW hE hdense T 1 hAt O).1
  obtain ⟨hL,hFullL,hSharpL,hOrdL,_hNCL,_hDenseSL,hPrepL,hCountL⟩ := hAtU
  obtain ⟨hN₀,hSNC₀,hTr₀,hDense₀,hOrd₀,hPrep₀,hCount₀⟩ :=
    original_count_one_prefix_dictionary hn hWU hEU hDenseU L hL hFullL hOrdL hPrepL hCountL
  obtain ⟨B,hB⟩ := processed_row_exponents_bounded_on_compact_open
    hn hW hE hdense T hAt.1 hAt.2.1 O hCl
  have hNative := (native_factor_tau_dictionary (W := WO) EO L).1
  have hB₀ : ∃ M : ℕ,∀ x ∈ N₀,∀ i : Fin old₀.length,∀ j : Fin born₀.length,
      divExpAlong n N₀ (oldMonomialPart N₀ old₀ born₀ i) (born₀.get j) x ≤ M := by
    refine ⟨B,?_⟩
    intro x hx i j
    let i₀ := (oldEquiv EO L).symm i
    have h := hNative x i₀ j
    change divExpAlong n N₀ (oldMonomialPart N₀ old₀ born₀ (oldEquiv EO L i₀)) (born₀.get j) x = _ at h
    rw [show oldEquiv EO L i₀ = i from (oldEquiv EO L).apply_symm_apply i] at h
    exact h.trans_le (hB x ((N_geoTransformAlong _ _).symm ▸ hx) i₀ j)
  let e₀ := oldEquiv EO L
  let mask₀ := fun i => ((mask i).map e.toEmbedding).map e₀.toEmbedding
  have hLabels₀ : (labels.map mask₀).toFinset = (Finset.univ : Finset (Fin old₀.length)).powersetCard 1 := by
    rw [show mask₀ = (fun P => P.map (e.trans e₀).toEmbedding) ∘ mask by
      funext i
      exact Finset.map_map _ _ _]
    rw [← List.map_map]
    exact mask_cover_reindex (labels.map mask) (e.trans e₀) hLabels
  obtain ⟨Z,Q,hTape,hTestQ,hFullQ,hSharpQ,hZeroQ,hSmoothQ,hSNCQ,hNCQ⟩ :=
    native_count_one_labelled_cleanup_of_bounded_exponents
      hn hN₀ hSNC₀ hTr₀ hDense₀ hOrd₀ hPrep₀ hCount₀ (labels.map mask₀) hLabels₀ hB₀
  have hLabelsActual := native_history_to_ordered_processed hn WO EO L
    (fun i => (mask i).map e.toEmbedding) labels.reverse Q
    (by simpa only [List.map_reverse] using hTape)
  exact ⟨O,hKO,Z,Q,hLabelsActual,append_count_one_tail hWU hEU L hL hFullL hSharpL Q
    hTestQ hFullQ hSharpQ hZeroQ hSmoothQ hSNCQ hNCQ⟩


set_option maxHeartbeats 650000 in
/-- The held count-one proof extends the restricted literal original
prefix to full normal crossings over one neighbourhood of any compact
set. Both ordered tests and every actual sharp centre law are retained. -/
theorem exists_processed_count_one_cleanup_near_compact (hn : 0 < n) {W : Set X}
    {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hAt : At W E 1 T) (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X,K ⊆ O ∧ ∃ (Z : CMfd.{u} n) (Q : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
      let v := (Subtype.val : O → X)
      let WO := v ⁻¹' W
      let EO := E.map (v ⁻¹' ·)
      let U := (restrict O T).append Q
      let A := geoTransformAlong (geometricTemplate WO []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set O) EO) U).E
      IsGeoTestTower (geometricTemplate WO []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set O) EO) U ∧
      CurrentSharpCentres WO EO U ∧
      CentresOver (originalSharpBadLocus (n := n) WO EO) U ∧
      (∀ x ∈ A.N,tauD (factorMatrix WO EO U x)=0) ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) WO EO)ᶜ := by

  classical
  let F := (Finset.univ : Finset (Fin E.length)).powersetCard 1
  have hF : (F.toList.map id).toFinset = F := by simp
  obtain ⟨O,hKO,Z,Q,_hTape,hEnd⟩ := exists_labelled_processed_count_one_cleanup_near_compact
    hn hW hE hdense T hAt F.toList id hF K hK
  exact ⟨O,hKO,Z,Q,hEnd⟩

end
end Hironaka.HironakaG4ProcessedCountOneNearCompact
