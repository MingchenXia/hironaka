import Hironaka.Resolution.HironakaNativeGammaCanonical
import Hironaka.Resolution.HironakaG4NativeFactorTauDictionary
import Hironaka.Resolution.HironakaG4ProcessedCountOneNearCompact
import Hironaka.Resolution.HironakaG4NativeProcessedMaskReindex

/-! The original-family certificate for an actual prepared zero-residual
mask, including each singleton at count one. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4NativeProcessedMaskCanonical

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings DivisorExponentAlong MonomialPartAlong RestrictedIdealExtension
  RelativePrincipalizationSpan CanonicalCentres HironakaNativeGammaCanonical
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant
  HironakaActualProcessedMaskControlledSum HironakaActualProcessedMaskFiniteBlock
  HironakaActualProcessedSharpCleanup HironakaG4NativeFactorTauDictionary
  HironakaG4ZeroResidualMonomialSum HironakaG4ZeroMaskSameGammaHistory
  HironakaG4DivisorExponentIdealMonotone HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4NativeProcessedMaskReindex HomogenizedGlueingTower
  HironakaG34NonPureLowDim HironakaG4ProcessedStateRestriction HironakaG4ProcessedCountOneNearCompact
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalMultiBoundaryBadLocus
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X Y : CMfd.{u} n}

set_option maxHeartbeats 750000 in
/-- The native zero-residual phase of a selected actual original mask is a
terminal canonical history for the very same mask and original invariant.
Both boundary tests are for the actual current originals. The marked
transform at every actual prefix is still monomial. -/
theorem exists_count_one_native_original_canonical_tail (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (P : Finset (Fin E.length)) (hP : P.card = 1)
    (hAt : HironakaActualProcessedAllMasksDrop.At W E 1 T)
    (hBound : let A := geoTransformAlong (geometricTemplate W []) T
      ∃ C : ℕ,∀ x ∈ A.N,∀ i j,factorMatrix W E T x i j ≤ C) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
      let M := processedMaskMarked W E T P
      IsInvDomain (n+1) M ∧
      IsCanonical M ((invFamily hn (n+1)).inv M) Q ∧ IsGeoResolution M Q ∧
      IsGeoTestTower (geometricTemplate W []) (T.append Q) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) ∧
      CurrentSharpCentres W E (T.append Q) ∧
      (∀ k : ℕ,
        let B := geoTransformAlong M (BlowupTowerSplit.head Q k)
        IsMonomialAlong n B.N B.ideal B.E) := by
  let A := geoTransformAlong (geometricTemplate W []) T
  let N := strictAlong T W
  let O := E.map (strictAlong T)
  let e := oldEquiv E T
  let B := A.E
  let D := oldMonomialPart N O B
  let F : Y → Fin O.length → Fin B.length → ℕ := fun x i j =>
    divExpAlong n N (D i) (B.get j) x
  let P₀ := P.map e.toEmbedding
  let M := nativeMaskMarked N O B P₀
  have hId : processedMaskMarked W E T P = M := by
    have h := (native_processed_mask_eq (W := W) E T P₀).2
    change processedMaskMarked W E T (P₀.map e.symm.toEmbedding) = M at h
    simpa [P₀,Finset.map_map] using h
  have hCard : P₀.card = 1 := (Finset.card_map _).trans hP
  have hP₀ : P₀.Nonempty := Finset.card_pos.mp (hCard.symm ▸ Nat.one_pos)
  have hNeq : A.N = N := N_geoTransformAlong _ _
  have hFrame := original_prepared_prefix_dictionary hn hW hE hdense T
    hAt.1 hAt.2.1 hAt.2.2.2.1 hAt.2.2.2.2.2.2.1
  obtain ⟨hN,hFull,hTr,hDense,hOrd,hPrep⟩ := hFrame
  have hFar := native_factor_tau_dictionary (W := W) E T
  have hTop : ∀ x ∈ N,tauD (F x) ≤ P₀.card := by
    intro x hx
    rw [hFar.2 x,hCard]
    exact hAt.2.2.2.2.2.2.2 x (hNeq.symm ▸ hx)
  have hZero₀ : ∀ x ∈ N,tauD (F x) = P₀.card → nuOne (F x) = 0 :=
    fun x _ hCount => nuOne_eq_zero_of_tauD_eq_one (F x) (hCount.trans hCard)
  have hBound₀ : ∃ C,∀ x ∈ N,∀ i j,F x i j ≤ C := by
    obtain ⟨C,hC⟩ := hBound
    refine ⟨C,?_⟩
    intro x hx i j
    have h := hFar.1 x (e.symm i) j
    change F x (e (e.symm i)) j = _ at h
    rw [e.apply_symm_apply] at h
    exact h.trans_le (hC x (hNeq.symm ▸ hx) (e.symm i) j)
  obtain ⟨_hc,hNZ,_hMono,hWF,_hCos,_hRows,_hCentre,_hLocal⟩ :=
    actual_zero_residual_mask_sum_geometry hn hN hFull hTr hDense P₀ hP₀ hTop hZero₀
  have hDim : ResolutionInvariantSpec.DimLE n M.N (n+1) := by
    intro x hx
    obtain ⟨k,hk⟩ := hN.2 x hx
    exact ⟨k,le_trans hk.1 (Nat.le_succ n),hk⟩
  have hDom : IsInvDomain (n+1) M := ⟨hWF,hDim,le_rfl,hNZ⟩
  obtain ⟨v,hFirst,hGamma⟩ :=
    zero_mask_gamma_bound_of_uniform_rows hn hN hFull hTr hDense P₀ hP₀ hTop hZero₀ hBound₀
  obtain ⟨Z,Q,hGammaCan,hRes,hBornTest,hFullTest,hSharp,_hRowTests,hPrefix,_hErase⟩ :=
    exists_prepared_zero_mask_bounded_noncompact_history
      hn hN hFull hTr hDense hOrd hPrep P₀ hP₀ hTop hZero₀ v hFirst hGamma
  have hMonomial (k : ℕ) :
      let U := geoTransformAlong M (BlowupTowerSplit.head Q k)
      IsMonomialAlong n U.N U.ideal U.E := by
    obtain ⟨hMarked,_hN,_hFull,_hTr,_hDense,_hOrder,_hPrep,_hCount,_hAct,_hZero,
      _hWF,_hNZ,hMono,_hCos,_hParts⟩ := hPrefix k
    change geoTransformAlong M (BlowupTowerSplit.head Q k) = _ at hMarked
    dsimp only
    rw [hMarked]
    exact hMono
  have hCan := original_canonical_of_monomial_segment hn n M Q hRes.1 hGammaCan hMonomial
  refine ⟨Z,Q,?_⟩
  dsimp only
  rw [hId]
  have hBoundary :=
    HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E T
  have hTestAll : IsGeoTestTower (geometricTemplate W []) (T.append Q) := by
    rw [isGeoTestTower_append_iff,template_current]
    exact ⟨hAt.1,hBornTest⟩
  have hFullAll : IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) := by
    rw [isGeoTestTower_append_iff,template_current,strict_univ,hBoundary]
    exact ⟨hAt.2.1,hFullTest⟩
  have hSharpAll : CurrentSharpCentres W E (T.append Q) := by
    apply currentSharp_append W E T Q hAt.2.2.1
    rw [hBoundary]
    exact hSharp
  exact ⟨hDom,hCan,hRes,hTestAll,hFullAll,hSharpAll,hMonomial⟩

/-- A prescribed literal open with compact closure supports a canonical
singleton phase, even when the sharp bad locus in that open is noncompact. -/
theorem exists_count_one_native_processed_mask_on_compact_open (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (P : Finset (Fin E.length)) (hP : P.card = 1)
    (hAt : HironakaActualProcessedAllMasksDrop.At W E 1 T)
    (O : Opens X) (hCl : IsCompact (closure (O : Set X))) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
      let v := (Subtype.val : O → X)
      let WO := v ⁻¹' W
      let EO := E.map (v ⁻¹' ·)
      let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
      let PO := P.map e.toEmbedding
      let L := restrict O T
      let M := processedMaskMarked WO EO L PO
      IsInvDomain (n+1) M ∧
      IsCanonical M ((invFamily hn (n+1)).inv M) Q ∧ IsGeoResolution M Q ∧
      IsGeoTestTower (geometricTemplate WO []) (L.append Q) ∧
      IsGeoTestTower (geometricTemplate (univ : Set O) EO) (L.append Q) ∧
      CurrentSharpCentres WO EO (L.append Q) ∧
      (∀ k : ℕ,
        let B := geoTransformAlong M (BlowupTowerSplit.head Q k)
        IsMonomialAlong n B.N B.ideal B.E) := by
  let v := (Subtype.val : O → X)
  let WO := v ⁻¹' W
  let EO := E.map (v ⁻¹' ·)
  let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
  let PO := P.map e.toEmbedding
  let L := restrict O T
  have hWO : IsClosedSubmanifold n WO :=
    BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O
  have hEO : IsSNCDivisor n EO := NormalCrossingsInvariance.isSNCDivisor_map_preimage
    (NormalCrossingsInvariance.pullsBackCoordinates_val (n := n) O) continuous_subtype_val hE
  have hDenseO : WO ⊆ closure (WO \ ⋃ H ∈ EO,H) := open_full_density hdense O
  have hAtO := (processed_at_restrict hn hW hE hdense T 1 hAt O).1
  have hPO : PO.card = 1 := (Finset.card_map _).trans hP
  have hBound := processed_row_exponents_bounded_on_compact_open hn hW hE hdense T hAt.1 hAt.2.1 O hCl
  exact exists_count_one_native_original_canonical_tail hn hWO hEO hDenseO L PO hPO hAtO hBound

end
end Hironaka.HironakaG4NativeProcessedMaskCanonical
