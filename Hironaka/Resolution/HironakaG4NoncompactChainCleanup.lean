import Hironaka.Resolution.HironakaG4ZeroMaskFixedQFold
import Hironaka.Resolution.HironakaG4NoncompactFixedQFiniteTraces
import Hironaka.Resolution.HironakaActualProcessedSharpCleanup
import Hironaka.Resolution.HironakaSharpOriginalDynamicGoodPrefixes
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4NoncompactChainCleanup
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings RelativePrincipalizationSpan HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4PreparedCentreCoordinates HironakaG4MonomialFamilyInvariant HironakaG4MonomialRowChain
  HironakaG4CompactWholeMonomialMaskPhase HomogenizedGlueingTower RestrictedIdealExtension
  MonomialPartAlong DivisorExponentAlong GermIdealOrder RestrictEmptyTower
variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem cleanup_with_count (hn : 0 < n) : ∀ q : ℕ,
    ∀ {X : CMfd.{u} n} {N : Set X} {O B : List (Set X)},
    (hN : IsClosedSubmanifold n N) → (hE : IsSNCDivisor n (O ++ B)) →
    (hTr : IsTransverse n N B) → (hdense : N ⊆ closure (N \ ⋃ H ∈ O ++ B,H)) →
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1) →
    (hPrep : ∀ x ∈ N,IsPreparedResidualSNCAt N O B x) →
    (∀ x ∈ N,tauD (fun i j => divExpAlong n N (oldMonomialPart N O B i) (B.get j) x) ≤ q) →
    (∀ x ∈ N,RowsChain (fun i j => divExpAlong n N (oldMonomialPart N O B i) (B.get j) x)) →
    (∃ C,∀ x ∈ N,∀ i : Fin O.length,∀ j : Fin B.length,
      divExpAlong n N (oldMonomialPart N O B i) (B.get j) x ≤ C) →
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N B) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (O ++ B)) T ∧
      CurrentSharpCentres N (O ++ B) T ∧
      IsClosedSubmanifold n (strictAlong T N) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) T).E ∧
      HasNormalCrossings n (strictAlong T N)
        (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) T).E := by
  intro q
  induction q with
  | zero =>
      intro X N O B hN hE hTr hdense hOrd hPrep hCount _hChain _hBounds
      have hZero : ∀ x ∈ N,tauD (fun i j =>
          divExpAlong n N (oldMonomialPart N O B i) (B.get j) x)=0 := by
        intro x hx
        exact Nat.eq_zero_of_le_zero (hCount x hx)
      have hNC := HironakaActualProcessedSharpCleanup.prepared_tau_zero_normalCrossings
        hn hN hE hTr hdense hOrd hPrep hZero
      refine ⟨X,.refl,trivial,trivial,trivial,?_,?_,?_⟩
      · exact hN
      · exact hE
      · exact hNC
  | succ q ih =>
      intro X N O B hN hE hTr hdense hOrd hPrep hCount hChain hBounds
      obtain ⟨Y,T,hBorn,hFull,hSharp,hNT,hSNC,hTrT,hDenseT,hOrdT,hPrepT,hDrop,hChainT,hBoundsT⟩ :=
        HironakaG4ZeroMaskFixedQFold.exists_prepared_chain_fixed_q_drop
          hn hN hE hTr hdense hOrd hPrep (q+1) (by omega) hCount hChain hBounds
      let NT := strictAlong T N
      let OT := O.map (strictAlong T)
      let BT := (geoTransformAlong (geometricTemplate N B) T).E
      have hCountT : ∀ z ∈ NT,tauD (fun i j =>
          divExpAlong n NT (oldMonomialPart NT OT BT i) (BT.get j) z) ≤ q := by
        intro z hz
        exact Nat.lt_succ_iff.mp (hDrop z hz)
      obtain ⟨Z,R,hRborn,hRfull,hRsharp,hSmooth,hRSNC,hRNC⟩ :=
        ih hNT hSNC hTrT hDenseT hOrdT hPrepT hCountT hChainT hBoundsT
      let U := T.append R
      have hTemplate : geoTransformAlong (geometricTemplate N B) T=geometricTemplate NT BT :=
        template_current N B T
      have hBoundary : (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) T).E=OT ++ BT := by
        have h := full_ordered N O.get B T
        have ho : List.ofFn O.get=O := List.ofFn_get O
        have hm : List.ofFn (fun i => strictAlong T (O.get i))=OT := by
          simpa only [List.get_eq_getElem] using List.ofFn_getElem_eq_map O (strictAlong T)
        rw [ho,hm] at h
        exact h
      have hFullTemplate : geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) T=
          geometricTemplate (univ : Set Y) (OT ++ BT) := by
        rw [template_current,strict_univ,hBoundary]
      have hUBorn : IsGeoTestTower (geometricTemplate N B) U := by
        apply (isGeoTestTower_append_iff _ T R).mpr
        exact ⟨hBorn,hTemplate.symm ▸ hRborn⟩
      have hUFull : IsGeoTestTower (geometricTemplate (univ : Set X) (O ++ B)) U := by
        apply (isGeoTestTower_append_iff _ T R).mpr
        exact ⟨hFull,hFullTemplate.symm ▸ hRfull⟩
      have hUSharp : CurrentSharpCentres N (O ++ B) U := by
        apply currentSharp_append N (O ++ B) T R hSharp
        rw [hBoundary]
        exact hRsharp
      have hCarrier : strictAlong U N=strictAlong R NT := by
        simp [U,NT,MemberInterLocusAlong.strictAlong_append]
      have hFullBoundary : (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) U).E =
          (geoTransformAlong (geometricTemplate (univ : Set Y) (OT ++ BT)) R).E := by
        rw [show U=T.append R from rfl,geoTransformAlong_append,hFullTemplate]
      refine ⟨Z,U,hUBorn,hUFull,hUSharp,?_,?_,?_⟩
      · exact hCarrier.symm ▸ hSmooth
      · exact hFullBoundary.symm ▸ hRSNC
      · rw [hCarrier,hFullBoundary]
        exact hRNC

/-- Comparable source rows and a uniform source exponent bound give a complete
prepared noncompact sharp cleanup on one actual finite history. -/
theorem noncompact_prepared_chain_cleanup (hn : 0 < n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O ++ B))
    (hTr : IsTransverse n N B) (hdense : N ⊆ closure (N \ ⋃ H ∈ O ++ B,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1)
    (hPrep : ∀ x ∈ N,IsPreparedResidualSNCAt N O B x)
    (hChain : ∀ x ∈ N,RowsChain (fun i j =>
      divExpAlong n N (oldMonomialPart N O B i) (B.get j) x))
    (hBounds : ∃ C,∀ x ∈ N,∀ i : Fin O.length,∀ j : Fin B.length,
      divExpAlong n N (oldMonomialPart N O B i) (B.get j) x ≤ C) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N B) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (O ++ B)) T ∧
      CurrentSharpCentres N (O ++ B) T ∧
      CentresOver (originalSharpBadLocus (n := n) N (O ++ B)) T ∧
      IsClosedSubmanifold n (strictAlong T N) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) T).E ∧
      HasNormalCrossings n (strictAlong T N)
        (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) T).E ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ IsIsomorphismOver n T.proj (originalSharpBadLocus (n := n) N (O ++ B))ᶜ := by
  have hCount : ∀ x ∈ N,tauD (fun i j =>
      divExpAlong n N (oldMonomialPart N O B i) (B.get j) x) ≤ O.length := by
    intro x hx
    unfold tauD
    simpa using Finset.card_le_univ (properRows (fun i j =>
      divExpAlong n N (oldMonomialPart N O B i) (B.get j) x))
  obtain ⟨Y,T,hBorn,hFull,hSharp,hSmooth,hSNC,hNC⟩ :=
    cleanup_with_count hn O.length hN hE hTr hdense hOrd hPrep hCount hChain hBounds
  have hOver := (HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint
    hN.1 hE.1 T hSharp).2
  exact ⟨Y,T,hBorn,hFull,hSharp,hOver,hSmooth,hSNC,hNC,T.contMDiff_proj,
    HironakaLocalPrincipalization.isProperMap_proj T,
    HironakaSharpOriginalDynamicGoodPrefixes.isIsomorphismOver_proj_of_centresOver _ T hOver⟩

/-- Finite source trace components supply the uniform source bound. -/
theorem noncompact_prepared_chain_cleanup_of_finite_traces (hn : 0 < n) {N : Set X} {O B : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (O ++ B))
    (hTr : IsTransverse n N B) (hdense : N ⊆ closure (N \ ⋃ H ∈ O ++ B,H))
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N O B i) x ≤ 1)
    (hPrep : ∀ x ∈ N,IsPreparedResidualSNCAt N O B x)
    (hChain : ∀ x ∈ N,RowsChain (fun i j =>
      divExpAlong n N (oldMonomialPart N O B i) (B.get j) x))
    (hComp : ∀ j : Fin B.length,Finite (ConnectedComponents
      {x : X | x ∈ N ∧ x ∈ B.get j})) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate N B) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) (O ++ B)) T ∧
      CurrentSharpCentres N (O ++ B) T ∧
      CentresOver (originalSharpBadLocus (n := n) N (O ++ B)) T ∧
      IsClosedSubmanifold n (strictAlong T N) ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) T).E ∧
      HasNormalCrossings n (strictAlong T N)
        (geoTransformAlong (geometricTemplate (univ : Set X) (O ++ B)) T).E ∧
      ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ T.proj ∧
      IsProperMap T.proj ∧ IsIsomorphismOver n T.proj (originalSharpBadLocus (n := n) N (O ++ B))ᶜ := by
  have hBounds := HironakaG4NoncompactFixedQFiniteTraces.all_old_rows_uniform_of_finite_trace_components
    hn hN hE hTr hdense hComp
  exact noncompact_prepared_chain_cleanup hn hN hE hTr hdense hOrd hPrep hChain hBounds

end
end Hironaka.HironakaG4NoncompactChainCleanup
