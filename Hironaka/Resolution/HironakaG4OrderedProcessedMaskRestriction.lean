import Hironaka.Resolution.HironakaG4OrderedProcessedMaskRebase

/-! Literal open restriction of all actual canonical mask phases. -/

set_option autoImplicit false

open Set TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.HironakaG4OrderedProcessedMaskRestriction

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism BlowupTowerIsoTail MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism MarkedIdealTowerTransport MarkedIdealRestrictOpen
  HomogenizedGlueingTower NormalCrossings NormalCrossingsInvariance
  HironakaG34NonPureLowDim HironakaSharpActualFiniteChronologicalHistory
  HironakaG4ProcessedMaskRestriction HironakaG4OrderedProcessedMaskHistory
  HironakaG4OrderedProcessedMaskRebase HironakaActualProcessedMaskControlledSum
  CanonicalCentres InvDomainTowerAlong IdealWeightPowers
open ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ} {X Y : CMfd.{u} n} {ι : Type v}

private abbrev ref (A : CMfd.{u} n) := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) A ∞

private theorem processed_mask_index_change (W : Set X) (T : BlowupTower X Y)
    {E F : List (Set X)} (P : Finset (Fin E.length)) (h : E = F) :
    processedMaskMarked W F T (P.map (finCongr (congrArg List.length h)).toEmbedding) =
      processedMaskMarked W E T P := by
  subst F
  simp

set_option maxHeartbeats 650000 in
/-- After literal base restriction, all labels remain and the resulting
phase factorization is isomorphic to the literal physical restriction. -/
theorem ordered_processed_restrict (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (mask : ι → Finset (Fin E.length)) (O : Opens X) :
    ∀ (L : List ι) {Z : CMfd.{u} n} (Q : BlowupTower Y Z),
      let v := (Subtype.val : O → X)
      let EO := E.map (v ⁻¹' ·)
      let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
      IsGeoTestTower (geometricTemplate W []) (T.append Q) →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) →
      OrderedProcessedMaskHistory hn W E T mask Q L →
      ∃ (Z₀ : CMfd.{u} n) (Q₀ : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z₀)
        (χ : Z₀ ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage (T.append Q) O)),
        IsTowerIso (ref (CMfd.of (n := n) O)) ((restrict O T).append Q₀)
          (restrict O (T.append Q)) χ ∧
        OrderedProcessedMaskHistory hn (v ⁻¹' W) EO (restrict O T)
          (fun a => (mask a).map e.toEmbedding) Q₀ L := by
  let v := (Subtype.val : O → X)
  let WO := v ⁻¹' W
  let EO := E.map (v ⁻¹' ·)
  let e : Fin E.length ≃ Fin EO.length := finCongr (List.length_map _).symm
  let T₀ := restrict O T
  have hWO : IsClosedSubmanifold n WO := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O
  have hEO : IsSNCDivisor n EO := isSNCDivisor_map_preimage
    (pullsBackCoordinates_val (n := n) O) continuous_subtype_val hE
  have hDenseO : WO ⊆ closure (WO \ ⋃ H ∈ EO,H) := open_full_density hdense O
  dsimp only
  intro L
  induction L with
  | nil =>
    intro Z Q _hTest _hFull hQ
    cases hQ
    exact ⟨_,.refl,ref _,IsTowerIso.refl_self T₀,.nil⟩
  | cons label L ih =>
    intro Z Q hTest hFull hQ
    cases hQ with
    | @snoc A Z P _ _ S hPrev hBlock =>
      rw [←BlowupTower.append_assoc] at hTest hFull
      let R := T.append P
      let M := processedMaskMarked W E R (mask label)
      let U := openPreimage R O
      let ν := (Subtype.val : U → A)
      let M₀ := MarkedIdeal.pullback ν M
      have hPrevTest := ((isGeoTestTower_append_iff _ R S).mp hTest).1
      have hPrevFull := ((isGeoTestTower_append_iff _ R S).mp hFull).1
      obtain ⟨A₀,P₀,χ,hχ,hHist⟩ := ih P hPrevTest hPrevFull hPrev
      let S₀ := transport χ (restrict U S)
      have hSiso := transport_isTowerIso χ (restrict U S)
      have hR₀Test := isGeoTestTower_restrict O hW isCoherent_unitIdeal R hPrevTest
      rw [template_pullback (X := X) (Y := CMfd.of (n := n) O),List.map_nil] at hR₀Test
      have hR₀Full := isGeoTestTower_restrict O isClosedSubmanifold_univ isCoherent_unitIdeal R hPrevFull
      rw [template_pullback (X := X) (Y := CMfd.of (n := n) O),preimage_univ] at hR₀Full
      have hId₀ : processedMaskMarked WO EO (restrict O R) ((mask label).map e.toEmbedding) = M₀ :=
        ((processed_mask_matrix_restrict hn hW hE hdense R hPrevTest hPrevFull O).1 (mask label))
      have hId := processed_mask_pullback_of_isTowerIso hn hWO hEO hDenseO
        (restrict O R) hR₀Test hR₀Full hχ ((mask label).map e.toEmbedding)
      have hEOId : EO.map ((ref (CMfd.of (n := n) O)) ⁻¹' ·) = EO := by
        change EO.map (fun A => id ⁻¹' A) = EO
        exact List.map_id EO
      have hNew : processedMaskMarked WO EO (T₀.append P₀) ((mask label).map e.toEmbedding) =
          MarkedIdeal.pullback χ M₀ := by
        rw [←hId₀]
        dsimp only at hId
        have hChange := processed_mask_index_change WO (T₀.append P₀)
          ((mask label).map e.toEmbedding) hEOId.symm
        exact hChange.symm.trans hId
      have hDom₀ : IsInvDomain (n+1) M₀ := isInvDomain_pullback_val U hBlock.1
      have hCan₀ := Seq.ResolutionInvariantExt.isCanonical_restrict (invFamily hn (n+1)) hBlock.1 U S hBlock.2.1
      have hRes₀ := isGeoResolution_restrict U hBlock.1.isWellFormed.isClosedSubmanifold_N
        hBlock.1.isWellFormed.isCoherent hBlock.2.2
      have hCan := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso
        (invFamily hn (n+1)) hDom₀ χ hSiso hCan₀
      have hRes := (IsTowerIso.isGeoResolution_iff χ hDom₀.isWellFormed.isClosedSubmanifold_N
        hDom₀.isWellFormed.isCoherent hSiso).mpr hRes₀
      let η := S₀.back.trans (opensCongr (openPreimage_append R S O).symm).symm
      have hAppend := (hχ.append hSiso).trans (isTowerIso_restrict_append O R S).symm
      rw [←BlowupTower.append_assoc T P S]
      refine ⟨S₀.target,P₀.append S₀.tower,η,?_,OrderedProcessedMaskHistory.snoc label _ hHist ?_⟩
      · rw [←BlowupTower.append_assoc]
        simpa only [Diffeomorph.refl_trans,Diffeomorph.symm_refl] using hAppend
      · dsimp only
        rw [hNew]
        exact ⟨isInvDomain_pullback χ hDom₀,hCan,hRes⟩

end
end Hironaka.HironakaG4OrderedProcessedMaskRestriction
