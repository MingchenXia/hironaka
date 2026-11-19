import Hironaka.Resolution.HironakaG3StoppedTransport
import Hironaka.Resolution.HironakaG3StoppedBoundaryAmbientBridge
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3LocalStoppedCoupledProducer
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdealTowerTransport
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism NormalCrossings NormalCrossingsInvariance
  SubmanifoldChartedSpace HironakaActualNativeSectionFiniteHistory HironakaDisjointNativeOpenLift
  HironakaDisjointNativeReferenceWindow HironakaDisjointFiniteControlledHistory
  HironakaOriginalBoundaryEmptyBaseComparison HironakaG3RStoppedOverlap HironakaG3StoppedTransport
  GermIdealPullbackCalculus HironakaSmoothSubmersionOrderedChoiceImageTrace CanonicalCentres MaxLocusLocal
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

/-- A stopped native history over an ambient open produces its actual
mark-one coupled ambient history, preserving the stopped history on return. -/
theorem local_coupled_of_stopped
    {d t : ℕ} (ht : 0 < t) {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (J : GermIdeal (d+t) X) (hJ : J.IsCoherent) (hNorm : (vanishingIdeal (n := d+t) N).Le J) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (V : Set (nativeManifold (Nat.le_add_right d t) N hN))
      (_hTrace : GermIdeal.pullback (m := d) (Subtype.val : N → X) J = vanishingIdeal (n := d) V)
      (_hdom : IsInvDomain d (⟨univ, B.map ((Subtype.val : N → X) ⁻¹' ·), vanishingIdeal (n := d) V, 1⟩ :
        MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)))
      (O : Opens (nativeManifold (Nat.le_add_right d t) N hN)) (U : Opens X)
      {Q : CMfd.{0} d} (S : BlowupTower (CMfd.of (n := d) (nativeWindow (Nat.le_add_right d t) N hN U)) Q),
      stoppedClass (⟨univ, B.map ((Subtype.val : N → X) ⁻¹' ·), vanishingIdeal (n := d) V, 1⟩ :
        MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)) O
        (nativeWindow (Nat.le_add_right d t) N hN U) Q S →
      letI := chartedSpace (Nat.le_add_right d t) (openSection_regular hN U)
      letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) (openSection_regular hN U)
      ∃ (R : CMfd.{0} d)
        (T : BlowupTower (nativeManifold (Nat.le_add_right d t) (openSection N U) (openSection_regular hN U)) R)
        (Y : CMfd.{0} (d+t)) (A : BlowupTower (CMfd.of (n := d+t) U) Y) (η : R → Y),
        let J_U := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) J
        let B_U := B.map ((Subtype.val : U → X) ⁻¹' ·)
        let M_U := fullMarked (B_U.map ((Subtype.val : openSection N U → U) ⁻¹' ·))
          (GermIdeal.pullback (m := d) (Subtype.val : openSection N U → U) J_U)
        IsInvDomain d M_U ∧ IsGeoTestTower M_U T ∧ IsGeoTestTower (fullMarked B_U J_U) A ∧
        CoupledHistory (openSection N U) B_U J_U (Subtype.val : openSection N U → U) M_U T A η ∧
        stoppedClass (⟨univ, B.map ((Subtype.val : N → X) ⁻¹' ·), vanishingIdeal (n := d) V, 1⟩ :
          MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN)) O
          (nativeWindow (Nat.le_add_right d t) N hN U) _
          (transport (windowEquiv (Nat.le_add_right d t) N hN hNc U).symm T).tower := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  intro V hTrace hdom O U Q S hStop
  let N_U := openSection N U
  let hNU := openSection_regular hN U
  let := chartedSpace (Nat.le_add_right d t) hNU
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hNU
  let A := nativeWindow (Nat.le_add_right d t) N hN U
  let e := windowEquiv (Nat.le_add_right d t) N hN hNc U
  let K : MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN) :=
    ⟨univ, B.map ((Subtype.val : N → X) ⁻¹' ·), vanishingIdeal (n := d) V, 1⟩
  let K_A := MarkedIdeal.pullback (Subtype.val : A → nativeManifold (Nat.le_add_right d t) N hN) K
  let J_U := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) J
  let B_U := B.map ((Subtype.val : U → X) ⁻¹' ·)
  let M_U := fullMarked (B_U.map ((Subtype.val : N_U → U) ⁻¹' ·))
    (GermIdeal.pullback (m := d) (Subtype.val : N_U → U) J_U)
  have hKA : IsInvDomain d K_A := InvDomainTowerAlong.isInvDomain_pullback_val A hdom
  have hJU : J_U.IsCoherent := isCoherent_pullback contMDiff_subtype_val hJ
  have hNormU : (vanishingIdeal (n := d+t) N_U).Le J_U := by
    have h : (GermIdeal.pullback (m := d+t) (Subtype.val : U → X) (vanishingIdeal (n := d+t) N)).Le J_U :=
      pullback_le_pullback hNorm
    rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal U N] at h
    exact h
  have hBU : IsSNCDivisor (d+t) B_U :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hB
  have hTrU : IsTransverse (d+t) N_U B_U := isTransverse_preimage (pullsBackCoordinates_val U) hTrans
  have hHol : ∀ x g, J.mem x g → HolomorphicAt (d+t) g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hJ hg
  have hHolV : ∀ x g, (vanishingIdeal (n := d) V).mem x g → HolomorphicAt d g x := fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hdom.isWellFormed.isCoherent hg
  have hMarked : MarkedIdeal.pullback e K_A = M_U := by
    apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
    · simp [MarkedIdeal.pullback,K_A,K,M_U,fullMarked]
    · simp only [MarkedIdeal.pullback,K_A,K,M_U,fullMarked,B_U,List.map_map,Function.comp_def]
      rfl
    · change GermIdeal.pullback (m := d) e
          (GermIdeal.pullback (m := d) (Subtype.val : A → nativeManifold (Nat.le_add_right d t) N hN)
            (vanishingIdeal (n := d) V)) =
        GermIdeal.pullback (m := d) (Subtype.val : N_U → U)
          (GermIdeal.pullback (m := d+t) (Subtype.val : U → X) J)
      calc
        _ = GermIdeal.pullback (m := d)
            ((Subtype.val : A → nativeManifold (Nat.le_add_right d t) N hN) ∘ e) (vanishingIdeal (n := d) V) :=
          (whole_pullback_comp contMDiff_subtype_val e.contMDiff (vanishingIdeal (n := d) V) hHolV).symm
        _ = GermIdeal.pullback (m := d)
            ((Subtype.val : N → X) ∘ ((Subtype.val : A → nativeManifold (Nat.le_add_right d t) N hN) ∘ e)) J := by
          rw [← hTrace]
          exact (whole_pullback_comp (contMDiff_val (Nat.le_add_right d t) hN)
            (contMDiff_subtype_val.comp e.contMDiff) J hHol).symm
        _ = GermIdeal.pullback (m := d) ((Subtype.val : U → X) ∘ (Subtype.val : N_U → U)) J := by
          congr 1
        _ = _ := whole_pullback_comp contMDiff_subtype_val (contMDiff_val (Nat.le_add_right d t) hNU) J hHol
    · rfl
  have hcS : IsCanonical K_A ((canonicalInvariant d).inv K_A) S := hStop.1
  obtain ⟨hdomT,hcanT,_hi,_hproj,_hrec,_hmax,_hres,_ha⟩ := canonical_transport_dictionary K_A hKA e S hcS
  rw [hMarked] at hdomT hcanT
  have htest : IsGeoTestTower M_U (transport e S).tower :=
    (canonicalInvariant d).isInvValue.isGeoTestTower_of_isCanonical hdomT _ hcanT
  obtain ⟨Y,A',η,hAT,_hlen,hCoupled,_hEnd⟩ :=
    exists_actual_finite_controlled_history (hNc.preimage continuous_subtype_val) hNU ht hBU hTrU J_U hJU hNormU
      (transport e S).tower htest
  change IsStopped K_A (nestedOpens A O) S at hStop
  have hround := stopped_roundtrip K_A hKA e (nestedOpens A O) S hStop
  exact ⟨_,(transport e S).tower,Y,A',η,hdomT,htest,hAT,hCoupled,hround⟩

end
end Hironaka.HironakaG3LocalStoppedCoupledProducer
