import Hironaka.Resolution.HironakaG3CoupledNonerasure
import Hironaka.Resolution.HironakaG3StoppedCoupledGeometry
import Hironaka.Resolution.HironakaG3CoupledAvoidance
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3StoppedCoupledNonerasure
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal RestrictEmptyTower
  HironakaDisjointFiniteControlledHistory HironakaG3CoupledAvoidance HironakaG3CoupledNonerasure
  HironakaG3RBoundaryEmbedded HironakaG3RStoppedOverlap HironakaG3StoppedTransport
  BlowupTowerIsomorphism BlowupTowerIsoTail MarkedIdealTowerTransport MarkedIdealBiholomorphism
  NormalCrossings CanonicalCentres HironakaOriginalBoundaryEmptyBaseComparison
  SubmanifoldChartedSpace HironakaActualNativeSectionFiniteHistory HironakaDisjointNativeOpenLift
  HironakaDisjointNativeReferenceWindow HironakaActualNativeInvariantDomain MaxLocusLocal

/-- Every actual native-stopped coupled chart retains its entire target under the conventional ambient strict transform. -/
theorem actual_stopped_coupled_nonerasure
    {d t : ℕ} (_hd : 0 < d) (ht : 0 < t) {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (J : GermIdeal (d+t) X) :
    letI := chartedSpace (Nat.le_add_right d t) hN
    letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
    ∀ (V : Set (nativeManifold (Nat.le_add_right d t) N hN))
      (_hVa : IsComplexAnalyticSubset (n := d) V)
      {r : ℕ} (_hr : r < d) (_hpure : V ⊆ closure (regularLocus (n := d) V r))
      (_hAvoid : V ⊆ closure (V \ ⋃ H ∈ B.map ((Subtype.val : N → X) ⁻¹' ·), H))
      (U : Opens X),
      letI := chartedSpace (Nat.le_add_right d t) (openSection_regular hN U)
      letI := isComplexManifold_chartedSpace (Nat.le_add_right d t) (openSection_regular hN U)
      ∀ {R : CMfd.{0} d} (T : BlowupTower
        (nativeManifold (Nat.le_add_right d t) (openSection N U) (openSection_regular hN U)) R)
        {Y : CMfd.{0} (d+t)} (A : BlowupTower (CMfd.of (n := d+t) U) Y) (η : R → Y),
        let J_U := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) J
        let B_U := B.map ((Subtype.val : U → X) ⁻¹' ·)
        let M_U := fullMarked (B_U.map ((Subtype.val : openSection N U → U) ⁻¹' ·))
          (GermIdeal.pullback (m := d) (Subtype.val : openSection N U → U) J_U)
        CoupledHistory (openSection N U) B_U J_U (Subtype.val : openSection N U → U) M_U T A η →
        stoppedClass (⟨univ, B.map ((Subtype.val : N → X) ⁻¹' ·), vanishingIdeal (n := d) V, 1⟩ :
          MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN))
          (bdryOpen V r (B.map ((Subtype.val : N → X) ⁻¹' ·)))
          (nativeWindow (Nat.le_add_right d t) N hN U) _
          (transport (windowEquiv (Nat.le_add_right d t) N hN hNc U).symm T).tower →
        let W_U := (Subtype.val : U → X) ⁻¹' ((Subtype.val : N → X) '' V)
        A.proj '' strictTransform (d+t) A.proj W_U = W_U := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  intro V hVa r hr hpure hAvoid U
  let N_U := openSection N U
  let hNU := openSection_regular hN U
  let := chartedSpace (Nat.le_add_right d t) hNU
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hNU
  intro R T Y A η
  dsimp only
  intro hC hStop
  let E := B.map ((Subtype.val : N → X) ⁻¹' ·)
  let A0 := nativeWindow (Nat.le_add_right d t) N hN U
  let e := windowEquiv (Nat.le_add_right d t) N hN hNc U
  let K : MarkedIdeal d (nativeManifold (Nat.le_add_right d t) N hN) :=
    ⟨univ,E,vanishingIdeal (n := d) V,1⟩
  let K_A := MarkedIdeal.pullback (Subtype.val : A0 → nativeManifold (Nat.le_add_right d t) N hN) K
  let V_A : Set (CMfd.of (n := d) A0) := (Subtype.val : A0 → nativeManifold (Nat.le_add_right d t) N hN) ⁻¹' V
  let O_A := nestedOpens A0 (bdryOpen V r E)
  let V_U := e ⁻¹' V_A
  let O_U := baseOpen e O_A
  have hE : IsSNCDivisor d E := isSNCDivisor_native_preimage (by omega) (Nat.le_add_right d t) hN hB hTrans
  have hdom := isInvDomain_bdry hVa hr hpure hE
  have hKA := InvDomainTowerAlong.isInvDomain_pullback_val A0 hdom
  change IsStopped K_A O_A (transport e.symm T).tower at hStop
  have hst := stopped_of_isTowerIso K_A hKA e O_A (transport_isTowerIso e.symm T).symm hStop
  have ha : CentresAvoid O_U T := hst.2.1
  have hdense : V ⊆ closure (V ∩ bdryOpen V r E) :=
    subset_closure_inter_bdryOpen hVa.isClosed hpure hE.1 hAvoid
  have hdenseA : V_A ⊆ closure (V_A ∩ (O_A : Set (CMfd.of (n := d) A0))) := by
    intro x hx
    exact (Set.ext_iff.mp (A0.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val (V ∩ (bdryOpen V r E : Set (nativeManifold (Nat.le_add_right d t) N hN)))) x).mp (hdense hx)
  have hdenseU : V_U ⊆ closure (V_U ∩ (O_U : Set _)) := by
    intro p hp
    have h := hdenseA hp
    exact (Set.ext_iff.mp (e.toHomeomorph.isOpenMap.preimage_closure_eq_closure_preimage
      e.contMDiff.continuous (V_A ∩ (O_A : Set (CMfd.of (n := d) A0)))) p).mp h
  have hclosedU : IsClosed V_U := (hVa.isClosed.preimage continuous_subtype_val).preimage e.contMDiff.continuous
  have hEmb : Topology.IsClosedEmbedding (Subtype.val : N_U → U) :=
    (hNc.preimage continuous_subtype_val).isClosedEmbedding_subtypeVal
  have heq := coupled_projection_strictTransform_eq hC hEmb V_U hclosedU O_U hdenseU ha
  have hImage : (Subtype.val : N_U → U) '' V_U =
      (Subtype.val : U → X) ⁻¹' ((Subtype.val : N → X) '' V) := by
    ext x
    constructor
    · rintro ⟨p,hp,rfl⟩
      exact ⟨(e p).val,hp,rfl⟩
    · rintro ⟨p,hp,hpx⟩
      have hpU : p.val ∈ U := hpx ▸ x.property
      refine ⟨⟨⟨p.val,hpU⟩,p.property⟩,?_,?_⟩
      · exact hp
      · exact Subtype.ext hpx
  rw [hImage] at heq
  exact heq

end
end Hironaka.HironakaG3StoppedCoupledNonerasure
