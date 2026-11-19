import Hironaka.Resolution.HironakaActualRetainedBoundaryMaskBlock
import Hironaka.Resolution.HironakaG34JointMaskEquivariance
import Hironaka.Resolution.HironakaG34NonPureLowDim
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal

/-! Actual fixed-profile joint sharp service on an open neighbourhood of a
compact enclosure. The complete profile cosupport may be noncompact. -/

set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u

namespace Hironaka.HironakaG4LocalJointProfileMask
noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  HomogenizedGlueingTower MarkedIdealBiholomorphism MarkedIdealRestrictOpen
  HironakaActualRetainedBoundaryJointStep HironakaActualRetainedBoundaryMaskBlock
  HironakaActualRetainedBornResidualSeed HironakaActualRetainedBornResidualOpen
  HironakaG34JointMaskEquivariance HironakaG34NonPureLowDim
  HironakaG4PreparedCentreCoordinates HironakaActualFiniteMarkedSumHistories
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualDistinctCountOpenNaturality
  HironakaSharpOriginalProductTraceOrder HironakaG4SharpBadFootprint HironakaG4CompactWholeMonomialMaskPhase
  RelativePrincipalizationSpan DivisorExponentAlong GermIdealOrder NonmonomialOrderLocal
  RestrictEmptyTower HironakaEmbeddedResolutionLocal
open ResolutionInvariantSpec (IsCanonical IsInvDomain)

variable {n : ℕ} {X : CMfd.{u} n}

private theorem cast_toList_map {a b : ℕ} (h : a = b) (P : Finset (Fin a)) :
    (P.map (finCongr h).toEmbedding).toList = P.toList.map (finCongr h) := by
  subst b
  change (P.map (Equiv.refl (Fin a)).toEmbedding).toList = P.toList.map id
  simp

private theorem count_fin_cast {a b : ℕ} (h : a = b)
    (I : Fin b → GermIdeal n X) (x : X) :
    actualDistinctProperCount (fun i : Fin a => I ((finCongr h) i)) x =
      actualDistinctProperCount I x := by
  subst b
  rfl

private theorem unit_mem_pullback_val_iff (U : Opens X) {J : GermIdeal n X}
    (hJ : J.IsCoherent) (x : U) :
    (GermIdeal.pullback (m := n) (Subtype.val : U → X) J).mem x 1 ↔ J.mem x.val 1 := by
  have hOne : extendOpens U (1 : U → ℂ) =ᶠ[𝓝 x.val] (1 : X → ℂ) :=
    (eventually_nhds_val_iff U).mpr (Eventually.of_forall fun y => by simp)
  rw [mem_pullback_val_iff U hJ]
  exact ⟨fun h => HomogenizedIdeal.mem_congr hJ h hOne,
    fun h => HomogenizedIdeal.mem_congr hJ h hOne.symm⟩


/-- Pull back the literal joint record to an open chart, retaining the
ordered original row positions under the canonical index cast. -/
theorem jointProfileMarked_pullback_open_embedding (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ G ∈ old ++ born,G)) {Y : CMfd.{u} n}
    (f : Y → X) (hf : HironakaBaseChange.IsOpenHoloEmbedding n f)
    (q : ℕ) (P : Finset (Fin old.length)) :
    let O := old.map (f ⁻¹' ·)
    let e : Fin old.length ≃ Fin O.length := finCongr (List.length_map _).symm
    MarkedIdeal.pullback f (jointProfileMarked N old born q P) =
      jointProfileMarked (f ⁻¹' N) O (born.map (f ⁻¹' ·)) q (P.map e.toEmbedding) := by
  intro O e
  rw [pullback_jointProfileMarked hf hn hN hE hTr hdense]
  unfold jointProfileMarked
  congr 1
  rw [cast_toList_map (List.length_map _).symm P,List.map_map]
  apply List.map_congr_left
  intro i _hi
  simp only [Function.comp_apply,canonicalFactorMarked,oldMonomialPart,oldTraceIdeal,factorOf]
  rw [show O.get ((finCongr _) i) = f ⁻¹' old.get i by simp [O]]

set_option maxHeartbeats 500000 in
/-- Restrict the actual fixed-profile hypotheses from an ambient open to
its native marked records, keeping all original old-label positions. -/
theorem retained_joint_profile_open_data (hn : 0 < n) {N : Set X}
    {old born : List (Set X)} (hN : IsClosedSubmanifold n N)
    (hE : IsSNCDivisor n (old ++ born)) (hTr : IsTransverse n N born)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (U : Opens X) (profile : Fin old.length → ℕ) (q : ℕ) (hsum : ∑ i,profile i=q)
    (hOrd : ∀ x ∈ U,x ∈ N → ∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCount : ∀ x ∈ U,x ∈ N → ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      actualDistinctProperCount (oldResidualPart N old born) x < q)
    (P : Finset (Fin old.length)) (hP : ∀ i ∈ P,profile i=0)
    (hBound : ∀ x ∈ U,x ∈ N → ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      (inactiveCanonicalRows N old born profile x).card ≤ P.card) :
    let XU := CMfd.of (n := n) U
    let NU := (Subtype.val : U → X) ⁻¹' N
    let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
    let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
    let e : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
    let pU := fun j => profile (e.symm j)
    let PU := P.map e.toEmbedding
    IsClosedSubmanifold n NU ∧ IsSNCDivisor n (OU ++ BU) ∧ IsTransverse n NU BU ∧
    NU ⊆ closure (NU \ ⋃ H ∈ OU ++ BU,H) ∧
    MarkedIdeal.pullback (Subtype.val : U → X) (jointProfileMarked N old born q P) =
      jointProfileMarked (X := XU) NU OU BU q PU ∧
    (∑ j,pU j) = q ∧ (∀ j ∈ PU,pU j=0) ∧
    (∀ x ∈ NU,∀ j,ordinaryTraceOrder NU (oldResidualPart (X := XU) NU OU BU j) x ≤ pU j) ∧
    (∀ x ∈ NU,ordinaryTraceOrder NU (canonicalProductMarked (X := XU) NU OU BU q).ideal x=q →
      actualDistinctProperCount (oldResidualPart (X := XU) NU OU BU) x < q) ∧
    ∀ x ∈ NU,ordinaryTraceOrder NU (canonicalProductMarked (X := XU) NU OU BU q).ideal x=q →
      (inactiveCanonicalRows (X := XU) NU OU BU pU x).card ≤ PU.card := by
  classical
  let M := jointProfileMarked N old born q P
  let NU := (Subtype.val : U → X) ⁻¹' N
  let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let e : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
  let pU := fun j => profile (e.symm j)
  let PU := P.map e.toEmbedding
  have hNU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
  have hEU : IsSNCDivisor n (OU ++ BU) := by
    simpa only [List.map_append] using isSNCDivisor_map_preimage
      (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hTU : IsTransverse n NU BU := isTransverse_preimage (pullsBackCoordinates_val U) hTr
  have hDenseU : NU ⊆ closure (NU \ ⋃ H ∈ OU ++ BU,H) := by
    simpa only [List.map_append] using open_full_density hdense U
  have hGet (i : Fin old.length) : OU.get (e i) = (Subtype.val : U → X) ⁻¹' old.get i := by
    simp [OU, e]
  have hJoint : MarkedIdeal.pullback (Subtype.val : U → X) M =
      jointProfileMarked (X := CMfd.of (n := n) U) NU OU BU q PU :=
    jointProfileMarked_pullback_open_embedding (Y := CMfd.of (n := n) U) hn hN hE hTr hdense
      (Subtype.val : U → X) (HironakaBaseChange.isOpenHoloEmbedding_val U) q P
  have hSumU : ∑ j,pU j = q := (e.symm.sum_comp profile).trans hsum
  have hPU : ∀ j ∈ PU,pU j = 0 := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    simpa only [pU, Equiv.toEmbedding_apply, e.symm_apply_apply] using hP i hi
  have hSeed (i : Fin old.length) := retainedResidualMarked_geometry hn hN hE hTr hdense i
  have hRow (i : Fin old.length) :
      GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i) =
        oldResidualPart (X := CMfd.of (n := n) U) NU OU BU (e i) := by
    exact congrArg (fun L : MarkedIdeal n U => L.ideal)
      (retainedResidualMarked_pullback_open hn hN hE hTr hdense U i)
  have hOrdU : ∀ x ∈ NU,∀ j,ordinaryTraceOrder NU
      (oldResidualPart (X := CMfd.of (n := n) U) NU OU BU j) x ≤ pU j := by
    intro x hx j
    let i := e.symm j
    have h := nmOrd_pullback_val hn (ordinaryTraceMarked_isWellFormed hN (hSeed i).1.isCoherent)
      (hSeed i).2.1 U x
    change ordinaryTraceOrder (X := CMfd.of (n := n) U) NU
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i)) x =
        ordinaryTraceOrder N (oldResidualPart N old born i) x.val at h
    rw [hRow, show e i = j from e.apply_symm_apply j] at h
    exact h.trans_le (hOrd x.val x.property hx i)
  have hProd := retained_product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial
  have hProdCoh : (canonicalProductMarked N old born q).ideal.IsCoherent := hProd.1
  have hProdNZ : ∀ x ∈ N,IsNonzeroAlongAt N (canonicalProductMarked N old born q).ideal x := hProd.2.1
  have hProdOpen := canonicalProductMarked_pullback_open hn hN hE hTr hdense q U
  let RP := canonicalProductMarked N old born q
  let RPU := canonicalProductMarked (X := CMfd.of (n := n) U) NU OU BU q
  have hProdOrder (x : U) : ordinaryTraceOrder NU RPU.ideal x = ordinaryTraceOrder N RP.ideal x.val := by
    have h := nmOrd_pullback_val hn (ordinaryTraceMarked_isWellFormed hN hProdCoh) hProdNZ U x
    change ordinaryTraceOrder (X := CMfd.of (n := n) U) NU
      (GermIdeal.pullback (m := n) (Subtype.val : U → X) RP.ideal) x =
        ordinaryTraceOrder N RP.ideal x.val at h
    rw [show GermIdeal.pullback (m := n) (Subtype.val : U → X) RP.ideal = RPU.ideal from
      congrArg (fun L : MarkedIdeal n U => L.ideal) hProdOpen] at h
    exact h
  have hCountU : ∀ x ∈ NU,ordinaryTraceOrder NU RPU.ideal x=q →
      actualDistinctProperCount (oldResidualPart (X := CMfd.of (n := n) U) NU OU BU) x < q := by
    intro x hx hxq
    have h := actual_distinct_proper_count_open (oldResidualPart N old born)
      (fun i => (hSeed i).1.isCoherent) U x
    rw [show (fun i => GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldResidualPart N old born i)) =
      (fun i => oldResidualPart (X := CMfd.of (n := n) U) NU OU BU (e i)) from funext hRow] at h
    have hCast := count_fin_cast (X := CMfd.of (n := n) U) (List.length_map (as := old) _).symm
      (oldResidualPart (X := CMfd.of (n := n) U) NU OU BU) x
    rw [←hCast, h]
    exact hCount x.val x.property hx ((hProdOrder x).symm.trans hxq)
  have hMon (x : U) (i : Fin old.length) :
      (oldMonomialPart (X := CMfd.of (n := n) U) NU OU BU (e i)).mem x 1 ↔ (oldMonomialPart N old born i).mem x.val 1 := by
    have hPart := congrArg (fun L : MarkedIdeal n U => L.ideal)
      (pullback_factorOf (Y := CMfd.of (n := n) U) (f := (Subtype.val : U → X))
        (HironakaBaseChange.isOpenHoloEmbedding_val U) born hN
        (VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn
          (isSNCDivisor_of_sublist hE (List.sublist_append_left _ _)) i)))
    have hPart' : GermIdeal.pullback (m := n) (Subtype.val : U → X) (oldMonomialPart N old born i) =
        oldMonomialPart (X := CMfd.of (n := n) U) NU OU BU (e i) := by
      unfold oldMonomialPart oldTraceIdeal
      rw [hGet]
      exact hPart
    rw [←hPart']
    exact unit_mem_pullback_val_iff U (actual_old_parts_geometry hn hN hE hTr hdense i).2.2.2.2.1 x
  have hBoundU : ∀ x ∈ NU,ordinaryTraceOrder NU RPU.ideal x=q →
      (inactiveCanonicalRows (X := CMfd.of (n := n) U) NU OU BU pU x).card ≤ PU.card := by
    intro x hx hxq
    have hMask : inactiveCanonicalRows (X := CMfd.of (n := n) U) NU OU BU pU x =
        (inactiveCanonicalRows N old born profile x.val).map e.toEmbedding := by
      ext j
      obtain ⟨i,rfl⟩ := e.surjective j
      rw [show e i = e.toEmbedding i from rfl, Finset.mem_map_equiv]
      change e i ∈ inactiveCanonicalRows (X := CMfd.of (n := n) U) NU OU BU pU x ↔
        i ∈ inactiveCanonicalRows N old born profile x.val
      simp only [inactiveCanonicalRows, Finset.mem_filter, Finset.mem_univ, true_and, pU,
        e.symm_apply_apply, hMon]
    rw [hMask, Finset.card_map, show PU.card = P.card from Finset.card_map e.toEmbedding]
    exact hBound x.val x.property hx ((hProdOrder x).symm.trans hxq)
  exact ⟨hNU,hEU,hTU,hDenseU,hJoint,hSumU,hPU,hOrdU,hCountU,hBoundU⟩

set_option maxHeartbeats 500000 in
/-- One actual finite sharp joint-mask block around an arbitrary compact
enclosure already lying in a fixed profile domain. The original product
cosupport need not be compact. -/
theorem exists_actual_retained_joint_mask_locally_on_compact
    (hn : 0 < n) {N : Set X} {old born : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hE : IsSNCDivisor n (old ++ born))
    (hTr : IsTransverse n N born) (hdense : N ⊆ closure (N \ ⋃ H ∈ old ++ born,H))
    (profile : Fin old.length → ℕ) (q : ℕ) (hq : 1 ≤ q) (hsum : ∑ i, profile i = q)
    (hOrd : ∀ x ∈ N,∀ i,ordinaryTraceOrder N (oldResidualPart N old born i) x ≤ profile i)
    (hCount : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      actualDistinctProperCount (oldResidualPart N old born) x < q)
    (P : Finset (Fin old.length)) (hP : ∀ i ∈ P,profile i = 0)
    (hBound : ∀ x ∈ N,ordinaryTraceOrder N (canonicalProductMarked N old born q).ideal x=q →
      (inactiveCanonicalRows N old born profile x).card ≤ P.card)
    {K : Set X} (hK : IsCompact K) :
    ∃ U : Opens X, K ⊆ U ∧ ∃ (Z : CMfd.{u} n) (R : BlowupTower (CMfd.of (n := n) U) Z),
      let NU := (Subtype.val : U → X) ⁻¹' N
      let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
      let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
      let e : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
      let pU := fun j => profile (e.symm j)
      let PU := P.map e.toEmbedding
      let M := MarkedIdeal.pullback (Subtype.val : U → X) (jointProfileMarked N old born q P)
      IsCanonical M ((CanonicalCentres.invFamily hn (n+1)).inv M) R ∧
      IsGeoResolution M R ∧
      RetainedJointMaskResult NU OU BU pU q PU R ∧
      CentresOver ((Subtype.val : U → X) ⁻¹' (canonicalProductMarked N old born q).cosupp) R ∧
      CentresOver ((Subtype.val : U → X) ⁻¹' (jointProfileMarked N old born q P).cosupp) R := by
  classical
  let M := jointProfileMarked N old born q P
  have hDom : IsInvDomain (n+1) M := (actual_retained_boundary_joint_step
    (Y := X) hn hN hE hTr hdense profile q hq hsum hOrd P hP hBound).1
  obtain ⟨U, hKU, Z, R, hCan, hRes⟩ := exists_local_resolution_isCanonical
    (CanonicalCentres.invFamily hn (n+1)) hDom hK
  let NU := (Subtype.val : U → X) ⁻¹' N
  let OU := old.map ((Subtype.val : U → X) ⁻¹' ·)
  let BU := born.map ((Subtype.val : U → X) ⁻¹' ·)
  let e : Fin old.length ≃ Fin OU.length := finCongr (List.length_map _).symm
  let pU := fun j => profile (e.symm j)
  let PU := P.map e.toEmbedding
  obtain ⟨hNU,hEU,hTU,hDenseU,hJoint,hSumU,hPU,hOrdU,hCountU,hBoundU⟩ :=
    retained_joint_profile_open_data hn hN hE hTr hdense U profile q hsum
      (fun x _ => hOrd x) (fun x _ => hCount x) P hP (fun x _ => hBound x)
  have hResOriginal := hRes
  rw [hJoint] at hRes
  let RP := canonicalProductMarked N old born q
  let RPU := canonicalProductMarked (X := CMfd.of (n := n) U) NU OU BU q
  have hProdOpen := canonicalProductMarked_pullback_open hn hN hE hTr hdense q U
  have hProdCoh : RP.ideal.IsCoherent :=
    (retained_product_geometry hn hN hE hTr hdense q (.refl : BlowupTower X X) trivial).1
  have hRead := retained_boundary_joint_mask_terminal_readout hn hNU hEU hTU hDenseU pU q hq hSumU
    hOrdU hCountU PU hPU hBoundU R hRes
  have hOver := hRead.2.1
  have hCos : RPU.cosupp = (Subtype.val : U → X) ⁻¹' RP.cosupp := by
    rw [show RPU = MarkedIdeal.pullback (Subtype.val : U → X) RP from hProdOpen.symm]
    exact cosupp_pullback_val RP (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hProdCoh h) U
  rw [hCos] at hOver
  have hJointWF := hDom.isWellFormed
  have hJointCos : (jointProfileMarked (X := CMfd.of (n := n) U) NU OU BU q PU).cosupp =
      (Subtype.val : U → X) ⁻¹' M.cosupp := by
    rw [←hJoint]
    exact cosupp_pullback_val M (fun _ _ h => GermIdeal.IsCoherent.holomorphicAt_mem hJointWF.isCoherent h) U
  have hJointWU : (jointProfileMarked (X := CMfd.of (n := n) U) NU OU BU q PU).IsWellFormed :=
    hJoint ▸ (InvDomainTowerAlong.isInvDomain_pullback_val U hDom).isWellFormed
  have hJointOver := HironakaAdmissibleSequence.centresOver_cosupp
    (jointProfileMarked (X := CMfd.of (n := n) U) NU OU BU q PU)
    hJointWU.isClosedSubmanifold_N hJointWU.isCoherent R hRes.1
  rw [hJointCos] at hJointOver
  exact ⟨U, hKU, Z, R, hCan, hResOriginal, hRead, hOver,hJointOver⟩

end
end Hironaka.HironakaG4LocalJointProfileMask
