import Hironaka.Resolution.HironakaG4OriginalOrderBlock
import Hironaka.Resolution.HironakaG4EquimultipleRelativeOrder
import Hironaka.Resolution.HironakaG4RecordedTowerResidualCompatibility
import Hironaka.Resolution.HironakaG4IncidentOldBornStratumCentre
import Hironaka.Resolution.HironakaSharpActualMaximumMemberOrders
import Hironaka.Resolution.HironakaSharpActualCurveContactBudgetDomination

/-! Full original ambient boundary on one fixed initial product plateau.
Complete source-first proof: `hironaka-g4-original-plateau-history-compatibility.tex`.
Later lower plateaux with inherited unit residual rows are a separate problem. -/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators

universe u

namespace Hironaka.HironakaG4OriginalPlateauHistoryCompatibility

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MemberInterTowerAlong BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SimultaneousNormalCrossings
  HironakaG4OriginalOrderBlock HironakaG4EquimultipleRelativeOrder
  HironakaG4RecordedTowerResidualCompatibility HironakaG4IncidentOldBornStratumCentre
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualOriginalControlledHistory HironakaSharpActualOriginalDynamicStep
  HironakaSharpActualDynamicDistinctCentre
  HironakaSharpActualInitialFullCompatibility HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalProductTraceOrder
  HironakaSharpActualMaximumMemberOrders HironakaSharpActualCurveContactBudgetDomination
  HironakaSharpActualCurveWholeBoundaryTransversality HironakaCoherentTransformExtension
  HironakaSharpActualChronologicalStrictStep HironakaSharpActualCurveExceptionalDifference
  RelativePrincipalizationSpan RestrictedIdealExtension DivisorExponentAlong
  MonomialPartAlong GermIdealOrder InvertibleIdealQuotient IdealWeightPowers
  NonmonomialOrderLocal NonmonomialOrderCanonical NonmonomialOrderRegime HironakaSharpOriginalFirstDefectOpenNaturality
  MarkedIdealRestrictOpen CanonicalCentres HironakaAdmissibleSequence RestrictEmptyTower

open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem chronological_order_sum (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    {y : Y} (hy : y ∈ (geoTransformAlong (geometricTemplate W []) T).N) :
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) y =
      ∑ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y := by
  have hsum := (original_chronological_full_product_actual_geometry hn hW hE hdense T hT).2.2.2 y hy
  have hList : chronologicalMemberFamily W E T = List.ofFn
      (fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) := by
    unfold chronologicalMemberFamily
    conv_lhs => rw [←List.ofFn_get E,List.map_ofFn]
    rfl
  simpa only [hList,List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hsum

private theorem initial_product_order (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hx : x ∈ W) :
    ordinaryTraceOrder W (chronologicalMemberProduct W E (.refl : BlowupTower X X)) x =
      ordinaryTraceOrder W (originalMemberProduct E) x := by
  rw [initial_actual_product_eq_restrictOn_source hn hW hE]
  exact ordinaryTraceOrder_restrictOn_eq hW (isCoherent_originalMemberProduct hn hE)
    (fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hE hdense hy) hx

private theorem plateau_history_and_orders (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {q : ℕ} (hq : 1 ≤ q)
    (hbound : ∀ x ∈ W,ordinaryTraceOrder W (originalMemberProduct E) x ≤ q) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsGeoTestTower (originalMemberProductMarked W E q) T →
      CentresOrdGt (originalMemberProductMarked W E q) (q-1) T →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
        ∀ (i : Fin E.length) y,y ∈ (geoTransformAlong (geometricTemplate W []) T).N →
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤
          ordinaryTraceOrder W (originalRelativeMemberMarked W (E.get i)).ideal (T.proj y)
  | _,.refl,_hT,_hGt => ⟨trivial,fun _ _ _ => le_rfl⟩
  | _,.step T C π hπ,hT,hGt => by
    rename_i Z Y
    classical
    let M := originalMemberProductMarked W E q
    let A := geoTransformAlong (geometricTemplate W []) T
    let F := fun i : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    let F0 := fun i : Fin E.length => (originalRelativeMemberMarked W (E.get i)).ideal
    obtain ⟨hFull,hOrders⟩ := plateau_history_and_orders hn hW hE hdense hq hbound T hT.1 hGt.1
    have hw : M.IsWellFormed := ⟨hW,isCoherent_originalMemberProduct hn hE,
      isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hdom : IsInvDomain (n+1) M :=
      ⟨hw,fun x hx => by
        obtain ⟨d,hd⟩ := hW.2 x hx
        exact ⟨d,hd.1.trans (Nat.le_succ n),hd⟩,
        hq,fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
    have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong hdom T hT.1
    have hGeom := actual_original_test_history_template M hw T hT.1
    have hGeomStep := actual_original_test_history_template M hw (.step T C π hπ) hT
    have hRecorded := actual_recorded_tower_residual_dictionary hn hW hE hdense T hGeom hFull
    have hN : IsClosedSubmanifold n A.N := hRecorded.1
    have hCN : C ⊆ A.N := hGeomStep.2.subset_N
    have hFamily : ∀ i : Fin E.length,(F i).IsCoherent ∧
        (∀ y ∈ A.N,IsNonzeroAlongAt A.N (F i) y) ∧
        ∀ y ∈ A.N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
          ∀ g,(F i).mem y g ↔ HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) A.N (·=f) y g := by
      intro i
      obtain ⟨hNi,_hEi,_hdi,hwi,hnzi,hpri⟩ :=
        original_members_actual_finite_chronological_geometry hn hW hE hdense i T hGeom
      rw [hNi] at hnzi hpri
      exact ⟨hwi.isCoherent,hnzi,hpri⟩
    have hProjN {y : Y} (hy : y ∈ A.N) : T.proj y ∈ W := by
      apply strictAlong_subset_preimage T hW.1
      change y ∈ strictAlong T (geometricTemplate W []).N
      rw [←N_geoTransformAlong]
      exact hy
    have hSum (y : Y) (hy : y ∈ A.N) :
        ordinaryTraceOrder A.N (chronologicalMemberProduct W E T) y =
          ∑ i,ordinaryTraceOrder A.N (F i) y :=
      chronological_order_sum hn hW hE hdense T hGeom hy
    have hSum0 (x : X) (hx : x ∈ W) : (∑ i,ordinaryTraceOrder W (F0 i) x) ≤ q := by
      have hs0 : ordinaryTraceOrder W (chronologicalMemberProduct W E (.refl : BlowupTower X X)) x =
          ∑ i,ordinaryTraceOrder W (F0 i) x :=
        chronological_order_sum hn hW hE hdense (.refl : BlowupTower X X) (by trivial) hx
      rw [←hs0,initial_product_order hn hW hE hdense hx]
      exact hbound x hx
    have hSumLe (y : Y) (hy : y ∈ A.N) : (∑ i,ordinaryTraceOrder A.N (F i) y) ≤ q :=
      (Finset.sum_le_sum (fun i _ => hOrders i y hy)).trans (hSum0 (T.proj y) (hProjN hy))
    have hLevel (c : Y) (hc : c ∈ C) :
        ordinaryTraceOrder A.N (chronologicalMemberProduct W E T) c=q := by
      have hcM : c ∈ (geoTransformAlong M T).N := (geoTransformAlong M T).cosupp_subset_N
        (hT.2.2.1 hc)
      have hge := (mem_ordGe_iff hdomT.isWellFormed hdomT.isNonzeroAlongAt hcM (q-1+1)).mp
        (hGt.2 hc)
      rw [original_product_nmOrd_eq_current hn hW hE hdense q T hT.1,
        currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T hGeom] at hge
      change q-1+1 ≤ ordinaryTraceOrder A.N (chronologicalMemberProduct W E T) c at hge
      have hle := hSumLe c (hCN hc)
      rw [←hSum c (hCN hc)] at hle
      omega
    have hLoc (x : Y) (hx : x ∈ C) :
        ∀ᶠ y in 𝓝 x,y ∈ C → ∀ i,ordinaryTraceOrder A.N (F i) y=ordinaryTraceOrder A.N (F i) x := by
      apply eventually_member_orders_of_constant_product hn hN F
        (fun i => (hFamily i).1) (fun i => (hFamily i).2.1)
        (fun i => (hFamily i).2.2) hCN ?_ hx
      intro c hc d hd
      rw [←chronological_product_eq_actual_family_product W E T]
      exact (hLevel c hc).trans (hLevel d hd).symm
    have hCNC : HasNormalCrossings n C (E.map (strictAlong T) ++ A.E) := by
      intro x hx
      apply actual_incident_old_normalCrossingsAt hRecorded.2.1 hGeomStep.2.2.2 hx
      intro j hj
      let i : Fin E.length := ⟨j.val,by simpa using j.isLt⟩
      have hGet : (E.map (strictAlong T)).get j=strictAlong T (E.get i) := by simp [i]
      rw [hGet] at hj ⊢
      have hxW := hProjN (hCN hx)
      have hHi := hE.1 _ (List.get_mem E i)
      have hxHi : T.proj x ∈ E.get i := strictAlong_subset_preimage T hHi hj
      obtain ⟨_hNi0,_hEi0,_hdi0,hwi0,hnzi0,_hpri0⟩ :=
        original_members_actual_finite_chronological_geometry hn hW hE hdense i
          (.refl : BlowupTower X X) (by trivial)
      have hPos0 : 0<ordinaryTraceOrder W (F0 i) (T.proj x) :=
        (actual_normalized_vanishing_order_positive_iff hW hHi hwi0.isCoherent hnzi0 hxW).mpr hxHi
      have hSumEq : (∑ k,ordinaryTraceOrder A.N (F k) x)=
          ∑ k,ordinaryTraceOrder W (F0 k) (T.proj x) := by
        have hle : (∑ k : Fin E.length,ordinaryTraceOrder A.N (F k) x) ≤
            ∑ k : Fin E.length,ordinaryTraceOrder W (F0 k) (T.proj x) :=
          Finset.sum_le_sum (fun k _ => hOrders k x (hCN hx))
        have h0 := hSum0 (T.proj x) hxW
        have hqeq := (hSum x (hCN hx)).symm.trans (hLevel x hx)
        omega
      have hTerm := (Finset.sum_eq_sum_iff_of_le
        (fun k (_hk : k ∈ Finset.univ) => hOrders k x (hCN hx))).mp hSumEq i (Finset.mem_univ i)
      have hPos : 0<ordinaryTraceOrder A.N (F i) x := by
        change ordinaryTraceOrder A.N (F i) x=ordinaryTraceOrder W (F0 i) (T.proj x) at hTerm
        omega
      obtain ⟨hcI,hnzI,hNm,_hFactor⟩ := hRecorded.2.2.2.2 i
      have hClosedHi : IsClosed (strictAlong T (E.get i)) := isClosed_strictAlong T hHi
      filter_upwards [hLoc x hx] with y hy hyC
      have hPosY : 0<ordinaryTraceOrder A.N (F i) y := by rw [(hy hyC) i]; exact hPos
      have hCosJ := (ordinaryTraceOrder_cosupport_iff hN (hFamily i).1 (hFamily i).2.1 (hCN hyC) 1).mpr hPosY
      have hCosI : y ∈ cosupport n A.N
          (restrictOn n A.N (vanishingIdeal (n := n) (strictAlong T (E.get i)))) 1 := by
        refine ⟨hCN hyC,fun g hg => hCosJ.2 g ?_⟩
        change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.mem y g
        rw [←hNm]
        exact NonmonomialTransformAlong.le_nonmonomialPartAlong_self hcI y g hg
      exact (actual_normalized_vanishing_order_positive_iff hN hClosedHi hcI hnzI (hCN hyC)).mp
        ((ordinaryTraceOrder_cosupport_iff hN hcI hnzI (hCN hyC) 1).mp hCosI)
    have hFullNext : IsGeoTestTower (geometricTemplate (univ : Set X) E) (.step T C π hπ) := by
      let L := geometricTemplate (univ : Set X) E
      have hL := pullback_eq_mul_geoTransformAlong (𝔪 := L) rfl isCoherent_unitIdeal T hFull
      have hd : (geoTransformAlong L T).d=0 := d_geoTransformAlong L T
      have hCos : (geoTransformAlong L T).cosupp=univ := by
        change cosupport n (geoTransformAlong L T).N (geoTransformAlong L T).ideal
          (geoTransformAlong L T).d=univ
        rw [hd,cosupport_zero (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hL.2.1 hg),hL.1]
      refine ⟨hFull,⟨hπ.1,?_,?_⟩⟩
      · rw [hCos]
        exact subset_univ C
      · rw [actual_whole_ambient_boundary_ordered_dictionary W E T]
        exact hCNC
    refine ⟨hFullNext,?_⟩
    intro i z hz
    have hzN : π z ∈ A.N := geoStrictTransform_subset_preimage hπ.contMDiff.continuous hN.1 hz
    have hRowLoc (x : Y) (hx : x ∈ C) :
        ∀ᶠ y in 𝓝 x,y ∈ C → ordinaryTraceOrder A.N (F i) y=ordinaryTraceOrder A.N (F i) x := by
      filter_upwards [hLoc x hx] with y hy hyC
      exact hy hyC i
    have hStep := nextRelativeStrict_order_le_of_locally_constant_on_centre hn hN
      (hFamily i).1 (hFamily i).2.1 (hFamily i).2.2 hπ hCN hRowLoc hz
    have hChronoN := (chronologicalMarked_geometric_fields
      (originalRelativeMemberMarked W (E.get i)) T).1
    change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N at hChronoN
    change ordinaryTraceOrder _ (nextRelativeStrict _ (F i) C π) z ≤ _
    rw [hChronoN]
    exact hStep.trans (hOrders i (π z) hzN)

/-- ONLY original geometry, the original global q-bound and the actual native
same-original plateau centre predicate produce full original ambient testness. -/
theorem actual_original_plateau_full_ambient_test_tower (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {q : ℕ} (hq : 1 ≤ q)
    (hbound : ∀ x ∈ W,ordinaryTraceOrder W (originalMemberProduct E) x ≤ q)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E q) T)
    (hGt : CentresOrdGt (originalMemberProductMarked W E q) (q-1) T) :
    IsGeoTestTower (geometricTemplate (univ : Set X) E) T :=
  (plateau_history_and_orders hn hW hE hdense hq hbound T hT hGt).1

/-- The internally chosen original top-order window and SAME actual canonical
order-exit block now retain FULL ambient old-plus-born geometric testness. -/
theorem exists_original_top_order_block_full_ambient_test (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1)) (hcomp : IsCompact W)
    (hne : (HironakaSharpOriginalDistinctDefectPhase.originalDistinctDefectPhase W E).Nonempty) :
    ∃ (q : ℕ) (U : Opens X) (D : Set X),
      let WU := (Subtype.val : U → X) ⁻¹' W
      let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
      let M := originalMemberProductMarked (X := CMfd.of (n := n) U) WU EU q
      1 ≤ q ∧ D.Nonempty ∧ IsCompact D ∧ D ⊆ U ∧
      D=HironakaSharpOriginalDistinctDefectPhase.originalDistinctDefectPhase W E ∩
        (originalMemberProductMarked W E q).cosupp ∧
      (∀ x ∈ HironakaSharpOriginalDistinctDefectPhase.originalDistinctDefectPhase W E,
        ordinaryTraceOrder W (originalMemberProduct E) x ≤ q) ∧
      (∀ x ∈ D,ordinaryTraceOrder W (originalMemberProduct E) x=q) ∧
      (∀ x ∈ W,x ∈ U → ordinaryTraceOrder W (originalMemberProduct E) x ≤ q ∧
        HironakaSharpOriginalMultiBoundaryBadLocus.distinctProperTraceGermCount (n := n) W E x < q) ∧
      M.cosupp=(Subtype.val : U → X) ⁻¹' D ∧ IsCompact M.cosupp ∧
      ∃ (Y : CMfd.{u} n) (T : BlowupTower (CMfd.of (n := n) U) Y),
        IsCanonical M ((invFamily hn (n+1)).inv M) T ∧ IsGeoTestTower M T ∧
        IsGeoTestTower (geometricTemplate (univ : Set (CMfd.of (n := n) U)) EU) T ∧
        IsDistinctPhaseTower WU EU T ∧ CentresOrdGt M (q-1) T ∧
        IsGeoTestTower (geometricTemplate WU []) T ∧ CentresOver M.cosupp T ∧
        IsProperMap T.proj ∧ IsIsomorphismOver n T.proj M.cosuppᶜ ∧
        (∀ y ∈ (geoTransformAlong (geometricTemplate WU []) T).N,
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate WU []) T).N
            (chronologicalMemberProduct WU EU T) y < q) ∧
        IsClosedSubmanifold n (geoTransformAlong (geometricTemplate WU []) T).N ∧
        IsSNCDivisor n (geoTransformAlong (geometricTemplate WU []) T).E ∧
        IsTransverse n (geoTransformAlong (geometricTemplate WU []) T).N
          (geoTransformAlong (geometricTemplate WU []) T).E := by
  obtain ⟨q,U,D,hq,hDne,hDc,hDU,hDeq,hmax,hDν,hwindow,hcos,hcompact,Y,T,hcan,hT,hRest⟩ :=
    exists_original_top_order_block hn hW hE hdense d hreg hcomp hne
  let WU := (Subtype.val : U → X) ⁻¹' W
  let EU := E.map ((Subtype.val : U → X) ⁻¹' ·)
  have hWU : IsClosedSubmanifold n WU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW U
  have hEU : IsSNCDivisor n EU := NormalCrossingsInvariance.isSNCDivisor_map_preimage
    (NormalCrossingsInvariance.pullsBackCoordinates_val U) continuous_subtype_val hE
  have hDenseU : WU ⊆ closure (WU \ ⋃ H ∈ EU,H) := by
    intro y hy
    have hp : y ∈ (Subtype.val : U → X) ⁻¹' closure (W \ ⋃ H ∈ E,H) := hdense hy
    erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
      continuous_subtype_val (W \ ⋃ H ∈ E,H)] at hp
    convert hp using 1
    congr 1
    ext z
    simp [WU,EU]
  have hBoundU : ∀ x ∈ WU,ordinaryTraceOrder (X := CMfd.of (n := n) U)
      WU (originalMemberProduct EU) x ≤ q := by
    intro x hx
    rw [original_product_order_open hn hW hE hdense U x]
    exact (hwindow x.val hx x.property).1
  have hFull := actual_original_plateau_full_ambient_test_tower hn hWU hEU hDenseU hq
    hBoundU T hT hRest.2.1
  exact ⟨q,U,D,hq,hDne,hDc,hDU,hDeq,hmax,hDν,hwindow,hcos,hcompact,Y,T,hcan,hT,hFull,hRest⟩

end

end Hironaka.HironakaG4OriginalPlateauHistoryCompatibility
