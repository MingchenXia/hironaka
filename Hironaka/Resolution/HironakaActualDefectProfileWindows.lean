import Hironaka.Resolution.HironakaActualChronologicalDefectSharpBad
import Hironaka.Resolution.HironakaSharpActualEquimultipleResidualHistory

/-! Genuine finite realized profile target-opens of the SAME actual current
chronological DISTINCT defect, with compact native residual cosupport.
No global profile, sharp-selector certificate or restarted history is input.
Source-first proof: `hironaka-actual-defect-profile-windows-20261101.tex`. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualDefectProfileWindows
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower MarkedIdeals MarkedIdeals.MarkedIdeal
  NormalCrossings NormalCrossingsComparison RelativePrincipalizationSpan RestrictedIdealExtension
  MarkedIdealRestrictOpen MarkedIdealBiholomorphism
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualDynamicDistinctCentre
  HironakaActualChronologicalDefectSharpBad HironakaG4RecordedTowerResidualCompatibility
  HironakaG4CompactWholeMonomialMaskPhase HironakaG4SharpBadFootprint
  HironakaSharpNormalCrossingsOpenLocus HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualEquimultipleResidualHistory
  DivisorExponentAlong GermIdealOrder MarkedIdealOperationsAlong

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Actual top-defect product cosupport with ALL original row thresholds. -/
def topProfileStratum (W : Set X) (E : List (Set X)) (T : BlowupTower X Y)
    (q : ℕ) (profile : Fin E.length → ℕ) : Set Y :=
  chronologicalDistinctDefect W E T ∩ (residualMarked W E q T).cosupp ∩
    ⋂ i : Fin E.length,cosupport n (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (profile i)

/-- A genuine CURRENT TARGET open, defined by actual row bounds and TRUE
quotient count strictly below q; no supplied sharp selector is used. -/
def profileWindow (W : Set X) (E : List (Set X)) (T : BlowupTower X Y)
    (q : ℕ) (profile : Fin E.length → ℕ) : Opens Y :=
  ⟨interior {x | (∀ i : Fin E.length,
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ profile i) ∧
      actualDistinctProperCount (fun i : Fin E.length =>
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) x < q},isOpen_interior⟩

private theorem profile_window_bounds (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) (q : ℕ) (profile : Fin E.length → ℕ) {x : Y}
    (hx : x ∈ profileWindow W E T q profile) :
    (∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ profile i) ∧
      actualDistinctProperCount (fun i : Fin E.length =>
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) x < q := by
  exact (interior_subset (s := {y : Y | (∀ i : Fin E.length,
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ profile i) ∧
      actualDistinctProperCount (fun i : Fin E.length =>
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) y < q})) hx

/-- Only genuinely realized profiles in the fixed finite cube {0,...,q}. -/
def realizedProfiles (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) (q : ℕ) :
    Finset (Fin E.length → Fin (q+1)) := by
  classical
  exact Finset.univ.filter fun profile => (∑ i,(profile i).val)=q ∧
    (topProfileStratum W E T q (fun i => (profile i).val)).Nonempty

/-- Original COMPACT SHARP BAD, rather than compact whole carrier, supplies
compactness of the SAME actual current distinct defect. -/
theorem isCompact_actual_chronological_distinct_defect (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) :
    IsCompact (chronologicalDistinctDefect W E T) := by
  have hClosed := (original_chronological_distinct_defect_analytic hn hW hE hdense d hReg T hT).isClosed
  have hBad := actual_chronological_distinct_defect_subset_current_sharp_bad hn hW hE hdense T hT hFull
  have hN : (geoTransformAlong (geometricTemplate W []) T).N=strictAlong T W := N_geoTransformAlong _ _
  have hBoundary := HironakaSharpActualCurveWholeBoundaryTransversality.actual_whole_ambient_boundary_ordered_dictionary W E T
  rw [hN,←hBoundary] at hBad
  have hOver := (currentSharpCentres_original_footprint hW.1 hE.1 T hSharp).1
  exact ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK).of_isClosed_subset
    hClosed (hBad.trans hOver)

private theorem chronological_product_order_sum (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    {x : Y} (hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N) :
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) x=
      ∑ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x := by
  have h := (original_chronological_full_product_actual_geometry hn hW hE hdense T hT).2.2.2 x hx
  have hL : chronologicalMemberFamily W E T=List.ofFn
      (fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) := by
    unfold chronologicalMemberFamily
    conv_lhs => rw [←List.ofFn_get E,List.map_ofFn]
    rfl
  simpa only [hL,List.map_ofFn,List.sum_ofFn,Function.comp_apply] using h

private theorem family_geometry (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    let N := (geoTransformAlong (geometricTemplate W []) T).N
    ∀ i : Fin E.length,
      let J := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
      J.IsCoherent ∧ ∀ y ∈ N,IsNonzeroAlongAt N J y := by
  dsimp only
  intro i
  obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,_hpri⟩ :=
    original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  rw [hNi] at hnzi
  exact ⟨hwi.isCoherent,hnzi⟩

private theorem ordinary_order_usc (hn : 0 < n) {N : Set X}
    (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hc : I.IsCoherent)
    (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y) :
    ResolutionInvariantOrder.IsInvUSCOn (ordinaryTraceOrder N I) N :=
  fun _x hx => (eventually_ordinaryTraceOrder_le hn hN hc hnz hx).mono fun _ hy _ => hy

private theorem isClosed_ordinary_cosupport (hn : 0 < n) {N : Set X}
    (hN : IsClosedSubmanifold n N) {I : GermIdeal n X} (hc : I.IsCoherent)
    (hnz : ∀ y ∈ N,IsNonzeroAlongAt N I y) (q : ℕ) :
    IsClosed (cosupport n N I q) := by
  have h := (ordinary_order_usc hn hN hc hnz).isClosed_superlevel hN.1 q
  convert h using 1
  ext x
  constructor
  · intro hx
    exact ⟨hx.1,(ordinaryTraceOrder_cosupport_iff hN hc hnz hx.1 q).mp hx⟩
  · intro hx
    exact (ordinaryTraceOrder_cosupport_iff hN hc hnz hx.1 q).mpr hx.2

private theorem top_profile_orders (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (q : ℕ) (profile : Fin E.length → ℕ) (hsum : ∑ i,profile i=q)
    (hMax : ∀ x ∈ chronologicalDistinctDefect W E T,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) x ≤ q)
    {x : Y} (hx : x ∈ topProfileStratum W E T q profile) :
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) x=q ∧
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x=profile i := by
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hFam := family_geometry hn hW hE hdense T hT
  have hp := original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  have hxN := hx.1.1.1
  have hLow := (ordinaryTraceOrder_cosupport_iff hRec.1 hp.1 hp.2.1 hxN q).mp hx.1.2
  have hEq := (hMax x hx.1.1).antisymm hLow
  have hSum := chronological_product_order_sum hn hW hE hdense T hT hxN
  have hRow (i : Fin E.length) : profile i ≤
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x :=
    (ordinaryTraceOrder_cosupport_iff hRec.1 (hFam i).1 (hFam i).2 hxN _).mp (mem_iInter.mp hx.2 i)
  have hSumEq := hsum.trans (hEq.symm.trans hSum)
  have hRows := (Finset.sum_eq_sum_iff_of_le (fun i _ => hRow i)).mp hSumEq
  exact ⟨hEq,fun i => (hRows i (Finset.mem_univ i)).symm⟩

private theorem isClosed_top_profile_stratum (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (q : ℕ) (profile : Fin E.length → ℕ) :
    IsClosed (topProfileStratum W E T q profile) := by
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hp := original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  have hFam := family_geometry hn hW hE hdense T hT
  exact ((original_chronological_distinct_defect_analytic hn hW hE hdense d hReg T hT).isClosed.inter
    (isClosed_ordinary_cosupport hn hRec.1 hp.1 hp.2.1 q)).inter
      (isClosed_iInter fun i => isClosed_ordinary_cosupport hn hRec.1 (hFam i).1 (hFam i).2 (profile i))

private theorem top_profile_subset_window (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (q : ℕ) (profile : Fin E.length → ℕ) (hsum : ∑ i,profile i=q)
    (hMax : ∀ x ∈ chronologicalDistinctDefect W E T,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) x ≤ q) :
    topProfileStratum W E T q profile ⊆ profileWindow W E T q profile := by
  intro x hx
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hFam := family_geometry hn hW hE hdense T hT
  have hOrders := top_profile_orders hn hW hE hdense T hT hFull q profile hsum hMax hx
  have hCount : actualDistinctProperCount (fun i : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) x < q := by
    have h := hx.1.1.2
    rw [←chronological_product_eq_actual_family_product W E T,hOrders.1] at h
    exact h
  have hRows : ∀ᶠ y in 𝓝 x,∀ i : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ profile i := by
    apply eventually_all.mpr
    intro i
    have h := eventually_ordinaryTraceOrder_le hn hRec.1 (hFam i).1 (hFam i).2 hx.1.1.1
    rw [hOrders.2 i] at h
    exact h
  change x ∈ interior _
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hRows,eventually_actualDistinctProperCount_le (fun i => (hFam i).1) x] with y hRow hCt
  exact ⟨hRow,hCt.trans_lt hCount⟩

private theorem window_cosupport (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (q : ℕ) (profile : Fin E.length → ℕ) (hsum : ∑ i,profile i=q) :
    (MarkedIdeal.pullback (Subtype.val : profileWindow W E T q profile → Y)
      (residualMarked W E q T)).cosupp=
      (Subtype.val : profileWindow W E T q profile → Y) ⁻¹' topProfileStratum W E T q profile := by
  let N := (geoTransformAlong (geometricTemplate W []) T).N
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hp := original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  have hFam := family_geometry hn hW hE hdense T hT
  rw [MarkedIdealRestrictOpen.cosupp_pullback_val _
    (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hp.1 hg)]
  ext z
  constructor
  · intro hz
    have hzN : z.val ∈ N := hz.1
    have hWin : (∀ i : Fin E.length,ordinaryTraceOrder N (F i) z.val ≤ profile i) ∧
        actualDistinctProperCount F z.val < q := profile_window_bounds W E T q profile z.property
    have hSum := chronological_product_order_sum hn hW hE hdense T hT hzN
    have hLow := (ordinaryTraceOrder_cosupport_iff hRec.1 hp.1 hp.2.1 hzN q).mp hz
    have hUp : ordinaryTraceOrder N (chronologicalMemberProduct W E T) z.val ≤ q :=
      hSum.trans_le ((Finset.sum_le_sum (fun i _ => hWin.1 i)).trans_eq hsum)
    have hEq := hUp.antisymm hLow
    have hSumEq := hSum.symm.trans (hEq.trans hsum.symm)
    have hRows := (Finset.sum_eq_sum_iff_of_le (fun i _ => hWin.1 i)).mp hSumEq
    have hzZ : z.val ∈ chronologicalDistinctDefect W E T := by
      refine ⟨hzN,?_⟩
      rw [←chronological_product_eq_actual_family_product W E T]
      exact hWin.2.trans_eq hEq.symm
    refine ⟨⟨hzZ,hz⟩,mem_iInter.mpr (fun i => ?_)⟩
    apply (ordinaryTraceOrder_cosupport_iff hRec.1 (hFam i).1 (hFam i).2 hzN _).mpr
    exact (hRows i (Finset.mem_univ i)).ge
  · exact fun hz => hz.1.2

private theorem realized_profile_cover (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (q : ℕ) {x : Y} (hx : x ∈ chronologicalDistinctDefect W E T)
    (hxq : ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) x=q) :
    ∃ profile ∈ realizedProfiles W E T q,
      x ∈ topProfileStratum W E T q (fun i => (profile i).val) := by
  classical
  let N := (geoTransformAlong (geometricTemplate W []) T).N
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hp := original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  have hFam := family_geometry hn hW hE hdense T hT
  have hSum := chronological_product_order_sum hn hW hE hdense T hT hx.1
  have hLe (i : Fin E.length) : ordinaryTraceOrder N (F i) x ≤ q :=
    (Finset.single_le_sum (f := fun j => ordinaryTraceOrder N (F j) x)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq (hSum.symm.trans hxq)
  let profile : Fin E.length → Fin (q+1) := fun i =>
    ⟨ordinaryTraceOrder N (F i) x,by have h := hLe i; omega⟩
  have hProfSum : ∑ i,(profile i).val=q := hSum.symm.trans hxq
  have hxD : x ∈ topProfileStratum W E T q (fun i => (profile i).val) := by
    refine ⟨⟨hx,(ordinaryTraceOrder_cosupport_iff hRec.1 hp.1 hp.2.1 hx.1 q).mpr hxq.ge⟩,
      mem_iInter.mpr (fun i => ?_)⟩
    exact (ordinaryTraceOrder_cosupport_iff hRec.1 (hFam i).1 (hFam i).2 hx.1 _).mpr le_rfl
  exact ⟨profile,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hProfSum,⟨x,hxD⟩⟩,hxD⟩

private theorem residual_domain (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (q : ℕ) (hq : 1 ≤ q) :
    ResolutionInvariantSpec.IsInvDomain (n+1) (residualMarked W E q T) := by
  have h := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hp := original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  refine ⟨⟨h.1,hp.1,isSNCDivisor_of_sublist h.2.1 (List.sublist_append_right _ _),h.2.2.1⟩,
    ?_,hq,hp.2.1⟩
  intro x hx
  obtain ⟨k,hk⟩ := h.1.2 x hx
  exact ⟨k,hk.1.trans (Nat.le_succ n),hk⟩

/-- Individual actual row-order bounds give a bound for the native
chronological product on the current defect, also on a noncompact carrier. -/
theorem actual_distinct_defect_product_order_bound_of_row_bounds (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (r : Fin E.length → ℕ)
    (hBound : ∀ x ∈ chronologicalDistinctDefect W E T, ∀ i : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ r i) :
    ∀ x ∈ chronologicalDistinctDefect W E T,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) x ≤ ∑ i, r i := by
  intro x hx
  rw [chronological_product_order_sum hn hW hE hdense T hT hx.1]
  exact Finset.sum_le_sum fun i _ => hBound x hx i

/-- A finite bound on current product order yields a closed top profile
stratum in its actual target window, with exact native cosupport. -/
theorem exists_actual_distinct_defect_profile_windows_of_bounded_defect_order (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (B : ℕ) (hBound : ∀ x ∈ chronologicalDistinctDefect W E T,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) x ≤ B)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ q : ℕ,1 ≤ q ∧
      (∃ a ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) a=q) ∧
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) x ≤ q) ∧
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) x=q →
        ∃ profile ∈ realizedProfiles W E T q,
          x ∈ topProfileStratum W E T q (fun i => (profile i).val)) ∧
      ∀ profile ∈ realizedProfiles W E T q,
        let r := fun i => (profile i).val
        let D := topProfileStratum W E T q r
        let U := profileWindow W E T q r
        D.Nonempty ∧ IsClosed D ∧ D ⊆ U ∧ D ⊆ chronologicalDistinctDefect W E T ∧
        (∀ x ∈ D,
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMemberProduct W E T) x=q ∧
          ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x=r i) ∧
        (∀ x ∈ U,
          (∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ r i) ∧
          actualDistinctProperCount (fun i : Fin E.length =>
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) x < q) ∧
        (MarkedIdeal.pullback (Subtype.val : U → Y) (residualMarked W E q T)).cosupp=
          (Subtype.val : U → Y) ⁻¹' D ∧
        ResolutionInvariantSpec.IsInvDomain (n+1)
          (MarkedIdeal.pullback (Subtype.val : U → Y) (residualMarked W E q T)) := by
  classical
  let order : Y → ℕ := fun x => ordinaryTraceOrder
    (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) x
  let values := (Finset.range (B+1)).filter fun k =>
    ∃ x ∈ chronologicalDistinctDefect W E T, order x = k
  have hValue : ∀ x ∈ chronologicalDistinctDefect W E T, order x ∈ values := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (hBound x hx)), x, hx, rfl⟩
  obtain ⟨a₀, ha₀⟩ := hne
  obtain ⟨q, hqValue, hMaxValue⟩ := Finset.exists_max_image values id ⟨order a₀, hValue a₀ ha₀⟩
  obtain ⟨a, ha, haq⟩ := (Finset.mem_filter.mp hqValue).2
  have hMax : ∀ x ∈ chronologicalDistinctDefect W E T, order x ≤ q :=
    fun x hx => hMaxValue (order x) (hValue x hx)
  have hq : 1 ≤ q := by
    have h := ha.2
    rw [←chronological_product_eq_actual_family_product W E T] at h
    change _ < order a at h
    rw [haq] at h
    omega
  refine ⟨q,hq,⟨a,ha,haq⟩,hMax,?_,?_⟩
  · exact fun x hx hxq => realized_profile_cover hn hW hE hdense T hT hFull q hx hxq
  · intro profile hProfile
    dsimp only
    let r : Fin E.length → ℕ := fun i => (profile i).val
    let D := topProfileStratum W E T q r
    let U := profileWindow W E T q r
    have hProf := (Finset.mem_filter.mp hProfile).2
    have hSum : ∑ i,r i=q := hProf.1
    have hDne : D.Nonempty := hProf.2
    have hDclosed := isClosed_top_profile_stratum hn hW hE hdense d hReg T hT hFull q r
    have hDU : D ⊆ U := top_profile_subset_window hn hW hE hdense T hT hFull q r hSum hMax
    have hCos := window_cosupport hn hW hE hdense T hT hFull q r hSum
    exact ⟨hDne,hDclosed,hDU,(fun _ hx => hx.1.1),
      (fun _ hx => top_profile_orders hn hW hE hdense T hT hFull q r hSum hMax hx),
      (fun _ hx => profile_window_bounds W E T q r hx),hCos,
      InvDomainTowerAlong.isInvDomain_pullback_val U (residual_domain hn hW hE hdense T hT hFull q hq)⟩

/-- Compactness of the current chronological defect supplies the finite
profile windows and compact native residual cosupport. -/
theorem exists_actual_distinct_defect_profile_windows_of_compact_defect (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hCompact : IsCompact (chronologicalDistinctDefect W E T))
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ q : ℕ,1 ≤ q ∧
      (∃ a ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) a=q) ∧
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) x ≤ q) ∧
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) x=q →
        ∃ profile ∈ realizedProfiles W E T q,
          x ∈ topProfileStratum W E T q (fun i => (profile i).val)) ∧
      ∀ profile ∈ realizedProfiles W E T q,
        let r := fun i => (profile i).val
        let D := topProfileStratum W E T q r
        let U := profileWindow W E T q r
        D.Nonempty ∧ IsCompact D ∧ D ⊆ U ∧ D ⊆ chronologicalDistinctDefect W E T ∧
        (∀ x ∈ D,
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMemberProduct W E T) x=q ∧
          ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x=r i) ∧
        (∀ x ∈ U,
          (∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ r i) ∧
          actualDistinctProperCount (fun i : Fin E.length =>
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) x < q) ∧
        (MarkedIdeal.pullback (Subtype.val : U → Y) (residualMarked W E q T)).cosupp=
          (Subtype.val : U → Y) ⁻¹' D ∧
        IsCompact (MarkedIdeal.pullback (Subtype.val : U → Y) (residualMarked W E q T)).cosupp ∧
        ResolutionInvariantSpec.IsInvDomain (n+1)
          (MarkedIdeal.pullback (Subtype.val : U → Y) (residualMarked W E q T)) := by
  classical
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hp := original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  have hUSC := (ordinary_order_usc hn hRec.1 hp.1 hp.2.1).mono
    (fun _ (hx : _ ∈ chronologicalDistinctDefect W E T) => hx.1)
  obtain ⟨a,ha,hMax⟩ := hUSC.exists_isMaxOn hCompact hne
  let q := ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
    (chronologicalMemberProduct W E T) a
  obtain ⟨q, hq, hAttained, hBound, hCover, hProfiles⟩ :=
    exists_actual_distinct_defect_profile_windows_of_bounded_defect_order hn hW hE hdense d hReg T hT hFull q hMax hne
  refine ⟨q, hq, hAttained, hBound, hCover, ?_⟩
  intro profile hProfile
  dsimp only
  let r := fun i => (profile i).val
  let D := topProfileStratum W E T q r
  let U := profileWindow W E T q r
  obtain ⟨hDne, hDclosed, hDU, hDsub, hOrders, hWindow, hCos, hDomain⟩ := hProfiles profile hProfile
  have hDcompact : IsCompact D := hCompact.of_isClosed_subset hDclosed hDsub
  have hCompactNative : IsCompact (MarkedIdeal.pullback (Subtype.val : U → Y) (residualMarked W E q T)).cosupp := by
    rw [hCos]
    apply Subtype.isCompact_iff.mpr
    rw [Set.image_preimage_eq_of_subset (show D ⊆ Set.range (Subtype.val : U → Y) from
      fun x hx => ⟨⟨x,hDU hx⟩,rfl⟩)]
    exact hDcompact
  exact ⟨hDne, hDcompact, hDU, hDsub, hOrders, hWindow, hCos, hCompactNative, hDomain⟩

/-- Original geometry constructs genuine finite CURRENT TARGET profile opens:
all original rows are bounded, true count<q excludes good crossings, and the
actual native product q-cosupport is EXACTLY the compact top-defect stratum.
No global row profile, sharp selector or future history is supplied. -/
theorem exists_actual_distinct_defect_profile_windows (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ q : ℕ,1 ≤ q ∧
      (∃ a ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) a=q) ∧
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) x ≤ q) ∧
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) x=q →
        ∃ profile ∈ realizedProfiles W E T q,
          x ∈ topProfileStratum W E T q (fun i => (profile i).val)) ∧
      ∀ profile ∈ realizedProfiles W E T q,
        let r := fun i => (profile i).val
        let D := topProfileStratum W E T q r
        let U := profileWindow W E T q r
        D.Nonempty ∧ IsCompact D ∧ D ⊆ U ∧ D ⊆ chronologicalDistinctDefect W E T ∧
        (∀ x ∈ D,
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMemberProduct W E T) x=q ∧
          ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x=r i) ∧
        (∀ x ∈ U,
          (∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ r i) ∧
          actualDistinctProperCount (fun i : Fin E.length =>
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) x < q) ∧
        (MarkedIdeal.pullback (Subtype.val : U → Y) (residualMarked W E q T)).cosupp=
          (Subtype.val : U → Y) ⁻¹' D ∧
        IsCompact (MarkedIdeal.pullback (Subtype.val : U → Y) (residualMarked W E q T)).cosupp ∧
        ResolutionInvariantSpec.IsInvDomain (n+1)
          (MarkedIdeal.pullback (Subtype.val : U → Y) (residualMarked W E q T)) :=
  exists_actual_distinct_defect_profile_windows_of_compact_defect hn hW hE hdense d hReg T hT hFull
    (isCompact_actual_chronological_distinct_defect hn hW hE hdense d hReg hK T hT hFull hSharp) hne

end
end Hironaka.HironakaActualDefectProfileWindows
