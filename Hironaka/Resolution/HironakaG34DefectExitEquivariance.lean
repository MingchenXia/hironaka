import Hironaka.Resolution.HironakaActualGlobalDistinctDefectExit
import Hironaka.Resolution.HironakaG34PreparedRowDefectFree
import Hironaka.Resolution.HironakaG34ProfileWindowNaturality

/-! # The true-defect exit (J4) with an equivariance conclusion (eighth brick of EQ_d)

Lane G34 (run 0080, round 9).  Blueprint: `hironaka-g34-resume-defect-exit-equivariance.tex`.  Route note:
`work/hironaka-resume-20261111/G34/GENERAL-D-ROUTE.md` §1 (row "carrier"), §2(c)(ii).

`HironakaG34DefectExitCentresOver` (lane G34, run 0080) re-derived the held true-defect exit with its centres over the
TRUE distinct defect.  This module re-derives it once more (its private helpers are copied; that file is not edited), with
the profile blocks of `HironakaG34ProfileBlockEquivariance.exists_actual_global_original_profile_blocks_equivariant` and
one more field in the kept endpoint: "an equivariant prefix stays equivariant"
(`HironakaG34ProfileWindowNaturality.isEquivariant_append_profile_block` for each block, composed along the profile-card,
fixed-`q` and bound descents).

* `exists_actual_global_original_distinct_defect_exit_equivariant`: the outputs of
  `HironakaG34DefectExitCentresOver.exists_actual_global_original_distinct_defect_exit_centresOver` plus
  `IsEquivariant W E T → IsEquivariant W E (T.append Q)`.
* `exists_actual_global_original_distinct_defect_exit_protected_equivariant`: the protected form, with the same clause.
* Corollary from the empty prefix: the exit tower itself is equivariant for `(W, E)`
  (`exists_actual_original_distinct_defect_exit_isEquivariant`). -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG34DefectExitEquivariance
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong
  NormalCrossings RelativePrincipalizationSpan
  HironakaActualGlobalDefectProfileBlock HironakaActualDefectProfileWindows
  HironakaG4RecordedTowerResidualCompatibility HironakaG4CompactWholeMonomialMaskPhase
  HironakaG4SharpBadFootprint HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualEquimultipleResidualHistory
  HironakaSharpOriginalProductTraceOrder DivisorExponentAlong GermIdealOrder RestrictEmptyTower
  HironakaG34MaskFoldEquivariance HironakaG34ProfileBlockEquivariance HironakaG34ProfileWindowNaturality
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X Y Z V : CMfd.{u} n}

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


private theorem product_order_nonincrease (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (S : BlowupTower Y Z) (hTS : IsGeoTestTower (geometricTemplate W []) (T.append S))
    (hRows : ∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append S)).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append S)).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append S)).ideal y ≤
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (S.proj y))
    (hFoot : chronologicalDistinctDefect W E (T.append S) ⊆ S.proj ⁻¹' chronologicalDistinctDefect W E T)
    {y : Z} (hy : y ∈ chronologicalDistinctDefect W E (T.append S)) :
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append S)).N
      (chronologicalMemberProduct W E (T.append S)) y ≤
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMemberProduct W E T) (S.proj y) := by
  rw [chronological_product_order_sum hn hW hE hdense (T.append S) hTS hy.1,
    chronological_product_order_sum hn hW hE hdense T hT (hFoot hy).1]
  exact Finset.sum_le_sum (fun i _ => hRows y hy.1 i)

private theorem q_rows_unchanged (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (S : BlowupTower Y Z) (hTS : IsGeoTestTower (geometricTemplate W []) (T.append S))
    (hRows : ∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append S)).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append S)).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append S)).ideal y ≤
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (S.proj y))
    (hFoot : chronologicalDistinctDefect W E (T.append S) ⊆ S.proj ⁻¹' chronologicalDistinctDefect W E T)
    (q : ℕ) (hBound : ∀ x ∈ chronologicalDistinctDefect W E T,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) x ≤ q)
    {y : Z} (hy : y ∈ chronologicalDistinctDefect W E (T.append S))
    (hyq : ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append S)).N
      (chronologicalMemberProduct W E (T.append S)) y=q) :
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) (S.proj y)=q ∧
    ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append S)).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append S)).ideal y=
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (S.proj y) := by
  have hLe := product_order_nonincrease hn hW hE hdense T hT S hTS hRows hFoot hy
  have hOldEq := (hBound (S.proj y) (hFoot hy)).antisymm (by rwa [hyq] at hLe)
  refine ⟨hOldEq,?_⟩
  have hSumNew := chronological_product_order_sum hn hW hE hdense (T.append S) hTS hy.1
  have hSumOld := chronological_product_order_sum hn hW hE hdense T hT (hFoot hy).1
  have hSumEq := hSumNew.symm.trans (hyq.trans (hOldEq.symm.trans hSumOld))
  have hEqual := (Finset.sum_eq_sum_iff_of_le (fun i _ => hRows y hy.1 i)).mp hSumEq
  exact fun i => hEqual i (Finset.mem_univ i)

private theorem new_top_profile_maps_to_old (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (S : BlowupTower Y Z) (hTS : IsGeoTestTower (geometricTemplate W []) (T.append S))
    (hFullTS : IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append S))
    (hRows : ∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append S)).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append S)).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append S)).ideal y ≤
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (S.proj y))
    (hFoot : chronologicalDistinctDefect W E (T.append S) ⊆ S.proj ⁻¹' chronologicalDistinctDefect W E T)
    (q : ℕ) (hBound : ∀ x ∈ chronologicalDistinctDefect W E T,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) x ≤ q)
    (profile : Fin E.length → ℕ) (hsum : ∑ i,profile i=q)
    {y : Z} (hy : y ∈ topProfileStratum W E (T.append S) q profile) :
    S.proj y ∈ topProfileStratum W E T q profile := by
  have hBoundNew : ∀ x ∈ chronologicalDistinctDefect W E (T.append S),
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append S)).N
        (chronologicalMemberProduct W E (T.append S)) x ≤ q := by
    intro x hx
    exact (product_order_nonincrease hn hW hE hdense T hT S hTS hRows hFoot hx).trans
      (hBound (S.proj x) (hFoot hx))
  have hNew := top_profile_orders hn hW hE hdense (T.append S) hTS hFullTS q profile hsum hBoundNew hy
  have hOld := q_rows_unchanged hn hW hE hdense T hT S hTS hRows hFoot q hBound hy.1.1 hNew.1
  have hOldZ := hFoot hy.1.1
  have hRec := actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hFam := family_geometry hn hW hE hdense T hT
  have hp := original_chronological_full_product_actual_geometry hn hW hE hdense T hT
  refine ⟨⟨hOldZ,?_⟩,?_⟩
  · exact (ordinaryTraceOrder_cosupport_iff hRec.1 hp.1 hp.2.1 hOldZ.1 q).mpr (by rw [hOld.1])
  · apply mem_iInter.mpr
    intro i
    apply (ordinaryTraceOrder_cosupport_iff hRec.1 (hFam i).1 (hFam i).2 hOldZ.1 (profile i)).mpr
    rw [←hOld.2 i,hNew.2 i]
private theorem centresOver_mono {Q : CMfd.{u} n} {F G : Set Q} (hFG : F ⊆ G) :
    ∀ {Z : CMfd.{u} n} (R : BlowupTower Q Z), CentresOver F R → CentresOver G R
  | _, .refl, _ => trivial
  | _, .step R _ _ _, h => ⟨centresOver_mono hFG R h.1, h.2.trans (preimage_mono hFG)⟩

/-- The held profile-card drop, keeping `CentresOver (defect T)`. -/
private theorem profile_card_drop_centres (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hCompact : IsCompact (chronologicalDistinctDefect W E T))
    (q : ℕ) (hBound : ∀ x ∈ chronologicalDistinctDefect W E T,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) x ≤ q)
    (hProfiles : (realizedProfiles W E T q).Nonempty) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append Q) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) ∧
      CurrentSharpCentres W E (T.append Q) ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N,
        ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append Q)).ideal y ≤
            ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
              (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (Q.proj y)) ∧
      chronologicalDistinctDefect W E (T.append Q) ⊆ Q.proj ⁻¹' chronologicalDistinctDefect W E T ∧
      CentresOver (chronologicalDistinctDefect W E T) Q ∧
      (∀ y ∈ chronologicalDistinctDefect W E (T.append Q),
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMemberProduct W E (T.append Q)) y ≤ q) ∧
      realizedProfiles W E (T.append Q) q ⊂ realizedProfiles W E T q ∧
      (IsEquivariant W E T → IsEquivariant W E (T.append Q)) := by
  classical
  obtain ⟨r,hr⟩ := hProfiles
  obtain ⟨hSum,⟨x,hx⟩⟩ := (Finset.mem_filter.mp hr).2
  have hTop := top_profile_orders hn hW hE hdense T hT hFull q (fun i => (r i).val) hSum hBound hx
  have hne : (chronologicalDistinctDefect W E T).Nonempty := ⟨x,hx.1.1⟩
  obtain ⟨q0,_hq0,hA0,hM0,_hC0,hWindows⟩ :=
    exists_actual_distinct_defect_profile_windows_of_compact_defect hn hW hE hdense d hReg T hT hFull hCompact hne
  have hEq0 : q0=q := by
    obtain ⟨a,ha,haq⟩ := hA0
    exact (haq.symm.trans_le (hBound a ha)).antisymm (hTop.1.symm.trans_le (hM0 x hx.1.1))
  subst q0
  have hDU : topProfileStratum W E T q (fun i => (r i).val) ⊆
      profileWindow W E T q (fun i => (r i).val) := (hWindows r hr).2.2.1
  obtain ⟨q1,_hq1,hA1,hM1,_hC1,hBlocks⟩ :=
    exists_actual_global_original_profile_blocks_equivariant_of_compact_defect hn hW hE hdense d hReg T hT hFull hSharp hCompact hne
  have hEq1 : q1=q := by
    obtain ⟨a,ha,haq⟩ := hA1
    exact (haq.symm.trans_le (hBound a ha)).antisymm (hTop.1.symm.trans_le (hM1 x hx.1.1))
  subst q1
  obtain ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hOverQ,_hNativeQ,hHeadsRows,hHeadsFoot,hExitQ,hEquivQ⟩ := hBlocks r hr
  have hRows : ∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N,
      ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append Q)).ideal y ≤
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (Q.proj y) := by
    cases Q <;> exact hHeadsRows 0
  have hFoot : chronologicalDistinctDefect W E (T.append Q) ⊆ Q.proj ⁻¹' chronologicalDistinctDefect W E T := by
    cases Q <;> exact hHeadsFoot 0
  have hBoundNew : ∀ y ∈ chronologicalDistinctDefect W E (T.append Q),
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
        (chronologicalMemberProduct W E (T.append Q)) y ≤ q := by
    intro y hy
    exact (product_order_nonincrease hn hW hE hdense T hT Q hTQ hRows hFoot hy).trans
      (hBound (Q.proj y) (hFoot hy))
  have hSubset : realizedProfiles W E (T.append Q) q ⊆ realizedProfiles W E T q := by
    intro s hs
    obtain ⟨hSumS,⟨y,hy⟩⟩ := (Finset.mem_filter.mp hs).2
    have hOld := new_top_profile_maps_to_old hn hW hE hdense T hT hFull Q hTQ hFullTQ
      hRows hFoot q hBound (fun i => (s i).val) hSumS hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ s,hSumS,⟨Q.proj y,hOld⟩⟩
  have hRemoved : r ∉ realizedProfiles W E (T.append Q) q := by
    intro hrNew
    obtain ⟨hSumNew,⟨y,hy⟩⟩ := (Finset.mem_filter.mp hrNew).2
    have hOld := new_top_profile_maps_to_old hn hW hE hdense T hT hFull Q hTQ hFullTQ
      hRows hFoot q hBound (fun i => (r i).val) hSumNew hy
    have hExact := top_profile_orders hn hW hE hdense (T.append Q) hTQ hFullTQ q
      (fun i => (r i).val) hSumNew hBoundNew hy
    have hLt := hExitQ y hy.1.1.1 (hDU hOld)
    rw [hExact.1] at hLt
    exact Nat.lt_irrefl q hLt
  have hStrict : realizedProfiles W E (T.append Q) q ⊂ realizedProfiles W E T q := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hSubset,?_⟩
    intro hEq
    rw [hEq] at hRemoved
    exact hRemoved hr
  have hOverD : CentresOver (chronologicalDistinctDefect W E T) Q :=
    centresOver_mono (fun z hz => hz.1.1) Q hOverQ
  exact ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hRows,hFoot,hOverD,hBoundNew,hStrict,
    fun hEqT => isEquivariant_append_profile_block hn hW hE hdense T hT hFull hEqT q (fun i => (r i).val) Q hEquivQ⟩

private def KeptEndpointC (W : Set X) (E : List (Set X)) (T : BlowupTower X Y) (S : BlowupTower Y Z) : Prop :=
  IsGeoTestTower (geometricTemplate W []) (T.append S) ∧
  IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append S) ∧
  CurrentSharpCentres W E (T.append S) ∧
  (∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append S)).N,
    ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append S)).N
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append S)).ideal y ≤
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (S.proj y)) ∧
  chronologicalDistinctDefect W E (T.append S) ⊆ S.proj ⁻¹' chronologicalDistinctDefect W E T ∧
  CentresOver (chronologicalDistinctDefect W E T) S ∧
  (IsEquivariant W E T → IsEquivariant W E (T.append S))

private theorem keptEndpointC_refl {W : Set X} {E : List (Set X)} (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) : KeptEndpointC W E T (.refl : BlowupTower Y Y) := by
  exact ⟨hT,hFull,hSharp,(fun _ _ _ => le_rfl),(fun _ h => h),trivial,fun h => h⟩

private theorem keptEndpointC_append {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (T : BlowupTower X Y) (Q : BlowupTower Y Z) (R : BlowupTower Z V)
    (hQ : KeptEndpointC W E T Q) (hR : KeptEndpointC W E (T.append Q) R) :
    KeptEndpointC W E T (Q.append R) := by
  have hN : IsClosedSubmanifold n (geoTransformAlong (geometricTemplate W []) (T.append Q)).N :=
    (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      (𝔪 := geometricTemplate W []) hW IdealWeightPowers.isCoherent_unitIdeal (T.append Q) hQ.1).1
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [BlowupTower.append_assoc] using hR.1
  · simpa only [BlowupTower.append_assoc] using hR.2.1
  · simpa only [BlowupTower.append_assoc] using hR.2.2.1
  · intro y hy i
    have hyR : y ∈ (geoTransformAlong (geometricTemplate W []) ((T.append Q).append R)).N := by
      simpa only [BlowupTower.append_assoc] using hy
    have hyQ : R.proj y ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N := by
      apply MemberInterTowerAlong.strictAlong_subset_preimage R hN.1
      have hStrict := N_geoTransformAlong (geoTransformAlong (geometricTemplate W []) (T.append Q)) R
      rw [geoTransformAlong_append,hStrict] at hyR
      exact hyR
    have hh := (hR.2.2.2.1 y hyR i).trans (hQ.2.2.2.1 (R.proj y) hyQ i)
    simpa only [BlowupTower.append_assoc,BlowupTower.proj_append,Function.comp_apply] using hh
  · intro y hy
    have hyR : y ∈ chronologicalDistinctDefect W E ((T.append Q).append R) := by
      simpa only [BlowupTower.append_assoc] using hy
    have hh := hQ.2.2.2.2.1 (hR.2.2.2.2.1 hyR)
    simpa only [BlowupTower.proj_append,Set.mem_preimage,Function.comp_apply] using hh
  · exact (centresOver_append_iff _ Q R).mpr
      ⟨hQ.2.2.2.2.2.1,centresOver_mono hQ.2.2.2.2.1 R hR.2.2.2.2.2.1⟩
  · exact isEquivariant_clause_trans hQ.2.2.2.2.2.2 hR.2.2.2.2.2.2

private theorem compact_defect_append (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hReg : ∀ x ∈ W, RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (Q : BlowupTower Y Z)
    (hCompact : IsCompact (chronologicalDistinctDefect W E T))
    (hTQ : IsGeoTestTower (geometricTemplate W []) (T.append Q))
    (hFoot : chronologicalDistinctDefect W E (T.append Q) ⊆ Q.proj ⁻¹' chronologicalDistinctDefect W E T) :
    IsCompact (chronologicalDistinctDefect W E (T.append Q)) :=
  ((HironakaLocalPrincipalization.isProperMap_proj Q).isCompact_preimage hCompact).of_isClosed_subset
    (original_chronological_distinct_defect_analytic hn hW hE hdense d hReg (T.append Q) hTQ).isClosed hFoot

private theorem fixed_q_exit_by_card_centres (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (q k : ℕ) :
    ∀ (Y₀ : CMfd.{u} n) (T : BlowupTower X Y₀),
      IsGeoTestTower (geometricTemplate W []) T →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T →
      CurrentSharpCentres W E T →
      IsCompact (chronologicalDistinctDefect W E T) →
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) x ≤ q) →
      (realizedProfiles W E T q).card=k →
      ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y₀ Z),KeptEndpointC W E T Q ∧
        ∀ y ∈ chronologicalDistinctDefect W E (T.append Q),
          ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
            (chronologicalMemberProduct W E (T.append Q)) y < q := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro Y₀ T hT hFull hSharp hCompact hBound hCard
    by_cases hProfiles : (realizedProfiles W E T q).Nonempty
    · obtain ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hRowsQ,hFootQ,hOverQ,hBoundQ,hStrict,hEquivQ⟩ :=
        profile_card_drop_centres hn hW hE hdense d hReg T hT hFull hSharp hCompact q hBound hProfiles
      have hSmaller : (realizedProfiles W E (T.append Q) q).card < k :=
        (Finset.card_lt_card hStrict).trans_eq hCard
      have hCompactQ := compact_defect_append hn hW hE hdense d hReg T Q hCompact hTQ hFootQ
      obtain ⟨V,R,hKeptR,hExitR⟩ := ih (realizedProfiles W E (T.append Q) q).card hSmaller
        Z (T.append Q) hTQ hFullTQ hSharpTQ hCompactQ hBoundQ rfl
      have hKeptQ : KeptEndpointC W E T Q := ⟨hTQ,hFullTQ,hSharpTQ,hRowsQ,hFootQ,hOverQ,hEquivQ⟩
      refine ⟨V,Q.append R,keptEndpointC_append hW T Q R hKeptQ hKeptR,?_⟩
      simpa only [BlowupTower.append_assoc] using hExitR
    · refine ⟨Y₀,BlowupTower.refl,keptEndpointC_refl T hT hFull hSharp,?_⟩
      intro x hx
      change x ∈ chronologicalDistinctDefect W E T at hx
      change ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMemberProduct W E T) x < q
      by_contra hNot
      have hxq := (hBound x hx).antisymm (Nat.le_of_not_gt hNot)
      obtain ⟨q0,_hq0,hA0,hM0,hCover0,_hWindows⟩ :=
        exists_actual_distinct_defect_profile_windows_of_compact_defect hn hW hE hdense d hReg T hT hFull hCompact ⟨x,hx⟩
      have hEq0 : q0=q := by
        obtain ⟨a,ha,haq⟩ := hA0
        exact (haq.symm.trans_le (hBound a ha)).antisymm (hxq.symm.trans_le (hM0 x hx))
      subst q0
      obtain ⟨r,hr,_hrx⟩ := hCover0 x hx hxq
      exact hProfiles ⟨r,hr⟩

private theorem product_order_positive_on_true_defect (W : Set X) (E : List (Set X))
    (T : BlowupTower X Y) {y : Y} (hy : y ∈ chronologicalDistinctDefect W E T) :
    1 ≤ ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (chronologicalMemberProduct W E T) y := by
  rw [chronological_product_eq_actual_family_product]
  exact Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt hy.2)

private theorem true_defect_exit_by_bound_centres (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (q : ℕ) :
    ∀ (Y₀ : CMfd.{u} n) (T : BlowupTower X Y₀),
      IsGeoTestTower (geometricTemplate W []) T →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T →
      CurrentSharpCentres W E T →
      IsCompact (chronologicalDistinctDefect W E T) →
      (∀ x ∈ chronologicalDistinctDefect W E T,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) x ≤ q) →
      ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y₀ Z),KeptEndpointC W E T Q ∧
        chronologicalDistinctDefect W E (T.append Q)=∅ := by
  induction q with
  | zero =>
    intro Y₀ T hT hFull hSharp hCompact hBound
    refine ⟨Y₀,BlowupTower.refl,keptEndpointC_refl T hT hFull hSharp,?_⟩
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    change y ∈ chronologicalDistinctDefect W E T at hy
    have hPositive := product_order_positive_on_true_defect W E T hy
    have hUpper := hBound y hy
    omega
  | succ q ih =>
    intro Y₀ T hT hFull hSharp hCompact hBound
    obtain ⟨Z,Q,hKeptQ,hExitQ⟩ :=
      fixed_q_exit_by_card_centres hn hW hE hdense d hReg (q+1) (realizedProfiles W E T (q+1)).card
        Y₀ T hT hFull hSharp hCompact hBound rfl
    have hBoundQ : ∀ y ∈ chronologicalDistinctDefect W E (T.append Q),
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMemberProduct W E (T.append Q)) y ≤ q := by
      intro y hy
      exact Nat.le_of_lt_succ (hExitQ y hy)
    have hCompactQ := compact_defect_append hn hW hE hdense d hReg T Q hCompact
      hKeptQ.1 hKeptQ.2.2.2.2.1
    obtain ⟨V,R,hKeptR,hEmptyR⟩ :=
      ih Z (T.append Q) hKeptQ.1 hKeptQ.2.1 hKeptQ.2.2.1 hCompactQ hBoundQ
    refine ⟨V,Q.append R,keptEndpointC_append hW T Q R hKeptQ hKeptR,?_⟩
    simpa only [BlowupTower.append_assoc] using hEmptyR

/-- The equivariant true-defect exit assumes compactness only on the
current chronological defect. Every chosen centre projects into that
defect on the current source. -/
theorem exists_actual_global_original_distinct_defect_exit_equivariant_of_compact_defect (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hCompact : IsCompact (chronologicalDistinctDefect W E T)) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append Q) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) ∧
      CurrentSharpCentres W E (T.append Q) ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N,
        ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append Q)).ideal y ≤
            ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
              (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (Q.proj y)) ∧
      chronologicalDistinctDefect W E (T.append Q) ⊆ Q.proj ⁻¹' chronologicalDistinctDefect W E T ∧
      CentresOver (chronologicalDistinctDefect W E T) Q ∧
      (IsEquivariant W E T → IsEquivariant W E (T.append Q)) ∧
      chronologicalDistinctDefect W E (T.append Q)=∅ := by
  classical
  have hExists : ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),KeptEndpointC W E T Q ∧
      chronologicalDistinctDefect W E (T.append Q)=∅ := by
    by_cases hne : (chronologicalDistinctDefect W E T).Nonempty
    · obtain ⟨q,_hq,_hAttain,hBound,_hCover,_hWindows⟩ :=
        exists_actual_distinct_defect_profile_windows_of_compact_defect hn hW hE hdense d hReg T hT hFull hCompact hne
      exact true_defect_exit_by_bound_centres hn hW hE hdense d hReg q Y T hT hFull hSharp hCompact hBound
    · have hEmpty := Set.not_nonempty_iff_eq_empty.mp hne
      exact ⟨Y,BlowupTower.refl,keptEndpointC_refl T hT hFull hSharp,hEmpty⟩
  simpa only [KeptEndpointC,and_assoc] using hExists

/-- **The true-defect exit, equivariant**: the outputs of
`HironakaG34DefectExitCentresOver.exists_actual_global_original_distinct_defect_exit_centresOver` (same construction), plus:
an equivariant prefix stays equivariant. -/
theorem exists_actual_global_original_distinct_defect_exit_equivariant (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append Q) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) ∧
      CurrentSharpCentres W E (T.append Q) ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N,
        ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append Q)).ideal y ≤
            ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
              (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (Q.proj y)) ∧
      chronologicalDistinctDefect W E (T.append Q) ⊆ Q.proj ⁻¹' chronologicalDistinctDefect W E T ∧
      CentresOver (chronologicalDistinctDefect W E T) Q ∧
      (IsEquivariant W E T → IsEquivariant W E (T.append Q)) ∧
      chronologicalDistinctDefect W E (T.append Q)=∅ :=
  exists_actual_global_original_distinct_defect_exit_equivariant_of_compact_defect hn hW hE hdense d hReg T hT hFull hSharp
    (isCompact_actual_chronological_distinct_defect hn hW hE hdense d hReg hK T hT hFull hSharp)

/-- **The constructed true-defect exit is a literal empty phase near every prepared row.**
The SAME history as above: for every row `i` prepared at the start (order `≤ 1`, `S_i` NC with
`F_i`, dense off `F_i`) there is an open neighbourhood `U` of `S_i` over which the history
restricts to a tower with only empty centres. -/
theorem exists_actual_global_original_distinct_defect_exit_protected_equivariant (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append Q) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append Q) ∧
      CurrentSharpCentres W E (T.append Q) ∧
      (∀ y ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N,
        ∀ i : Fin E.length,ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append Q)).ideal y ≤
            ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
              (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal (Q.proj y)) ∧
      chronologicalDistinctDefect W E (T.append Q)=∅ ∧
      (IsEquivariant W E T → IsEquivariant W E (T.append Q)) ∧
      ∀ i : Fin E.length,
        (∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
          ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1) →
        (let A := geoTransformAlong (geometricTemplate W []) T
          let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
          HasNormalCrossings n S ((E.map (strictAlong T)).eraseIdx i.val ++ A.E)) →
        (let A := geoTransformAlong (geometricTemplate W []) T
          let S := A.N ∩ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
          S ⊆ closure (S \ ⋃ H ∈ (E.map (strictAlong T)).eraseIdx i.val ++ A.E,H)) →
        ∃ U : Opens Y,
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N ∩
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus ⊆ U ∧
          IsEmptyTower (restrict U Q) := by
  obtain ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hRows,_hFoot,hOver,hEquiv,hEmpty⟩ :=
    exists_actual_global_original_distinct_defect_exit_equivariant hn hW hE hdense d hReg hK T hT hFull hSharp
  refine ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hRows,hEmpty,hEquiv,fun i hOrd hNC hDenseS => ?_⟩
  obtain ⟨U,hUeq,hSU⟩ := HironakaG34PreparedRowDefectFree.actual_prepared_row_defect_free_near
    hn hW hE hdense d hReg i T hT hFull hOrd hNC hDenseS
  refine ⟨U,hSU,isEmptyTower_restrict_of_centresOver U ?_ Q hOver⟩
  rw [hUeq]
  exact disjoint_compl_left

/-- **The true-defect exit from the original data is equivariant for `(W, E)`** (the empty prefix is equivariant). -/
theorem exists_actual_original_distinct_defect_exit_isEquivariant (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hReg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Z : CMfd.{u} n) (Q : BlowupTower X Z),
      IsGeoTestTower (geometricTemplate W []) Q ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) Q ∧
      CurrentSharpCentres W E Q ∧
      CentresOver (chronologicalDistinctDefect W E (.refl : BlowupTower X X)) Q ∧
      chronologicalDistinctDefect W E Q=∅ ∧
      IsEquivariant W E Q := by
  obtain ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,_hRows,_hFoot,hOver,hEquiv,hEmpty⟩ :=
    exists_actual_global_original_distinct_defect_exit_equivariant hn hW hE hdense d hReg hK
      (.refl : BlowupTower X X) trivial trivial trivial
  have hEq := hEquiv (isEquivariant_refl W E)
  simp only [BlowupTower.refl_append] at hTQ hFullTQ hSharpTQ hEmpty hEq
  exact ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hOver,hEmpty,hEq⟩

end
end Hironaka.HironakaG34DefectExitEquivariance
