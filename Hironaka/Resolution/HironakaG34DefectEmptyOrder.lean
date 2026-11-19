import Hironaka.Resolution.HironakaG34DefectExitCentresOver

/-! # Empty true distinct defect forces order at most one on every row

Lane G34 (run 0080).  Blueprint: `hironaka-g34-resume-defect-empty-order.tex`.

* `ordinaryTraceOrder_le_one_of_distinctDefect_eq_empty`: if the TRUE chronological distinct
  defect of an actual mixed prefix is empty, every residual row has ordinary trace order `≤ 1` at
  every point of the current carrier.  (A row of order `≥ 2` at `x` makes the product order, which
  is the sum of the row orders, exceed the number of proper rows, which bounds the number of
  distinct proper germs.)  Empty defect still does NOT give normal crossings of the supports.
* `exists_actual_carrier_phase_protected`: the held true-defect exit, re-derived with centres
  over the defect, is a carrier-preparation phase in the sense needed by the held lower sharp
  entry: at its end every row has order `≤ 1` and the true defect is empty, and it restricts to a
  literal empty tower near the support of every row prepared at its start. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaG34DefectEmptyOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4SharpBadFootprint
  GermIdealOrder DivisorExponentAlong RestrictEmptyTower HomogenizedGlueingTower
  HironakaG4CompactWholeMonomialMaskPhase
open ResolutionInvariantExt (IsEmptyTower)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- Private copy (`HironakaActualGlobalDefectProfileFold`, private there). -/
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

/-- **Empty true distinct defect gives order `≤ 1` on every row.** -/
theorem ordinaryTraceOrder_le_one_of_distinctDefect_eq_empty (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hEmpty : chronologicalDistinctDefect W E T = ∅) :
    ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N, ∀ a : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1 := by
  intro x hxN a
  let A := geoTransformAlong (geometricTemplate W []) T
  let F := fun b : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get b)) T).ideal
  have hN : IsClosedSubmanifold n A.N :=
    (MarkedIdealRestrictOpen.isClosedSubmanifold_N_and_isCoherent_geoTransformAlong
      (𝔪 := geometricTemplate W []) hW IdealWeightPowers.isCoherent_unitIdeal T hT).1
  have hGeo : ∀ b : Fin E.length, (F b).IsCoherent ∧ ∀ z ∈ A.N, IsNonzeroAlongAt A.N (F b) z := by
    intro b
    obtain ⟨hNb,_hEb,_hDb,hwb,hnzb,_hprb⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense b T hT
    refine ⟨hwb.isCoherent,?_⟩
    rw [←hNb]
    exact hnzb
  -- a row of positive order at `x` is proper
  have hProper : ∀ b : Fin E.length, 1 ≤ ordinaryTraceOrder A.N (F b) x →
      b ∈ actualProperPositions F x := by
    intro b hb
    have hcos := (ordinaryTraceOrder_cosupport_iff hN (hGeo b).1 (hGeo b).2 hxN 1).mpr hb
    rw [cosupport_one (fun z g hg => MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent (hGeo b).1 z g hg)] at hcos
    exact (actual_proper_iff_zeroLocus (fun c => (hGeo c).1) b x).mpr hcos.2
  -- a proper row has positive order
  have hPos : ∀ b : Fin E.length, b ∈ actualProperPositions F x →
      1 ≤ ordinaryTraceOrder A.N (F b) x := by
    intro b hb
    have hz := (actual_proper_iff_zeroLocus (fun c => (hGeo c).1) b x).mp hb
    have hcos : x ∈ cosupport n A.N (F b) 1 := by
      rw [cosupport_one (fun z g hg => MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent (hGeo b).1 z g hg)]
      exact ⟨hxN,hz⟩
    exact (ordinaryTraceOrder_cosupport_iff hN (hGeo b).1 (hGeo b).2 hxN 1).mp hcos
  by_contra hNot
  have hTwo : 2 ≤ ordinaryTraceOrder A.N (F a) x := by
    change ¬ ordinaryTraceOrder A.N (F a) x ≤ 1 at hNot
    omega
  have haP : a ∈ actualProperPositions F x := hProper a (by omega)
  let ind := fun b : Fin E.length => if ¬(F b).mem x (1 : Y → ℂ) then 1 else 0
  have hInd : ∀ b, ind b ≤ ordinaryTraceOrder A.N (F b) x := by
    intro b
    by_cases hb : ¬(F b).mem x (1 : Y → ℂ)
    · simp only [ind,if_pos hb]
      exact hPos b (Finset.mem_filter.mpr ⟨Finset.mem_univ b,hb⟩)
    · simp only [ind,if_neg hb]
      exact Nat.zero_le _
  have hCard : (actualProperPositions F x).card = ∑ b, ind b := by
    unfold actualProperPositions
    rw [Finset.card_filter]
  have haP' : ¬(F a).mem x (1 : Y → ℂ) := (Finset.mem_filter.mp haP).2
  have hSumInd : ∑ b, ind b = 1 + ∑ b ∈ Finset.univ.erase a, ind b := by
    rw [←Finset.add_sum_erase _ _ (Finset.mem_univ a)]
    simp only [ind,if_pos haP']
  have hSumOrd : ∑ b, ordinaryTraceOrder A.N (F b) x =
      ordinaryTraceOrder A.N (F a) x + ∑ b ∈ Finset.univ.erase a, ordinaryTraceOrder A.N (F b) x :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ a)).symm
  have hErase : ∑ b ∈ Finset.univ.erase a, ind b ≤
      ∑ b ∈ Finset.univ.erase a, ordinaryTraceOrder A.N (F b) x :=
    Finset.sum_le_sum fun b _ => hInd b
  have hCount : actualDistinctProperCount F x ≤ (actualProperPositions F x).card :=
    Finset.card_image_le
  have hProd := chronological_product_order_sum hn hW hE hdense T hT hxN
  have hDef : x ∈ chronologicalDistinctDefect W E T := by
    refine ⟨hxN,?_⟩
    change actualDistinctProperCount F x <
      ordinaryTraceOrder A.N (relativeIdealListProduct A.N (List.ofFn F)) x
    rw [←chronological_product_eq_actual_family_product W E T]
    rw [hProd]
    change actualDistinctProperCount F x < ∑ b, ordinaryTraceOrder A.N (F b) x
    omega
  rw [hEmpty] at hDef
  exact hDef

/-- **The carrier-preparation phase of the sharp row loop, protected.**  From an actual sharp
state, the held true-defect exit (with centres over the defect) reaches a state where EVERY row
has order `≤ 1` and the true defect is empty (the row hypotheses of the held lower sharp entry), and
it is a literal empty phase near the support of every row prepared at its start. -/
theorem exists_actual_carrier_phase_protected (hn : 0 < n)
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
      CentresOver (chronologicalDistinctDefect W E T) Q ∧
      chronologicalDistinctDefect W E (T.append Q) = ∅ ∧
      (∀ x ∈ (geoTransformAlong (geometricTemplate W []) (T.append Q)).N, ∀ a : Fin E.length,
        ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) (T.append Q)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) (T.append Q)).ideal x ≤ 1) ∧
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
  obtain ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,_hRows,_hFoot,hOver,hEmpty⟩ :=
    HironakaG34DefectExitCentresOver.exists_actual_global_original_distinct_defect_exit_centresOver
      hn hW hE hdense d hReg hK T hT hFull hSharp
  refine ⟨Z,Q,hTQ,hFullTQ,hSharpTQ,hOver,hEmpty,
    ordinaryTraceOrder_le_one_of_distinctDefect_eq_empty hn hW hE hdense (T.append Q) hTQ hEmpty,
    fun i hOrd hNC hDenseS => ?_⟩
  obtain ⟨U,hUeq,hSU⟩ := HironakaG34PreparedRowDefectFree.actual_prepared_row_defect_free_near
    hn hW hE hdense d hReg i T hT hFull hOrd hNC hDenseS
  refine ⟨U,hSU,isEmptyTower_restrict_of_centresOver U ?_ Q hOver⟩
  rw [hUeq]
  exact disjoint_compl_left

end
end Hironaka.HironakaG34DefectEmptyOrder
