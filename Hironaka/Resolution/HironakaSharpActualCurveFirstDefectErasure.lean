/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveWholeDefectCentre

/-! Actual small-order proper-position/count rigidity and genuine one-step
curve FIRST-Z erasure on the SAME ORIGINAL mark-one test history. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveFirstDefectErasure
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveWholeDefectCentre HironakaSharpActualCurveExceptionalResidualUnit
  HironakaSharpActualFirstGoodCurveBase HironakaSharpActualFirstGoodReducedTraces
  HironakaSharpActualOriginalControlledHistory HironakaSharpActualOriginalDynamicStep
  HironakaSharpOriginalMemberProductDomain HironakaSharpActualDynamicDistinctCentre
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpOriginalProductTraceOrder
  HironakaCoherentTransformExtension RelativePrincipalizationSpan DivisorExponentAlong
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder IdealWeightPowers
  NonmonomialOrderLocal RestrictedIdealExtension
open ResolutionInvariantSpec (IsInvDomain)
variable {n m : ℕ} {X Y : CMfd.{u} n}

/-- True additivity and properness construct BOTH actual indexed and genuine
quotient-image counts when the ACTUAL product order is at most one. -/
theorem actual_product_order_le_one_count_dictionary {N : Set X} (hN : IsClosedSubmanifold n N)
    {F : Fin m → GermIdeal n X} (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ a,(F i).mem y a ↔
      HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    {x : X} (hx : x ∈ N)
    (hle : ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x ≤ 1) :
    (actualProperPositions F x).card=ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x ∧
      actualDistinctProperCount F x=ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x ∧
      x ∉ actualFamilyDistinctDefect N F := by
  have hall : ∀ I ∈ List.ofFn F,I.IsCoherent ∧ (∀ y ∈ N,IsNonzeroAlongAt N I y) ∧
      ∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ a,I.mem y a ↔
        HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a := by
    intro I hI
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hI
    exact ⟨hc i,hnz i,hpr i⟩
  have hs := (relativeIdealListProduct_actual_geometry hN (List.ofFn F)
    (fun I hI => (hall I hI).1) (fun I hI => (hall I hI).2.1)
    (fun I hI => (hall I hI).2.2)).2.2.2 x hx
  have hsum : ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x=
      ∑ i,ordinaryTraceOrder N (F i) x := by
    simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hs
  have hpos (i : Fin m) : 1 ≤ ordinaryTraceOrder N (F i) x ↔ i ∈ actualProperPositions F x := by
    rw [actual_proper_iff_zeroLocus hc i x]
    have hcos := cosupport_one (N := N)
      (fun _ _ ha => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem (hc i) ha)
    rw [←ordinaryTraceOrder_cosupport_iff hN (hc i) (hnz i) hx 1,hcos]
    simp only [mem_inter_iff,hx,true_and]
  have hfactor (i : Fin m) : ordinaryTraceOrder N (F i) x ≤ 1 :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (ordinaryTraceOrder N (F j) x))
      (Finset.mem_univ i)).trans (hsum ▸ hle)
  have hval (i : Fin m) : ordinaryTraceOrder N (F i) x=if i ∈ actualProperPositions F x then 1 else 0 := by
    by_cases hi : i ∈ actualProperPositions F x
    · rw [if_pos hi]
      exact Nat.le_antisymm (hfactor i) ((hpos i).mpr hi)
    · rw [if_neg hi]
      have hh := mt (hpos i).mp hi
      omega
  have hcard : (actualProperPositions F x).card=ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x := by
    rw [hsum]
    simp_rw [hval]
    simp
  have hcard1 : (actualProperPositions F x).card ≤ 1 := hcard.trans_le hle
  have hinj : Set.InjOn (Quotient.mk (actualIdealGermSetoid F x)) (actualProperPositions F x) := by
    intro i hi j hj _hij
    exact Finset.card_le_one.mp hcard1 i hi j hj
  have hcount : actualDistinctProperCount F x=ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x :=
    (Finset.card_image_of_injOn hinj).trans hcard
  refine ⟨hcard,hcount,?_⟩
  intro hz
  exact (ne_of_lt hz.2) hcount

/-- ONLY original curve inputs give the actual FIRST-good order bound by
true pairwise trace separation and real proper-position membership. -/
theorem original_curve_first_good_order_le_one (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    {x : Y} (hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N)
    (hxGood : x ∉ chronologicalDistinctDefect W E T) :
    ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N (chronologicalMemberProduct W E T) x ≤ 1 := by
  obtain ⟨O,hO,hTraces⟩ := exists_original_curve_first_good_trace_separation hn hW hE hdense hr T hT
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hc (i : Fin E.length) := (original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT).2.2.2.1.isCoherent
  have hxO : x ∈ O := by
    change x ∈ (O : Set Y)
    rw [hO]
    exact hxGood
  let z : O := ⟨x,hxO⟩
  have hcard : (actualProperPositions F x).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hne
    have hxi : z ∈ (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T :=
      ⟨hx,(actual_proper_iff_zeroLocus hc i x).mp hi⟩
    have hxj : z ∈ (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E j T :=
      ⟨hx,(actual_proper_iff_zeroLocus hc j x).mp hj⟩
    exact Set.disjoint_left.mp ((hTraces i).2.2.2 j (Ne.symm hne)) hxi hxj
  have hcount : actualDistinctProperCount F x ≤ 1 := Finset.card_image_le.trans hcard
  have hν : ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
      (relativeIdealListProduct (geoTransformAlong (geometricTemplate W []) T).N (List.ofFn F)) x ≤
        actualDistinctProperCount F x := by
    apply Nat.le_of_not_gt
    intro h
    exact hxGood ⟨hx,h⟩
  rw [←chronological_product_eq_actual_family_product W E T] at hν
  exact hν.trans hcount

/-- EVERY actual whole-FIRST-Z blowup genuinely extends the SAME original
record and erases the NEW FIRST Z; actual new counts are proved, not inferred
from an original order equality. -/
theorem original_curve_whole_defect_blowup_erases_first_defect (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {Z : CMfd.{u} n} {π : Z → Y} (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E T) π) :
    chronologicalDistinctDefect W E (.step T (chronologicalDistinctDefect W E T) π hπ)=∅ := by
  let M := originalMemberProductMarked W E 1
  let C := chronologicalDistinctDefect W E T
  let T' := BlowupTower.step T C π hπ
  have hInit : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit T hT
  have hC := (original_curve_whole_defect_admissible hn hW hE hdense hr T hT).1
  have hT' : IsGeoTestTower M T' := ⟨hT,hC⟩
  have hGeom := actual_original_test_history_template M hInit.isWellFormed T hT
  have hGeom' := actual_original_test_history_template M hInit.isWellFormed T' hT'
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwOld := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hGeom
  have hwNew := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T' hGeom'
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  by_cases hzC : π z ∈ C
  · have hzE : z ∈ ⋃ H ∈ (geoTransformAlong (geometricTemplate W []) T').E,H := by
      change z ∈ ⋃ H ∈ ((geoTransformAlong (geometricTemplate W []) T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π C) ++ [π ⁻¹' C]),H
      exact mem_iUnion₂.mpr ⟨π ⁻¹' C,by simp,hzC⟩
    exact (original_curve_exceptional_residual_units_and_defect_disjoint hn hW hE hdense hr T' hGeom' z hz.1 hzE).2.2 hz
  · have hmaps := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage (C := C)
      hπ.contMDiff.continuous hwOld.isClosedSubmanifold_N.1
    have hzOld : π z ∈ (geoTransformAlong (geometricTemplate W []) T).N := hmaps hz.1
    have hOldLE := original_curve_first_good_order_le_one hn hW hE hdense hr T hGeom hzOld hzC
    have hold := (original_product_nmOrd_eq_current hn hW hE hdense 1 T hT (π z)).trans
      (currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T hGeom (π z))
    have hnew := (original_product_nmOrd_eq_current hn hW hE hdense 1 T' hT' z).trans
      (currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T' hGeom' z)
    have heq := nmOrd_geoTransform_of_notMem hn hDom hC hπ hzC
    change nmOrd (geoTransformAlong M T') z=nmOrd (geoTransformAlong M T) (π z) at heq
    have hNewLE : ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T').N
        (chronologicalMemberProduct W E T') z ≤ 1 := by
      rw [←hnew,heq,hold]
      exact hOldLE
    let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T').ideal
    have hfam : ∀ i : Fin E.length,(F i).IsCoherent ∧
        (∀ y ∈ (geoTransformAlong (geometricTemplate W []) T').N,
          IsNonzeroAlongAt (geoTransformAlong (geometricTemplate W []) T').N (F i) y) ∧
        ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T').N,∃ f : Z → ℂ,HolomorphicAt n f y ∧
          ∀ a,(F i).mem y a ↔ HolomorphicAt n a y ∧
            IsInSpanOnAt (n := n) (geoTransformAlong (geometricTemplate W []) T').N (·=f) y a := by
      intro i
      obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T' hGeom'
      rw [hNi] at hnzi hpri
      exact ⟨hwi.isCoherent,hnzi,hpri⟩
    rw [chronological_product_eq_actual_family_product W E T'] at hNewLE
    exact (actual_product_order_le_one_count_dictionary hwNew.isClosedSubmanifold_N
      (fun i => (hfam i).1) (fun i => (hfam i).2.1) (fun i => (hfam i).2.2) hz.1 hNewLE).2.2 hz

/-- ONLY original inputs construct the SAME global projection, whole good
complement isomorphism and ORIGINAL test append with EMPTY NEW FIRST Z. -/
theorem exists_original_curve_first_defect_erasing_step (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    ∃ (Z : CMfd.{u} n) (π : Z → Y)
      (hπ : IsBlowupAlong n (chronologicalDistinctDefect W E T) π),
      IsProperMap π ∧ ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π ∧
      IsIsomorphismOver n π (chronologicalDistinctDefect W E T)ᶜ ∧
      IsGeoTestTower (originalMemberProductMarked W E 1)
        (.step T (chronologicalDistinctDefect W E T) π hπ) ∧
      IsInvDomain 1 (geoTransformAlong (originalMemberProductMarked W E 1)
        (.step T (chronologicalDistinctDefect W E T) π hπ)) ∧
      IsSNCDivisor n ((geoTransformAlong (originalMemberProductMarked W E 1) T).E.map
        (BlowupStrictSubmanifold.geoStrictTransform π (chronologicalDistinctDefect W E T)) ++
          [π ⁻¹' chronologicalDistinctDefect W E T]) ∧
      chronologicalDistinctDefect W E (.step T (chronologicalDistinctDefect W E T) π hπ)=∅ := by
  obtain ⟨Z,π,hπ,hproper,hholo,hiso,hnew,hdom,hSNC⟩ :=
    exists_original_curve_whole_defect_blowup hn hW hE hdense hr T hT
  exact ⟨Z,π,hπ,hproper,hholo,hiso,hnew,hdom,hSNC,
    original_curve_whole_defect_blowup_erases_first_defect hn hW hE hdense hr T hT hπ⟩

end
end Hironaka.HironakaSharpActualCurveFirstDefectErasure
