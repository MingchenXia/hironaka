/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalDeepProductBlowup

/-! True original FIRST-phase nu versus DISTINCT proper trace classes at ALL
carrier points. This is NOT the full non-NC locus Sigma. Complete source-first
mathematics precedes code; recursive intersections/exceptional cleanup remain open. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalDistinctDefectPhase
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers GermIdealOrder NormalCrossings
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalAllBoundaryCentre
  HironakaSharpOriginalDeepProductBlowup HironakaSharpOriginalMultiBoundaryBadLocus
  DivisorExponentAlong
variable {n : ℕ} {X : CMfd.{u} n}

/-- True original proper trace positions coincide with actual member incidence, even at BAD points. -/
theorem properTraceMembers_eq_incident {W : Set X} {E : List (Set X)}
    (hE : ∀ H ∈ E,IsClosed H) {x : X} (hx : x ∈ W) :
    properTraceMembers (n := n) W E x = Finset.univ.filter fun i => x ∈ E.get i := by
  ext i
  simp only [properTraceMembers,Finset.mem_filter,Finset.mem_univ,true_and,
    traceSpan_unit_iff_notMem (hE _ (List.get_mem E i)) hx,not_not]

/-- Actual factor order-one cosupport detects true incidence at EVERY original carrier point. -/
theorem one_le_originalMemberTraceOrder_iff (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hx : x ∈ W) (i : Fin E.length) :
    1 ≤ ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x ↔ x ∈ E.get i := by
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
  have hne : ∀ y ∈ W,IsNonzeroAlongAt W (vanishingIdeal (n := n) (E.get i)) y :=
    fun _ hy => originalMemberIdeal_isNonzeroAlongAt hE hdense (List.get_mem E i) hy
  rw [← ordinaryTraceOrder_cosupport_iff hW hI hne hx 1,
    SmoothCentreLocus.cosupport_vanishingIdeal_one (hE.1 _ (List.get_mem E i))]
  exact ⟨fun h => h.2,fun h => ⟨hx,h⟩⟩

theorem originalMemberTraceOrder_eq_zero_of_notMem (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hx : x ∈ W)
    (i : Fin E.length) (hi : x ∉ E.get i) :
    ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x = 0 := by
  have hh := one_le_originalMemberTraceOrder_iff hn hW hE hdense hx i
  have hnot : ¬1 ≤ ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x := fun h => hi (hh.mp h)
  omega

/-- The SAME literal original finite factor sum, with all multiplicities retained. -/
theorem originalProductOrder_eq_fin_sum (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hx : x ∈ W) :
    ordinaryTraceOrder W (originalMemberProduct (n := n) E) x =
      ∑ i : Fin E.length,ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x := by
  rw [originalMemberProduct_traceOrder_eq_sum hn hW E hE hdense hx]
  conv_lhs => rw [← List.ofFn_get E,List.map_ofFn,List.sum_ofFn]
  rfl

theorem distinctProperTraceGermCount_le_incident {W : Set X} {E : List (Set X)}
    (hE : ∀ H ∈ E,IsClosed H) {x : X} (hx : x ∈ W) :
    distinctProperTraceGermCount (n := n) W E x ≤ BoundaryCount.boundaryCount E x := by
  unfold distinctProperTraceGermCount
  exact Finset.card_image_le.trans_eq (congrArg Finset.card (properTraceMembers_eq_incident hE hx))

theorem distinctProperTraceGermCount_le_length {W : Set X} {E : List (Set X)}
    (hE : ∀ H ∈ E,IsClosed H) {x : X} (hx : x ∈ W) :
    distinctProperTraceGermCount (n := n) W E x ≤ E.length := by
  have hcard : BoundaryCount.boundaryCount E x ≤ E.length := by
    unfold BoundaryCount.boundaryCount
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simp)
  exact (distinctProperTraceGermCount_le_incident hE hx).trans hcard

/-- This bound uses true factor orders, never a BAD-point DISTINCT/indexed-count substitution. -/
theorem boundaryCount_le_originalProductTraceOrder (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hx : x ∈ W) :
    BoundaryCount.boundaryCount E x ≤ ordinaryTraceOrder W (originalMemberProduct (n := n) E) x := by
  rw [originalProductOrder_eq_fin_sum hn hW hE hdense hx]
  have hb : BoundaryCount.boundaryCount E x = ∑ i : Fin E.length,if x ∈ E.get i then (1 : ℕ) else 0 := by
    simp [BoundaryCount.boundaryCount,Finset.sum_boole]
  rw [hb]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : x ∈ E.get i
  · simp only [hi,ite_true]
    exact (one_le_originalMemberTraceOrder_iff hn hW hE hdense hx i).mpr hi
  · simp only [hi,ite_false]
    exact Nat.zero_le _

/-- True ALL-point nu >= actual DISTINCT proper trace classes. -/
theorem distinctProperTraceGermCount_le_originalProductTraceOrder (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hx : x ∈ W) :
    distinctProperTraceGermCount (n := n) W E x ≤ ordinaryTraceOrder W (originalMemberProduct (n := n) E) x :=
  (distinctProperTraceGermCount_le_incident hE.1 hx).trans (boundaryCount_le_originalProductTraceOrder hn hW hE hdense hx)

/-- Exact FIRST-phase equality recognition retains true order-one factors and actual DISTINCT germ classes. -/
theorem originalProductOrder_eq_distinct_iff (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hx : x ∈ W) :
    ordinaryTraceOrder W (originalMemberProduct (n := n) E) x = distinctProperTraceGermCount (n := n) W E x ↔
      (∀ i : Fin E.length,x ∈ E.get i → ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x=1) ∧
      Set.InjOn (Quotient.mk (traceGermSetoid (n := n) W E x)) (properTraceMembers (n := n) W E x) := by
  let a : Fin E.length → ℕ := fun i => ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x
  let b : Fin E.length → ℕ := fun i => if x ∈ E.get i then 1 else 0
  have hsuma := originalProductOrder_eq_fin_sum hn hW hE hdense hx
  have hsumb : BoundaryCount.boundaryCount E x = ∑ i,b i := by
    simp [BoundaryCount.boundaryCount,b,Finset.sum_boole]
  have hpcard : (properTraceMembers (n := n) W E x).card = BoundaryCount.boundaryCount E x :=
    congrArg Finset.card (properTraceMembers_eq_incident hE.1 hx)
  have hb_le : ∀ i,b i ≤ a i := by
    intro i
    by_cases hi : x ∈ E.get i
    · change (if x ∈ E.get i then 1 else 0) ≤ a i
      rw [if_pos hi]
      exact (one_le_originalMemberTraceOrder_iff hn hW hE hdense hx i).mpr hi
    · change (if x ∈ E.get i then 1 else 0) ≤ a i
      rw [if_neg hi]
      exact Nat.zero_le _
  constructor
  · intro heq
    have hcount : BoundaryCount.boundaryCount E x = ordinaryTraceOrder W (originalMemberProduct (n := n) E) x :=
      (boundaryCount_le_originalProductTraceOrder hn hW hE hdense hx).antisymm
        (heq ▸ distinctProperTraceGermCount_le_incident hE.1 hx)
    have hsum : (∑ i,b i) = ∑ i,a i := hsumb.symm.trans (hcount.trans hsuma)
    have hfactor := factor_eq_of_sum_eq hb_le hsum
    refine ⟨?_,?_⟩
    · intro i hi
      have hiFactor := hfactor i
      change (if x ∈ E.get i then 1 else 0) = a i at hiFactor
      rw [if_pos hi] at hiFactor
      exact hiFactor.symm
    · have hclass : distinctProperTraceGermCount (n := n) W E x = (properTraceMembers (n := n) W E x).card :=
        heq.symm.trans (hcount.symm.trans hpcard.symm)
      exact Finset.card_image_iff.mp hclass
  · rintro ⟨hfactor,hinj⟩
    have hsum : (∑ i,a i) = ∑ i,b i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : x ∈ E.get i
      · change ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x = if x ∈ E.get i then 1 else 0
        rw [if_pos hi]
        exact hfactor i hi
      · change ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x = if x ∈ E.get i then 1 else 0
        rw [if_neg hi]
        exact originalMemberTraceOrder_eq_zero_of_notMem hn hW hE hdense hx i hi
    calc
      ordinaryTraceOrder W (originalMemberProduct (n := n) E) x = ∑ i,a i := hsuma
      _ = ∑ i,b i := hsum
      _ = BoundaryCount.boundaryCount E x := hsumb.symm
      _ = (properTraceMembers (n := n) W E x).card := hpcard.symm
      _ = distinctProperTraceGermCount (n := n) W E x := (Finset.card_image_of_injOn hinj).symm

/-- The genuine initial FIRST product phase; subsequent intersection/monomial defects need not belong here. -/
def originalDistinctDefectPhase (W : Set X) (E : List (Set X)) : Set X :=
  {x | x ∈ W ∧ distinctProperTraceGermCount (n := n) W E x <
    ordinaryTraceOrder W (originalMemberProduct (n := n) E) x}

/-- True deep product order forces membership in the actual first-phase DISTINCT defect. -/
theorem originalDeepProduct_cosupp_subset_distinctDefectPhase (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) :
    (originalMemberProductMarked W E (E.length+1)).cosupp ⊆ originalDistinctDefectPhase W E := by
  intro x hx
  have hI := isCoherent_originalMemberProduct hn hE
  have hne : ∀ y ∈ W,IsNonzeroAlongAt W (originalMemberProduct (n := n) E) y :=
    fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hE hdense hy
  have hq := (ordinaryTraceOrder_cosupport_iff hW hI hne hx.1 (E.length+1)).mp hx
  exact ⟨hx.1,(distinctProperTraceGermCount_le_length hE.1 hx.1).trans_lt (Nat.lt_of_succ_le hq)⟩

/-- Original inputs select the SAME true deep maxC inside actual FIRST-phase Z, with real ALL-E admissibility. -/
theorem exists_actual_original_firstPhase_deep_centre (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x d)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hcompact : IsCompact W)
    (hne : (originalMemberProductMarked W E (E.length+1)).cosupp.Nonempty) :
    ∃ C : Set X,C.Nonempty ∧ (originalMemberProductMarked W E (E.length+1)).IsAdmissibleCentre C ∧
      C ⊆ originalDistinctDefectPhase W E ∧ C ⊆ originalSharpBadLocus (n := n) W E ∧
      Disjoint C (originalGoodLocus (n := n) W E) ∧
      (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      C=ResolutionDriver.maxLocus ((CanonicalCentres.invFamily hn (n+1)).inv
        (originalMemberProductMarked W E (E.length+1)) (.refl : BlowupTower X X))
        (originalMemberProductMarked W E (E.length+1)).cosupp := by
  obtain ⟨C,hneC,hadm,hbad,_hboundary,hdis,hemb,heq⟩ :=
    exists_actual_original_deepProduct_centre hn hW hE hd hreg hdense hcompact hne
  exact ⟨C,hneC,hadm,hadm.2.1.trans (originalDeepProduct_cosupp_subset_distinctDefectPhase hn hW hE hdense),
    hbad,hdis,hemb,heq⟩

end
end Hironaka.HironakaSharpOriginalDistinctDefectPhase
