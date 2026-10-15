/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalSharedTraceBranchDimension
import Hironaka.Resolution.HironakaEmbeddedAnalyticLocal

/-! Literal FIRST Z={nu>actual DISTINCT proper trace count} has genuine finite
analytic equations from original factor multiplicities and actual shared
trace ideal / pair dimension recognition. FIRST Z remains distinct from the
full sharp simultaneous-NC bad locus. Complete source-first BP precedes code. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalDistinctDefectAnalytic
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpOriginalSharedTraceBranchDimension HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalMemberProduct
  AnalyticDimensionBasics GermIdealOrder NormalCrossings RelativePrincipalizationSpan
variable {n : ℕ} {X : CMfd.{u} n}

/-- The true distinct quotient collision, retaining all actual original positions. -/
theorem originalDistinctDefectPhase_iff_actual_witness (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hx : x ∈ W) :
    x ∈ originalDistinctDefectPhase W E ↔
      (∃ i : Fin E.length,2 ≤ ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x) ∨
      ∃ i j : Fin E.length,i ≠ j ∧ x ∈ E.get i ∧ x ∈ E.get j ∧ (traceGermSetoid (n := n) W E x).r i j := by
  have hbound := distinctProperTraceGermCount_le_originalProductTraceOrder hn hW hE hdense hx
  have heq := originalProductOrder_eq_distinct_iff hn hW hE hdense hx
  have hproper (i : Fin E.length) : i ∈ properTraceMembers (n := n) W E x ↔ x ∈ E.get i := by
    rw [properTraceMembers_eq_incident hE.1 hx]
    simp
  constructor
  · intro hz
    by_cases hhigh : ∃ i : Fin E.length,2 ≤ ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x
    · exact Or.inl hhigh
    · right
      have hfactor : ∀ i : Fin E.length,x ∈ E.get i → ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x=1 := by
        intro i hi
        have hpos := (one_le_originalMemberTraceOrder_iff hn hW hE hdense hx i).mpr hi
        have hnot : ¬2 ≤ ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x := fun h => hhigh ⟨i,h⟩
        omega
      by_contra hcollision
      have hinj : Set.InjOn (Quotient.mk (traceGermSetoid (n := n) W E x)) (properTraceMembers (n := n) W E x) := by
        intro i hi j hj hij
        by_contra hne
        exact hcollision ⟨i,j,hne,(hproper i).mp hi,(hproper j).mp hj,Quotient.exact hij⟩
      exact (ne_of_gt hz.2) (heq.mpr ⟨hfactor,hinj⟩)
  · intro hwitness
    refine ⟨hx,lt_of_le_of_ne hbound ?_⟩
    intro he
    obtain ⟨hfactor,hinj⟩ := heq.mp he.symm
    rcases hwitness with ⟨i,hi⟩ | ⟨i,j,hne,hxi,hxj,hrel⟩
    · have hxi := (one_le_originalMemberTraceOrder_iff hn hW hE hdense hx i).mp (by omega)
      have hoi := hfactor i hxi
      omega
    · exact hne (hinj ((hproper i).mpr hxi) ((hproper j).mpr hxj) (Quotient.sound hrel))

/-- Literal high-factor equations for the SAME original member ideals. -/
def originalHighFactorOrderLocus (W : Set X) (E : List (Set X)) : Set X :=
  ⋃ i : Fin E.length,cosupport n W (vanishingIdeal (n := n) (E.get i)) 2

/-- Actual distinct-pair local dimension equations, with the true diagonal excluded. -/
def originalSharedTraceDimensionLocus (W : Set X) (E : List (Set X)) (d : ℕ) : Set X :=
  ⋃ i : Fin E.length,⋃ j : Fin E.length,if i=j then ∅ else {x | LocDimGE (n := n) (W ∩ E.get i ∩ E.get j) x d}

private theorem pair_analytic (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (i j : Fin E.length) :
    IsComplexAnalyticSubset (n := n) (W ∩ E.get i ∩ E.get j) :=
  ((AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hW).inter
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold (MonomialPart.isClosedSubmanifold_get hn hE i))).inter
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold (MonomialPart.isClosedSubmanifold_get hn hE j))

/-- BOTH actual high-order / pair-dimension directions at EVERY actual original point. -/
theorem originalDistinctDefectPhase_eq_finite_geometric_loci (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1)) :
    originalDistinctDefectPhase W E=originalHighFactorOrderLocus W E ∪ originalSharedTraceDimensionLocus W E d := by
  have hI (i : Fin E.length) := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
  have hNE (i : Fin E.length) : ∀ x ∈ W,DivisorExponentAlong.IsNonzeroAlongAt W (vanishingIdeal (n := n) (E.get i)) x :=
    fun _ hx => originalMemberIdeal_isNonzeroAlongAt hE hdense (List.get_mem E i) hx
  have hhigh (x : X) : x ∈ originalHighFactorOrderLocus W E ↔
      ∃ i : Fin E.length,x ∈ cosupport n W (vanishingIdeal (n := n) (E.get i)) 2 := by
    simp only [originalHighFactorOrderLocus,mem_iUnion]
  have hpair (x : X) : x ∈ originalSharedTraceDimensionLocus W E d ↔
      ∃ i j : Fin E.length,i ≠ j ∧ LocDimGE (n := n) (W ∩ E.get i ∩ E.get j) x d := by
    simp only [originalSharedTraceDimensionLocus,mem_iUnion]
    constructor
    · rintro ⟨i,j,hx⟩
      by_cases hij : i=j
      · simp [hij] at hx
      · exact ⟨i,j,hij,by simpa only [if_neg hij,mem_ofPred_eq] using hx⟩
    · rintro ⟨i,j,hij,hdim⟩
      exact ⟨i,j,by simpa only [if_neg hij,mem_ofPred_eq] using hdim⟩
  ext x
  constructor
  · intro hz
    rcases (originalDistinctDefectPhase_iff_actual_witness hn hW hE hdense hz.1).mp hz with hhi | ⟨i,j,hij,hxi,hxj,hrel⟩
    · obtain ⟨i,hi⟩ := hhi
      exact Or.inl ((hhigh x).mpr ⟨i,(ordinaryTraceOrder_cosupport_iff hW (hI i) (hNE i) hz.1 2).mpr hi⟩)
    · by_cases hhi : ∃ a : Fin E.length,2 ≤ ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get a)) x
      · obtain ⟨a,ha⟩ := hhi
        exact Or.inl ((hhigh x).mpr ⟨a,(ordinaryTraceOrder_cosupport_iff hW (hI a) (hNE a) hz.1 2).mpr ha⟩)
      · have hoi : ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x=1 := by
          have hpos := (one_le_originalMemberTraceOrder_iff hn hW hE hdense hz.1 i).mpr hxi
          have hnot : ¬2 ≤ ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x := fun hi => hhi ⟨i,hi⟩
          omega
        exact Or.inr ((hpair x).mpr ⟨i,j,hij,pair_locDimGE_of_original_traceGerm_rel hn hW hE hdense hz.1 (hreg x hz.1) i j hoi hrel⟩)
  · rintro (hhi | hp)
    · obtain ⟨i,hi⟩ := (hhigh x).mp hhi
      exact (originalDistinctDefectPhase_iff_actual_witness hn hW hE hdense hi.1).mpr
        (Or.inl ⟨i,(ordinaryTraceOrder_cosupport_iff hW (hI i) (hNE i) hi.1 2).mp hi⟩)
    · obtain ⟨i,j,hij,hdim⟩ := (hpair x).mp hp
      have hxA := CodimOneSupport.mem_of_locDimGE (pair_analytic hn hW hE i j).isClosed hdim
      have hxW := hxA.1.1
      apply (originalDistinctDefectPhase_iff_actual_witness hn hW hE hdense hxW).mpr
      by_cases hhi : ∃ a : Fin E.length,2 ≤ ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get a)) x
      · exact Or.inl hhi
      · have horder (a : Fin E.length) (hxa : x ∈ E.get a) :
            ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get a)) x=1 := by
          have hpos := (one_le_originalMemberTraceOrder_iff hn hW hE hdense hxW a).mpr hxa
          have hnot : ¬2 ≤ ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get a)) x := fun ha => hhi ⟨a,ha⟩
          omega
        exact Or.inr ⟨i,j,hij,hxA.1.2,hxA.2,original_traceGerm_rel_of_pair_locDimGE hn hW hE hdense hxW
          (hreg x hxW) i j (horder i hxA.1.2) (horder j hxA.2) hdim⟩

private theorem analytic_finset_union {ι : Type*} (t : Finset ι) (A : ι → Set X)
    (hA : ∀ i ∈ t,IsComplexAnalyticSubset (n := n) (A i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i ∈ t,A i) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.set_biUnion_insert]
    exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
      (hA i (Finset.mem_insert_self i t)) (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

private theorem analytic_finite_union {ι : Type*} [Fintype ι] (A : ι → Set X)
    (hA : ∀ i,IsComplexAnalyticSubset (n := n) (A i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i,A i) := by
  simpa only [Finset.mem_univ,iUnion_true] using analytic_finset_union Finset.univ A (fun i _ => hA i)

/-- GENUINE original-only global analytic producer for the literal FIRST defect. -/
theorem isComplexAnalyticSubset_originalDistinctDefectPhase (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1)) :
    IsComplexAnalyticSubset (n := n) (originalDistinctDefectPhase W E) := by
  rw [originalDistinctDefectPhase_eq_finite_geometric_loci hn hW hE hdense d hreg]
  apply HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
  · apply analytic_finite_union
    intro i
    exact CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along
      (VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)) hW (by omega)
  · apply analytic_finite_union
    intro i
    apply analytic_finite_union
    intro j
    by_cases hij : i=j
    · simp only [if_pos hij]
      simp
    · simp only [if_neg hij]
      exact isComplexAnalyticSubset_locDimGE (pair_analytic hn hW hE i j) d

/-- Closedness is independently inherited from the actual whole analytic equations. -/
theorem isClosed_originalDistinctDefectPhase (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1)) :
    IsClosed (originalDistinctDefectPhase W E) :=
  (isComplexAnalyticSubset_originalDistinctDefectPhase hn hW hE hdense d hreg).isClosed

/-- Actual compact carrier now internally supplies compactness of SAME literal FIRST Z. -/
theorem isCompact_originalDistinctDefectPhase (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1)) (hcomp : IsCompact W) :
    IsCompact (originalDistinctDefectPhase W E) :=
  hcomp.of_isClosed_subset (isClosed_originalDistinctDefectPhase hn hW hE hdense d hreg) (fun _ hx => hx.1)

end
end Hironaka.HironakaSharpOriginalDistinctDefectAnalytic
