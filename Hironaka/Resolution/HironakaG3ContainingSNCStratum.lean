import Hironaka.Invariant.BoundaryCount
import Hironaka.Resolution.HironakaG8MemberLoci
import Hironaka.Invariant.BoundaryCountAlong
import Hironaka.Resolution.HironakaActualFullBoundaryContainmentPatterns
import Hironaka.Resolution.HironakaG3MixedComponentOpen
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ContainingSNCStratum
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings BoundaryCount HironakaG8MemberLoci
  BoundaryCountAlong SimultaneousNormalCrossings HironakaActualFullBoundaryContainmentPatterns
  HironakaG3MixedComponentOpen

/-- A finite intersection of distinct members of an SNC divisor is smooth of
the expected fixed dimension at every point. -/
theorem memberInter_regularAtDim {n : ℕ} {X : CMfd.{0} n} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (S : Finset (Fin E.length)) :
    ∀ x ∈ memberInter E S, RegularAtDim (n := n) (memberInter E S) x (n - S.card) ∧ S.card ≤ n := by
  intro x hx
  obtain ⟨C,⟨Φ,hsrc,h0,hEq⟩,hcard,hinj⟩ := hE.2 x
  have hThrough (i : Fin E.length) (hi : i ∈ S) : x ∈ E.get i := hx i hi
  have hDis (i j : Fin E.length) (hi : i ∈ S) (hj : j ∈ S) (hne : i ≠ j) :
      Disjoint (C i) (C j) := by
    obtain ⟨a,ha⟩ := Finset.card_eq_one.mp (hcard i (hThrough i hi))
    obtain ⟨b,hb⟩ := Finset.card_eq_one.mp (hcard j (hThrough j hj))
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    have hka : k = a := by simpa only [ha,Finset.mem_singleton] using hki
    have hkb : k = b := by simpa only [hb,Finset.mem_singleton] using hkj
    apply hne
    apply hinj (hThrough i hi) (hThrough j hj)
    rw [ha,hb,hka.symm.trans hkb]
  have hDisS : (↑S : Set (Fin E.length)).PairwiseDisjoint C := by
    intro i hi j hj hne
    exact hDis i j hi hj hne
  have hCard : (S.biUnion C).card = S.card := by
    rw [Finset.card_biUnion hDisS]
    calc
      ∑ i ∈ S, (C i).card = ∑ _i ∈ S, 1 := Finset.sum_congr rfl (fun i hi => hcard i (hThrough i hi))
      _ = S.card := by simp
  have hFlat : ∀ {y : X}, y ∈ (complexChartAt (n := n) x).val.source →
      (complexChartAt (n := n) x).val y ∈ Φ.source →
      (y ∈ memberInter E S ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S.biUnion C)) := by
    intro y hy hyΦ
    rw [mem_coordSubspace_biUnion]
    exact forall₂_congr fun i hi => hEq i (hThrough i hi) hy hyΦ
  have hr := regularAtDim_of_flat_coordSubspace Φ hsrc h0 hFlat
  refine ⟨by simpa only [hCard] using hr,?_⟩
  rw [← hCard]
  simpa using Finset.card_le_univ (S.biUnion C)
private theorem isComplexAnalyticSubset_boundaryMember {n : ℕ} {X : CMfd.{0} n} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (i : Fin E.length) :
    IsComplexAnalyticSubset (n:=n) (E.get i) := by
  by_cases hn : 0<n
  · exact AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
      (MonomialPart.isClosedSubmanifold_get hn hE i)
  · have hn0 : n=0:=by omega
    have hEmpty : E.get i=∅:=by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨S,_hCoord,hCard,_hInj⟩:=hE.2 x
      have hOne:=hCard i hx
      have hLe:=Finset.card_le_univ (s:=S i)
      simp only [Fintype.card_fin] at hLe
      omega
    rw [hEmpty]
    exact isComplexAnalyticSubset_empty


/-- All boundary members containing an irreducible analytic component define
a proper smooth SNC contact. The complementary original sublist is transverse
to it, and the component is dense away from that sublist. -/
theorem irreducible_containing_snc_stratum {n : ℕ} {X : CMfd.{0} n}
    {C : Set X} (hC : IsComplexAnalyticallyIrreducible (n := n) C)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hContained : ∃ H ∈ E, C ⊆ H) :
    let S := Finset.univ.filter (fun i : Fin E.length => C ⊆ E.get i)
    let N := memberInter E S
    let B := remainingBoundary E S
    S.Nonempty ∧ S.card ≤ n ∧ C ⊆ N ∧ IsClosed N ∧
    (∀ x ∈ N, RegularAtDim (n := n) N x (n - S.card)) ∧
    B.Sublist E ∧ (∀ H ∈ E, H ∉ B → N ⊆ H) ∧ IsTransverse n N B ∧
    C ⊆ closure (C \ ⋃ H ∈ B, H) := by
  dsimp only
  let S : Finset (Fin E.length) := Finset.univ.filter (fun i => C ⊆ E.get i)
  let N := memberInter E S
  let B := remainingBoundary E S
  have hS : S.Nonempty := by
    obtain ⟨H,hH,hCH⟩ := hContained
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hH
    refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩⟩
    rw [hi]
    exact hCH
  have hCN : C ⊆ N := by
    intro x hx i hi
    exact ((Finset.mem_filter.mp hi).2) hx
  obtain ⟨x,hx⟩ := hC.nonempty
  have hCard : S.card ≤ n := (memberInter_regularAtDim hE S x (hCN hx)).2
  have hNc : IsClosed N := isClosed_memberInter hE.1 S
  have hNr : ∀ x ∈ N, RegularAtDim (n := n) N x (n - S.card) :=
    fun x hx => (memberInter_regularAtDim hE S x hx).1
  have hBsub : B.Sublist E := remainingBoundary_sublist E S
  have hOmit : ∀ H ∈ E, H ∉ B → N ⊆ H := by
    intro H hH hNot
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hH
    have hiS : i ∈ S := by
      by_contra hiS
      exact hNot ((mem_remainingBoundary E S H).mpr ⟨i,hiS,hi⟩)
    intro y hy
    rw [← hi]
    exact hy i hiS
  have hTrans : IsTransverse n N B := by
    have h := isTransverse_inter_memberInter_drop hE (isTransverse_univ_of_isSNCDivisor hE) S
    change IsTransverse n (memberInter E S) (remainingBoundary E S)
    simpa only [univ_inter,remainingBoundary] using h
  have hBa : ∀ H ∈ B, IsComplexAnalyticSubset (n := n) H := by
    intro H hH
    obtain ⟨i,_,hi⟩ := (mem_remainingBoundary E S H).mp hH
    rw [← hi]
    exact isComplexAnalyticSubset_boundaryMember hE i
  have hNot : ∀ H ∈ B, ¬ C ⊆ H := by
    intro H hH hCH
    obtain ⟨i,hiS,hi⟩ := (mem_remainingBoundary E S H).mp hH
    apply hiS
    simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]
    rwa [hi]
  exact ⟨hS,hCard,hCN,hNc,hNr,hBsub,hOmit,hTrans,irreducible_dense_off_list hC B hBa hNot⟩
end
end Hironaka.HironakaG3ContainingSNCStratum
