/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualMaximumMemberOrders

/-!
# Actual finite weighted pieces of an adapted centre

The complete member-order profile cuts a real admissible centre into
finitely many entire closed admissible pieces. Each piece is admissible
at the literal individual member marks, with the unchanged boundary.
Blueprint: `hironaka-sharp-actual-member-order-strata-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff BigOperators
universe u v
namespace Hironaka.HironakaSharpActualMemberOrderStrata
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal RelativePrincipalizationSpan
  MarkedIdealRestrictOpen MarkedIdealBiholomorphism ResolutionInvariantDriver
  HironakaSharpActualMaximumMemberOrders HironakaSharpActualFiniteMemberProduct
  HironakaSharpOriginalProductTraceOrder DivisorExponentAlong GermIdealOrder
variable {n m : ℕ} {X : CMfd.{u} n}

/-- An entire locally constant profile fibre retains actual global admissibility. -/
theorem admissible_fibre_of_eventually_constant (M : MarkedIdeal n X)
    (hc : M.ideal.IsCoherent) {C : Set X} (hC : M.IsAdmissibleCentre C)
    {β : Type v} (f : X → β)
    (hloc : ∀ x ∈ C,∀ᶠ y in 𝓝 x,y ∈ C → f y=f x) (a : β) :
    M.IsAdmissibleCentre {x | x ∈ C ∧ f x=a} := by
  have hhol : ∀ x g,M.ideal.mem x g → HolomorphicAt n g x :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hc hg
  apply isAdmissibleCentre_of_forall_exists_opens hhol
  intro x
  by_cases hx : x ∈ C
  · obtain ⟨O,hO,hopen,hxO⟩ := mem_nhds_iff.mp (hloc x hx)
    let U : Opens X := ⟨O,hopen⟩
    by_cases ha : f x=a
    · refine ⟨U,hxO,?_⟩
      have heq : (Subtype.val : U → X) ⁻¹' {y | y ∈ C ∧ f y=a}=
          (Subtype.val : U → X) ⁻¹' C := by
        ext y
        exact ⟨fun hy => hy.1,fun hy => ⟨hy,(hO y.property hy).trans ha⟩⟩
      rw [heq]
      exact MarkedIdealRestrictOpen.IsAdmissibleCentre.pullback_val hhol hC U
    · refine ⟨U,hxO,?_⟩
      have heq : (Subtype.val : U → X) ⁻¹' {y | y ∈ C ∧ f y=a}=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro y hy
        exact ha ((hO y.property hy.1).symm.trans hy.2)
      rw [heq]
      exact isAdmissibleCentre_empty _
  · let U : Opens X := ⟨Cᶜ,hC.1.1.isOpen_compl⟩
    refine ⟨U,hx,?_⟩
    have heq : (Subtype.val : U → X) ⁻¹' {y | y ∈ C ∧ f y=a}=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact y.property hy.1
    rw [heq]
    exact isAdmissibleCentre_empty _

/-- The literal whole piece attached to an individual member-order vector. -/
def memberOrderStratum {N : Set X} (F : Fin m → GermIdeal n X)
    (C : Set X) {q : ℕ} (a : Fin m → Fin (q+1)) : Set X :=
  {x | x ∈ C ∧ ∀ i,ordinaryTraceOrder N (F i) x=(a i).val}

private theorem product_order_sum {N : Set X}
    (hN : IsClosedSubmanifold n N) (F : Fin m → GermIdeal n X)
    (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧
      ∀ a,(F i).mem y a ↔ HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    {x : X} (hx : x ∈ N) :
    ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x =
      ∑ i,ordinaryTraceOrder N (F i) x := by
  have hall : ∀ I ∈ List.ofFn F,I.IsCoherent ∧
      (∀ y ∈ N,IsNonzeroAlongAt N I y) ∧
      ∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧
        ∀ a,I.mem y a ↔ HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a := by
    intro I hI
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hI
    exact ⟨hc i,hnz i,hpr i⟩
  have hh := (relativeIdealListProduct_actual_geometry hN (List.ofFn F)
    (fun I hI => (hall I hI).1) (fun I hI => (hall I hI).2.1)
    (fun I hI => (hall I hI).2.2)).2.2.2 x hx
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hh

/-- The actual bounded order vectors give a finite partition into admissible whole pieces. -/
theorem finite_member_order_strata (hn : 0<n) (M : MarkedIdeal n X)
    (hcM : M.ideal.IsCoherent) {N C : Set X}
    (hN : IsClosedSubmanifold n N) (hC : M.IsAdmissibleCentre C) (hCN : C ⊆ N)
    (F : Fin m → GermIdeal n X) (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧
      ∀ a,(F i).mem y a ↔ HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    {q : ℕ} (hq : ∀ x ∈ C,
      ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x=q) :
    (⋃ a : Fin m → Fin (q+1),memberOrderStratum (N := N) F C a)=C ∧
      Pairwise (fun a b : Fin m → Fin (q+1) =>
        Disjoint (memberOrderStratum (N := N) F C a) (memberOrderStratum (N := N) F C b)) ∧
      ∀ a : Fin m → Fin (q+1),M.IsAdmissibleCentre (memberOrderStratum (N := N) F C a) := by
  have hbound : ∀ x ∈ C,∀ i,ordinaryTraceOrder N (F i) x≤q := by
    intro x hx i
    have hs := product_order_sum hN F hc hnz hpr (hCN hx)
    rw [hq x hx] at hs
    rw [hs]
    exact Finset.single_le_sum (f := fun i => ordinaryTraceOrder N (F i) x)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  refine ⟨?_,?_,?_⟩
  · ext x
    constructor
    · intro hx
      obtain ⟨a,ha⟩ := mem_iUnion.mp hx
      exact ha.1
    · intro hx
      let a : Fin m → Fin (q+1) := fun i => ⟨ordinaryTraceOrder N (F i) x,Nat.lt_succ_of_le (hbound x hx i)⟩
      exact mem_iUnion.mpr ⟨a,hx,fun _ => rfl⟩
  · intro a b hab
    apply disjoint_left.mpr
    intro x hxa hxb
    apply hab
    funext i
    exact Fin.ext ((hxa.2 i).symm.trans (hxb.2 i))
  · intro a
    have hloc : ∀ x ∈ C,∀ᶠ y in 𝓝 x,y ∈ C →
        (fun i => ordinaryTraceOrder N (F i) y)=(fun i => ordinaryTraceOrder N (F i) x) := by
      intro x hx
      filter_upwards [eventually_member_orders_of_constant_product hn hN F hc hnz hpr hCN
        (fun x hx y hy => (hq x hx).trans (hq y hy).symm) hx] with y hy hyC
      exact funext (hy hyC)
    have ha := admissible_fibre_of_eventually_constant M hcM hC
      (fun x i => ordinaryTraceOrder N (F i) x) hloc (fun i => (a i).val)
    simpa only [memberOrderStratum,funext_iff] using ha

/-- Each whole piece is simultaneously admissible at every literal individual mark. -/
theorem member_order_strata_weighted_admissible (hn : 0<n) (M : MarkedIdeal n X)
    (hcM : M.ideal.IsCoherent) {N C : Set X}
    (hN : IsClosedSubmanifold n N) (hC : M.IsAdmissibleCentre C) (hCN : C ⊆ N)
    (F : Fin m → GermIdeal n X) (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧
      ∀ a,(F i).mem y a ↔ HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    {q : ℕ} (hq : ∀ x ∈ C,
      ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x=q)
    (a : Fin m → Fin (q+1)) (i : Fin m) :
    (⟨N,M.E,F i,(a i).val⟩ : MarkedIdeal n X).IsAdmissibleCentre
      (memberOrderStratum (N := N) F C a) := by
  have ha := (finite_member_order_strata hn M hcM hN hC hCN F hc hnz hpr hq).2.2 a
  refine ⟨ha.1,?_,ha.2.2⟩
  intro x hx
  change x ∈ cosupport n N (F i) (a i).val
  rw [ordinaryTraceOrder_cosupport_iff hN (hc i) (hnz i) (hCN hx.1) (a i).val]
  exact Nat.le_of_eq (hx.2 i).symm

end
end Hironaka.HironakaSharpActualMemberOrderStrata
