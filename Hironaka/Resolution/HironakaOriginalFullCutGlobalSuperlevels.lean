/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFullCutPositiveGlobalSuperlevels
import Hironaka.Resolution.HironakaMonomialAnalyticSuperlevels
/-! All literal original FULL thresholds on genuine DOMAIN2 whole-cut histories.
No CAN or numerical analytic-locus certificate enters the actual producers. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFullCutGlobalSuperlevels
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  GeneralValue CanonicalCentres NonmonomialOrderLocal InvDomainTowerAlong CodimOneSupportAlong
  HironakaOriginalFiniteFullCutSmoothHistory HironakaOriginalFiniteOrderCutCompanionTests
  HironakaOriginalFullCutPositiveGlobalSuperlevels HironakaMonomialAnalyticSuperlevels
  HironakaOrderTupleAnalyticSuperlevels
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem actual_domain_at_depth (d : ℕ) {M : MarkedIdeal n X}
    (hM : IsInvDomain 2 M) : IsInvDomain (d+2) M := by
  refine ⟨hM.isWellFormed,?_,hM.one_le_d,hM.isNonzeroAlongAt⟩
  intro x hx
  obtain ⟨j,hj,hr⟩ := hM.dimLE x hx
  exact ⟨j,by omega,hr⟩

/-- Actual zero-coordinate set dictionaries use true original TEST geometry,
not a canonical or numerical analytic-locus premise. -/
theorem isComplexAnalyticSubset_zero_full_superlevel (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T)
    (β : WithBot MonomialInvariant.Val ⊕ₗ WithTop (ℕ ×ₗ WithTop (ValTy (d+1)))) :
    IsComplexAnalyticSubset (n := n) {y | y∈(geoTransformAlong M T).cosupp ∧
      toLex (0,β)≤(invFamily hn (d+2)).inv M T y} := by
  have hD := actual_domain_at_depth d hM
  have hCurrent := isInvDomain_geoTransformAlong hM T hT
  have hA := isComplexAnalyticSubset_cosupport_along hCurrent.isWellFormed.isCoherent
    hCurrent.isWellFormed.isClosedSubmanifold_N hCurrent.one_le_d
  refine Lex.rec (fun b => ?_) β
  rcases b with v|a
  · have hmon := isComplexAnalyticSubset_canonical_monomial_superlevel hn M hD T hT v
    have heq : {y | y∈(geoTransformAlong M T).cosupp ∧
        toLex (0,toLex (Sum.inl v))≤(invFamily hn (d+2)).inv M T y} =
        (geoTransformAlong M T).cosupp ∩ {y | y∈(geoTransformAlong M T).N ∧
          toLex (0,toLex (Sum.inl v))≤(invFamily hn (d+2)).inv M T y} := by
      ext y
      exact ⟨fun hy => ⟨hy.1,(geoTransformAlong M T).cosupp_subset_N hy.1,hy.2⟩,
        fun hy => ⟨hy.1,hy.2.2⟩⟩
    rw [heq]
    exact hA.inter hmon
  · have hord := isComplexAnalyticSubset_canonical_first_superlevel hn M hD T hT 1
    have heq : {y | y∈(geoTransformAlong M T).cosupp ∧
        toLex (0,toLex (Sum.inr a))≤(invFamily hn (d+2)).inv M T y} =
        (geoTransformAlong M T).cosupp ∩ {y | y∈(geoTransformAlong M T).N ∧
          1≤(ofLex ((invFamily hn (d+2)).inv M T y)).1} := by
      ext y
      let lower := fun {A : CMfd.{u} n} (J : MarkedIdeal n A) {B : CMfd.{u} n}
        (S : BlowupTower A B) (z : B) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) J S z
      have he : (invFamily hn (d+2)).inv M T y=genInv lower M T y := rfl
      simp only [mem_ofPred_eq,mem_inter_iff,he]
      by_cases ho : nmOrd (geoTransformAlong M T) y=0
      · rw [genInv_of_nmOrd_eq_zero lower M T ho]
        simp [Prod.Lex.toLex_le_toLex]
      · have hp : 0<nmOrd (geoTransformAlong M T) y := Nat.pos_of_ne_zero ho
        have hfirst : 1≤(ofLex (genInv lower M T y)).1 := hp
        have hv : toLex (0,toLex (Sum.inr a))≤genInv lower M T y := by
          rw [genInv,Prod.Lex.toLex_le_toLex]
          exact Or.inl hp
        exact ⟨fun hy => ⟨hy.1,(geoTransformAlong M T).cosupp_subset_N hy.1,hfirst⟩,
          fun hy => ⟨hy.1,hv⟩⟩
    rw [heq]
    exact hA.inter hord

/-- At positive first threshold, a genuine monomial threshold tests exactly
ordinary nonmonomial order, including the extended bottom threshold. -/
theorem isComplexAnalyticSubset_positive_monomial_full_superlevel (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsGeoTestTower M T) (q : ℕ) (hq : 0<q) (v : WithBot MonomialInvariant.Val) :
    IsComplexAnalyticSubset (n := n) {y | y∈(geoTransformAlong M T).cosupp ∧
      toLex (q,toLex (Sum.inl v))≤(invFamily hn (d+2)).inv M T y} := by
  have hD := actual_domain_at_depth d hM
  have hCurrent := isInvDomain_geoTransformAlong hM T hT
  have hA := isComplexAnalyticSubset_cosupport_along hCurrent.isWellFormed.isCoherent
    hCurrent.isWellFormed.isClosedSubmanifold_N hCurrent.one_le_d
  have hord := isComplexAnalyticSubset_canonical_first_superlevel hn M hD T hT q
  have heq : {y | y∈(geoTransformAlong M T).cosupp ∧
      toLex (q,toLex (Sum.inl v))≤(invFamily hn (d+2)).inv M T y} =
      (geoTransformAlong M T).cosupp ∩ {y | y∈(geoTransformAlong M T).N ∧
        q≤(ofLex ((invFamily hn (d+2)).inv M T y)).1} := by
    ext y
    constructor
    · intro hy
      have hlex := Prod.Lex.le_iff.mp hy.2
      have hge : q≤nmOrd (geoTransformAlong M T) y :=
        hlex.elim (fun h => h.le) (fun h => h.1.le)
      exact ⟨hy.1,(geoTransformAlong M T).cosupp_subset_N hy.1,hge⟩
    · intro hy
      refine ⟨hy.1,?_⟩
      let lower := fun {A : CMfd.{u} n} (J : MarkedIdeal n A) {B : CMfd.{u} n}
        (S : BlowupTower A B) (z : B) => Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) J S z
      have hge : q≤nmOrd (geoTransformAlong M T) y := hy.2.2
      rcases lt_or_eq_of_le hge with hlt|he
      · exact Prod.Lex.le_iff.mpr (Or.inl hlt)
      · change _≤genInv lower M T y
        rw [genInv_of_nmOrd_ne_zero lower M T he.symm (Nat.ne_of_gt hq)]
        simp [Prod.Lex.toLex_le_toLex]
  rw [heq]
  exact hA.inter hord

/-- ALL thresholds of the unchanged original FULL value, on the ENTIRE actual
current cosupport, are analytic from genuine original whole cuts alone. -/
theorem isComplexAnalyticSubset_full_superlevel (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsFullCutTower hn d M T) (l : ValTy (d+2)) :
    IsComplexAnalyticSubset (n := n) {y | y∈(geoTransformAlong M T).cosupp ∧
      l≤(invFamily hn (d+2)).inv M T y} := by
  have hTest := orderCutTower_geoTest M T (fullCutTower_orderCut hn d M T hT)
  obtain ⟨q,β⟩ := l
  by_cases hq : q=0
  · subst q
    exact isComplexAnalyticSubset_zero_full_superlevel hn d M hM T hTest β
  · refine Lex.rec (fun b => ?_) β
    rcases b with v|a
    · exact isComplexAnalyticSubset_positive_monomial_full_superlevel hn d M hM T hTest q
        (Nat.pos_of_ne_zero hq) v
    · exact isComplexAnalyticSubset_positive_full_superlevel hn d M hM T hT q
        (Nat.pos_of_ne_zero hq) a

private theorem actual_usc_of_all_closed_superlevels {A Λ : Type*} [TopologicalSpace A]
    [LinearOrder Λ] [WellFoundedLT Λ] (f : A → Λ) (S : Set A)
    (hClosed : ∀ l,IsClosed {y | y∈S ∧ l≤f y}) :
    ResolutionInvariantOrder.IsInvUSCOn f S := by
  intro x hx
  by_cases hAbove : ∃ a,f x<a
  · obtain ⟨a,ha,hmin⟩ := wellFounded_lt.has_min {l | f x<l} hAbove
    have hxL : x∉{y | y∈S ∧ a≤f y} := fun h => (not_le.mpr ha) h.2
    filter_upwards [(hClosed a).isOpen_compl.mem_nhds hxL] with y hy hyS
    by_contra hnot
    have hxy : f x<f y := lt_of_not_ge hnot
    exact hy ⟨hyS,not_lt.mp (hmin (f y) hxy)⟩
  · exact Eventually.of_forall fun y _ => le_of_not_gt (fun h => hAbove ⟨f y,h⟩)

/-- True well-order least-above selection turns internally proved analytic
superlevels into the algorithm's precise local upper bound, without CAN. -/
theorem isInvUSCOn_full_value (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsFullCutTower hn d M T) :
    ResolutionInvariantOrder.IsInvUSCOn ((invFamily hn (d+2)).inv M T)
      (geoTransformAlong M T).cosupp :=
  actual_usc_of_all_closed_superlevels _ _
    (fun l => (isComplexAnalyticSubset_full_superlevel hn d M hM T hT l).isClosed)

/-- Ordinary compactness internally gives an actual attained FULL value and
its true ambient analytic superlevel, with exact maximum trace on K. -/
theorem exists_compact_full_maximum_analytic_superlevel (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsFullCutTower hn d M T) (K : Set Y) (hK : IsCompact K)
    (hKA : K⊆(geoTransformAlong M T).cosupp) (hne : K.Nonempty) :
    ∃ x∈K,(∀ y∈K,(invFamily hn (d+2)).inv M T y≤(invFamily hn (d+2)).inv M T x) ∧
      IsComplexAnalyticSubset (n := n) {y | y∈(geoTransformAlong M T).cosupp ∧
        (invFamily hn (d+2)).inv M T x≤(invFamily hn (d+2)).inv M T y} ∧
      {y | y∈K ∧ (invFamily hn (d+2)).inv M T x≤(invFamily hn (d+2)).inv M T y}=
        {y | y∈K ∧ (invFamily hn (d+2)).inv M T y=(invFamily hn (d+2)).inv M T x} := by
  have hUSC := isInvUSCOn_full_value hn d M hM T hT
  obtain ⟨x,hx,hmax⟩ := (hUSC.mono hKA).exists_isMaxOn hK hne
  refine ⟨x,hx,hmax,isComplexAnalyticSubset_full_superlevel hn d M hM T hT _,?_⟩
  ext y
  exact ⟨fun h => ⟨h.1,le_antisymm (hmax y h.1) h.2⟩,fun h => ⟨h.1,h.2.ge⟩⟩
end
end Hironaka.HironakaOriginalFullCutGlobalSuperlevels
