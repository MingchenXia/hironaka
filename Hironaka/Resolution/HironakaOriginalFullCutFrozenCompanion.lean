/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFullCutCompanionHistory
import Hironaka.Resolution.HironakaOriginalFrozenCompanionPresentation
import Hironaka.Resolution.HironakaDimensionTwoStepOneAnalyticSuperlevels
/-! Actual whole frozen-companion threshold dictionaries on genuine FULL
cut histories, without CAN, numerical presentations or lower certificates. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalFullCutFrozenCompanion
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms BlowupTowerSplit
  NonmonomialOrderLocal NonmonomialOrderRegime NonmonomialOrderTail
  StepOneValue CanonicalCentres GeneralValue GeneralCompare GeneralCanonicalTail HomogenizedIdealAlong
  HironakaOriginalFullCutCompanionHistory HironakaOriginalFiniteFullCutSmoothHistory
  HironakaOriginalFiniteOrderCutCompanionTests HironakaOriginalFrozenCompanionPresentation
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y : CMfd.{u} n}

/-- All actual frozen-companion fields are internally supplied from the
original whole FULL cuts; no CAN or lower-history data is input. -/
theorem full_cut_frozen_companion_data (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsFullCutTower hn d M T) (x : Y)
    (hx : x∈(geoTransformAlong M T).cosupp) (hq : 0<orderAt M T x) :
    x∈patchAt M T x ∧ IsInvDomain 2 (companionAt M T x) ∧
      IsMaximalOrderAlong (companionAt M T x).N (companionAt M T x).ideal (companionAt M T x).d ∧
      HironakaOriginalFiniteStepOneCutMaskAvoidance.IsStepOneCutTower hn (d+1)
        (companionAt M T x) (companionTailAt M T x) ∧
      IsInvDomain 2 (geoTransformAlong (companionAt M T x) (companionTailAt M T x)) ∧
      ∀ p : patchAt M T x,p∈(geoTransformAlong (companionAt M T x) (companionTailAt M T x)).cosupp ↔
        p.val∈(geoTransformAlong M T).cosupp ∧ nmOrd (geoTransformAlong M T) p.val=orderAt M T x := by
  have hOrder := fullCutTower_orderCut hn d M T hT
  obtain ⟨hJ,hMax,_hTest,hCurrent,hpx,_hPoint,hDict⟩ :=
    orderCutTower_current_companion_data hn M hM T hOrder x hx hq
  exact ⟨hpx,hJ,hMax,fullCutTower_current_companion_stepone_cut hn d M hM T hT _ hq x,hCurrent,hDict⟩

/-- EVERY actual fixed companion point has its entire original FULL law,
using the same frozen record after all true query recipes were constructed. -/
theorem full_cut_value_eq_frozen_companion (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsFullCutTower hn d M T) (x : Y)
    (hx : x∈(geoTransformAlong M T).cosupp) (hq : 0<orderAt M T x)
    (p : patchAt M T x)
    (hp : p∈(geoTransformAlong (companionAt M T x) (companionTailAt M T x)).cosupp) :
    (invFamily hn (d+2)).inv M T p.val=
      toLex (orderAt M T x,toLex (Sum.inr
        ((Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1))
          (companionAt M T x) (companionTailAt M T x) p :
          ℕ ×ₗ WithTop (ValTy (d+1))) : WithTop (ℕ ×ₗ WithTop (ValTy (d+1)))))) :=
  full_value_eq_fixed_companion_of_own_cuts hn d M hM T (fullCutTower_orderCut hn d M T hT)
    (orderAt M T x) hq x hx rfl
    (fun y => fullCutTower_current_companion_stepone_cut hn d M hM T hT _ hq y) p hp

private theorem actual_order_bound_on_patch (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsFullCutTower hn d M T) (x : Y) (hq : 0<orderAt M T x)
    (p : patchAt M T x) (hp : p.val∈(geoTransformAlong M T).cosupp) :
    nmOrd (geoTransformAlong M T) p.val≤orderAt M T x := by
  have hOrder := fullCutTower_orderCut hn d M T hT
  have hUpper := orderCutTower_geoTest M T hOrder
  have hComp := orderCutTower_current_companion_test hn M hM T hOrder (orderAt M T x) hq x
  obtain ⟨hH,hS⟩ := (isGeoTestTower_iff_head_tail M T (runAt M T x)).mp hUpper
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hM (head T (runAt M T x)) hH
  have hp' : p.val∈(geoTransformAlong (geoTransformAlong M (head T (runAt M T x)))
      (tail T (runAt M T x))).cosupp := by rw [←geoTransformAlong_head_tail];exact hp
  have hb := nmOrd_le_of_notMem (notMem_ordGe_of_mask hn hDom hq (maskAt M T x)
    (fun y _ hy => (mem_ordMask_iff hn hDom.isWellFormed hDom.isNonzeroAlongAt (orderAt M T x) y).mp hy)
    (tail T (runAt M T x)) hS hComp p.val hp' p.property)
  rwa [←geoTransformAlong_head_tail] at hb

/-- ENTIRE arbitrary extended lower thresholds use the SAME actual
companion, without assuming a numerical/analytic superlevel certificate. -/
theorem full_cut_superlevel_pullback_eq_frozen_companion (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsFullCutTower hn d M T) (x : Y)
    (hx : x∈(geoTransformAlong M T).cosupp) (hq : 0<orderAt M T x)
    (β : WithTop (ℕ ×ₗ WithTop (ValTy (d+1)))) :
    (Subtype.val : patchAt M T x → Y) ⁻¹' {y | y∈(geoTransformAlong M T).cosupp ∧
      toLex (orderAt M T x,toLex (Sum.inr β))≤(invFamily hn (d+2)).inv M T y}=
      {p | p∈(geoTransformAlong (companionAt M T x) (companionTailAt M T x)).cosupp ∧
        β≤(Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1))
          (companionAt M T x) (companionTailAt M T x) p : WithTop (ℕ ×ₗ WithTop (ValTy (d+1))))} := by
  obtain ⟨_,_,_,_,_,hDict⟩ := full_cut_frozen_companion_data hn d M hM T hT x hx hq
  ext p
  constructor
  · intro hp
    have hle := actual_order_bound_on_patch hn d M hM T hT x hq p hp.1
    have hge : orderAt M T x≤nmOrd (geoTransformAlong M T) p.val := by
      have hh := Prod.Lex.le_iff.mp hp.2
      change orderAt M T x<nmOrd (geoTransformAlong M T) p.val ∨
        orderAt M T x=nmOrd (geoTransformAlong M T) p.val ∧ _ at hh
      exact hh.elim (fun h => h.le) (fun h => h.1.le)
    have hpK := (hDict p).mpr ⟨hp.1,hle.antisymm hge⟩
    have hv := full_cut_value_eq_frozen_companion hn d M hM T hT x hx hq p hpK
    have hcomp := hp.2
    rw [hv,Prod.Lex.toLex_le_toLex] at hcomp
    exact ⟨hpK,Sum.Lex.inr_le_inr_iff.mp (hcomp.resolve_left (lt_irrefl _)).2⟩
  · intro hp
    refine ⟨((hDict p).mp hp.1).1,?_⟩
    rw [full_cut_value_eq_frozen_companion hn d M hM T hT x hx hq p hp.1,Prod.Lex.toLex_le_toLex]
    exact Or.inr ⟨rfl,Sum.Lex.inr_le_inr_iff.mpr hp.2⟩

/-- Genuine coefficient TEST and DOMAIN2 analytic geometry are internally
supplied before EVERY extended threshold on the ENTIRE actual patch. -/
theorem isComplexAnalyticSubset_full_cut_frozen_superlevel (hn : 0<n) (d : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain 2 M) (T : BlowupTower X Y)
    (hT : IsFullCutTower hn d M T) (x : Y)
    (hx : x∈(geoTransformAlong M T).cosupp) (hq : 0<orderAt M T x)
    (β : WithTop (ℕ ×ₗ WithTop (ValTy (d+1)))) :
    IsComplexAnalyticSubset (n := n)
      ((Subtype.val : patchAt M T x → Y) ⁻¹' {y | y∈(geoTransformAlong M T).cosupp ∧
        toLex (orderAt M T x,toLex (Sum.inr β))≤(invFamily hn (d+2)).inv M T y}) := by
  rw [full_cut_superlevel_pullback_eq_frozen_companion hn d M hM T hT x hx hq β]
  obtain ⟨_,hJ,hMax,_hRecipe,_hCurrent,_hDict⟩ := full_cut_frozen_companion_data hn d M hM T hT x hx hq
  let J := companionAt M T x
  let R := companionTailAt M T x
  have hOrder := fullCutTower_orderCut hn d M T hT
  have hTest := orderCutTower_current_companion_test hn M hM T hOrder (orderAt M T x) hq x
  have hEquiv := HomogenizedIdealAlongTower.coeff_homAlong_wEquiv (X := CMfd.of (n := n) (maskAt M T x)) J
    hJ.isWellFormed.isClosedSubmanifold_N hJ.isWellFormed.isCoherent hJ.one_le_d
  have hBar : IsGeoTestTower (barMarked J) R := (hEquiv.2 R).1.mpr hTest
  have hCos : (geoTransformAlong (barMarked J) R).cosupp=(geoTransformAlong J R).cosupp :=
    (hEquiv.2 R).2 hBar
  cases β using WithTop.recTopCoe with
  | top =>
    have he : {p : patchAt M T x | p∈(geoTransformAlong J R).cosupp ∧
        (⊤ : WithTop (ℕ ×ₗ WithTop (ValTy (d+1))))≤
          (Seq.StepOneValueMasked.stepOneInvM (invFamily hn (d+1)) J R p :
            WithTop (ℕ ×ₗ WithTop (ValTy (d+1))))}=∅ := by
      ext p
      simp
    rw [he]
    exact isComplexAnalyticSubset_empty
  | coe b =>
    obtain ⟨s,α,hb⟩ : ∃ (s : ℕ) (α : WithTop (ValTy (d+1))),b=toLex (s,α) :=
      ⟨(ofLex b).1,(ofLex b).2,rfl⟩
    subst b
    have ha := HironakaDimensionTwoStepOneAnalyticSuperlevels.isComplexAnalyticSubset_stepOneInvM_superlevel
      (X := CMfd.of (n := n) (maskAt M T x)) (Y := CMfd.of (n := n) (patchAt M T x))
      (invFamily hn (d+1)) hn J hJ.isWellFormed hJ.one_le_d hMax hJ.dimLE R hBar s α
    simpa only [hCos,WithTop.coe_le_coe] using ha

end
end Hironaka.HironakaOriginalFullCutFrozenCompanion
