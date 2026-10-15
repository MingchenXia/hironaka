/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveWholeAmbientDifferenceCentre

/-! Actual finite literal whole-Delta phase on the SAME original curve record,
from true compact CURRENT cosupport. No endpoint/history/decrease certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveFiniteAmbientDifferencePhase
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveWholeAmbientDifferenceCentre HironakaSharpActualCurveContactBudgetDomination
  HironakaSharpActualCurveControlledOrderShift HironakaSharpActualCurveExceptionalDifference
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain HironakaCoherentTransformExtension
  NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantOrder IdealWeightPowers
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Literal geometric recipe: EACH actual centre is the independently computed
whole actual difference of the SAME appended original prefix. -/
def actualAmbientDifferenceSteps (W : Set X) (E : List (Set X)) (P : BlowupTower X Y) :
    {Z : CMfd.{u} n} → BlowupTower Y Z → Prop
  | _,.refl => True
  | _,.step S C _ _ => actualAmbientDifferenceSteps W E P S ∧ C=actualAmbientExceptionalDifference W E (P.append S)

/-- Actual whole-Delta geometry supplies each real original admissibility
field before the literal recipe becomes an ORIGINAL TEST. -/
theorem actual_ambient_difference_steps_original_test (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),actualAmbientDifferenceSteps W E P S →
      IsGeoTestTower (originalMemberProductMarked W E 1) (P.append S)
  | _,.refl,_ => hP
  | _,.step S C π hπ,hs => by
    have ht := actual_ambient_difference_steps_original_test hn hW hE hdense hr P hP S hs.1
    have hC : (geoTransformAlong (originalMemberProductMarked W E 1) (P.append S)).IsAdmissibleCentre C := by
      rw [hs.2]
      exact original_curve_whole_ambient_difference_admissible hn hW hE hdense hr _ ht
    exact ⟨ht,hC⟩

/-- Actual support localization and SAME controlled ordinary-order shift give
a genuine length bound on EVERY actual remaining Delta point. -/
theorem actual_ambient_difference_steps_order_bound (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P)
    (b : ℕ) (hb : ∀ x ∈ actualAmbientExceptionalDifference W E P,
      ordinaryTraceOrder (geoTransformAlong (originalMemberProductMarked W E 1) P).N
        (geoTransformAlong (originalMemberProductMarked W E 1) P).ideal x≤b) :
    ∀ {Z : CMfd.{u} n} (S : BlowupTower Y Z),actualAmbientDifferenceSteps W E P S →
      ∀ z ∈ actualAmbientExceptionalDifference W E (P.append S),
        ordinaryTraceOrder (geoTransformAlong (originalMemberProductMarked W E 1) (P.append S)).N
          (geoTransformAlong (originalMemberProductMarked W E 1) (P.append S)).ideal z+S.length≤b
  | _,.refl,_hs,z,hz => by simpa only [BlowupTower.append_refl,BlowupTower.length,Nat.add_zero] using hb z hz
  | _,.step S C π hπ,hs,z,hz => by
    obtain ⟨hs,hCeq⟩ := hs
    subst C
    have ht := actual_ambient_difference_steps_original_test hn hW hE hdense hr P hP S hs
    have hC := original_curve_whole_ambient_difference_admissible hn hW hE hdense hr (P.append S) ht
    have hxD := original_curve_new_ambient_difference_over_old hn hW hE hdense hr (P.append S) ht hπ hz
    have hIH := actual_ambient_difference_steps_order_bound hn hW hE hdense hr P hP b hb S hs (π z) hxD
    have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := originalMemberProductMarked W E 1)
      (𝔪 := geometricTemplate W []) rfl (P.append (.step S (actualAmbientExceptionalDifference W E (P.append S)) π hπ))
    have hzN : z ∈ (geoTransformAlong (originalMemberProductMarked W E 1)
        (P.append (.step S (actualAmbientExceptionalDifference W E (P.append S)) π hπ))).N := by
      rw [hQN]
      exact hz.1
    have hOrd := original_curve_product_next_controlled_order_drop hn hW hE hdense hr (P.append S) ht hC hπ hzN hxD
    change ordinaryTraceOrder (geoTransformAlong (originalMemberProductMarked W E 1)
        (P.append (.step S (actualAmbientExceptionalDifference W E (P.append S)) π hπ))).N
      (geoTransformAlong (originalMemberProductMarked W E 1)
        (P.append (.step S (actualAmbientExceptionalDifference W E (P.append S)) π hπ))).ideal z+(S.length+1)≤b
    simp only [BlowupTower.append_step]
    omega

/-- True compact CURRENT cosupport and actual ordinary USC internally choose
a bound; neither ambient compactness nor a maximum certificate is supplied. -/
theorem original_curve_compact_current_actual_order_bound (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P)
    (hK : IsCompact (geoTransformAlong (originalMemberProductMarked W E 1) P).cosupp) :
    ∃ b : ℕ,∀ x ∈ actualAmbientExceptionalDifference W E P,
      ordinaryTraceOrder (geoTransformAlong (originalMemberProductMarked W E 1) P).N
        (geoTransformAlong (originalMemberProductMarked W E 1) P).ideal x≤b := by
  let M := originalMemberProductMarked W E 1
  let Q := geoTransformAlong M P
  have hInit : IsInvDomain 1 M :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit P hP
  have hsub := original_curve_actual_difference_subset_cosupport hn hW hE hdense hr P hP
  have hUSC : IsInvUSCOn (ordinaryTraceOrder Q.N Q.ideal) Q.cosupp := by
    intro x hx
    exact (eventually_ordinaryTraceOrder_le hn hDom.isWellFormed.isClosedSubmanifold_N
      hDom.isWellFormed.isCoherent hDom.isNonzeroAlongAt hx.1).mono (fun _ hy _ => hy)
  by_cases hne : Q.cosupp.Nonempty
  · obtain ⟨x,_hx,hmax⟩ := hUSC.exists_isMaxOn hK hne
    exact ⟨ordinaryTraceOrder Q.N Q.ideal x,fun y hy => hmax y (hsub hy)⟩
  · exact ⟨0,fun x hx => False.elim (hne ⟨x,hsub hx⟩)⟩

/-- Genuine global whole-Delta blowups construct literal recipe tails of EVERY
length BEFORE the termination bound is used. -/
theorem exists_actual_ambient_difference_tail_length (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P) :
    ∀ N : ℕ,∃ (Z : CMfd.{u} n) (S : BlowupTower Y Z),S.length=N ∧ actualAmbientDifferenceSteps W E P S
  | 0 => ⟨Y,.refl,rfl,trivial⟩
  | N+1 => by
    obtain ⟨Z,S,hLen,hs⟩ := exists_actual_ambient_difference_tail_length hn hW hE hdense hr P hP N
    have ht := actual_ambient_difference_steps_original_test hn hW hE hdense hr P hP S hs
    obtain ⟨Z',π,hπ,_hProper,_hHol,_hIso,_hTest,_hDom,_hSNC,_hDrop⟩ :=
      exists_original_curve_whole_ambient_difference_blowup hn hW hE hdense hr (P.append S) ht
    refine ⟨Z',.step S (actualAmbientExceptionalDifference W E (P.append S)) π hπ,?_,hs,rfl⟩
    change S.length+1=N+1
    rw [hLen]

/-- ONLY original inputs plus actual compact CURRENT cosupport construct an
actual finite whole-difference erasure phase on the SAME ORIGINAL record. -/
theorem exists_original_curve_finite_ambient_difference_phase (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (P : BlowupTower X Y) (hP : IsGeoTestTower (originalMemberProductMarked W E 1) P)
    (hK : IsCompact (geoTransformAlong (originalMemberProductMarked W E 1) P).cosupp) :
    ∃ (Z : CMfd.{u} n) (S : BlowupTower Y Z),actualAmbientDifferenceSteps W E P S ∧
      IsGeoTestTower (originalMemberProductMarked W E 1) (P.append S) ∧
      actualAmbientExceptionalDifference W E (P.append S)=∅ ∧ IsProperMap S.proj ∧
      IsInvDomain 1 (geoTransformAlong (originalMemberProductMarked W E 1) (P.append S)) ∧
      IsSNCDivisor n (geoTransformAlong (originalMemberProductMarked W E 1) (P.append S)).E := by
  obtain ⟨b,hb⟩ := original_curve_compact_current_actual_order_bound hn hW hE hdense hr P hP hK
  obtain ⟨Z,S,hLen,hs⟩ := exists_actual_ambient_difference_tail_length hn hW hE hdense hr P hP (b+1)
  have ht := actual_ambient_difference_steps_original_test hn hW hE hdense hr P hP S hs
  have hEmpty : actualAmbientExceptionalDifference W E (P.append S)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hh := actual_ambient_difference_steps_order_bound hn hW hE hdense hr P hP b hb S hs z hz
    rw [hLen] at hh
    omega
  have hInit : IsInvDomain 1 (originalMemberProductMarked W E 1) :=
    ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
      fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
      fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit _ ht
  exact ⟨Z,S,hs,ht,hEmpty,HironakaLocalPrincipalization.isProperMap_proj S,hDom,hDom.isWellFormed.isSNCDivisor⟩

end
end Hironaka.HironakaSharpActualCurveFiniteAmbientDifferencePhase
