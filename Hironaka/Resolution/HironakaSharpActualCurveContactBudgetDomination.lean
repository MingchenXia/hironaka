/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualCurveOffCentreOrders

/-! Actual original ANYTEST controlled order dominates the independently
computed true ambient-contact budget; no support or comparison certificate. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualCurveContactBudgetDomination
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualCurveOffCentreOrders HironakaSharpActualCurveControlledOrderShift
  HironakaSharpActualCurveExceptionalDifference HironakaSharpActualCurveAmbientContactBudget
  HironakaSharpActualChronologicalAmbientTrace HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualOriginalControlledHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain HironakaCoherentTransformExtension
  RelativePrincipalizationSpan RestrictedIdealExtension RestrictedIdealWeight IdealWeightPowers MonomialPartAlong NormalCrossings NormalCrossingsComparison
  MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder DivisorExponentAlong InvertibleIdealQuotient HomogenizedGlueingTower
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

private theorem original_curve_domain (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) :
    IsInvDomain 1 (originalMemberProductMarked W E 1) :=
  ⟨⟨hW,isCoherent_originalMemberProduct hn hE,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩,
    fun x hx => ⟨1,le_rfl,hr x hx⟩,le_rfl,
    fun _ hx => originalMemberProduct_isNonzeroAlongAt hn hE hdense hx⟩

/-- Genuine relative finite spans and the actual unit test detect positive
ordinary normalized contact at a real carrier point. -/
theorem actual_normalized_vanishing_order_positive_iff {N H : Set X}
    (hN : IsClosedSubmanifold n N) (hH : IsClosed H)
    (hcI : (restrictOn n N (vanishingIdeal (n := n) H)).IsCoherent)
    (hnzI : ∀ x ∈ N,IsNonzeroAlongAt N (restrictOn n N (vanishingIdeal (n := n) H)) x)
    {x : X} (hx : x ∈ N) :
    0<ordinaryTraceOrder N (restrictOn n N (vanishingIdeal (n := n) H)) x ↔ x ∈ H := by
  constructor
  · intro hpos
    by_contra hxH
    have h1 := (actual_normalized_vanishing_unit_iff hH hx).mpr hxH
    have hc := (ordinaryTraceOrder_cosupport_iff hN hcI hnzI hx 1).mpr hpos
    exact one_ne_zero ((vanishesToOrderOn_one_iff hx (holomorphicAt_const 1)).mp (hc.2 1 h1))
  · intro hxH
    apply (ordinaryTraceOrder_cosupport_iff hN hcI hnzI hx 1).mp
    rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hcI hg)]
    refine ⟨hx,?_⟩
    rintro g ⟨_hg,r,s,a,hs,_ha,heq⟩
    have he := heq.self_of_nhds hx
    have hz : ∀ i : Fin r,s i x=0 := fun i => (hs i).2.self_of_nhds hxH
    exact he.trans (by simp only [hz,mul_zero,Finset.sum_const_zero])

/-- ONLY actual original curve tests internally construct every trace before
true incidence gives positivity of the literal ambient-contact budget. -/
theorem original_curve_budget_positive_iff_incident (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {x : Y} (hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N) :
    0<actualAmbientContactBudget W E T x ↔ ∃ i : Fin E.length,x ∈ strictAlong T (E.get i) := by
  have hInit := original_curve_domain hn hW hE hdense hr
  have hGeom := actual_original_test_history_template _ hInit.isWellFormed T hT
  have hDisc := original_domain_one_test_actual_discrete_centres _ hInit T hT
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hwA := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hGeom
  have hFactor (i : Fin E.length) :
      0<ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (restrictOn n (geoTransformAlong (geometricTemplate W []) T).N
          (vanishingIdeal (n := n) (strictAlong T (E.get i)))) x ↔ x ∈ strictAlong T (E.get i) := by
    have hSingle : IsSNCDivisor n [E.get i] := isSNCDivisor_of_sublist hE (by simp)
    have hDenseI : W ⊆ closure (W \ E.get i) := by
      apply Subset.trans hdense
      apply closure_mono
      exact fun _ hy => ⟨hy.1,fun hi => hy.2 (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hi⟩)⟩
    obtain ⟨hHT,_hDense,hcI,hnzI,_hPr⟩ := actual_finite_ambient_strict_trace_geometry hn hW hSingle hDenseI T hGeom hDisc
    exact actual_normalized_vanishing_order_positive_iff hwA.isClosedSubmanifold_N
      (hHT.1 _ (by simp)) hcI hnzI hx
  constructor
  · intro hpos
    by_contra hNo
    have hzero : actualAmbientContactBudget W E T x=0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      have hnp := mt (hFactor i).mp (fun hi => hNo ⟨i,hi⟩)
      omega
    omega
  · rintro ⟨i,hi⟩
    unfold actualAmbientContactBudget
    apply lt_of_lt_of_le ((hFactor i).mpr hi)
    apply Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)

/-- No incident ORIGINAL position forces the actual entire contact budget zero. -/
theorem original_curve_budget_eq_zero_of_no_incidence (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T)
    {x : Y} (hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N)
    (hNo : ∀ i : Fin E.length,x ∉ strictAlong T (E.get i)) :
    actualAmbientContactBudget W E T x=0 := by
  have hPos := original_curve_budget_positive_iff_incident hn hW hE hdense hr T hT hx
  have hnpos : ¬0<actualAmbientContactBudget W E T x := by
    intro hp
    obtain ⟨i,hi⟩ := hPos.mp hp
    exact hNo i hi
  omega


/-- Finite genuine ORIGINAL test induction: initial actual product SUM, then
real above-centre shifts and independent off-centre equalities. -/
theorem original_curve_controlled_order_dominates_budget (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (originalMemberProductMarked W E 1) T →
      ∀ x ∈ (geoTransformAlong (originalMemberProductMarked W E 1) T).N,
        actualAmbientContactBudget W E T x≤
          ordinaryTraceOrder (geoTransformAlong (originalMemberProductMarked W E 1) T).N
            (geoTransformAlong (originalMemberProductMarked W E 1) T).ideal x
  | _,.refl,_hT,x,hx => by
    have hSum := originalMemberProduct_traceOrder_eq_sum hn hW E hE hdense hx
    have hFin : (∑ i : Fin E.length,ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x)=
        (E.map fun H => ordinaryTraceOrder W (vanishingIdeal (n := n) H) x).sum := by
      simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using
        congrArg (fun L : List (Set X) => (L.map fun H => ordinaryTraceOrder W (vanishingIdeal (n := n) H) x).sum)
          (List.ofFn_get E)
    have hNorm : actualAmbientContactBudget W E (.refl : BlowupTower X X) x=
        ∑ i : Fin E.length,ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x := by
      apply Finset.sum_congr rfl
      intro i _hi
      have hcH := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
      have hnzH : ∀ y ∈ W,IsNonzeroAlongAt W (vanishingIdeal (n := n) (E.get i)) y :=
        fun _ hy => originalMemberIdeal_isNonzeroAlongAt hE hdense (List.get_mem E i) hy
      exact HironakaSharpActualFiniteMemberProduct.ordinaryTraceOrder_restrictOn_eq hW hcH hnzH hx
    change actualAmbientContactBudget W E (.refl : BlowupTower X X) x≤ordinaryTraceOrder W (originalMemberProduct E) x
    rw [hNorm,hFin,←hSum]
  | _,.step T C π hπ,hT,z,hz => by
    let M := originalMemberProductMarked W E 1
    let Q := geoTransformAlong M T
    have hInit := original_curve_domain hn hW hE hdense hr
    have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit T hT.1
    have hx : π z ∈ Q.N := BlowupStrictSubmanifold.geoStrictTransform_subset_preimage
      hπ.contMDiff.continuous hDom.isWellFormed.isClosedSubmanifold_N.1 hz
    have hIH := original_curve_controlled_order_dominates_budget hn hW hE hdense hr T hT.1 (π z) hx
    have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
    have hQNNew := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl (.step T C π hπ)
    have hxA : π z ∈ (geoTransformAlong (geometricTemplate W []) T).N := hQN ▸ hx
    have hzA : z ∈ (geoTransformAlong (geometricTemplate W []) (.step T C π hπ)).N := hQNNew ▸ hz
    by_cases hzC : π z ∈ C
    · have hOrd := original_curve_product_next_controlled_order_drop hn hW hE hdense hr T hT.1 hT.2 hπ hz hzC
      have hBudget := original_curve_actual_contact_budget_evolution hn hW hE hdense hr T hT.1 hT.2 hπ hzA hzC
      by_cases hk : (actualAmbientIncidentPositions E T (π z)).card=0
      · have hEmpty := Finset.card_eq_zero.mp hk
        have hNo : ∀ i : Fin E.length,π z ∉ strictAlong T (E.get i) := by
          intro i hi
          have hm : i ∈ actualAmbientIncidentPositions E T (π z) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩
          rw [hEmpty] at hm
          simp at hm
        have hZero := original_curve_budget_eq_zero_of_no_incidence hn hW hE hdense hr T hT.1 hxA hNo
        omega
      · omega
    · have hOrd := actual_controlled_ordinary_order_off_centre Q hDom.isWellFormed hDom.isNonzeroAlongAt hT.2 hπ hz hzC
      have hBudget := original_curve_actual_contact_budget_off_centre hn hW hE hdense hr T hT.1 hT.2 hπ hzA hzC
      change ordinaryTraceOrder (geoTransformAlong M (.step T C π hπ)).N
        (geoTransformAlong M (.step T C π hπ)).ideal z=ordinaryTraceOrder Q.N Q.ideal (π z) at hOrd
      change actualAmbientContactBudget W E (.step T C π hπ) z≤
        ordinaryTraceOrder (geoTransformAlong M (.step T C π hπ)).N (geoTransformAlong M (.step T C π hπ)).ideal z
      rw [hBudget,hOrd]
      exact hIH

/-- Real true ambient incidence supplies positive budget BEFORE its proved
controlled domination gives the SAME original positive cosupport inclusion. -/
theorem original_curve_actual_difference_subset_cosupport (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x 1)
    (T : BlowupTower X Y) (hT : IsGeoTestTower (originalMemberProductMarked W E 1) T) :
    actualAmbientExceptionalDifference W E T ⊆ (geoTransformAlong (originalMemberProductMarked W E 1) T).cosupp := by
  let M := originalMemberProductMarked W E 1
  have hInit := original_curve_domain hn hW hE hdense hr
  have hDom := InvDomainTowerAlong.isInvDomain_geoTransformAlong hInit T hT
  have hQN := geoTransformAlong_N_eq_of_N_eq (𝔍 := M) (𝔪 := geometricTemplate W []) rfl T
  have hEq := original_curve_actual_exceptional_difference_eq hn hW hE hdense hr T hT
  intro x hxD
  have hxLit := hEq ▸ hxD
  have hx : x ∈ (geoTransformAlong M T).N := by rw [hQN];exact hxD.1
  have hPos : 0<actualAmbientContactBudget W E T x := by
    apply (original_curve_budget_positive_iff_incident hn hW hE hdense hr T hT hxD.1).mpr
    exact mem_iUnion.mp hxLit.2
  have hLe := original_curve_controlled_order_dominates_budget hn hW hE hdense hr T hT x hx
  change x ∈ cosupport n (geoTransformAlong M T).N (geoTransformAlong M T).ideal (geoTransformAlong M T).d
  rw [d_geoTransformAlong]
  apply (ordinaryTraceOrder_cosupport_iff hDom.isWellFormed.isClosedSubmanifold_N hDom.isWellFormed.isCoherent hDom.isNonzeroAlongAt hx 1).mpr
  omega

end
end Hironaka.HironakaSharpActualCurveContactBudgetDomination
