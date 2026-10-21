/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFullBornIncidence

/-!
# Original member orders on the same actual full maximum centre

Actual product-order additivity and individual upper semicontinuity give
simultaneous local constancy of every original normalised member order.
The original geometric endpoint chooses one real full maximum centre and
retains its entire proper-position profile and born-boundary incidences.
No modified-history decrease or sharp terminal resolution is asserted.
Blueprint: `hironaka-sharp-actual-maximum-member-orders-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaSharpActualMaximumMemberOrders
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualFiniteMemberProduct
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualDynamicDistinctCentre HironakaSharpActualFullBornIncidence
  RelativePrincipalizationSpan DivisorExponentAlong GermIdealOrder CanonicalCentres
  HironakaSharpOriginalMemberProductDomain
variable {n m : ℕ} {X : CMfd.{u} n}

private theorem actual_family_product_order_sum {N : Set X}
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

/-- Actual ordinary member orders are locally constant on a constant product-order stratum. -/
theorem eventually_member_orders_of_constant_product (hn : 0<n) {N C : Set X}
    (hN : IsClosedSubmanifold n N) (F : Fin m → GermIdeal n X)
    (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧
      ∀ a,(F i).mem y a ↔ HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    (hC : C ⊆ N)
    (hval : ∀ x ∈ C,∀ y ∈ C,
      ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x =
        ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) y)
    {x : X} (hx : x ∈ C) :
    ∀ᶠ y in 𝓝 x,y ∈ C → ∀ i,ordinaryTraceOrder N (F i) y=ordinaryTraceOrder N (F i) x := by
  have hle : ∀ᶠ y in 𝓝 x,∀ i,ordinaryTraceOrder N (F i) y≤ordinaryTraceOrder N (F i) x :=
    eventually_all.mpr fun i => eventually_ordinaryTraceOrder_le hn hN (hc i) (hnz i) (hC hx)
  filter_upwards [hle] with y hy hyC
  have hsum : (∑ i,ordinaryTraceOrder N (F i) y)=(∑ i,ordinaryTraceOrder N (F i) x) := by
    rw [← actual_family_product_order_sum hN F hc hnz hpr (hC hyC),
      ← actual_family_product_order_sum hN F hc hnz hpr (hC hx)]
    exact (hval x hx y hyC).symm
  exact fun i => (Finset.sum_eq_sum_iff_of_le (fun i _ => hy i)).mp hsum i (Finset.mem_univ i)

private theorem proper_position_iff_order {N : Set X}
    (hN : IsClosedSubmanifold n N) (F : Fin m → GermIdeal n X)
    (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    {x : X} (hx : x ∈ N) (i : Fin m) :
    i ∈ actualProperPositions F x ↔ 1≤ordinaryTraceOrder N (F i) x := by
  rw [actual_proper_iff_zeroLocus hc i x]
  have hcos := cosupport_one (N := N)
    (fun _ _ ha => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem (hc i) ha)
  rw [← ordinaryTraceOrder_cosupport_iff hN (hc i) (hnz i) hx 1,hcos]
  simp only [mem_inter_iff,hx,true_and]

/-- The same real neighbourhood fixes every member order and the whole proper-position set. -/
theorem eventually_member_orders_and_proper_positions (hn : 0<n) {N C : Set X}
    (hN : IsClosedSubmanifold n N) (F : Fin m → GermIdeal n X)
    (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧
      ∀ a,(F i).mem y a ↔ HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    (hC : C ⊆ N)
    (hval : ∀ x ∈ C,∀ y ∈ C,
      ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x =
        ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) y)
    {x : X} (hx : x ∈ C) :
    ∀ᶠ y in 𝓝 x,y ∈ C →
      (∀ i,ordinaryTraceOrder N (F i) y=ordinaryTraceOrder N (F i) x) ∧
      actualProperPositions F y=actualProperPositions F x := by
  filter_upwards [eventually_member_orders_of_constant_product hn hN F hc hnz hpr hC hval hx] with y hy hyC
  refine ⟨hy hyC,?_⟩
  apply Finset.ext
  intro i
  rw [proper_position_iff_order hN F hc hnz (hC hyC),
    proper_position_iff_order hN F hc hnz (hC hx),(hy hyC) i]

/-- Original geometry chooses one actual full maximum with stable member orders, proper positions and born incidences. -/
theorem exists_actual_dynamic_centre_member_order_profile (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hK : IsCompact W)
    {d : ℕ} (hd : d+1≤n) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (ht : IsGeoTestTower (geometricTemplate W []) T)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    ∃ C : Set Y,C.Nonempty ∧ C ⊆ chronologicalDistinctDefect W E T ∧
      (currentProductMarked W E T).IsAdmissibleCentre C ∧
      (geoTransformAlong (geometricTemplate W []) T).IsAdmissibleCentre C ∧
      C=ResolutionDriver.maxLocus
        ((invFamily hn (n+1)).inv (currentProductMarked W E T) (.refl : BlowupTower Y Y))
        (chronologicalDistinctDefect W E T) ∧
      let N := (geoTransformAlong (geometricTemplate W []) T).N
      let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
      ∀ x ∈ C,∀ᶠ y in 𝓝 x,y ∈ C →
        (∀ i,ordinaryTraceOrder N (F i) y=ordinaryTraceOrder N (F i) x) ∧
        actualProperPositions F y=actualProperPositions F x ∧
        ∀ i : Fin (currentProductMarked W E T).E.length,
          (y ∈ (currentProductMarked W E T).E.get i ↔ x ∈ (currentProductMarked W E T).E.get i) := by
  obtain ⟨C,hneC,hCZ,hCur,hTemp,hCeq,hBorn⟩ :=
    exists_actual_dynamic_distinct_centre_born_incidence hn hW hE hdense hK hd hr T ht hne
  let N := (geoTransformAlong (geometricTemplate W []) T).N
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hN := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
    (show (geometricTemplate W []).IsWellFormed from
      ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩) T ht).isClosedSubmanifold_N
  have hfam : ∀ i : Fin E.length,(F i).IsCoherent ∧
      (∀ y ∈ N,IsNonzeroAlongAt N (F i) y) ∧
      ∀ y ∈ N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ a,(F i).mem y a ↔ HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a := by
    intro i
    obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ :=
      original_members_actual_finite_chronological_geometry hn hW hE hdense i T ht
    rw [hNi] at hnzi hpri
    exact ⟨hwi.isCoherent,hnzi,hpri⟩
  have hsub : C ⊆ N := fun _ hy => (hCZ hy).1
  have hval : ∀ x ∈ C,∀ y ∈ C,
      ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x =
        ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) y := by
    intro x hx y hy
    have heq := ((hCeq ▸ hy).2 x (hCeq ▸ hx).1).antisymm ((hCeq ▸ hx).2 y (hCeq ▸ hy).1)
    have hfirst := congrArg (fun v : CanonicalCentres.ValTy (n+1) => (ofLex v).1) heq
    change NonmonomialOrderLocal.nmOrd (geoTransformAlong (currentProductMarked W E T) .refl) x =
      NonmonomialOrderLocal.nmOrd (geoTransformAlong (currentProductMarked W E T) .refl) y at hfirst
    rw [geoTransformAlong_refl] at hfirst
    rw [currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T ht,
      currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T ht] at hfirst
    rw [chronological_product_eq_actual_family_product W E T] at hfirst
    exact hfirst
  refine ⟨C,hneC,hCZ,hCur,hTemp,hCeq,?_⟩
  change ∀ x ∈ C,∀ᶠ y in 𝓝 x,y ∈ C →
    (∀ i,ordinaryTraceOrder N (F i) y=ordinaryTraceOrder N (F i) x) ∧
    actualProperPositions F y=actualProperPositions F x ∧
    ∀ i : Fin (currentProductMarked W E T).E.length,
      (y ∈ (currentProductMarked W E T).E.get i ↔ x ∈ (currentProductMarked W E T).E.get i)
  intro x hx
  filter_upwards [eventually_member_orders_and_proper_positions hn hN F
    (fun i => (hfam i).1) (fun i => (hfam i).2.1) (fun i => (hfam i).2.2) hsub hval hx,hBorn x hx] with y hy hb hyC
  exact ⟨(hy hyC).1,(hy hyC).2,hb hyC⟩

end
end Hironaka.HironakaSharpActualMaximumMemberOrders
