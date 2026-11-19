/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualMemberOrderStrata

/-!
# Original-only finite weighted adaptation of the same full maximum

One unchanged actual FULL maximum is partitioned into its entire finite
member-order pieces. Original geometry supplies all member domains and
the constant product mark; no order-profile certificate is an input.
Blueprint: `hironaka-sharp-actual-full-maximum-weighted-partition-extension.tex`.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaSharpActualFullMaximumWeightedPartition
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  MarkedIdeals MarkedIdeals.MarkedIdeal RelativePrincipalizationSpan NormalCrossings
  HironakaSharpActualMaximumMemberOrders HironakaSharpActualMemberOrderStrata
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualDynamicDistinctCentre
  HironakaSharpActualChronologicalDistinctDefect HironakaSharpActualFiniteMemberProduct
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalProductTraceOrder
  DivisorExponentAlong CanonicalCentres
variable {n : ℕ} {X : CMfd.{u} n}

/-- Original geometry internally supplies the full centre and every literal weighted piece. -/
theorem exists_actual_full_maximum_weighted_partition (hn : 0<n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hK : IsCompact W)
    {d : ℕ} (hd : d+1≤n) (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (ht : IsGeoTestTower (geometricTemplate W []) T)
    (hne : (chronologicalDistinctDefect W E T).Nonempty) :
    let N := (geoTransformAlong (geometricTemplate W []) T).N
    let F := fun i : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    ∃ (C : Set Y) (q : ℕ),C.Nonempty ∧ C ⊆ chronologicalDistinctDefect W E T ∧
      (currentProductMarked W E T).IsAdmissibleCentre C ∧
      (geoTransformAlong (geometricTemplate W []) T).IsAdmissibleCentre C ∧
      C=ResolutionDriver.maxLocus
        ((invFamily hn (n+1)).inv (currentProductMarked W E T) (.refl : BlowupTower Y Y))
        (chronologicalDistinctDefect W E T) ∧
      (∀ x ∈ C,ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x=q) ∧
      (⋃ a : Fin E.length → Fin (q+1),memberOrderStratum (N := N) F C a)=C ∧
      Pairwise (fun a b : Fin E.length → Fin (q+1) =>
        Disjoint (memberOrderStratum (N := N) F C a) (memberOrderStratum (N := N) F C b)) ∧
      ∀ a : Fin E.length → Fin (q+1),
        (currentProductMarked W E T).IsAdmissibleCentre (memberOrderStratum (N := N) F C a) ∧
        (geoTransformAlong (geometricTemplate W []) T).IsAdmissibleCentre (memberOrderStratum (N := N) F C a) ∧
        ∀ i : Fin E.length,
          (⟨N,(currentProductMarked W E T).E,F i,(a i).val⟩ : MarkedIdeal n Y).IsAdmissibleCentre
            (memberOrderStratum (N := N) F C a) ∧
          ∀ x ∈ memberOrderStratum (N := N) F C a,ordinaryTraceOrder N (F i) x=(a i).val := by
  let N := (geoTransformAlong (geometricTemplate W []) T).N
  let F := fun i : Fin E.length =>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  obtain ⟨C,hneC,hCZ,hCur,hTemp,hCeq,_hprofile⟩ :=
    exists_actual_dynamic_centre_member_order_profile hn hW hE hdense hK hd hr T ht hne
  obtain ⟨c,hcC⟩ := hneC
  let q := ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) c
  have hq : ∀ x ∈ C,ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x=q := by
    intro x hx
    have heq := ((hCeq ▸ hx).2 c (hCeq ▸ hcC).1).antisymm
      ((hCeq ▸ hcC).2 x (hCeq ▸ hx).1)
    have hfirst := congrArg (fun v : CanonicalCentres.ValTy (n+1) => (ofLex v).1) heq.symm
    change NonmonomialOrderLocal.nmOrd (geoTransformAlong (currentProductMarked W E T) .refl) x =
      NonmonomialOrderLocal.nmOrd (geoTransformAlong (currentProductMarked W E T) .refl) c at hfirst
    rw [geoTransformAlong_refl] at hfirst
    rw [currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T ht,
      currentProductMarked_nmOrd_eq_ordinaryTraceOrder hn hW hE hdense T ht] at hfirst
    rw [chronological_product_eq_actual_family_product W E T] at hfirst
    exact hfirst
  have hdom := currentProductMarked_isInvDomain hn hW hE hdense hK hd hr T ht
  have hTemplate : (geoTransformAlong (geometricTemplate W []) T).IsWellFormed :=
    MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong
      (show (geometricTemplate W []).IsWellFormed from
        ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩) T ht
  have hN : IsClosedSubmanifold n N := hTemplate.isClosedSubmanifold_N
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
  have hp := finite_member_order_strata hn (currentProductMarked W E T)
    hdom.isWellFormed.isCoherent hN hCur hsub F
    (fun i => (hfam i).1) (fun i => (hfam i).2.1) (fun i => (hfam i).2.2) hq
  have htpart := finite_member_order_strata hn (geoTransformAlong (geometricTemplate W []) T)
    hTemplate.isCoherent hN hTemp hsub F
    (fun i => (hfam i).1) (fun i => (hfam i).2.1) (fun i => (hfam i).2.2) hq
  refine ⟨C,q,⟨c,hcC⟩,hCZ,hCur,hTemp,hCeq,hq,hp.1,hp.2.1,?_⟩
  intro a
  refine ⟨hp.2.2 a,htpart.2.2 a,?_⟩
  intro i
  exact ⟨member_order_strata_weighted_admissible hn (currentProductMarked W E T)
    hdom.isWellFormed.isCoherent hN hCur hsub F
    (fun i => (hfam i).1) (fun i => (hfam i).2.1) (fun i => (hfam i).2.2) hq a i,
    fun _ hx => hx.2 i⟩

end
end Hironaka.HironakaSharpActualFullMaximumWeightedPartition
