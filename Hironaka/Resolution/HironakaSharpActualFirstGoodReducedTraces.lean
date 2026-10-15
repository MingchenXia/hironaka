/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualOriginalDynamicStep

/-! TRUE reduced smooth lower trace carriers on the COMPUTED FIRST-Z complement.
No joint SNC, Z-erasing driver, higher original history or termination claim. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualFirstGoodReducedTraces
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualOriginalDynamicStep HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualPrincipalOrderOneTrace
  HironakaSharpOriginalProductTraceOrder HironakaSharpActualFiniteMemberProduct
  RelativePrincipalizationSpan RestrictedIdealExtension DivisorExponentAlong NormalCrossings
  MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers MonomialPartAlong
variable {n : ℕ} {X Y : CMfd.{u} n}

private theorem actual_family_geometry (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    ∀ i : Fin E.length,
      let N := (geoTransformAlong (geometricTemplate W []) T).N
      let I := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
      I.IsCoherent ∧ (∀ y ∈ N,IsNonzeroAlongAt N I y) ∧
      ∀ y ∈ N,∃ f : Y → ℂ,HolomorphicAt n f y ∧ ∀ g,I.mem y g ↔
        HolomorphicAt n g y ∧ IsInSpanOnAt (n := n) N (·=f) y g := by
  intro i
  obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  rw [hNi] at hnzi hpri
  exact ⟨hwi.isCoherent,hnzi,hpri⟩

/-- True original geometry supplies genuine factor rigidity on the literal
FIRST-good locus, retaining the proper full ideal-germ quotient classes. -/
theorem original_first_good_factor_rigidity (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    {x : Y} (hx : x ∈ (geoTransformAlong (geometricTemplate W []) T).N)
    (hxZ : x ∉ chronologicalDistinctDefect W E T) :
    let N := (geoTransformAlong (geometricTemplate W []) T).N
    let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    (∀ i ∈ actualProperPositions F x,ordinaryTraceOrder N (F i) x=1) ∧
      Set.InjOn (Quotient.mk (actualIdealGermSetoid F x)) (actualProperPositions F x) := by
  let N := (geoTransformAlong (geometricTemplate W []) T).N
  let F := fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hN := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hT).isClosedSubmanifold_N
  have hFam := actual_family_geometry hn hW hE hdense T hT
  have hLe := actual_distinct_count_le_productOrder hN (fun i => (hFam i).1)
    (fun i => (hFam i).2.1) (fun i => (hFam i).2.2) hx
  have hNot : ¬actualDistinctProperCount F x < ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x :=
    fun h => hxZ ⟨hx,h⟩
  have heq := Nat.le_antisymm (Nat.le_of_not_gt hNot) hLe
  exact (actual_productOrder_eq_distinct_iff hN (fun i => (hFam i).1)
    (fun i => (hFam i).2.1) (fun i => (hFam i).2.2) hx).mp heq

/-- The actual current trace, with its literal same carrier and real ideal. -/
def actualChronologicalTrace (W : Set X) (E : List (Set X)) (i : Fin E.length)
    (T : BlowupTower X Y) : Set Y :=
  (geoTransformAlong (geometricTemplate W []) T).N ∩
    (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus

private theorem actual_trace_at_first_good (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) (i : Fin E.length)
    {x : Y} (hx : x ∈ actualChronologicalTrace W E i T) (hxZ : x ∉ chronologicalDistinctDefect W E T) :
    let N := (geoTransformAlong (geometricTemplate W []) T).N
    let I := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
    (∀ g,I.mem x g ↔ (vanishingIdeal (n := n) (actualChronologicalTrace W E i T)).mem x g) ∧
      ∃ k,RegularAtDim (n := n) N x k ∧ RegularAtDim (n := n) (actualChronologicalTrace W E i T) x (k-1) := by
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hN := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hT).isClosedSubmanifold_N
  have hFam := actual_family_geometry hn hW hE hdense T hT
  have hProper := (actual_proper_iff_zeroLocus (fun j => (hFam j).1) i x).mpr hx.2
  have hOrd := (original_first_good_factor_rigidity hn hW hE hdense T hT hx.1 hxZ).1 i hProper
  obtain ⟨f,hf,hgen⟩ := (hFam i).2.2 x hx.1
  obtain ⟨_U,_u,_hxU,_hu,_hux,_hs,hRed,hReg⟩ := actual_orderOne_relative_reduced_trace hN
    (hFam i).1 (hFam i).2.1 hx.1 f hf hgen hOrd
  exact ⟨hRed,hReg⟩

private theorem vanishing_unit_off_closed {S : Set Y} (hS : IsClosed S) {x : Y} (hx : x ∉ S)
    (g : Y → ℂ) (hg : HolomorphicAt n g x) : (vanishingIdeal (n := n) S).mem x g := by
  refine ⟨hg,?_⟩
  filter_upwards [hS.isOpen_compl.mem_nhds hx] with y hy hyS
  exact False.elim (hy hyS)

/-- ONLY original inputs construct the COMPUTED first-good open, actual lower
trace smoothness and BOTH full normalized-ideal directions on its ENTIRE domain. -/
theorem exists_actual_first_good_open_reduced_traces (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hr : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    ∃ O : Opens Y,(O : Set Y)=(chronologicalDistinctDefect W E T)ᶜ ∧
      ∀ i : Fin E.length,
        IsClosedSubmanifold n ((Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T) ∧
        (∀ x : O,x ∈ (Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T →
          ∃ k,RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N (x : Y) k ∧
            RegularAtDim (n := n) ((Subtype.val : O → Y) ⁻¹' actualChronologicalTrace W E i T) x (k-1)) ∧
        ∀ x ∈ (O : Set Y),∀ g,
          (restrictOn n (geoTransformAlong (geometricTemplate W []) T).N
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal).mem x g ↔
            (vanishingIdeal (n := n) (actualChronologicalTrace W E i T)).mem x g := by
  have hZa := original_chronological_distinct_defect_analytic hn hW hE hdense d hr T hT
  let O : Opens Y := ⟨(chronologicalDistinctDefect W E T)ᶜ,hZa.isClosed.isOpen_compl⟩
  have hw0 : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hN := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw0 T hT).isClosedSubmanifold_N
  have hFam := actual_family_geometry hn hW hE hdense T hT
  refine ⟨O,rfl,?_⟩
  intro i
  let I := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
  let S := actualChronologicalTrace W E i T
  have hSc : IsClosed S := hN.1.inter (CodimOneSupport.isComplexAnalyticSubset_zeroLocus (hFam i).1).isClosed
  refine ⟨⟨hSc.preimage continuous_subtype_val,?_⟩,?_,?_⟩
  · intro x hx
    obtain ⟨_hRed,k,_hNk,hSk⟩ := actual_trace_at_first_good hn hW hE hdense T hT i hx x.property
    exact ⟨k-1,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hSk⟩
  · intro x hx
    obtain ⟨_hRed,k,hNk,hSk⟩ := actual_trace_at_first_good hn hW hE hdense T hT i hx x.property
    exact ⟨k,hNk,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr hSk⟩
  · intro x hxO g
    by_cases hxS : x ∈ S
    · obtain ⟨hRed,_hReg⟩ := actual_trace_at_first_good hn hW hE hdense T hT i hxS hxO
      obtain ⟨f,hf,hgen⟩ := (hFam i).2.2 x hxS.1
      constructor
      · intro hg
        apply (hRed g).mp
        exact (hgen g).mpr ⟨hg.1,IsInSpanOnAt.trans (fun a ha => ((hgen a).mp ha).2) hg.2⟩
      · intro hg
        exact le_restrictOn (hFam i).1 x g ((hRed g).mpr hg)
    · by_cases hxN : x ∈ (geoTransformAlong (geometricTemplate W []) T).N
      · have hxZ : x ∉ I.zeroLocus := fun h => hxS ⟨hxN,h⟩
        have h1 : I.mem x (1 : Y → ℂ) := by
          by_contra hn1
          have hProper : i ∈ actualProperPositions (fun j : Fin E.length =>
              (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal) x := by
            simp only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and]
            exact hn1
          exact hxZ ((actual_proper_iff_zeroLocus (fun j => (hFam j).1) i x).mp hProper)
        constructor
        · intro hg
          exact vanishing_unit_off_closed hSc hxS g hg.1
        · intro hg
          have hgI : I.mem x g := HomogenizedIdeal.mem_of_isInSpanAt (hFam i).1
            (isInSpanAt_of_eq_mul h1 hg.1 hg.1 (Eventually.of_forall fun y => by simp))
          exact le_restrictOn (hFam i).1 x g hgI
      · exact ⟨fun hg => vanishing_unit_off_closed hSc hxS g hg.1,
          fun hg => restrictOn_eq_top_of_disjoint hN.1.isOpen_compl hxN (by simp) hg.1⟩

end
end Hironaka.HironakaSharpActualFirstGoodReducedTraces
