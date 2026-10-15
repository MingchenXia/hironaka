/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalOrderOneTraceIdeal
import Hironaka.Resolution.HironakaSharpOriginalDistinctTraceUSC

/-! Actual shared order-one original trace IDEALS are recognized by true pair
intersection local dimension. Genuine ideal dictionaries precede all branch
recognition; complete source-first blueprint precedes this source. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalSharedTraceBranchDimension
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpOriginalOrderOneTraceIdeal HironakaSharpOriginalOrderOneTraceGeometry
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalDistinctDefectPhase HironakaSharpOriginalDistinctTraceUSC
  HironakaSharpOriginalMultiBoundaryBadLocus RelativePrincipalizationSpan RestrictedIdealExtension
  AnalyticDimensionBasics PureDimension RegularPointDimension GermIdealOrder
  NormalCrossings MonomialPartAlong
variable {n : ℕ} {X : CMfd.{u} n}

/-- Whole actual dimension lower locus, from genuine analytic decompositions. -/
theorem isComplexAnalyticSubset_locDimGE {A : Set X} (hA : IsComplexAnalyticSubset (n := n) A) (q : ℕ) :
    IsComplexAnalyticSubset (n := n) {x | LocDimGE (n := n) A x q} := by
  have heq : {x | LocDimGE (n := n) A x q}=closure (regularStratum (n := n) A (q ≤ ·)) := by
    ext x
    rw [mem_closure_iff_nhds]
    constructor
    · intro hx U hU
      obtain ⟨y,hy,k,hq,hreg⟩ := hx U hU
      exact ⟨y,hy,mem_regularStratum.mpr ⟨k,hq,hreg⟩⟩
    · intro hx U hU
      obtain ⟨y,hy,hyS⟩ := hx U hU
      obtain ⟨k,hq,hreg⟩ := mem_regularStratum.mp hyS
      exact ⟨y,hy,k,hq,hreg⟩
  rw [heq]
  exact isComplexAnalyticSubset_closure_regularStratum hA _

private theorem pair_analytic (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) (i j : Fin E.length) :
    IsComplexAnalyticSubset (n := n) (W ∩ E.get i ∩ E.get j) :=
  ((AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hW).inter
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold (MonomialPart.isClosedSubmanifold_get hn hE i))).inter
    (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold (MonomialPart.isClosedSubmanifold_get hn hE j))

/-- True large pair dimension supplies the actual original trace ideal relation. -/
theorem original_traceGerm_rel_of_pair_locDimGE (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hxW : x ∈ W) {d : ℕ}
    (hreg : RegularAtDim (n := n) W x (d+1)) (i j : Fin E.length)
    (hoi : ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x=1)
    (hoj : ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get j)) x=1)
    (hdim : LocDimGE (n := n) (W ∩ E.get i ∩ E.get j) x d) :
    (traceGermSetoid (n := n) W E x).r i j := by
  have hA := pair_analytic hn hW hE i j
  have hsupport : ∀ (a : Fin E.length),
      W ∩ E.get i ∩ E.get j ⊆ W ∩ E.get a →
      ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get a)) x=1 →
      ∀ᶠ y in 𝓝 x,y ∈ W ∩ E.get i ∩ E.get j ↔ y ∈ W ∩ E.get a := by
    intro a ha hoa
    obtain ⟨U,u,hxU,hu,_hgen,hs⟩ := exists_actual_original_orderOne_principal_contact hn hW hE hdense hxW a hoa
    have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE a)
    have hAS : W ∩ E.get i ∩ E.get j ⊆ cosupport n W (vanishingIdeal (n := n) (E.get a)) 1 := by
      intro y hy
      rw [cosupport_one (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg),
        BlowupExceptionalDivisor.zeroLocus_vanishingIdeal (hE.1 _ (List.get_mem E a))]
      exact ha hy
    filter_upwards [CodimOneSupportAlong.eventually_mem_iff_of_locDimGE_along hI hW le_rfl hA hAS hu hxU hreg hdim,
      hs,hu.isOpen.mem_nhds hxU] with y hy hyS hyU
    exact hy.trans ⟨fun h => hyS.mpr ⟨h,hyU⟩,fun h => (hyS.mp h).1⟩
  have hs : ∀ᶠ y in 𝓝 x,y ∈ W ∩ E.get i ↔ y ∈ W ∩ E.get j := by
    filter_upwards [hsupport i (fun _ hy => hy.1) hoi,
      hsupport j (fun _ hy => ⟨hy.1.1,hy.2⟩) hoj] with y hi hj
    exact hi.symm.trans hj
  intro g hg
  have hei := original_orderOne_restrictOn_mem_iff_vanishingIdeal_trace hn hW hE hdense hxW i hoi g
  have hej := original_orderOne_restrictOn_mem_iff_vanishingIdeal_trace hn hW hE hdense hxW j hoj g
  have hv : (vanishingIdeal (n := n) (W ∩ E.get i)).mem x g ↔
      (vanishingIdeal (n := n) (W ∩ E.get j)).mem x g := by
    constructor
    · rintro ⟨hol,hvan⟩
      refine ⟨hol,?_⟩
      filter_upwards [hvan,hs] with y hy hyS hyH
      exact hy (hyS.mpr hyH)
    · rintro ⟨hol,hvan⟩
      refine ⟨hol,?_⟩
      filter_upwards [hvan,hs] with y hy hyS hyH
      exact hy (hyS.mp hyH)
  exact ⟨fun h => ((hej.mpr (hv.mp (hei.mp ⟨hg,h⟩)))).2,
    fun h => ((hei.mpr (hv.mpr (hej.mp ⟨hg,h⟩)))).2⟩

/-- Actual coherent trace equality yields SAME literal pair regularity and dimension. -/
theorem pair_locDimGE_of_original_traceGerm_rel (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hxW : x ∈ W) {d : ℕ}
    (hreg : RegularAtDim (n := n) W x (d+1)) (i j : Fin E.length)
    (hoi : ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x=1)
    (hrel : (traceGermSetoid (n := n) W E x).r i j) :
    LocDimGE (n := n) (W ∩ E.get i ∩ E.get j) x d := by
  have hs : ∀ᶠ y in 𝓝 x,y ∈ W ∩ E.get i ∩ E.get j ↔ y ∈ W ∩ E.get i := by
    filter_upwards [eventually_original_traceGerm_rel hn hW hE i j hrel] with y hy
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h,?_⟩
      by_contra hyj
      have hiUnit := (hy (fun _ => 1) (holomorphicAt_const 1)).mpr
        ((traceSpan_unit_iff_notMem (hE.1 _ (List.get_mem E j)) h.1).mpr hyj)
      exact (traceSpan_unit_iff_notMem (hE.1 _ (List.get_mem E i)) h.1).mp hiUnit h.2
  obtain ⟨k,hWk,htrace⟩ := original_orderOne_member_trace_regularAt hn hW hE hdense hxW i hoi
  have hk : k=d+1 := eq_of_regularAtDim hWk hreg
  rw [hk,Nat.add_sub_cancel] at htrace
  exact locDimGE_of_regularAtDim (CodimOneSupport.regularAtDim_of_eventually_mem_iff (hs.mono fun _ h => h.symm) htrace)

/-- BOTH actual branch/dimension directions for the SAME genuine original trace ideals. -/
theorem original_orderOne_traceGerm_rel_iff_pair_locDimGE (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hxW : x ∈ W) {d : ℕ}
    (hreg : RegularAtDim (n := n) W x (d+1)) (i j : Fin E.length)
    (hoi : ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x=1)
    (hoj : ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get j)) x=1) :
    (traceGermSetoid (n := n) W E x).r i j ↔ LocDimGE (n := n) (W ∩ E.get i ∩ E.get j) x d :=
  ⟨pair_locDimGE_of_original_traceGerm_rel hn hW hE hdense hxW hreg i j hoi,
    original_traceGerm_rel_of_pair_locDimGE hn hW hE hdense hxW hreg i j hoi hoj⟩

end
end Hironaka.HironakaSharpOriginalSharedTraceBranchDimension
