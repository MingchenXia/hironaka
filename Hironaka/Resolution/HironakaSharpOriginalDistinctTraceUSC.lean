/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalDistinctDefectPhase

/-! True coherent original trace-germ persistence BEFORE actual DISTINCT count
USC and original first-phase invariant-stratum saturation. No Z-analyticity,
restricted-Z maximum driver or full sharp history is asserted. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalDistinctTraceUSC
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms RelativePrincipalizationSpan RestrictedIdealExtension
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalAllBoundaryCentre
  HironakaSharpOriginalDistinctDefectPhase HironakaSharpOriginalMultiBoundaryBadLocus
  NormalCrossings CanonicalCentres
variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual finite coherent generators construct ENTIRE nearby germ inclusion. -/
theorem eventually_coherent_germ_le {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent)
    {x : X} (hle : ∀ g,I.mem x g → J.mem x g) :
    ∀ᶠ y in 𝓝 x,∀ g,I.mem y g → J.mem y g := by
  obtain ⟨U,hU,hxU,N,a,ha,hgen⟩ := hI x
  have hax : ∀ i : Fin N,I.mem x (a i) := fun i => IdealWeightComparison.mem_of_isPresentation hU hxU ha hgen i
  have hay : ∀ᶠ y in 𝓝 x,∀ i : Fin N,J.mem y (a i) :=
    Filter.eventually_all.mpr fun i => HomogenizedGlueing.eventually_mem hJ (hle _ (hax i))
  filter_upwards [hay,hU.mem_nhds hxU] with y hy hyU g hg
  refine HomogenizedIdeal.mem_of_isInSpanAt hJ (IsInSpanAt.trans ?_ ((hgen y hyU g).mp hg))
  rintro t ⟨i,rfl⟩
  exact InvertibleIdealQuotient.isInSpanAt_self (hy i) (GermIdeal.IsCoherent.holomorphicAt_mem hJ (hy i))

theorem eventually_coherent_germ_eq {I J : GermIdeal n X} (hI : I.IsCoherent) (hJ : J.IsCoherent)
    {x : X} (heq : ∀ g,I.mem x g ↔ J.mem x g) :
    ∀ᶠ y in 𝓝 x,∀ g,I.mem y g ↔ J.mem y g := by
  filter_upwards [eventually_coherent_germ_le hI hJ (fun g => (heq g).mp),
    eventually_coherent_germ_le hJ hI (fun g => (heq g).mpr)] with y hIJ hJI g
  exact ⟨hIJ g,hJI g⟩

/-- The SAME whole original restricted trace equivalence persists by actual ideal coherence. -/
theorem eventually_original_traceGerm_rel (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E) {x : X} (i j : Fin E.length)
    (hrel : (traceGermSetoid (n := n) W E x).r i j) :
    ∀ᶠ y in 𝓝 x,(traceGermSetoid (n := n) W E y).r i j := by
  let I := restrictOn n W (vanishingIdeal (n := n) (E.get i))
  let J := restrictOn n W (vanishingIdeal (n := n) (E.get j))
  have hI : I.IsCoherent := isCoherent_restrictOn_of_isClosedSubmanifold
    (VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)) hW
  have hJ : J.IsCoherent := isCoherent_restrictOn_of_isClosedSubmanifold
    (VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE j)) hW
  have heq : ∀ g,I.mem x g ↔ J.mem x g := by
    intro g
    exact ⟨fun hg => ⟨hg.1,(hrel g hg.1).mp hg.2⟩,fun hg => ⟨hg.1,(hrel g hg.1).mpr hg.2⟩⟩
  filter_upwards [eventually_coherent_germ_eq hI hJ heq] with y hy g hg
  exact ⟨fun h => ((hy g).mp ⟨hg,h⟩).2,fun h => ((hy g).mpr ⟨hg,h⟩).2⟩

/-- The genuine old-to-new quotient map bounds actual DISTINCT proper class cardinality. -/
theorem distinct_count_le_of_rel_and_proper (W : Set X) (E : List (Set X)) (x y : X)
    (hproper : properTraceMembers (n := n) W E y ⊆ properTraceMembers (n := n) W E x)
    (hrel : ∀ i j,(traceGermSetoid (n := n) W E x).r i j → (traceGermSetoid (n := n) W E y).r i j) :
    distinctProperTraceGermCount (n := n) W E y ≤ distinctProperTraceGermCount (n := n) W E x := by
  let f : Quotient (traceGermSetoid (n := n) W E x) → Quotient (traceGermSetoid (n := n) W E y) :=
    Quotient.map id hrel
  let Q := (properTraceMembers (n := n) W E x).image (Quotient.mk (traceGermSetoid (n := n) W E x))
  have hsub : (properTraceMembers (n := n) W E y).image (Quotient.mk (traceGermSetoid (n := n) W E y)) ⊆ Q.image f := by
    intro q hq
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_image.mpr ⟨Quotient.mk (traceGermSetoid (n := n) W E x) i,
      Finset.mem_image.mpr ⟨i,hproper hi,rfl⟩,rfl⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

/-- Actual restricted coherence and closed original members internally construct true DISTINCT-count USC. -/
theorem eventually_distinctProperTraceGermCount_le (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {x : X} (hx : x ∈ W) :
    ∀ᶠ y in 𝓝 x,y ∈ W → distinctProperTraceGermCount (n := n) W E y ≤
      distinctProperTraceGermCount (n := n) W E x := by
  have hrelation : ∀ᶠ y in 𝓝 x,∀ i j,(traceGermSetoid (n := n) W E x).r i j →
      (traceGermSetoid (n := n) W E y).r i j := by
    apply Filter.eventually_all.mpr
    intro i
    apply Filter.eventually_all.mpr
    intro j
    by_cases hrel : (traceGermSetoid (n := n) W E x).r i j
    · exact (eventually_original_traceGerm_rel hn hW hE i j hrel).mono fun _ hy _ => hy
    · exact Eventually.of_forall fun _ hy => False.elim (hrel hy)
  have hincidence : ∀ᶠ y in 𝓝 x,∀ i : Fin E.length,y ∈ E.get i → x ∈ E.get i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : x ∈ E.get i
    · exact Eventually.of_forall fun _ _ => hi
    · filter_upwards [(hE.1 _ (List.get_mem E i)).isOpen_compl.mem_nhds hi] with y hy hyH
      exact False.elim (hy hyH)
  filter_upwards [hrelation,hincidence] with y hyRel hyInc hyW
  have hproper : properTraceMembers (n := n) W E y ⊆ properTraceMembers (n := n) W E x := by
    rw [properTraceMembers_eq_incident hE.1 hyW,properTraceMembers_eq_incident hE.1 hx]
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,hyInc i (Finset.mem_filter.mp hi).2⟩
  exact distinct_count_le_of_rel_and_proper W E x y hproper hyRel

/-- The actual SAME-order stratum germ at any real FIRST-phase defect point is internally in Z. -/
theorem eventually_originalDistinctDefectPhase_of_same_order (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {x : X} (hx : x ∈ originalDistinctDefectPhase W E) :
    ∀ᶠ y in 𝓝 x,y ∈ W → ordinaryTraceOrder W (originalMemberProduct (n := n) E) y =
      ordinaryTraceOrder W (originalMemberProduct (n := n) E) x → y ∈ originalDistinctDefectPhase W E := by
  filter_upwards [eventually_distinctProperTraceGermCount_le hn hW hE hx.1] with y hy hyW horder
  refine ⟨hyW,?_⟩
  rw [horder]
  exact (hy hyW).trans_lt hx.2

/-- SAME actual constructed full product-invariant stratum germs are internally saturated in FIRST-phase Z. -/
theorem eventually_originalDistinctDefectPhase_of_same_invariant (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (q : ℕ) {x : X} (hx : x ∈ originalDistinctDefectPhase W E) :
    ∀ᶠ y in 𝓝 x,y ∈ W →
      (invFamily hn (n+1)).inv (originalMemberProductMarked W E q) (.refl : BlowupTower X X) y =
        (invFamily hn (n+1)).inv (originalMemberProductMarked W E q) (.refl : BlowupTower X X) x →
      y ∈ originalDistinctDefectPhase W E := by
  filter_upwards [eventually_originalDistinctDefectPhase_of_same_order hn hW hE hx] with y hy hyW hvalue
  have hfirst := congrArg (fun v : ValTy (n+1) => (ofLex v).1) hvalue
  change NonmonomialOrderLocal.nmOrd (geoTransformAlong
    (originalMemberProductMarked W E q) (.refl : BlowupTower X X)) y =
    NonmonomialOrderLocal.nmOrd (geoTransformAlong
    (originalMemberProductMarked W E q) (.refl : BlowupTower X X)) x at hfirst
  rw [geoTransformAlong_refl,nmOrd_originalMemberProductMarked,nmOrd_originalMemberProductMarked] at hfirst
  exact hy hyW hfirst

end
end Hironaka.HironakaSharpOriginalDistinctTraceUSC
