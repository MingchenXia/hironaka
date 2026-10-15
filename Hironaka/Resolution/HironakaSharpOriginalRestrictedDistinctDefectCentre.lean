/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalDistinctDefectAnalytic

/-! Actual original full invariant is maximized on literal FIRST Z; real local
USC and genuine stratum saturation construct original open admissible centres
before true global smoothness and ALL original boundary compatibility. No
selected centre, desired local model or driver certificate is an input. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalRestrictedDistinctDefectCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpOriginalDistinctDefectAnalytic HironakaSharpOriginalDistinctDefectPhase
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMemberProductDomain HironakaSharpOriginalMemberProduct
  HironakaSharpOriginalAllBoundaryCentre HironakaSharpOriginalDeepProductBlowup
  HironakaSharpOriginalDistinctTraceUSC MarkedIdeals MarkedIdeals.MarkedIdeal
  GermIdealOrder NormalCrossings RelativePrincipalizationSpan RestrictedIdealExtension
  MarkedIdealRestrictOpen SimultaneousNormalCrossings CanonicalCentres
  NormalCrossingsInvariance ResolutionDriver ResolutionInvariantDriver
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

/-- Real full trace germ relation transports to the SAME indexed original open members. -/
theorem original_traceGerm_rel_preimage_val (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hE : IsSNCDivisor n E) (U : Opens X) {x : U} (i j : Fin E.length)
    (hrel : (traceGermSetoid (n := n) W E (x : X)).r i j) :
    (traceGermSetoid (n := n) ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) x).r
      (Fin.cast (List.length_map _).symm i) (Fin.cast (List.length_map _).symm j) := by
  intro g hg
  have hext : HolomorphicAt n (extendOpens U g) (x : X) := (holomorphicAt_iff_extendOpens U).mp hg
  have hdict (a : Fin E.length) :
      traceSpan (n := n) ((Subtype.val : U → X) ⁻¹' W) ((Subtype.val : U → X) ⁻¹' E.get a) x g ↔
      traceSpan (n := n) W (E.get a) (x : X) (extendOpens U g) := by
    have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE a)
    have hspan := restrictOn_pullback_val_iff U (W := W) (x := x) (F := g) hI
    rw [SmoothCentreHomogeneity.pullback_val_vanishingIdeal] at hspan
    exact ⟨fun h => (hspan.mp ⟨hg,h⟩).2,fun h => (hspan.mpr ⟨hext,h⟩).2⟩
  simpa [get_map_preimage] using
    (hdict i).trans ((hrel (extendOpens U g) hext).trans (hdict j).symm)

/-- At actual good points, TRUE original product order equals actual DISTINCT count. -/
theorem original_good_productOrder_eq_distinct (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {x : X} (hxW : x ∈ W)
    (hxNC : HironakaSharpNormalCrossingsOpenLocus.normalCrossingsAt (n := n) W E x) :
    ordinaryTraceOrder W (originalMemberProduct (n := n) E) x=distinctProperTraceGermCount (n := n) W E x := by
  obtain ⟨U,hxU,hEU,hTU,hord⟩ := exists_actual_original_product_order_neighborhood hn hW.1 hE hdense hxNC
  let z : U := ⟨x,hxU⟩
  let q := ordinaryTraceOrder W (originalMemberProduct (n := n) E) x
  have hne : ∀ y ∈ W,DivisorExponentAlong.IsNonzeroAlongAt W (originalMemberProduct (n := n) E) y :=
    fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hE hdense hy
  have hcos : x ∈ (originalMemberProductMarked W E q).cosupp :=
    (ordinaryTraceOrder_cosupport_iff hW (isCoherent_originalMemberProduct hn hE) hne hxW q).mpr le_rfl
  have hz : z ∈ (originalMemberProductMarked (X := CMfd.of (n := n) U)
      ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) q).cosupp := by
    rw [← pullback_val_originalMemberProductMarked hn W hE q U,MarkedIdealRestrictOpen.cosupp_pullback_val]
    · exact hcos
    · exact fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem (isCoherent_originalMemberProduct hn hE) hg
  have hq := (hord z hxW q).mp hz
  rw [distinctProperTraceGermCount_eq_boundaryCount hn hEU hTU hxW,
    CodimOnePartCanonical.boundaryCount_map_preimage] at hq
  have heq : q=BoundaryCount.boundaryCount E x := hq.antisymm (boundaryCount_le_originalProductTraceOrder hn hW hE hdense hxW)
  have hinj : Set.InjOn (Quotient.mk (traceGermSetoid (n := n) W E x)) (properTraceMembers (n := n) W E x) := by
    intro i hi j hj hquot
    by_contra hij
    have hxi : x ∈ E.get i := by
      rw [properTraceMembers_eq_incident hE.1 hxW] at hi
      exact (Finset.mem_filter.mp hi).2
    have hxj : x ∈ E.get j := by
      rw [properTraceMembers_eq_incident hE.1 hxW] at hj
      exact (Finset.mem_filter.mp hj).2
    let di : Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length := Fin.cast (List.length_map _).symm i
    let dj : Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length := Fin.cast (List.length_map _).symm j
    have hdi : z ∈ (E.map ((Subtype.val : U → X) ⁻¹' ·)).get di := by simpa [di,get_map_preimage] using hxi
    have hdj : z ∈ (E.map ((Subtype.val : U → X) ⁻¹' ·)).get dj := by simpa [dj,get_map_preimage] using hxj
    have hdij : di ≠ dj := by
      intro h
      have hv : i.val=j.val := congrArg (fun a : Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length => a.val) h
      exact hij (Fin.ext hv)
    obtain ⟨g,hg,hgi,hgj⟩ := exists_traceSpan_separator hn hEU hTU hxW di dj hdi hdj hdij
    exact hgj ((original_traceGerm_rel_preimage_val hn hE U (x := z) i j (Quotient.exact hquot)) g hg |>.mp hgi)
  have hcount : distinctProperTraceGermCount (n := n) W E x=BoundaryCount.boundaryCount E x := by
    unfold distinctProperTraceGermCount
    rw [Finset.card_image_of_injOn hinj,properTraceMembers_eq_incident hE.1 hxW]
    rfl
  exact heq.trans hcount.symm

/-- Literal FIRST Z avoids every original good NC point, including boundary intersections. -/
theorem originalDistinctDefectPhase_disjoint_good (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) :
    Disjoint (originalDistinctDefectPhase W E) (originalGoodLocus (n := n) W E) := by
  apply Set.disjoint_left.mpr
  intro x hx hgood
  rcases hgood with hout | hnc
  · exact hout hx.1
  · have heq := original_good_productOrder_eq_distinct hn hW hE hdense hx.1 hnc.2
    exact (ne_of_gt hx.2) heq

/-- True FIRST Z inclusion in the larger literal sharp bad locus; no equality claim. -/
theorem originalDistinctDefectPhase_subset_sharpBad (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) :
    originalDistinctDefectPhase W E ⊆ originalSharpBadLocus (n := n) W E := by
  intro x hx
  exact ⟨hx.1,fun hnc => Set.disjoint_left.mp (originalDistinctDefectPhase_disjoint_good hn hW hE hdense) hx (Or.inr ⟨hx.1,hnc⟩)⟩

/-- ONLY original inputs select the genuine restricted FIRST Z maximum and internally
construct actual global smoothness, ALL original E NC, and whole-good avoidance. -/
theorem exists_actual_original_restrictedDistinctDefect_centre (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d : ℕ} (hd : d+1 ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hcompact : IsCompact W)
    (hne : (originalDistinctDefectPhase W E).Nonempty) :
    ∃ C : Set X,C.Nonempty ∧ C ⊆ originalDistinctDefectPhase W E ∧
      IsClosedSubmanifold n C ∧ (originalMemberProductMarked W E 1).IsAdmissibleCentre C ∧
      HasNormalCrossings n C E ∧ (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      Disjoint C (originalGoodLocus (n := n) W E) ∧
      C=maxLocus ((invFamily hn (n+1)).inv (originalMemberProductMarked W E 1) (.refl : BlowupTower X X))
        (originalDistinctDefectPhase W E) := by
  let M := originalMemberProductMarked W E 1
  let R := invFamily.{u} hn (n+1)
  let f := R.inv M (.refl : BlowupTower X X)
  let Z := originalDistinctDefectPhase W E
  have hbase := originalMemberProductMarked_isInvDomain hn hW hE hd hreg hdense le_rfl
  have hdom : IsInvDomain (n+1) M := ⟨hbase.isWellFormed,fun x hx => by
      obtain ⟨j,hj,hregj⟩ := hbase.dimLE x hx
      exact ⟨j,hj.trans (Nat.le_succ n),hregj⟩,hbase.one_le_d,hbase.isNonzeroAlongAt⟩
  have hZcos : Z ⊆ M.cosupp := by
    intro x hx
    have hlt : distinctProperTraceGermCount (n := n) W E x < ordinaryTraceOrder W (originalMemberProduct (n := n) E) x := hx.2
    exact (ordinaryTraceOrder_cosupport_iff hW (isCoherent_originalMemberProduct hn hE)
      (fun _ hy => originalMemberProduct_isNonzeroAlongAt hn hE hdense hy) hx.1 1).mpr (by omega)
  have husc := R.isInvValue.usc M hdom (.refl : BlowupTower X X) trivial
  rw [geoTransformAlong_refl] at husc
  have hZusc := husc.mono hZcos
  have hZclosed := isClosed_originalDistinctDefectPhase hn hW hE hdense d hreg
  have hZcompact := isCompact_originalDistinctDefectPhase hn hW hE hdense d hreg hcompact
  obtain ⟨a,ha,hmax⟩ := hZusc.exists_isMaxOn hZcompact hne
  let C := maxLocus f Z
  have hCeq : C={x | x ∈ Z ∧ f x=f a} := maxLocus_eq_level ⟨ha,hmax⟩
  have hCne : C.Nonempty := ⟨a,ha,hmax⟩
  have hCZ : C ⊆ Z := fun _ hx => hx.1
  have hCW : C ⊆ W := fun _ hx => hx.1.1
  have hCclosed : IsClosed C := hCeq ▸ hZusc.isClosed_maxLocus hZclosed hmax
  have hCsm : IsClosedSubmanifold n C := by
    refine ⟨hCclosed,?_⟩
    intro x hx
    have hxeq : f x=f a := (hCeq ▸ hx).2
    have hnb : ∀ᶠ y in 𝓝 x,(y ∈ M.cosupp → f y ≤ f x) ∧
        (y ∈ W → f y=f x → y ∈ Z) :=
      (husc x (hZcos hx.1)).and
        (eventually_originalDistinctDefectPhase_of_same_invariant hn hW hE 1 hx.1)
    obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hnb
    let U : Opens X := ⟨V,hVo⟩
    let z : U := ⟨x,hxV⟩
    have hAdm := R.isInvValue.admissible M hdom (.refl : BlowupTower X X) trivial U (f x)
      (fun y hy hyU => by simpa only [geoTransformAlong_refl] using (hV hyU).1 (by simpa only [geoTransformAlong_refl] using hy))
    rw [geoTransformAlong_refl] at hAdm
    have hlocal : (Subtype.val : U → X) ⁻¹' {y | y ∈ M.cosupp ∧ f y=f x}=
        (Subtype.val : U → X) ⁻¹' C := by
      ext y
      constructor
      · intro hy
        have hyZ : (y : X) ∈ Z := (hV y.property).2 (M.cosupp_subset_N hy.1) hy.2
        apply (show (y : X) ∈ C ↔ (y : X) ∈ Z ∧ f y=f a from by rw [hCeq]; rfl).mpr
        exact ⟨hyZ,hy.2.trans hxeq⟩
      · intro hy
        have hyEq := (hCeq ▸ hy).2
        exact ⟨hZcos hy.1,hyEq.trans hxeq.symm⟩
    rw [hlocal] at hAdm
    obtain ⟨j,hj⟩ := hAdm.1.2 z hx
    exact ⟨j,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hj⟩
  have hconstant : ∀ x ∈ C,∀ y ∈ C,ordinaryTraceOrder W (originalMemberProduct (n := n) E) x=
      ordinaryTraceOrder W (originalMemberProduct (n := n) E) y := by
    intro x hx y hy
    have hval : f x=f y := ((hCeq ▸ hx).2).trans ((hCeq ▸ hy).2).symm
    have hfirst := congrArg (fun v : ValTy (n+1) => (ofLex v).1) hval
    change NonmonomialOrderLocal.nmOrd (geoTransformAlong M (.refl : BlowupTower X X)) x=
      NonmonomialOrderLocal.nmOrd (geoTransformAlong M (.refl : BlowupTower X X)) y at hfirst
    simpa only [geoTransformAlong_refl,M,nmOrd_originalMemberProductMarked] using hfirst
  have hNCE : HasNormalCrossings n C E := hasNormalCrossings_of_eventually_incident_containment hCsm hE
    (fun _ hx i hi => eventually_original_incident_containment_of_constant_product hn hW hE hdense hCW hconstant hx i hi)
  have hadm : M.IsAdmissibleCentre C := ⟨hCsm,hCZ.trans hZcos,hasNormalCrossings_nil_of_isClosedSubmanifold hCsm⟩
  have hemb : (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C := by
    refine ⟨hCsm,?_,hNCE⟩
    rw [HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW.1 E]
    exact hCW
  exact ⟨C,hCne,hCZ,hCsm,hadm,hNCE,hemb,
    (originalDistinctDefectPhase_disjoint_good hn hW hE hdense).mono_left hCZ,rfl⟩

end
end Hironaka.HironakaSharpOriginalRestrictedDistinctDefectCentre
