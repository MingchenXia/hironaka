/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpOriginalProductTraceOrder

/-! Genuine internally selected original product maximum centres: true factor
USC and sum rigidity produce local containment and actual ALL-boundary NC.
Complete source-first mathematics precedes this first-centre producer. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpOriginalAllBoundaryCentre
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  HironakaSharpOriginalMemberProduct HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalProductTraceOrder NonmonomialOrderLocal GermIdealOrder
  CanonicalCentres ResolutionDriver DivisorExponentAlong
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

/-- Actual partial coordinates for all incident positions give literal pointwise NC. -/
theorem normalCrossingsAt_of_partial_incident {C : Set X} {E : List (Set X)} {x : X}
    (h : IsPartialNCAt n C E (Finset.univ.filter fun i => x ∈ E.get i) x) :
    HironakaSharpNormalCrossingsOpenLocus.normalCrossingsAt (n := n) C E x := by
  classical
  obtain ⟨Y,s,Θ,ht,h0,hC,hE⟩ := h
  refine ⟨Y,s,⟨Θ,ht,h0,?_⟩,?_⟩
  · rintro (_ | i) hi
    · exact hC
    · exact (hE i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩) hi).2
  · intro i hi
    exact (hE i (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩) hi).1

/-- The true open coordinate dictionary retains every original divisor position. -/
theorem normalCrossingsAt_preimage_val_iff {C : Set X} {E : List (Set X)}
    {U : Opens X} {x : U} :
    HironakaSharpNormalCrossingsOpenLocus.normalCrossingsAt (n := n)
      ((Subtype.val : U → X) ⁻¹' C) (E.map ((Subtype.val : U → X) ⁻¹' ·)) x ↔
      HironakaSharpNormalCrossingsOpenLocus.normalCrossingsAt (n := n) C E (x : X) := by
  classical
  let c : Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length → Fin E.length :=
    Fin.cast (List.length_map _)
  let d : Fin E.length → Fin (E.map ((Subtype.val : U → X) ⁻¹' ·)).length :=
    Fin.cast (List.length_map _).symm
  constructor
  · rintro ⟨Y,s,hfam,hcard⟩
    refine ⟨Y,fun i => s (d i),isCoordinateFamilyAt_preimage_val_iff.mp
      (IsCoordinateFamilyAt.reindex hfam (Option.map d) ?_ ?_),?_⟩
    · rintro (_ | i)
      · rfl
      · simp [d]
    · rintro (_ | i) <;> rfl
    · intro i hi
      exact hcard (d i) (by simpa [get_map_preimage,d] using hi)
  · rintro ⟨Y,s,hfam,hcard⟩
    refine ⟨Y,fun i => s (c i),
      IsCoordinateFamilyAt.reindex ((pullsBackCoordinates_val U) _ _ x hfam)
        (Option.map c) ?_ ?_,?_⟩
    · rintro (_ | i)
      · rfl
      · exact get_map_preimage E i
    · rintro (_ | i) <;> rfl
    · intro i hi
      exact hcard (c i) (by simpa [get_map_preimage,c] using hi)

/-- Genuine local incidence containment constructs actual ALL-boundary NC coordinates. -/
theorem hasNormalCrossings_of_eventually_incident_containment {C : Set X} {E : List (Set X)}
    (hC : IsClosedSubmanifold n C) (hE : IsSNCDivisor n E)
    (hlocal : ∀ x ∈ C, ∀ i : Fin E.length, x ∈ E.get i →
      ∀ᶠ y in 𝓝 x,y ∈ C → y ∈ E.get i) : HasNormalCrossings n C E := by
  classical
  intro x hx
  have hnb : ∀ᶠ y in 𝓝 x,∀ i : Fin E.length,x ∈ E.get i → y ∈ C → y ∈ E.get i := by
    apply (eventually_all_finite (Set.toFinite {i : Fin E.length | x ∈ E.get i})).mpr
    intro i hi
    exact hlocal x hx i hi
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hnb
  let U : Opens X := ⟨V,hVo⟩
  let z : U := ⟨x,hxV⟩
  let CU : Set U := (Subtype.val : U → X) ⁻¹' C
  let EU : List (Set U) := E.map ((Subtype.val : U → X) ⁻¹' ·)
  have hCU : IsClosedSubmanifold n CU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hC U
  have hEU : IsSNCDivisor n EU := isSNCDivisor_map_preimage
    (pullsBackCoordinates_val (n := n) U) continuous_subtype_val hE
  have hz : z ∈ CU := hx
  have hbase : IsPartialNCAt n CU EU ∅ z := by
    simpa using isPartialNCAt_of_hasNormalCrossings (E := EU)
      (hasNormalCrossings_nil_of_isClosedSubmanifold hCU) hz
  have hstep : ∀ I : Finset (Fin EU.length),
      (∀ i ∈ I,z ∈ EU.get i) → IsPartialNCAt n CU EU I z := by
    intro I
    refine Finset.induction_on I ?_ ?_
    · exact fun _ => hbase
    · intro i I _ ih hI
      have hi : z ∈ EU.get i := hI i (Finset.mem_insert_self i I)
      have hcontains : CU ⊆ EU.get i := by
        intro y hy
        rw [get_map_preimage] at hi ⊢
        exact hV y.property _ hi hy
      exact (ih fun j hj => hI j (Finset.mem_insert_of_mem hj)).insert hEU hz hcontains
  have hpartial := hstep (Finset.univ.filter fun i => z ∈ EU.get i)
    (fun _ hi => (Finset.mem_filter.mp hi).2)
  exact normalCrossingsAt_preimage_val_iff.mp (normalCrossingsAt_of_partial_incident
    (X := CMfd.of (n := n) U) hpartial)

/-- Componentwise upper bounds and true finite-sum equality force genuine equality of every factor. -/
theorem factor_eq_of_sum_eq {r : ℕ} {a b : Fin r → ℕ}
    (hle : ∀ i,a i ≤ b i) (hsum : (∑ i,a i) = ∑ i,b i) (i : Fin r) : a i=b i := by
  apply (hle i).antisymm
  by_contra hnot
  have hlt : a i < b i := Nat.lt_of_not_ge hnot
  have hsumlt := Finset.sum_lt_sum (fun j _ => hle j) ⟨i,Finset.mem_univ i,hlt⟩
  exact (ne_of_lt hsumlt) hsum

/-- Actual original sum rigidity and actual factor USC construct all local factor equalities. -/
theorem eventually_originalMemberTraceOrder_eq_on_constant_product (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {C : Set X} (hCW : C ⊆ W)
    (hconstant : ∀ x ∈ C,∀ y ∈ C,ordinaryTraceOrder W (originalMemberProduct (n := n) E) x =
      ordinaryTraceOrder W (originalMemberProduct (n := n) E) y)
    {x : X} (hx : x ∈ C) :
    ∀ᶠ y in 𝓝 x,y ∈ C → ∀ i : Fin E.length,
      ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) y =
        ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x := by
  have hbounds : ∀ᶠ y in 𝓝 x,∀ i : Fin E.length,
      ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) y ≤
        ordinaryTraceOrder W (vanishingIdeal (n := n) (E.get i)) x :=
    Filter.eventually_all.mpr fun i => eventually_originalMemberTraceOrder_le hn hW hE hdense (hCW hx) i
  filter_upwards [hbounds] with y hy hyC
  have hsum := (originalMemberProduct_traceOrder_eq_sum hn hW E hE hdense (hCW hyC)).symm.trans
    ((hconstant y hyC x hx).trans (originalMemberProduct_traceOrder_eq_sum hn hW E hE hdense (hCW hx)))
  have hmap (f : Set X → ℕ) : (E.map f).sum = ∑ i : Fin E.length,f (E.get i) := by
    conv_lhs => rw [← List.ofFn_get E,List.map_ofFn,List.sum_ofFn]
    rfl
  rw [hmap,hmap] at hsum
  exact fun i => factor_eq_of_sum_eq hy hsum i

/-- Real original factor order-one geometry turns the internally proved equality into actual containment. -/
theorem eventually_original_incident_containment_of_constant_product (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) {C : Set X} (hCW : C ⊆ W)
    (hconstant : ∀ x ∈ C,∀ y ∈ C,ordinaryTraceOrder W (originalMemberProduct (n := n) E) x =
      ordinaryTraceOrder W (originalMemberProduct (n := n) E) y)
    {x : X} (hx : x ∈ C) (i : Fin E.length) (hi : x ∈ E.get i) :
    ∀ᶠ y in 𝓝 x,y ∈ C → y ∈ E.get i := by
  have hI := VanishingIdealCoherent.isCoherent_vanishingIdeal (MonomialPart.isClosedSubmanifold_get hn hE i)
  have hne : ∀ y ∈ W,IsNonzeroAlongAt W (vanishingIdeal (n := n) (E.get i)) y :=
    fun _ hy => originalMemberIdeal_isNonzeroAlongAt hE hdense (List.get_mem E i) hy
  have hxcos : x ∈ cosupport n W (vanishingIdeal (n := n) (E.get i)) 1 := by
    rw [SmoothCentreLocus.cosupport_vanishingIdeal_one (hE.1 _ (List.get_mem E i))]
    exact ⟨hCW hx,hi⟩
  have hxord := (ordinaryTraceOrder_cosupport_iff hW hI hne (hCW hx) 1).mp hxcos
  filter_upwards [eventually_originalMemberTraceOrder_eq_on_constant_product hn hW hE hdense hCW hconstant hx]
    with y hy hyC
  have hycos := (ordinaryTraceOrder_cosupport_iff hW hI hne (hCW hyC) 1).mpr (by rwa [hy hyC i])
  rw [SmoothCentreLocus.cosupport_vanishingIdeal_one (hE.1 _ (List.get_mem E i))] at hycos
  exact hycos.2

/-- The SAME actual empty-boundary product order is independent of its positive mark. -/
theorem nmOrd_originalMemberProductMarked (W : Set X) (E : List (Set X)) (q : ℕ) (x : X) :
    nmOrd (originalMemberProductMarked W E q) x = ordinaryTraceOrder W (originalMemberProduct (n := n) E) x := rfl

/-- Equality of true maximum values constructs actual product first-order constancy. -/
theorem original_product_maxLocus_first_order_constant (hn : 0 < n)
    (W : Set X) (E : List (Set X)) (q : ℕ)
    {x y : X}
    (hx : x ∈ maxLocus ((invFamily hn (n+1)).inv (originalMemberProductMarked W E q) (.refl : BlowupTower X X))
      (originalMemberProductMarked W E q).cosupp)
    (hy : y ∈ maxLocus ((invFamily hn (n+1)).inv (originalMemberProductMarked W E q) (.refl : BlowupTower X X))
      (originalMemberProductMarked W E q).cosupp) :
    ordinaryTraceOrder W (originalMemberProduct (n := n) E) x =
      ordinaryTraceOrder W (originalMemberProduct (n := n) E) y := by
  have heq := (hy.2 x hx.1).antisymm (hx.2 y hy.1)
  have hfirst := congrArg (fun v : ValTy (n+1) => (ofLex v).1) heq
  change nmOrd (geoTransformAlong (originalMemberProductMarked W E q) (.refl : BlowupTower X X)) x =
    nmOrd (geoTransformAlong (originalMemberProductMarked W E q) (.refl : BlowupTower X X)) y at hfirst
  simpa only [geoTransformAlong_refl,nmOrd_originalMemberProductMarked] using hfirst

/-- ONLY original inputs select the actual maximum centre and construct its true
NC with ALL original E, not only its empty auxiliary boundary. -/
theorem exists_actual_original_allBoundary_product_centre (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    {d q : ℕ} (hd : d ≤ n) (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x d)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (hq : 1 ≤ q) (hcompact : IsCompact W)
    (hne : (originalMemberProductMarked W E q).cosupp.Nonempty) :
    ∃ C : Set X,C.Nonempty ∧ (originalMemberProductMarked W E q).IsAdmissibleCentre C ∧
      C ⊆ W ∧ HasNormalCrossings n C E ∧
      (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
      C=maxLocus ((invFamily hn (n+1)).inv (originalMemberProductMarked W E q) (.refl : BlowupTower X X))
        (originalMemberProductMarked W E q).cosupp := by
  let M := originalMemberProductMarked W E q
  let R := invFamily.{u} hn (n+1)
  have hbase := originalMemberProductMarked_isInvDomain hn hW hE hd hreg hdense hq
  have hdom : IsInvDomain (n+1) M :=
    ⟨hbase.isWellFormed,fun x hx => by
      obtain ⟨j,hj,hregj⟩ := hbase.dimLE x hx
      exact ⟨j,hj.trans (Nat.le_succ n),hregj⟩,
      hbase.one_le_d,hbase.isNonzeroAlongAt⟩
  have hclosed : IsClosed M.cosupp := GiraudAlong.isClosed_cosupport_along
    hdom.isWellFormed.isCoherent hdom.isWellFormed.isClosedSubmanifold_N _
  have hcompactC : IsCompact M.cosupp := hcompact.of_isClosed_subset hclosed M.cosupp_subset_N
  have husc := R.isInvValue.usc M hdom (.refl : BlowupTower X X) trivial
  rw [geoTransformAlong_refl] at husc
  obtain ⟨c,hc,hmax⟩ := husc.exists_isMaxOn hcompactC hne
  let C := maxLocus (R.inv M (.refl : BlowupTower X X)) M.cosupp
  have hadm := R.isInvValue.isAdmissibleCentre_maxLocus hdom (.refl : BlowupTower X X) trivial trivial
  rw [geoTransformAlong_refl] at hadm
  have hCW : C ⊆ W := hadm.2.1.trans M.cosupp_subset_N
  have hconstant : ∀ x ∈ C,∀ y ∈ C,ordinaryTraceOrder W (originalMemberProduct (n := n) E) x =
      ordinaryTraceOrder W (originalMemberProduct (n := n) E) y :=
    fun _ hx _ hy => original_product_maxLocus_first_order_constant hn W E q hx hy
  have hNCE : HasNormalCrossings n C E := hasNormalCrossings_of_eventually_incident_containment hadm.1 hE
    (fun _ hx i hi => eventually_original_incident_containment_of_constant_product hn hW hE hdense hCW hconstant hx i hi)
  have hemb : (⟨univ,E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C := by
    refine ⟨hadm.1,?_,hNCE⟩
    rw [HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW.1 E]
    exact hCW
  exact ⟨C,⟨c,hc,hmax⟩,hadm,hCW,hNCE,hemb,rfl⟩

end
end Hironaka.HironakaSharpOriginalAllBoundaryCentre
