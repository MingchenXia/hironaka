/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpActualFiniteMemberProduct

/-! Literal dynamic FIRST Z from TRUE actual ideal-germ quotient classes.
Genuine factor multiplicities and reduced pair geometry precede whole analyticity.
No raw indexed-count substitution, modified-driver or composite-factor claim. -/
set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSharpActualChronologicalDistinctDefect
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupTowers
  HironakaSharpActualFiniteMemberProduct HironakaSharpActualFiniteChronologicalHistory
  HironakaSharpActualPrincipalSharedBranchDimension HironakaSharpOriginalSharedTraceBranchDimension
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalAllBoundaryCentre
  RelativePrincipalizationSpan RestrictedIdealExtension GermIdealOrder DivisorExponentAlong
  NormalCrossings AnalyticDimensionBasics MarkedIdeals MarkedIdeals.MarkedIdeal
variable {n m : ℕ} {X : CMfd.{u} n}

/-- Equality of ACTUAL full ideal germ predicates, retaining every position. -/
def actualIdealGermSetoid (F : Fin m → GermIdeal n X) (x : X) : Setoid (Fin m) where
  r i j := ∀ a,(F i).mem x a ↔ (F j).mem x a
  iseqv := ⟨fun _ _ => Iff.rfl,fun h a => (h a).symm,fun h h' a => (h a).trans (h' a)⟩

def actualProperPositions (F : Fin m → GermIdeal n X) (x : X) : Finset (Fin m) :=
  Finset.univ.filter fun i => ¬(F i).mem x (1 : X → ℂ)

def actualDistinctProperCount (F : Fin m → GermIdeal n X) (x : X) : ℕ :=
  ((actualProperPositions F x).image (Quotient.mk (actualIdealGermSetoid F x))).card

def actualFamilyDistinctDefect (N : Set X) (F : Fin m → GermIdeal n X) : Set X :=
  {x | x ∈ N ∧ actualDistinctProperCount F x < ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x}

def chronologicalDistinctDefect (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) : Set Y :=
  actualFamilyDistinctDefect (geoTransformAlong (geometricTemplate W []) T).N
    (fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal)

theorem actual_proper_iff_zeroLocus {F : Fin m → GermIdeal n X}
    (hc : ∀ i,(F i).IsCoherent) (i : Fin m) (x : X) :
    i ∈ actualProperPositions F x ↔ x ∈ (F i).zeroLocus := by
  simp only [actualProperPositions,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hnot
    by_contra hx
    apply hnot
    obtain ⟨b,hb,hbx⟩ : ∃ b,(F i).mem x b ∧ b x ≠ 0 := by
      by_contra hh
      push Not at hh
      exact hx hh
    have hbhol := RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem (hc i) hb
    refine HomogenizedIdeal.mem_of_isInSpanAt (hc i) (isInSpanAt_of_eq_mul hb
      (holomorphicAt_const 1) (RelativePrincipalizationSpan.holomorphicAt_inv hbhol hbx) ?_)
    filter_upwards [hbhol.continuousAt.eventually_ne hbx] with y hy
    show (1 : ℂ)=(b y)⁻¹*b y
    field_simp
  · intro hx hunit
    exact one_ne_zero (hx 1 hunit)

private theorem one_le_order_iff_proper {N : Set X} (hN : IsClosedSubmanifold n N)
    {F : Fin m → GermIdeal n X} (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y) {x : X} (hx : x ∈ N) (i : Fin m) :
    1 ≤ ordinaryTraceOrder N (F i) x ↔ i ∈ actualProperPositions F x := by
  rw [actual_proper_iff_zeroLocus hc i x]
  have hcos := cosupport_one (N := N) (fun _ _ ha => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem (hc i) ha)
  rw [← ordinaryTraceOrder_cosupport_iff hN (hc i) (hnz i) hx 1,hcos]
  simp only [mem_inter_iff,hx,true_and]

private theorem family_product_sum {N : Set X} (hN : IsClosedSubmanifold n N)
    {F : Fin m → GermIdeal n X} (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ a,(F i).mem y a ↔
      HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    {x : X} (hx : x ∈ N) :
    ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x=∑ i,ordinaryTraceOrder N (F i) x := by
  have hall : ∀ I ∈ List.ofFn F,I.IsCoherent ∧ (∀ y ∈ N,IsNonzeroAlongAt N I y) ∧
      ∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ a,I.mem y a ↔
        HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a := by
    intro I hI
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hI
    exact ⟨hc i,hnz i,hpr i⟩
  have hh := (relativeIdealListProduct_actual_geometry hN (List.ofFn F)
    (fun I hI => (hall I hI).1) (fun I hI => (hall I hI).2.1) (fun I hI => (hall I hI).2.2)).2.2.2 x hx
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using hh

/-- Actual sum/cardinality bounds retain TRUE quotient classes. -/
theorem actual_distinct_count_le_productOrder {N : Set X} (hN : IsClosedSubmanifold n N)
    {F : Fin m → GermIdeal n X} (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ a,(F i).mem y a ↔
      HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    {x : X} (hx : x ∈ N) : actualDistinctProperCount F x ≤
      ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x := by
  have hb : (actualProperPositions F x).card ≤ ∑ i,ordinaryTraceOrder N (F i) x := by
    have hcard : (actualProperPositions F x).card=∑ i : Fin m,if i ∈ actualProperPositions F x then 1 else 0 := by simp
    rw [hcard]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i ∈ actualProperPositions F x
    · simpa only [if_pos hi] using (one_le_order_iff_proper hN hc hnz hx i).mpr hi
    · simp only [if_neg hi]
      exact Nat.zero_le _
  exact Finset.card_image_le.trans (hb.trans_eq (family_product_sum hN hc hnz hpr hx).symm)

/-- Actual factor rigidity and true quotient injection characterize equality. -/
theorem actual_productOrder_eq_distinct_iff {N : Set X} (hN : IsClosedSubmanifold n N)
    {F : Fin m → GermIdeal n X} (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ a,(F i).mem y a ↔
      HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    {x : X} (hx : x ∈ N) :
    ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x=actualDistinctProperCount F x ↔
      (∀ i ∈ actualProperPositions F x,ordinaryTraceOrder N (F i) x=1) ∧
      Set.InjOn (Quotient.mk (actualIdealGermSetoid F x)) (actualProperPositions F x) := by
  let a : Fin m → ℕ := fun i => ordinaryTraceOrder N (F i) x
  let b : Fin m → ℕ := fun i => if i ∈ actualProperPositions F x then 1 else 0
  have hsuma := family_product_sum hN hc hnz hpr hx
  have hsumb : (actualProperPositions F x).card=∑ i,b i := by simp [b]
  have hb_le : ∀ i,b i ≤ a i := by
    intro i
    by_cases hi : i ∈ actualProperPositions F x
    · exact (if_pos hi).trans_le ((one_le_order_iff_proper hN hc hnz hx i).mpr hi)
    · exact (if_neg hi).trans_le (Nat.zero_le _)
  have hbcard : (actualProperPositions F x).card ≤ ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x := by
    rw [hsumb,hsuma]
    exact Finset.sum_le_sum fun i _ => hb_le i
  have hclass : actualDistinctProperCount F x ≤ (actualProperPositions F x).card := Finset.card_image_le
  constructor
  · intro heq
    have hcount : (actualProperPositions F x).card=ordinaryTraceOrder N (relativeIdealListProduct N (List.ofFn F)) x :=
      hbcard.antisymm (heq ▸ hclass)
    have hfactor := factor_eq_of_sum_eq hb_le (hsumb.symm.trans (hcount.trans hsuma))
    refine ⟨?_,Finset.card_image_iff.mp (heq.symm.trans hcount.symm)⟩
    intro i hi
    have hh := hfactor i
    change (if i ∈ actualProperPositions F x then 1 else 0)=a i at hh
    rw [if_pos hi] at hh
    exact hh.symm
  · rintro ⟨hfactor,hinj⟩
    have hsum : (∑ i,a i)=∑ i,b i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ actualProperPositions F x
      · change ordinaryTraceOrder N (F i) x=(if i ∈ actualProperPositions F x then 1 else 0)
        rw [if_pos hi]
        exact hfactor i hi
      · have hh : ¬1 ≤ ordinaryTraceOrder N (F i) x := fun h => hi ((one_le_order_iff_proper hN hc hnz hx i).mp h)
        have hz : a i=0 := by change ordinaryTraceOrder N (F i) x=0; omega
        simpa only [b,if_neg hi] using hz
    exact hsuma.trans (hsum.trans (hsumb.symm.trans (Finset.card_image_of_injOn hinj).symm))

/-- The actual collision, not an indexed-count replacement, recognizes FIRST Z. -/
theorem actual_distinct_defect_iff_witness {N : Set X} (hN : IsClosedSubmanifold n N)
    {F : Fin m → GermIdeal n X} (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ a,(F i).mem y a ↔
      HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    {x : X} (hx : x ∈ N) : x ∈ actualFamilyDistinctDefect N F ↔
      (∃ i,2 ≤ ordinaryTraceOrder N (F i) x) ∨
      ∃ i j,i ≠ j ∧ i ∈ actualProperPositions F x ∧ j ∈ actualProperPositions F x ∧
        (actualIdealGermSetoid F x).r i j := by
  have hb := actual_distinct_count_le_productOrder hN hc hnz hpr hx
  have heq := actual_productOrder_eq_distinct_iff hN hc hnz hpr hx
  constructor
  · intro hz
    by_cases hhigh : ∃ i,2 ≤ ordinaryTraceOrder N (F i) x
    · exact Or.inl hhigh
    · right
      have hf : ∀ i ∈ actualProperPositions F x,ordinaryTraceOrder N (F i) x=1 := by
        intro i hi
        have hp := (one_le_order_iff_proper hN hc hnz hx i).mpr hi
        have hh : ¬2 ≤ ordinaryTraceOrder N (F i) x := fun h => hhigh ⟨i,h⟩
        omega
      by_contra hcollision
      have hinj : Set.InjOn (Quotient.mk (actualIdealGermSetoid F x)) (actualProperPositions F x) := by
        intro i hi j hj hij
        by_contra hne
        exact hcollision ⟨i,j,hne,hi,hj,Quotient.exact hij⟩
      exact (ne_of_gt hz.2) (heq.mpr ⟨hf,hinj⟩)
  · intro hw
    refine ⟨hx,lt_of_le_of_ne hb ?_⟩
    intro he
    obtain ⟨hf,hinj⟩ := heq.mp he.symm
    rcases hw with ⟨i,hi⟩ | ⟨i,j,hne,hpi,hpj,hrel⟩
    · have hpi := (one_le_order_iff_proper hN hc hnz hx i).mp (by omega)
      have hh := hf i hpi
      omega
    · exact hne (hinj hpi hpj (Quotient.sound hrel))

def actualHighOrderLocus (N : Set X) (F : Fin m → GermIdeal n X) : Set X :=
  ⋃ i,cosupport n N (F i) 2

def actualSharedDimensionLocus (N : Set X) (F : Fin m → GermIdeal n X) (d : ℕ) : Set X :=
  ⋃ i,⋃ j,if i=j then ∅ else {x | LocDimGE (n := n) (N ∩ (F i).zeroLocus ∩ (F j).zeroLocus) x d}

private theorem pair_analytic {N : Set X} (hN : IsClosedSubmanifold n N)
    {F : Fin m → GermIdeal n X} (hc : ∀ i,(F i).IsCoherent) (i j : Fin m) :
    IsComplexAnalyticSubset (n := n) (N ∩ (F i).zeroLocus ∩ (F j).zeroLocus) :=
  ((AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hN).inter
    (CodimOneSupport.isComplexAnalyticSubset_zeroLocus (hc i))).inter
    (CodimOneSupport.isComplexAnalyticSubset_zeroLocus (hc j))

/-- BOTH actual finite geometric directions, including every outside/unit case. -/
theorem actual_distinct_defect_eq_finite_geometric_loci {N : Set X} (hN : IsClosedSubmanifold n N)
    {F : Fin m → GermIdeal n X} (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ a,(F i).mem y a ↔
      HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    (d : ℕ) (hreg : ∀ x ∈ N,RegularAtDim (n := n) N x (d+1)) :
    actualFamilyDistinctDefect N F=actualHighOrderLocus N F ∪ actualSharedDimensionLocus N F d := by
  have hhigh (x : X) : x ∈ actualHighOrderLocus N F ↔ ∃ i,x ∈ cosupport n N (F i) 2 := by
    simp only [actualHighOrderLocus,mem_iUnion]
  have hpair (x : X) : x ∈ actualSharedDimensionLocus N F d ↔
      ∃ i j,i ≠ j ∧ LocDimGE (n := n) (N ∩ (F i).zeroLocus ∩ (F j).zeroLocus) x d := by
    simp only [actualSharedDimensionLocus,mem_iUnion]
    constructor
    · rintro ⟨i,j,hx⟩
      by_cases hij : i=j
      · simp [hij] at hx
      · exact ⟨i,j,hij,by simpa only [if_neg hij,mem_ofPred_eq] using hx⟩
    · rintro ⟨i,j,hij,hdim⟩
      exact ⟨i,j,by simpa only [if_neg hij,mem_ofPred_eq] using hdim⟩
  have horder (x : X) (hx : x ∈ N) (hno : ¬∃ i,2 ≤ ordinaryTraceOrder N (F i) x)
      (i : Fin m) (hi : i ∈ actualProperPositions F x) : ordinaryTraceOrder N (F i) x=1 := by
    have hp := (one_le_order_iff_proper hN hc hnz hx i).mpr hi
    have hh : ¬2 ≤ ordinaryTraceOrder N (F i) x := fun h => hno ⟨i,h⟩
    omega
  ext x
  constructor
  · intro hz
    rcases (actual_distinct_defect_iff_witness hN hc hnz hpr hz.1).mp hz with hhi | ⟨i,j,hij,hpi,hpj,hrel⟩
    · obtain ⟨i,hi⟩ := hhi
      exact Or.inl ((hhigh x).mpr ⟨i,(ordinaryTraceOrder_cosupport_iff hN (hc i) (hnz i) hz.1 2).mpr hi⟩)
    · by_cases hhi : ∃ a,2 ≤ ordinaryTraceOrder N (F a) x
      · obtain ⟨a,ha⟩ := hhi
        exact Or.inl ((hhigh x).mpr ⟨a,(ordinaryTraceOrder_cosupport_iff hN (hc a) (hnz a) hz.1 2).mpr ha⟩)
      · obtain ⟨f,hf,hfi⟩ := hpr i x hz.1
        exact Or.inr ((hpair x).mpr ⟨i,j,hij,actual_orderOne_pair_locDimGE_of_germ_eq hN (hc i) (hc j)
          (hnz i) hz.1 (hreg x hz.1) f hf hfi (horder x hz.1 hhi i hpi) hrel⟩)
  · rintro (hhi | hp)
    · obtain ⟨i,hi⟩ := (hhigh x).mp hhi
      exact (actual_distinct_defect_iff_witness hN hc hnz hpr hi.1).mpr
        (Or.inl ⟨i,(ordinaryTraceOrder_cosupport_iff hN (hc i) (hnz i) hi.1 2).mp hi⟩)
    · obtain ⟨i,j,hij,hdim⟩ := (hpair x).mp hp
      have hxA := CodimOneSupport.mem_of_locDimGE (pair_analytic hN hc i j).isClosed hdim
      have hxN := hxA.1.1
      apply (actual_distinct_defect_iff_witness hN hc hnz hpr hxN).mpr
      by_cases hhi : ∃ a,2 ≤ ordinaryTraceOrder N (F a) x
      · exact Or.inl hhi
      · have hpi := (actual_proper_iff_zeroLocus hc i x).mpr hxA.1.2
        have hpj := (actual_proper_iff_zeroLocus hc j x).mpr hxA.2
        obtain ⟨f,hf,hfi⟩ := hpr i x hxN
        obtain ⟨g,hg,hgj⟩ := hpr j x hxN
        exact Or.inr ⟨i,j,hij,hpi,hpj,actual_orderOne_germ_eq_of_pair_locDimGE hN (hc i) (hc j)
          (hnz i) (hnz j) hxN (hreg x hxN) f g hf hg hfi hgj
          (horder x hxN hhi i hpi) (horder x hxN hhi j hpj) hdim⟩

private theorem analytic_finset_union {ι : Type*} (t : Finset ι) (A : ι → Set X)
    (hA : ∀ i ∈ t,IsComplexAnalyticSubset (n := n) (A i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i ∈ t,A i) := by
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih =>
    rw [Finset.set_biUnion_insert]
    exact HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
      (hA i (Finset.mem_insert_self i t)) (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

private theorem analytic_finite_union {ι : Type*} [Fintype ι] (A : ι → Set X)
    (hA : ∀ i,IsComplexAnalyticSubset (n := n) (A i)) :
    IsComplexAnalyticSubset (n := n) (⋃ i,A i) := by
  simpa only [Finset.mem_univ,iUnion_true] using analytic_finset_union Finset.univ A (fun i _ => hA i)

/-- GENUINE whole analytic producer for the literal actual-family FIRST defect. -/
theorem isComplexAnalyticSubset_actualFamilyDistinctDefect {N : Set X} (hN : IsClosedSubmanifold n N)
    {F : Fin m → GermIdeal n X} (hc : ∀ i,(F i).IsCoherent)
    (hnz : ∀ i,∀ y ∈ N,IsNonzeroAlongAt N (F i) y)
    (hpr : ∀ i,∀ y ∈ N,∃ f : X → ℂ,HolomorphicAt n f y ∧ ∀ a,(F i).mem y a ↔
      HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) N (·=f) y a)
    (d : ℕ) (hreg : ∀ x ∈ N,RegularAtDim (n := n) N x (d+1)) :
    IsComplexAnalyticSubset (n := n) (actualFamilyDistinctDefect N F) := by
  rw [actual_distinct_defect_eq_finite_geometric_loci hN hc hnz hpr d hreg]
  apply HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union
  · apply analytic_finite_union
    intro i
    exact CodimOneSupportAlong.isComplexAnalyticSubset_cosupport_along (hc i) hN (by omega)
  · apply analytic_finite_union
    intro i
    apply analytic_finite_union
    intro j
    by_cases hij : i=j
    · simp only [if_pos hij]
      exact isComplexAnalyticSubset_empty
    · simp only [if_neg hij]
      exact isComplexAnalyticSubset_locDimGE (pair_analytic hN hc i j) d

private theorem template_regularAtDim {W : Set X} (hW : IsClosedSubmanifold n W) (d : ℕ)
    (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x d) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),IsGeoTestTower (geometricTemplate W []) T →
      ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
        RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N y d
  | _, .refl, _, _, hy => hreg _ hy
  | _, .step T C π hπ, ht, y, hy => by
    have hw : (geometricTemplate W []).IsWellFormed :=
      ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
    have hwT := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T ht.1
    exact BlowupStrictSubmanifold.regularAtDim_geoStrictTransform hπ hwT.isClosedSubmanifold_N.1
      (template_regularAtDim hW d hreg T ht.1) ht.2.subset_N hy

/-- Genuine chronological finite ordered product is exactly the real ofFn product. -/
theorem chronological_product_eq_actual_family_product (W : Set X) (E : List (Set X))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) :
    chronologicalMemberProduct W E T=relativeIdealListProduct (geoTransformAlong (geometricTemplate W []) T).N
      (List.ofFn fun i : Fin E.length => (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal) := by
  unfold chronologicalMemberProduct chronologicalMemberFamily
  congr 1
  conv_lhs => rw [← List.ofFn_get E,List.map_ofFn]
  rfl

/-- ONLY original pure-carrier/SNC/density and ACTUAL history construct the
whole dynamic FIRST Z analytic; no branch/count/analytic certificate is input. -/
theorem original_chronological_distinct_defect_analytic (hn : 0 < n)
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E,H)) (d : ℕ)
    (hreg : ∀ x ∈ W,RegularAtDim (n := n) W x (d+1))
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T) :
    IsComplexAnalyticSubset (n := n) (chronologicalDistinctDefect W E T) := by
  have hw : (geometricTemplate W []).IsWellFormed :=
    ⟨hW,IdealWeightPowers.isCoherent_unitIdeal,isSNCDivisor_nil,isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hN := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T hT).isClosedSubmanifold_N
  have hfam : ∀ i : Fin E.length,
      let I := (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal
      I.IsCoherent ∧ (∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,
        IsNonzeroAlongAt (geoTransformAlong (geometricTemplate W []) T).N I y) ∧
      ∀ y ∈ (geoTransformAlong (geometricTemplate W []) T).N,∃ f : Y → ℂ,HolomorphicAt n f y ∧
        ∀ a,I.mem y a ↔ HolomorphicAt n a y ∧ IsInSpanOnAt (n := n) (geoTransformAlong (geometricTemplate W []) T).N (·=f) y a := by
    intro i
    obtain ⟨hNi,_hEi,_hmi,hwi,hnzi,hpri⟩ := original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
    rw [hNi] at hnzi hpri
    exact ⟨hwi.isCoherent,hnzi,hpri⟩
  exact isComplexAnalyticSubset_actualFamilyDistinctDefect hN (fun i => (hfam i).1)
    (fun i => (hfam i).2.1) (fun i => (hfam i).2.2) d (template_regularAtDim hW (d+1) hreg T hT)

end
end Hironaka.HironakaSharpActualChronologicalDistinctDefect
