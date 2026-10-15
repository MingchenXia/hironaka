/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSharpNormalCrossingsOpenLocus
import Hironaka.Invariant.MemberTraceIdealAlong

/-! The literal true original multiboundary sharp defect: actual openness,
closedness/compactness and support, without analytic or modified-driver claims.
Complete mathematical blueprint precedes this isolated implementation. -/
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold

namespace Hironaka.HironakaSharpOriginalMultiBoundaryBadLocus

open Hironaka.BlowupSequences NormalCrossings
  HironakaSharpNormalCrossingsOpenLocus NormalCrossingsInvariance
  HironakaNormalCrossingsTransversality Hironaka.HolomorphicIdealSheaves
  MemberTraceIdealAlong BlowupFlatCoordinates MonomialPart MonomialPartAlong GiraudAlong

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- The actual original good set for the WHOLE original boundary list. -/
def originalGoodLocus (W : Set M) (E : List (Set M)) : Set M :=
  Wᶜ ∪ {x | x ∈ W ∧ normalCrossingsAt (n := n) W E x}

def originalSharpBadLocus (W : Set M) (E : List (Set M)) : Set M :=
  {x | x ∈ W ∧ ¬normalCrossingsAt (n := n) W E x}

theorem isOpen_originalPointwiseNCSet {W : Set M} {E : List (Set M)}
    (hW : IsClosed W) (hE : ∀ H ∈ E, IsClosed H) :
    IsOpen {x | normalCrossingsAt (n := n) W E x} := by
  rw [isOpen_iff_mem_nhds]
  exact fun _ hx => eventually_normalCrossingsAt hW hE hx

omit [IsComplexManifold n M] in
theorem originalGoodLocus_eq_union {W : Set M} {E : List (Set M)} :
    originalGoodLocus (n := n) W E = Wᶜ ∪ {x | normalCrossingsAt (n := n) W E x} := by
  ext x
  simp only [originalGoodLocus,mem_union,mem_compl_iff,mem_ofPred_eq]
  tauto

theorem isOpen_originalGoodLocus {W : Set M} {E : List (Set M)}
    (hW : IsClosed W) (hE : ∀ H ∈ E, IsClosed H) :
    IsOpen (originalGoodLocus (n := n) W E) := by
  rw [originalGoodLocus_eq_union]
  exact hW.isOpen_compl.union (isOpen_originalPointwiseNCSet hW hE)

omit [IsComplexManifold n M] in
theorem originalSharpBadLocus_eq_compl_good {W : Set M} {E : List (Set M)} :
    originalSharpBadLocus (n := n) W E = (originalGoodLocus (n := n) W E)ᶜ := by
  ext x
  simp only [originalGoodLocus,originalSharpBadLocus,mem_union,mem_compl_iff,mem_ofPred_eq]
  tauto

theorem isClosed_originalSharpBadLocus {W : Set M} {E : List (Set M)}
    (hW : IsClosed W) (hE : ∀ H ∈ E, IsClosed H) :
    IsClosed (originalSharpBadLocus (n := n) W E) := by
  rw [originalSharpBadLocus_eq_compl_good]
  exact (isOpen_originalGoodLocus hW hE).isClosed_compl

theorem isCompact_originalSharpBadLocus {W : Set M} {E : List (Set M)}
    (hW : IsClosed W) (hE : ∀ H ∈ E, IsClosed H) (hK : IsCompact W) :
    IsCompact (originalSharpBadLocus (n := n) W E) :=
  hK.of_isClosed_subset (isClosed_originalSharpBadLocus hW hE) fun _ hx => hx.1

theorem originalSharpBadLocus_subset_boundary {W : Set M} {E : List (Set M)}
    (hW : IsClosedSubmanifold n W) :
    originalSharpBadLocus (n := n) W E ⊆ W ∩ ⋃ H ∈ E, H := by
  intro x hx
  refine ⟨hx.1,?_⟩
  by_contra hout
  apply hx.2
  obtain ⟨S₀,S,⟨Φ,hsrc,h0,hflat⟩,_⟩ := hasNormalCrossings_nil_of_isClosedSubmanifold hW x hx.1
  refine ⟨S₀,fun _ => ∅,⟨Φ,hsrc,h0,?_⟩,?_⟩
  · intro o ho
    cases o with
    | none => exact hflat none ho
    | some i => exact False.elim (hout (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,ho⟩))
  · intro i hi
    exact False.elim (hout (mem_iUnion₂.mpr ⟨E.get i,List.get_mem E i,hi⟩))

theorem exists_actual_original_transverse_neighborhood {W : Set M} {E : List (Set M)}
    (hW : IsClosed W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {x : M}
    (hx : normalCrossingsAt (n := n) W E x) :
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧
      IsSNCDivisor n (E.map ((Subtype.val : U → M) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → M) ⁻¹' W) (E.map ((Subtype.val : U → M) ⁻¹' ·)) := by
  classical
  let U : TopologicalSpace.Opens M := ⟨{y | normalCrossingsAt (n := n) W E y},
    isOpen_originalPointwiseNCSet hW hE.1⟩
  have hNC : HasNormalCrossings n ((Subtype.val : U → M) ⁻¹' W)
      (E.map ((Subtype.val : U → M) ⁻¹' ·)) := by
    intro y _
    obtain ⟨S₀,S,hfamily,hcard⟩ := y.property
    let c : Fin (E.map ((Subtype.val : U → M) ⁻¹' ·)).length → Fin E.length :=
      Fin.cast (List.length_map _)
    refine ⟨S₀,fun i => S (c i),
      IsCoordinateFamilyAt.reindex ((pullsBackCoordinates_val U) _ _ y hfamily)
        (Option.map c) ?_ ?_,?_⟩
    · rintro (_ | i)
      · rfl
      · exact get_map_preimage E i
    · rintro (_ | i) <;> rfl
    · intro i hi
      rw [get_map_preimage] at hi
      exact hcard (c i) hi
  have hdU : (Subtype.val : U → M) ⁻¹' W ⊆
      closure ((Subtype.val : U → M) ⁻¹' W \ ⋃ H ∈ E.map ((Subtype.val : U → M) ⁻¹' ·), H) := by
    intro y hy
    have hp : y ∈ (Subtype.val : U → M) ⁻¹' closure (W \ ⋃ H ∈ E, H) := hdense hy
    erw [(U.isOpen.isOpenMap_subtype_val).preimage_closure_eq_closure_preimage
      continuous_subtype_val (W \ ⋃ H ∈ E, H)] at hp
    convert hp using 1
    congr 1
    ext z
    simp
  exact ⟨U,hx,isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE,
    isTransverse_of_hasNormalCrossings_of_subset_closure_diff hNC hdU⟩

/-- Literal whole restricted holomorphic germ-ideal membership. -/
def traceSpan (W H : Set M) (x : M) (g : M → ℂ) : Prop :=
  IsInSpanOnAt (n := n) W ((vanishingIdeal (n := n) H).mem x) x g

omit [IsComplexManifold n M] in
theorem traceSpan_unit_iff_notMem {W H : Set M} (hH : IsClosed H) {x : M} (hx : x ∈ W) :
    traceSpan (n := n) W H x (fun _ => 1) ↔ x ∉ H := by
  constructor
  · rintro ⟨N,s,a,hs,_ha,hsum⟩ hxH
    have heq := hsum.self_of_nhds hx
    have hs0 : ∀ i, s i x = 0 := fun i => (hs i).2.self_of_nhds hxH
    have : (1 : ℂ) = 0 := by
      simpa only [hs0,mul_zero,Finset.sum_const_zero] using heq
    exact one_ne_zero this
  · intro hxH
    have hunit : (vanishingIdeal (n := n) H).mem x (fun _ => 1) :=
      ⟨holomorphicAt_const 1,Filter.Eventually.mono (hH.isOpen_compl.mem_nhds hxH) fun _ hy hyH =>
        False.elim (hy hyH)⟩
    exact ⟨1,fun _ => (fun _ => 1),fun _ => (fun _ => 1),fun _ => hunit,
      fun _ => holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩

/-- A real original free member coordinate separates the TWO whole trace germ ideals. -/
theorem exists_traceSpan_separator (hn : 0 < n) {W : Set M} {E : List (Set M)}
    (hE : IsSNCDivisor n E) (hT : IsTransverse n W E) {x : M} (hx : x ∈ W)
    (i j : Fin E.length) (hi : x ∈ E.get i) (hj : x ∈ E.get j) (hij : i ≠ j) :
    ∃ g : M → ℂ, HolomorphicAt n g x ∧ traceSpan (n := n) W (E.get i) x g ∧
      ¬traceSpan (n := n) W (E.get j) x g := by
  obtain ⟨kC,kW,Φ,σ,hΦsrc,hσk,hσinj,hflat⟩ :=
    SimultaneousNormalCrossings.isAdaptedAt_of_hasNormalCrossings hn subset_rfl hE hT
      hT.hasNormalCrossings hx
  have hxD : x ∈ flatDomain Φ := mem_flatDomain_self Φ
  have hWflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ W ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ complexCoordinatePlane n kW) :=
    fun hy1 hy2 => (hflat hy1 hy2).2.1
  have hA : ∀ a, x ∈ E.get a → ∀ {y : M}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
      (y ∈ E.get a ↔ Φ.toFun (chartAt (ComplexModel n) x y) (σ a) = 0) :=
    fun a ha _ hy1 hy2 => (hflat hy1 hy2).2.2 a ha
  have hg : HolomorphicAt n (flatCoord Φ (σ i)) x := holomorphicAt_flatCoord Φ (σ i) hxD
  have hmem : (vanishingIdeal (n := n) (E.get i)).mem x (flatCoord Φ (σ i)) := by
    refine ⟨hg,?_⟩
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hxD] with y hy hyi
    exact (hA i hi hy.1 hy.2).mp hyi
  refine ⟨flatCoord Φ (σ i),hg,?_,?_⟩
  · exact ⟨1,fun _ => flatCoord Φ (σ i),fun _ => (fun _ => 1),fun _ => hmem,
      fun _ => holomorphicAt_const 1,Eventually.of_forall fun _ _ => by simp⟩
  · intro hspan
    have hvan := (isInSpanOnAt_vanishingIdeal_iff_mem hE hT hx j hg).mp hspan
    obtain ⟨z,⟨hzD,hzne,hzeq⟩,hzvan⟩ :=
      ((frequently_flatMap_ne_zero hΦsrc hxD {σ i}).and_eventually hvan.2).exists
    have hzW : z ∈ W := by
      apply (hWflat hzD.1 hzD.2).mpr
      intro l hl
      have hli : l ∉ ({σ i} : Finset (Fin n)) := by
        simp only [Finset.mem_singleton]
        intro heq
        have hfree := hσk i hi
        subst l
        omega
      change flatMap Φ z l = 0
      rw [hzeq l hli]
      exact (hWflat hxD.1 hxD.2).mp hx l hl
    have hjne : σ j ∉ ({σ i} : Finset (Fin n)) := by
      simp only [Finset.mem_singleton]
      intro heq
      exact hij (hσinj hi hj heq.symm)
    have hzj : z ∈ E.get j := by
      apply (hA j hj hzD.1 hzD.2).mpr
      change flatMap Φ z (σ j) = 0
      rw [hzeq (σ j) hjne]
      exact (hA j hj hxD.1 hxD.2).mp hj
    exact hzne (σ i) (Finset.mem_singleton_self _) (hzvan ⟨hzW,hzj⟩)

/-- Equality of the whole actual restricted holomorphic germ-ideal predicates. -/
def traceGermSetoid (W : Set M) (E : List (Set M)) (x : M) : Setoid (Fin E.length) where
  r i j := ∀ g, HolomorphicAt n g x →
    (traceSpan (n := n) W (E.get i) x g ↔ traceSpan (n := n) W (E.get j) x g)
  iseqv := ⟨fun _ _ _ => Iff.rfl,fun h g hg => (h g hg).symm,
    fun h₁ h₂ g hg => (h₁ g hg).trans (h₂ g hg)⟩

def properTraceMembers (W : Set M) (E : List (Set M)) (x : M) : Finset (Fin E.length) := by
  classical
  exact Finset.univ.filter fun i => ¬traceSpan (n := n) W (E.get i) x (fun _ => 1)

/-- Counts ACTUAL quotient classes of proper trace germ ideals, including at bad points. -/
def distinctProperTraceGermCount (W : Set M) (E : List (Set M)) (x : M) : ℕ := by
  classical
  exact ((properTraceMembers (n := n) W E x).image
    (Quotient.mk (traceGermSetoid (n := n) W E x))).card

theorem distinctProperTraceGermCount_eq_boundaryCount (hn : 0 < n)
    {W : Set M} {E : List (Set M)} (hE : IsSNCDivisor n E)
    (hT : IsTransverse n W E) {x : M} (hx : x ∈ W) :
    distinctProperTraceGermCount (n := n) W E x = BoundaryCount.boundaryCount E x := by
  classical
  have hproper : properTraceMembers (n := n) W E x = Finset.univ.filter fun i => x ∈ E.get i := by
    ext i
    simp only [properTraceMembers,Finset.mem_filter,Finset.mem_univ,true_and,
      traceSpan_unit_iff_notMem (hE.1 _ (List.get_mem E i)) hx,not_not]
  unfold distinctProperTraceGermCount
  rw [hproper,Finset.card_image_of_injOn]
  · rfl
  · intro i hi j hj heq
    by_contra hij
    obtain ⟨g,hg,hgi,hgj⟩ := exists_traceSpan_separator hn hE hT hx i j
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hij
    exact hgj ((Quotient.exact heq) g hg |>.mp hgi)

theorem exists_actual_original_distinct_trace_neighborhood (hn : 0 < n)
    {W : Set M} {E : List (Set M)} (hW : IsClosed W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) {x : M}
    (hx : normalCrossingsAt (n := n) W E x) :
    ∃ U : TopologicalSpace.Opens M, x ∈ U ∧
      IsSNCDivisor n (E.map ((Subtype.val : U → M) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U → M) ⁻¹' W) (E.map ((Subtype.val : U → M) ⁻¹' ·)) ∧
      ∀ p : U, p ∈ (Subtype.val : U → M) ⁻¹' W →
        distinctProperTraceGermCount (n := n) ((Subtype.val : U → M) ⁻¹' W)
          (E.map ((Subtype.val : U → M) ⁻¹' ·)) p =
          BoundaryCount.boundaryCount (E.map ((Subtype.val : U → M) ⁻¹' ·)) p := by
  obtain ⟨U,hxU,hEU,hTU⟩ := exists_actual_original_transverse_neighborhood hW hE hdense hx
  exact ⟨U,hxU,hEU,hTU,fun _ hp => distinctProperTraceGermCount_eq_boundaryCount hn hEU hTU hp⟩

end
end Hironaka.HironakaSharpOriginalMultiBoundaryBadLocus
