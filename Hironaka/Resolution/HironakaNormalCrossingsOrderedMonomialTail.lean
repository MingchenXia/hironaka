/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MonomialGammaAlongUnivExact
import Hironaka.Invariant.MonomialAmbientDataExact
import Hironaka.Resolution.HironakaNormalCrossingsFiniteMarkedCompletion
import Hironaka.Invariant.MonomialResolution
import Hironaka.Invariant.MonomialStepAlong

/-!
# Actual noncompact ordered marking-one monomial completion

The whole ideal and every intrinsic through-member exponent are produced from the
actual finite SNC indexed boundary. Its unchanged old gamma internally gives a
unique singleton maximum centre. Actual Cartier control and the true coefficient
sum produce a finite canonical monomial segment, including in dimension zero.
The original consumer uses the SAME original NC ideal and actual separating tower.
All empty and repeated literal entries remain. Identifying the preceding general
separation with the old general driver, and unrelated marked ideals, remain open.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaNormalCrossingsOrderedMonomialTail
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaNormalCrossingsFiniteMarkedCompletion HironakaNormalCrossingsOriginalExponents
  HironakaNormalCrossingsBoundaryTransform HironakaNormalCrossingsTotalIdeal
  HironakaNormalCrossingsMarkedAdmissibility HironakaNormalCrossingsLocalBranches BlowupFlatCoordinates BlowupStrictSubmanifold
  NormalCrossings BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal IdealWeightPowers
  DivisorExponent HironakaDivisorResidual MonomialInvariant MonomialCase
noncomputable section
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

omit [IsComplexManifold n M] in
/-- Actual whole vanishing ideal of the empty carrier is unit, at EVERY stalk. -/
theorem vanishingIdeal_empty_eq_unit : vanishingIdeal (n := n) (∅ : Set M) = unitIdeal n M := by
  refine GermIdeal.ext (funext fun x => funext fun f => propext ⟨fun hf => hf.1,fun hf => ?_⟩)
  exact ⟨hf,Eventually.of_forall fun _ hx => hx.elim⟩

omit [IsComplexManifold n M] in
/-- The true SAME SNC chart is an actual adapted empty-original pair. -/
theorem boundaryAdapted_empty_of_snc {E : List (Set M)} (hE : IsSNCDivisor n E) :
    IsBoundaryAdaptedCarrier (n := n) (∅ : Set M) E := by
  refine ⟨isClosed_empty,hE.1,fun x => ?_⟩
  obtain ⟨B,⟨Φ,hsrc,h0,hflat⟩,hcard,hinj⟩ := hE.2 x
  refine ⟨Φ,∅,B,hsrc,h0,?_,fun i hi => ⟨hcard i hi,Finset.disjoint_empty_left _⟩,hinj,?_⟩
  · intro y _
    simp
  · intro i hi y hy
    exact hflat i hi hy.1 hy.2

omit [TopologicalSpace M] in
private theorem present_indexed_pool (F : List (Set M × ℕ)) :
    ∀ p ∈ F, p.1 ∈ F.map Prod.fst := fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩

private theorem indexed_member_invertible (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∀ p ∈ F, (vanishingIdeal (n := n) p.1).IsInvertible := by
  intro p hp
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp (present_indexed_pool F p hp)
  exact hi ▸ isInvertible_vanishingIdeal_snc_member hF i

open Classical in
/-- True ordinary SNC product internally produces its COMPLETE centred indexed monomial generator. -/
theorem exists_whole_indexed_product_chart (hn : 0 < n) (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (x : M) :
    ∃ (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
      (σ : Fin F.length → Fin n),
      Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
      Φ.toFun (chartAt (ComplexModel n) x x) = 0 ∧
      Set.InjOn σ {i | x ∈ (F.get i).1} ∧
      (∀ i, x ∈ (F.get i).1 → ∀ y ∈ flatDomain Φ,
        y ∈ (F.get i).1 ↔ flatCoord Φ (σ i) y = 0) ∧
      ∀ᶠ y in 𝓝 x, ∀ g, (componentPowerProduct (n := n) F).mem y g ↔
        IsInSpanAt (n := n) (· = fun z => ∏ i ∈ Finset.univ.filter (fun i => x ∈ (F.get i).1),
          flatCoord Φ (σ i) z ^ (F.get i).2) y g := by
  classical
  obtain ⟨Φ,S,σ,hsrc,h0,hH,hinj,_,hflat,hgen⟩ := exists_joint_whole_weighted_generator hn F
    (boundaryAdapted_empty_of_snc hF) x
  have hS : S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hh : x ∈ (∅ : Set M) := (hH x (mem_flatDomain_self Φ)).mpr ⟨j,hj,?_⟩
    · exact hh.elim
    · change Φ.toFun (chartAt (ComplexModel n) x x) j = 0
      rw [h0]
      rfl
  have hc : (componentPowerProduct (n := n) F).IsCoherent :=
    (isWellFormed_monomialMarkedIdeal hF F (present_indexed_pool F)).isCoherent
  rw [vanishingIdeal_empty_eq_unit,RestrictLeCalculus.mul_unitIdeal hc,hS] at hgen
  refine ⟨Φ,σ,hsrc,h0,hinj,hflat,?_⟩
  simpa only [Finset.prod_empty,one_mul] using hgen

/-- Intrinsic exponents at every TRUE through member are produced from the SAME whole indexed ideal. -/
theorem indexed_product_divExp (hn : 0 < n) (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (x : M) (i : Fin F.length)
    (hx : x ∈ (F.get i).1) :
    divExp n (componentPowerProduct (n := n) F) (F.get i).1 x = (F.get i).2 := by
  obtain ⟨_,_,_,_,_,_,hd,_⟩ := exists_joint_whole_weighted_exponents hn F
    (boundaryAdapted_empty_of_snc hF) (indexed_member_invertible F hF) x
  have hc : (componentPowerProduct (n := n) F).IsCoherent :=
    (isWellFormed_monomialMarkedIdeal hF F (present_indexed_pool F)).isCoherent
  rw [vanishingIdeal_empty_eq_unit,RestrictLeCalculus.mul_unitIdeal hc] at hd
  exact hd i hx

/-- Actual finite indexed powers extended by zero beyond the true carrier-list length. -/
def indexedPowerData (F : List (Set M × ℕ)) (i : ℕ) : ℕ :=
  if h : i < F.length then (F.get ⟨i,h⟩).2 else 0

/-- The UNCHANGED actual intrinsic gamma reads the internally generated whole indexed powers. -/
theorem gamma_indexed_product_eq (hn : 0 < n) (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (x : M) (d : ℕ) :
    gamma n (componentPowerProduct (n := n) F) (F.map Prod.fst) d x =
      inv n (memberIdx (F.map Prod.fst) x) (indexedPowerData F) d := by
  unfold gamma
  apply inv_congr
  intro a ha
  obtain ⟨hlt,hx⟩ := (mem_memberIdx (F.map Prod.fst)).mp ha
  have hl : a < F.length := by simpa only [List.length_map] using hlt
  simp only [expData,indexedPowerData,dif_pos hlt,dif_pos hl,List.get_eq_getElem,List.getElem_map]
  exact indexed_product_divExp hn F hF x ⟨a,hl⟩ (by
    simpa only [List.get_eq_getElem,List.getElem_map] using hx)


/-- The UNCHANGED old top set at marking one is internally a true positive singleton. -/
theorem exists_singleton_top_mark_one {S : Finset ℕ} {a : ℕ → ℕ}
    (hn : S.card ≤ n) (h : 1 ≤ ∑ i ∈ S, a i) :
    ∃ j ∈ S, 1 ≤ a j ∧ inv n S a 1 = key n a {j} ∧
      ∀ K ∈ feasible S a 1, key n a K ≤ key n a {j} := by
  classical
  obtain ⟨I,hi,hv,ht⟩ := exists_top (n := n) h
  have hd := (mem_feasible.mp hi).2
  have hp : ∃ j ∈ I, 0 < a j := by
    by_contra hb
    push Not at hb
    have hz : ∑ j ∈ I, a j = 0 := Finset.sum_eq_zero (fun j hj => Nat.eq_zero_of_le_zero (hb j hj))
    omega
  obtain ⟨j,hj,haj⟩ := hp
  have hs : {j} ∈ feasible S a 1 := mem_feasible.mpr
    ⟨Finset.singleton_subset_iff.mpr ((mem_feasible.mp hi).1 hj),by simpa using (Nat.succ_le_of_lt haj)⟩
  have hcard : I.card = 1 := by
    have hu := card_le_of_top hn hi ht hs
    simp only [Finset.card_singleton] at hu
    exact Nat.le_antisymm hu (Finset.one_le_card.mpr ⟨j,hj⟩)
  obtain ⟨k,hk⟩ := Finset.card_eq_one.mp hcard
  have hjk : j = k := by simpa only [hk,Finset.mem_singleton] using hj
  subst k
  rw [hk] at hi hv ht
  exact ⟨j,(mem_feasible.mp hi).1 (Finset.mem_singleton_self j),haj,hv,ht⟩

/-- At marking one the unchanged invariant equals the maximum of actual positive singleton keys. -/
theorem inv_mark_one_eq_singleton_max {S : Finset ℕ} {a : ℕ → ℕ}
    (hn : S.card ≤ n) :
    inv n S a 1 = ((S.filter (fun j => 0 < a j)).image (fun j => key n a {j})).max := by
  classical
  by_cases h : 1 ≤ ∑ i ∈ S, a i
  · obtain ⟨j,hj,haj,hv,ht⟩ := exists_singleton_top_mark_one hn h
    rw [hv]
    apply le_antisymm
    · exact Finset.le_max (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hj,haj⟩))
    · apply Finset.max_le
      intro v hv
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hkS,hka⟩ := Finset.mem_filter.mp hk
      exact WithBot.coe_le_coe.mpr (ht {k} (mem_feasible.mpr
        ⟨Finset.singleton_subset_iff.mpr hkS,by simpa using (Nat.succ_le_of_lt hka)⟩))
  · rw [inv_eq_bot_iff.mpr (Nat.lt_of_not_ge h)]
    have hf : S.filter (fun j => 0 < a j) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      obtain ⟨hjS,haj⟩ := Finset.mem_filter.mp hj
      have hh : a j ≤ ∑ i ∈ S, a i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hjS
      omega
    simp only [hf,Finset.image_empty,Finset.max_empty]


open Classical in
/-- The real WHOLE old intrinsic invariant is the actual finite positive singleton-key maximum. -/
theorem gamma_indexed_product_singleton_max (hn : 0 < n) (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (x : M) :
    gamma n (componentPowerProduct (n := n) F) (F.map Prod.fst) 1 x =
      (((memberIdx (F.map Prod.fst) x).filter (fun j => 0 < indexedPowerData F j)).image
        (fun j => key n (indexedPowerData F) {j})).max := by
  rw [gamma_indexed_product_eq hn F hF x 1]
  exact inv_mark_one_eq_singleton_max (card_memberIdx_le (F.map Prod.fst) hF x)

open Classical in
/-- The true finite positive NONEMPTY actual carrier indices; no centre or value certificate. -/
def activeIndices (F : List (Set M × ℕ)) : Finset (Fin F.length) :=
  Finset.univ.filter fun i => 0 < (F.get i).2 ∧ (F.get i).1.Nonempty

/-- This is EXACTLY the unchanged colex singleton key, with actual literal historical index. -/
def singletonKey (F : List (Set M × ℕ)) (i : Fin F.length) : Val :=
  key n (indexedPowerData F) {i.val}

omit [TopologicalSpace M] in
/-- The old colex tie break uniquely determines a literal actual singleton index. -/
theorem singletonKey_injective (F : List (Set M × ℕ)) : Function.Injective (singletonKey (n := n) F) := by
  intro i j hij
  have hset := key_injective hij
  apply Fin.ext
  exact Finset.singleton_inj.mp hset

omit [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] in
/-- The actual finite family internally gives either no active carrier or its unique old-key maximum. -/
theorem exists_actual_maximum_index (F : List (Set M × ℕ)) :
    activeIndices F = ∅ ∨ ∃ j ∈ activeIndices F,
      (∀ i ∈ activeIndices F, singletonKey (n := n) F i ≤ singletonKey (n := n) F j) ∧
      ∀ k ∈ activeIndices F,
        (∀ i ∈ activeIndices F, singletonKey (n := n) F i ≤ singletonKey (n := n) F k) → k = j := by
  classical
  by_cases h : (activeIndices F).Nonempty
  · obtain ⟨j,hj,hmax⟩ := Finset.exists_max_image (activeIndices F) (singletonKey (n := n) F) h
    refine Or.inr ⟨j,hj,hmax,?_⟩
    intro k hk hm
    exact singletonKey_injective F (le_antisymm (hmax k hk) (hm j hj))
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp h)


open Classical in
/-- The SAME complete whole actual indexed product has its TRUE intrinsic order, not a supplied bound. -/
theorem indexed_product_order_eq (hn : 0 < n) (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (x : M) :
    GermIdealOrder.order n univ (componentPowerProduct (n := n) F) x =
      ((∑ i ∈ Finset.univ.filter (fun i => x ∈ (F.get i).1), (F.get i).2 : ℕ) : ℕ∞) := by
  classical
  obtain ⟨Φ,S,hsrc,h0,hH,ho,_,_⟩ := exists_joint_whole_weighted_exponents hn F
    (boundaryAdapted_empty_of_snc hF) (indexed_member_invertible F hF) x
  have hS : S = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro j hj
    have hh : x ∈ (∅ : Set M) := (hH x (mem_flatDomain_self Φ)).mpr ⟨j,hj,?_⟩
    · exact hh.elim
    · change Φ.toFun (chartAt (ComplexModel n) x x) j = 0
      rw [h0]
      rfl
  have hc : (componentPowerProduct (n := n) F).IsCoherent :=
    (isWellFormed_monomialMarkedIdeal hF F (present_indexed_pool F)).isCoherent
  rw [vanishingIdeal_empty_eq_unit,RestrictLeCalculus.mul_unitIdeal hc,hS] at ho
  simpa only [Finset.card_empty,zero_add] using ho

/-- Every actual mark-one cosupport point is exactly on an actual positive-power indexed carrier. -/
theorem mem_cosupp_indexed_product_iff (hn : 0 < n) (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (x : M) :
    x ∈ (monomialMarkedIdeal (n := n) (F.map Prod.fst) F).cosupp ↔
      ∃ i : Fin F.length, x ∈ (F.get i).1 ∧ 0 < (F.get i).2 := by
  classical
  let S : Finset (Fin F.length) := Finset.univ.filter fun i => x ∈ (F.get i).1
  have hc : (componentPowerProduct (n := n) F).IsCoherent :=
    (isWellFormed_monomialMarkedIdeal hF F (present_indexed_pool F)).isCoherent
  have ho := indexed_product_order_eq hn F hF x
  have hh := GermIdealOrder.le_order_iff (N := (univ : Set M)) (x := x) (fun g hg =>
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hc hg) (q := 1)
  change x ∈ univ ∧ GermIdealOrder.OrderGE n univ (componentPowerProduct (n := n) F) x 1 ↔ _
  constructor
  · intro hx
    have hl := hh.mpr hx.2
    rw [ho] at hl
    have hsum : 1 ≤ ∑ i ∈ S, (F.get i).2 := by exact_mod_cast hl
    have hp : ∃ i ∈ S, 0 < (F.get i).2 := by
      by_contra hb
      push Not at hb
      have hz : ∑ i ∈ S, (F.get i).2 = 0 := Finset.sum_eq_zero
        (fun i hi => Nat.eq_zero_of_le_zero (hb i hi))
      omega
    obtain ⟨i,hi,hp⟩ := hp
    exact ⟨i,(Finset.mem_filter.mp hi).2,hp⟩
  · rintro ⟨i,hxi,hpi⟩
    refine ⟨mem_univ x,hh.mp ?_⟩
    rw [ho]
    have hl : (F.get i).2 ≤ ∑ j ∈ S, (F.get j).2 :=
      Finset.single_le_sum (s := S) (f := fun j => (F.get j).2)
        (fun _ _ => Nat.zero_le _) (Finset.mem_filter.mpr ⟨Finset.mem_univ i,hxi⟩)
    have hp : 1 ≤ ∑ j ∈ S, (F.get j).2 := by omega
    exact_mod_cast hp


private theorem gamma_le_actual_maximum (hn : 0 < n) (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length)
    (hmax : ∀ i ∈ activeIndices F, singletonKey (n := n) F i ≤ singletonKey (n := n) F j)
    (x : M) : gamma n (componentPowerProduct (n := n) F) (F.map Prod.fst) 1 x ≤
      (singletonKey (n := n) F j : WithBot Val) := by
  classical
  rw [gamma_indexed_product_singleton_max hn F hF x]
  apply Finset.max_le
  intro v hv
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hix,hip⟩ := Finset.mem_filter.mp hi
  obtain ⟨hil,hxm⟩ := (mem_memberIdx (F.map Prod.fst)).mp hix
  have hl : i < F.length := by simpa only [List.length_map] using hil
  have hx : x ∈ (F.get ⟨i,hl⟩).1 := by simpa only [List.get_eq_getElem,List.getElem_map] using hxm
  have hp : 0 < (F.get ⟨i,hl⟩).2 := by simpa only [indexedPowerData,dif_pos hl] using hip
  have ha : (⟨i,hl⟩ : Fin F.length) ∈ activeIndices F :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp,⟨x,hx⟩⟩
  exact WithBot.coe_le_coe.mpr (hmax ⟨i,hl⟩ ha)

private theorem gamma_eq_actual_maximum_iff (hn : 0 < n) (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) (hj : j ∈ activeIndices F)
    (hmax : ∀ i ∈ activeIndices F, singletonKey (n := n) F i ≤ singletonKey (n := n) F j)
    (x : M) : gamma n (componentPowerProduct (n := n) F) (F.map Prod.fst) 1 x =
      (singletonKey (n := n) F j : WithBot Val) ↔ x ∈ (F.get j).1 := by
  classical
  obtain ⟨_,hjpos,_⟩ := Finset.mem_filter.mp hj
  constructor
  · intro hx
    rw [gamma_indexed_product_singleton_max hn F hF x] at hx
    obtain ⟨i,hi,hkey⟩ := Finset.mem_image.mp (Finset.mem_of_max hx)
    have heq : i = j.val := Finset.singleton_inj.mp (key_injective hkey)
    subst i
    obtain ⟨_,hxi⟩ := (mem_memberIdx (F.map Prod.fst)).mp (Finset.mem_filter.mp hi).1
    simpa only [List.get_eq_getElem,List.getElem_map] using hxi
  · intro hx
    apply le_antisymm (gamma_le_actual_maximum hn F hF j hmax x)
    rw [gamma_indexed_product_singleton_max hn F hF x]
    apply Finset.le_max
    apply Finset.mem_image_of_mem
    apply Finset.mem_filter.mpr
    refine ⟨(mem_memberIdx (F.map Prod.fst)).mpr ⟨by simpa only [List.length_map] using j.isLt,?_⟩,?_⟩
    · simpa only [List.get_eq_getElem,List.getElem_map] using hx
    · simpa only [indexedPowerData,dif_pos j.isLt] using hjpos

private theorem actual_maximum_locus_eq (hn : 0 < n) (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) (hj : j ∈ activeIndices F)
    (hmax : ∀ i ∈ activeIndices F, singletonKey (n := n) F i ≤ singletonKey (n := n) F j) :
    ResolutionDriver.maxLocus (gamma n (componentPowerProduct (n := n) F) (F.map Prod.fst) 1)
      (monomialMarkedIdeal (n := n) (F.map Prod.fst) F).cosupp = (F.get j).1 := by
  classical
  obtain ⟨_,hjpos,hjne⟩ := Finset.mem_filter.mp hj
  obtain ⟨z,hz⟩ := hjne
  have hzcs := (mem_cosupp_indexed_product_iff hn F hF z).mpr ⟨j,hz,hjpos⟩
  have hzg := (gamma_eq_actual_maximum_iff hn F hF j hj hmax z).mpr hz
  ext x
  constructor
  · rintro ⟨_,hxm⟩
    apply (gamma_eq_actual_maximum_iff hn F hF j hj hmax x).mp
    exact le_antisymm (gamma_le_actual_maximum hn F hF j hmax x) (hzg ▸ hxm z hzcs)
  · intro hx
    refine ⟨(mem_cosupp_indexed_product_iff hn F hF x).mpr ⟨j,hx,hjpos⟩,?_⟩
    intro y _
    rw [(gamma_eq_actual_maximum_iff hn F hF j hj hmax x).mpr hx]
    exact gamma_le_actual_maximum hn F hF j hmax y

/-- ONLY actual SNC input internally supplies the true whole old-gamma singleton centre and its unique literal index. -/
theorem exists_actual_gamma_maximum_centre (hn : 0 < n) (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    activeIndices F = ∅ ∨ ∃ j ∈ activeIndices F,
      ResolutionDriver.maxLocus (gamma n (componentPowerProduct (n := n) F) (F.map Prod.fst) 1)
        (monomialMarkedIdeal (n := n) (F.map Prod.fst) F).cosupp = (F.get j).1 ∧
      (∀ i ∈ activeIndices F, singletonKey (n := n) F i ≤ singletonKey (n := n) F j) ∧
      ∀ k ∈ activeIndices F,
        (∀ i ∈ activeIndices F, singletonKey (n := n) F i ≤ singletonKey (n := n) F k) → k = j := by
  rcases exists_actual_maximum_index (n := n) F with h|⟨j,hj,hm,hu⟩
  · exact Or.inl h
  · exact Or.inr ⟨j,hj,actual_maximum_locus_eq hn F hF j hj hm,hm,hu⟩


private theorem invertible_pool_product (F : List (Set M × ℕ))
    (hF : ∀ p ∈ F, (vanishingIdeal (n := n) p.1).IsInvertible) :
    (componentPowerProduct (n := n) F).IsInvertible := by
  induction F with
  | nil => exact BlowupExceptionalDivisor.isInvertible_unitIdeal
  | cons p F ih =>
    exact GermIdealTotalTransform.isInvertible_mul
      (BlowupExceptionalDivisor.isInvertible_idealPow (hF p (by simp)) p.2)
      (ih fun q hq => hF q (List.mem_cons_of_mem p hq))

private theorem component_product_perm {F G : List (Set M × ℕ)} (hp : F.Perm G) :
    (∀ p ∈ F, (vanishingIdeal (n := n) p.1).IsInvertible) →
      componentPowerProduct (n := n) F = componentPowerProduct (n := n) G := by
  induction hp with
  | nil => intro _; rfl
  | cons p hp ih =>
    intro hF
    change (idealPow (vanishingIdeal (n := n) p.1) p.2).mul (componentPowerProduct (n := n) _) = _
    rw [ih fun q hq => hF q (List.mem_cons_of_mem p hq)]
    rfl
  | swap p q F =>
    intro hF
    have hp := DivisorMetric.isCoherent_of_isInvertible
      (BlowupExceptionalDivisor.isInvertible_idealPow (hF p (by simp)) p.2)
    have hq := DivisorMetric.isCoherent_of_isInvertible
      (BlowupExceptionalDivisor.isInvertible_idealPow (hF q (by simp)) q.2)
    have ht := DivisorMetric.isCoherent_of_isInvertible (invertible_pool_product F
      (fun r hr => hF r (by simp only [List.mem_cons]; exact Or.inr (Or.inr hr))))
    change (idealPow (vanishingIdeal (n := n) q.1) q.2).mul
      ((idealPow (vanishingIdeal (n := n) p.1) p.2).mul (componentPowerProduct (n := n) F)) = _
    rw [← GermIdealTotalTransform.mul_assoc hq hp ht,RestrictLeCalculus.mul_comm'
      (idealPow (vanishingIdeal (n := n) q.1) q.2) (idealPow (vanishingIdeal (n := n) p.1) p.2),
      GermIdealTotalTransform.mul_assoc hp hq ht]
    rfl
  | trans hp hq ihp ihq =>
    intro hF
    exact (ihp hF).trans (ihq fun p hpG => hF p (hp.mem_iff.mpr hpG))

private theorem component_product_append_one (F : List (Set M × ℕ))
    (hF : ∀ p ∈ F, (vanishingIdeal (n := n) p.1).IsInvertible)
    (W : Set M) (a : ℕ) (hW : (vanishingIdeal (n := n) W).IsInvertible) :
    componentPowerProduct (n := n) (F++[(W,a)]) = (componentPowerProduct (n := n) F).mul
      (idealPow (vanishingIdeal (n := n) W) a) := by
  have hWc := DivisorMetric.isCoherent_of_isInvertible (BlowupExceptionalDivisor.isInvertible_idealPow hW a)
  induction F with
  | nil =>
    simp only [List.nil_append,componentPowerProduct]
    rw [RestrictLeCalculus.mul_unitIdeal hWc,BlowupControlledTransform.unitIdeal_mul hWc]
  | cons p F ih =>
    have ht := fun q hq => hF q (List.mem_cons_of_mem p hq)
    simp only [List.cons_append,componentPowerProduct]
    rw [ih ht,GermIdealTotalTransform.mul_assoc
      (DivisorMetric.isCoherent_of_isInvertible (BlowupExceptionalDivisor.isInvertible_idealPow (hF p (by simp)) p.2))
      (DivisorMetric.isCoherent_of_isInvertible (invertible_pool_product F ht)) hWc]

/-- The WHOLE ideal normalization retains the literal selected empty entry and appends its actual new carrier. -/
def dividedWeights (F : List (Set M × ℕ)) (j : Fin F.length) : List (Set M × ℕ) :=
  F.set j.val (∅,0) ++ [((F.get j).1,(F.get j).2-1)]

/-- Normalizing the old selected unit factor leaves EXACTLY the genuine remaining whole product. -/
theorem dividedWeights_ideal_dictionary (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) :
    componentPowerProduct (n := n) (dividedWeights F j) =
      componentPowerProduct (n := n) (((F.get j).1,(F.get j).2-1)::F.eraseIdx j.val) := by
  have hInv := indexed_member_invertible F hF
  have heInv : ∀ p ∈ F.eraseIdx j.val, (vanishingIdeal (n := n) p.1).IsInvertible :=
    fun p hp => hInv p (List.mem_of_mem_eraseIdx hp)
  have hPerm : (F.set j.val (∅,0)).Perm ((∅,0)::F.eraseIdx j.val) :=
    List.set_perm_cons_eraseIdx j.isLt (∅,0)
  have hNewInv : ∀ p ∈ F.set j.val (∅,0), (vanishingIdeal (n := n) p.1).IsInvertible := by
    intro p hp
    rcases List.mem_cons.mp (hPerm.mem_iff.mp hp) with rfl|hp
    · rw [vanishingIdeal_empty_eq_unit]
      exact BlowupExceptionalDivisor.isInvertible_unitIdeal
    · exact heInv p hp
  have hc := DivisorMetric.isCoherent_of_isInvertible (invertible_pool_product _ heInv)
  rw [dividedWeights,component_product_append_one _ hNewInv _ _ (hInv _ (List.get_mem _ _)),
    component_product_perm hPerm hNewInv]
  change ((idealPow (vanishingIdeal (n := n) (∅ : Set M)) 0).mul
    (componentPowerProduct (n := n) (F.eraseIdx j.val))).mul _ = _
  rw [idealPow_zero,BlowupControlledTransform.unitIdeal_mul hc,RestrictLeCalculus.mul_comm']
  rfl


private theorem strict_indexed_other (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (i j : Fin F.length) (hij : i ≠ j) :
    geoStrictTransform (id : M → M) (F.get j).1 (F.get i).1 = (F.get i).1 := by
  let i' : Fin (F.map Prod.fst).length := ⟨i.val,by simp only [List.length_map]; exact i.isLt⟩
  let j' : Fin (F.map Prod.fst).length := ⟨j.val,by simp only [List.length_map]; exact j.isLt⟩
  have hi : (F.map Prod.fst).get i' = (F.get i).1 := by simp [List.get_eq_getElem,i']
  have hj : (F.map Prod.fst).get j' = (F.get j).1 := by simp [List.get_eq_getElem,j']
  have hneq : i' ≠ j' := by
    intro h
    apply hij
    have hv := congrArg (fun k : Fin (F.map Prod.fst).length => k.val) h
    exact Fin.ext hv
  have h := geoStrictTransform_id_snc_other hF i' j' hneq
  rw [hi,hj] at h
  exact h

/-- EVERY transformed literal carrier agrees with the normalized actual coefficient list; no historical entry is deleted. -/
theorem dividedWeights_carriers (F : List (Set M × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) :
    (dividedWeights F j).map Prod.fst =
      (F.map Prod.fst).map (geoStrictTransform (id : M → M) (F.get j).1) ++ [(F.get j).1] := by
  rw [dividedWeights,List.map_append,List.map_singleton,List.map_set,List.map_map]
  apply congrArg (fun L => L++[(F.get j).1])
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hl : i < F.length := by simpa using hi'
    by_cases hij : i = j.val
    · subst i
      simp only [List.getElem_set_self,List.getElem_map]
      exact (geoStrictTransform_id_selected (C := (F.get j).1)).symm
    · rw [List.getElem_set_of_ne (Ne.symm hij)]
      simp only [List.getElem_map]
      exact (strict_indexed_other F hF ⟨i,hl⟩ j (fun h => hij (congrArg Fin.val h))).symm

variable {A : CMfd.{u} n}

/-- An actual positive indexed factor gives genuine same-whole-ideal Cartier admissibility. -/
theorem isAdmissibleCentre_indexed_positive (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) (hj : 0 < (F.get j).2) :
    (monomialMarkedIdeal (n := n) (F.map Prod.fst) F).IsAdmissibleCentre (F.get j).1 := by
  let R := F.eraseIdx j.val
  have hInv := indexed_member_invertible F hF
  have hp : ((F.get j)::R).Perm F := List.getElem_cons_eraseIdx_perm j.isLt
  have hHead := component_product_perm hp (fun p h => hInv p (hp.mem_iff.mp h))
  have hk : (F.get j).2-1+1 = (F.get j).2 := Nat.sub_add_cancel (Nat.succ_le_of_lt hj)
  have hpair : F.get j = ((F.get j).1,(F.get j).2-1+1) := Prod.ext rfl hk.symm
  rw [hpair] at hHead
  have hm : monomialMarkedIdeal (n := n) (F.map Prod.fst) F =
      monomialMarkedIdeal (n := n) (F.map Prod.fst) (((F.get j).1,(F.get j).2-1+1)::R) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hHead.symm rfl
  rw [hm]
  apply isAdmissibleCentre_monomial_succ hF
    (F.get j).1 (present_indexed_pool F _ (List.get_mem _ _)) R
    (fun p hp => present_indexed_pool F p (List.mem_of_mem_eraseIdx hp))

/-- TRUE Cartier control of a positive actual indexed factor is EXACTLY the complete normalized new product. -/
theorem geoTransform_indexed_positive (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) (hj : 0 < (F.get j).2) :
    (monomialMarkedIdeal (n := n) (F.map Prod.fst) F).geoTransform (F.get j).1 id =
      monomialMarkedIdeal (n := n) ((dividedWeights F j).map Prod.fst) (dividedWeights F j) := by
  let R := F.eraseIdx j.val
  have hInv := indexed_member_invertible F hF
  have hp : ((F.get j)::R).Perm F := List.getElem_cons_eraseIdx_perm j.isLt
  have hHead := component_product_perm hp (fun p h => hInv p (hp.mem_iff.mp h))
  have hk : (F.get j).2-1+1 = (F.get j).2 := Nat.sub_add_cancel (Nat.succ_le_of_lt hj)
  have hpair : F.get j = ((F.get j).1,(F.get j).2-1+1) := Prod.ext rfl hk.symm
  rw [hpair] at hHead
  have hm : monomialMarkedIdeal (n := n) (F.map Prod.fst) F =
      monomialMarkedIdeal (n := n) (F.map Prod.fst) (((F.get j).1,(F.get j).2-1+1)::R) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hHead.symm rfl
  rw [hm,geoTransform_monomial_succ hF (F.get j).1
    (present_indexed_pool F _ (List.get_mem _ _)) R
    (fun p hp => present_indexed_pool F p (List.mem_of_mem_eraseIdx hp))]
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl (dividedWeights_carriers F hF j).symm ?_ rfl
  exact (dividedWeights_ideal_dictionary F hF j).symm


/-- The actual WHOLE recorded coefficient sum decreases by precisely one at a genuine positive Cartier step. -/
theorem dividedWeights_sum_add_one (F : List (Set A × ℕ))
    (j : Fin F.length) (hj : 0 < (F.get j).2) :
    ((dividedWeights F j).map Prod.snd).sum + 1 = (F.map Prod.snd).sum := by
  have hOld := ((List.getElem_cons_eraseIdx_perm (l := F) j.isLt).map Prod.snd).sum_eq
  have hNew := ((List.set_perm_cons_eraseIdx (l := F) j.isLt (∅,0)).map Prod.snd).sum_eq
  simp only [List.map_cons,List.sum_cons,zero_add] at hOld hNew
  change (F.get j).2 + (F.eraseIdx j.val |>.map Prod.snd).sum = (F.map Prod.snd).sum at hOld
  rw [dividedWeights,List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,hNew]
  change (List.map Prod.snd (F.eraseIdx j.val)).sum + ((F.get j).2-1) +1 = (F.map Prod.snd).sum
  omega


private theorem product_eq_unit_of_inactive (F : List (Set A × ℕ))
    (hInv : ∀ p ∈ F, (vanishingIdeal (n := n) p.1).IsInvertible)
    (hz : ∀ p ∈ F, p.2 = 0 ∨ p.1 = ∅) : componentPowerProduct (n := n) F = unitIdeal n A := by
  induction F with
  | nil => rfl
  | cons p F ih =>
    change (idealPow (vanishingIdeal (n := n) p.1) p.2).mul (componentPowerProduct (n := n) F) = _
    rw [ih (fun q hq => hInv q (List.mem_cons_of_mem p hq)) (fun q hq => hz q (List.mem_cons_of_mem p hq))]
    rcases hz p (by simp) with hp|hp
    · rw [hp,idealPow_zero,BlowupControlledTransform.unitIdeal_mul isCoherent_unitIdeal]
    · rw [hp,vanishingIdeal_empty_eq_unit,BlowupControlledTransform.idealPow_unitIdeal,
        BlowupControlledTransform.unitIdeal_mul isCoherent_unitIdeal]

/-- A genuinely empty active family internally makes the SAME WHOLE ideal unit, retaining its entire literal boundary. -/
theorem indexed_product_eq_unit_of_no_active (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (he : activeIndices F = ∅) :
    componentPowerProduct (n := n) F = unitIdeal n A := by
  classical
  apply product_eq_unit_of_inactive F (indexed_member_invertible F hF)
  intro p hp
  by_cases hz : p.2 = 0
  · exact Or.inl hz
  · apply Or.inr
    apply Set.not_nonempty_iff_eq_empty.mp
    intro hc
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hp
    have ha : i ∈ activeIndices F := Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    · rw [he] at ha
      exact Finset.notMem_empty _ ha
    · rw [hi]
      exact ⟨Nat.pos_of_ne_zero hz,hc⟩

private theorem canonical_gamma_append {D B : CMfd.{u} n} (I : MarkedIdeal n A)
    (T : BlowupTower A D) (S : BlowupTower D B)
    (hT : ResolutionDriver.IsCanonicalSegment I (fun {V} R => MonomialStepAlong.towerInvAlong I (Y := V) R) T)
    (hS : ResolutionDriver.IsCanonicalSegment (geoTransformAlong I T)
      (fun {V} R => MonomialStepAlong.towerInvAlong (geoTransformAlong I T) (Y := V) R) S) :
    ResolutionDriver.IsCanonicalSegment I (fun {V} R => MonomialStepAlong.towerInvAlong I (Y := V) R) (T.append S) := by
  induction S with
  | refl => exact hT
  | step S C π hπ ih =>
    obtain ⟨hs,hne,hc⟩ := hS
    refine ⟨ih hs,hne,?_⟩
    change C = ResolutionDriver.maxLocus (MonomialStepAlong.towerInvAlong I (T.append S))
      (geoTransformAlong I (T.append S)).cosupp
    unfold MonomialStepAlong.towerInvAlong
    rw [geoTransformAlong_append]
    exact hc

/-- Actual natural coefficient recursion INTERNALLY produces a genuine UNCHANGED-gamma canonical test resolution. -/
theorem exists_actual_ordered_gamma_resolution (hn : 0 < n) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∃ S : BlowupTower A A, S.proj = id ∧ S.length ≤ (F.map Prod.snd).sum ∧
      ResolutionDriver.IsCanonicalSegment (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
        (fun {V} R => MonomialStepAlong.towerInvAlong
          (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (Y := V) R) S ∧
      IsGeoResolution (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) S ∧
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) S).ideal = unitIdeal n A := by
  classical
  have hrec : ∀ q (F : List (Set A × ℕ)), (F.map Prod.snd).sum = q → IsSNCDivisor n (F.map Prod.fst) →
      ∃ S : BlowupTower A A, S.proj = id ∧ S.length ≤ q ∧
        ResolutionDriver.IsCanonicalSegment (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
          (fun {V} R => MonomialStepAlong.towerInvAlong
            (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (Y := V) R) S ∧
        IsGeoResolution (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) S ∧
        (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) S).ideal = unitIdeal n A := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro F hq hF
      let M := monomialMarkedIdeal (n := n) (F.map Prod.fst) F
      rcases exists_actual_gamma_maximum_centre hn F hF with he|⟨j,hj,hcentre,_,_⟩
      · have hu := indexed_product_eq_unit_of_no_active F hF he
        have hr : IsGeoResolution M (BlowupTower.refl : BlowupTower A A) := by
          refine ⟨trivial,?_⟩
          change GermIdealOrder.cosupport n univ (componentPowerProduct (n := n) F) 1 = ∅
          rw [hu]
          exact GermIdealOrder.cosupport_unitIdeal le_rfl
        exact ⟨.refl,rfl,Nat.zero_le q,trivial,hr,hu⟩
      · obtain ⟨_,hjpos,hjne⟩ := Finset.mem_filter.mp hj
        let C := (F.get j).1
        let j' : Fin (F.map Prod.fst).length := ⟨j.val,by simp only [List.length_map]; exact j.isLt⟩
        have hget : (F.map Prod.fst).get j' = C := by simp [List.get_eq_getElem,j',C]
        have hπ : IsBlowupAlong n C (id : A → A) := hget ▸ isBlowupAlong_id_snc_member hF j'
        let T : BlowupTower A A := .step .refl C id hπ
        let G := dividedWeights F j
        have ht : IsGeoTestTower M T := ⟨trivial,isAdmissibleCentre_indexed_positive F hF j hjpos⟩
        have heq : geoTransformAlong M T = monomialMarkedIdeal (n := n) (G.map Prod.fst) G :=
          geoTransform_indexed_positive F hF j hjpos
        have hw : M.IsWellFormed := isWellFormed_monomialMarkedIdeal hF F (present_indexed_pool F)
        have hG : IsSNCDivisor n (G.map Prod.fst) := by
          have hh := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hw T ht).isSNCDivisor
          rw [heq] at hh
          exact hh
        have hdrop : (G.map Prod.snd).sum+1 = q := (dividedWeights_sum_add_one F j hjpos).trans hq
        have hlt : (G.map Prod.snd).sum < q := by omega
        obtain ⟨S,hp,hl,hcan,hr,hu⟩ := ih (G.map Prod.snd).sum hlt G rfl hG
        have hcT : ResolutionDriver.IsCanonicalSegment M
            (fun {V} R => MonomialStepAlong.towerInvAlong M (Y := V) R) T := by
          refine ⟨trivial,hjne,?_⟩
          change C = ResolutionDriver.maxLocus
            (MonomialCaseAlong.gammaAlong n univ (componentPowerProduct (n := n) F) (F.map Prod.fst) 1) M.cosupp
          have hγ : (MonomialCaseAlong.gammaAlong n univ (componentPowerProduct (n := n) F)
              (F.map Prod.fst) 1 : A → WithBot Val) = gamma n (componentPowerProduct (n := n) F)
                (F.map Prod.fst) 1 := funext fun z => MonomialCaseAlong.gammaAlong_univ 1 z
          rw [hγ]
          exact hcentre.symm
        refine ⟨T.append S,?_,?_,?_,?_,?_⟩
        · rw [BlowupTower.proj_append,hp]
          rfl
        · rw [BlowupTower.length_append]
          change 1+S.length ≤ q
          omega
        · apply canonical_gamma_append M T S hcT
          rw [heq]
          exact hcan
        · apply IsGeoResolution.append _ ht
          rw [heq]
          exact hr
        · rw [geoTransformAlong_append,heq]
          exact hu
  exact hrec (F.map Prod.snd).sum F rfl hF


/-- In dimension zero there is no true nonempty positive SNC carrier index. -/
theorem activeIndices_eq_empty_dimension_zero {D : CMfd.{u} 0} (F : List (Set D × ℕ))
    (hF : IsSNCDivisor 0 (F.map Prod.fst)) : activeIndices F = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨_,_,x,hx⟩ := Finset.mem_filter.mp hi
  obtain ⟨B,_,hcard,_⟩ := hF.2 x
  let i' : Fin (F.map Prod.fst).length := ⟨i.val,by simp only [List.length_map]; exact i.isLt⟩
  have hx' : x ∈ (F.map Prod.fst).get i' := by simpa only [List.get_eq_getElem,List.getElem_map] using hx
  have hc := hcard i' hx'
  have hb := Finset.card_le_univ (B i')
  simp only [Fintype.card_fin] at hb
  omega

/-- The actual whole old-gamma resolution covers ALL dimensions, with the real reflexive zero-dimensional case. -/
theorem exists_actual_ordered_gamma_resolution_all_dimensions (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) :
    ∃ S : BlowupTower A A, S.proj = id ∧ S.length ≤ (F.map Prod.snd).sum ∧
      ResolutionDriver.IsCanonicalSegment (monomialMarkedIdeal (n := n) (F.map Prod.fst) F)
        (fun {V} R => MonomialStepAlong.towerInvAlong
          (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) (Y := V) R) S ∧
      IsGeoResolution (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) S ∧
      (geoTransformAlong (monomialMarkedIdeal (n := n) (F.map Prod.fst) F) S).ideal = unitIdeal n A := by
  cases n with
  | zero =>
    have hu := indexed_product_eq_unit_of_no_active F hF (activeIndices_eq_empty_dimension_zero F hF)
    refine ⟨.refl,rfl,Nat.zero_le _,trivial,⟨trivial,?_⟩,hu⟩
    change GermIdealOrder.cosupport 0 univ (componentPowerProduct (n := 0) F) 1 = ∅
    rw [hu]
    exact GermIdealOrder.cosupport_unitIdeal le_rfl
  | succ m => exact exists_actual_ordered_gamma_resolution (Nat.succ_pos m) F hF

/-- The REAL current indexed monomial list after the SAME genuine terminal-original step; its actual new factor has power zero. -/
def originalTerminalIndexedWeights {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    List (Set (originalSeparation hH).D × ℕ) :=
  originalTerminalWeights hH ++ [(strictTransform n (originalSeparation hH).T.proj H,0)]

/-- The full indexed monomial carrier list is EXACTLY the actual entire boundary, retaining every historical empty entry. -/
theorem originalTerminalIndexedWeights_carriers {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (originalTerminalIndexedWeights hH).map Prod.fst = terminalBoundary hH := by
  rw [originalTerminalIndexedWeights,List.map_append,List.map_singleton,(originalTerminalWeights_geometry hH).1]
  rfl

/-- Whole factor-zero normalization internally preserves the SAME complete original controlled ideal. -/
theorem originalTerminalIndexedWeights_ideal {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    componentPowerProduct (n := n) (originalTerminalIndexedWeights hH) =
      componentPowerProduct (n := n) (originalTerminalWeights hH) := by
  have hInv : ∀ p ∈ originalTerminalWeights hH,
      (vanishingIdeal (n := n) p.1).IsInvertible :=
    recordedOriginalWeights_member_invertible H 1 (originalSeparation hH).T (originalSeparation hH).centres
  have hπ := originalTerminal_isBlowupAlong_id hH
  have hC := hπ.2.2.2.1
  rw [BlowupControlledTransform.pullback_id (BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ)] at hC
  rw [originalTerminalIndexedWeights,component_product_append_one _ hInv _ _ hC,idealPow_zero,
    RestrictLeCalculus.mul_unitIdeal (DivisorMetric.isCoherent_of_isInvertible (invertible_pool_product _ hInv))]

/-- The indexed whole datum is the EXACT actual SAME-original marked Cartier transform, not a caller ideal certificate. -/
theorem originalTerminal_indexed_marked_dictionary {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T).geoTransform
      (strictTransform n (originalSeparation hH).T.proj H) id =
    monomialMarkedIdeal (n := n) ((originalTerminalIndexedWeights hH).map Prod.fst)
      (originalTerminalIndexedWeights hH) := by
  rw [originalTerminal_geoTransform_dictionary]
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl
    (originalTerminalIndexedWeights_carriers hH).symm (originalTerminalIndexedWeights_ideal hH).symm rfl

/-- The SAME actual historical coefficient sum is untouched by the real appended zero-power factor. -/
theorem originalTerminalIndexedWeights_sum_le {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    ((originalTerminalIndexedWeights hH).map Prod.snd).sum ≤ (n-1)*(n-1) := by
  simpa only [originalTerminalIndexedWeights,List.map_append,List.map_singleton,List.sum_append,
    List.sum_singleton,add_zero] using originalTerminalWeights_sum_le hH


/-- True ordinary SNC and actual admissibility internally produce the WHOLE transformed SNC index list. -/
theorem dividedWeights_isSNCDivisor (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) (hj : 0 < (F.get j).2) :
    IsSNCDivisor n ((dividedWeights F j).map Prod.fst) := by
  let j' : Fin (F.map Prod.fst).length := ⟨j.val,by simp only [List.length_map]; exact j.isLt⟩
  have hget : (F.map Prod.fst).get j' = (F.get j).1 := by simp [List.get_eq_getElem,j']
  have hπ : IsBlowupAlong n (F.get j).1 (id : A → A) := hget ▸ isBlowupAlong_id_snc_member hF j'
  have h := (GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre
    (isWellFormed_monomialMarkedIdeal hF F (present_indexed_pool F))
    (isAdmissibleCentre_indexed_positive F hF j hj) hπ).isSNCDivisor
  rw [geoTransform_indexed_positive F hF j hj] at h
  exact h

/-- Exact intrinsic exponents of the SAME whole actual controlled ideal on EVERY actual through transformed member. -/
theorem dividedWeights_controlled_intrinsic_exponents (hn : 0 < n) (F : List (Set A × ℕ))
    (hF : IsSNCDivisor n (F.map Prod.fst)) (j : Fin F.length) (hj : 0 < (F.get j).2)
    (x : A) (i : Fin (dividedWeights F j).length) (hx : x ∈ ((dividedWeights F j).get i).1) :
    divExp n ((monomialMarkedIdeal (n := n) (F.map Prod.fst) F).geoTransform (F.get j).1 id).ideal
      ((dividedWeights F j).get i).1 x = ((dividedWeights F j).get i).2 := by
  rw [geoTransform_indexed_positive F hF j hj]
  exact indexed_product_divExp hn _ (dividedWeights_isSNCDivisor F hF j hj) x i hx

/-- The SAME actual original controlled datum after its genuine original Cartier step. -/
def originalOrderedMonomialDatum {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    MarkedIdeal n (originalSeparation hH).D :=
  (geoTransformAlong (originalMarkedIdeal H) (originalSeparation hH).T).geoTransform
    (strictTransform n (originalSeparation hH).T.proj H) id

/-- ONLY the original NC carrier internally produces a genuine UNCHANGED old-gamma canonical tail of the SAME actual datum. -/
theorem exists_original_ordered_gamma_tail {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    ∃ S : BlowupTower (originalSeparation hH).D (originalSeparation hH).D,
      S.proj = id ∧ S.length ≤ (n-1)*(n-1) ∧
      ResolutionDriver.IsCanonicalSegment (originalOrderedMonomialDatum hH)
        (fun {V} R => MonomialStepAlong.towerInvAlong (originalOrderedMonomialDatum hH) (Y := V) R) S ∧
      IsGeoResolution (originalOrderedMonomialDatum hH) S ∧
      (geoTransformAlong (originalOrderedMonomialDatum hH) S).ideal = unitIdeal n (originalSeparation hH).D := by
  have hF : IsSNCDivisor n ((originalTerminalIndexedWeights hH).map Prod.fst) := by
    rw [originalTerminalIndexedWeights_carriers]
    exact (originalSeparation_geometry hH).2.2.2.1
  obtain ⟨S,hp,hl,hcan,hr,hu⟩ := exists_actual_ordered_gamma_resolution_all_dimensions
    (originalTerminalIndexedWeights hH) hF
  refine ⟨S,hp,hl.trans (originalTerminalIndexedWeights_sum_le hH),?_,?_,?_⟩
  · unfold originalOrderedMonomialDatum
    rw [originalTerminal_indexed_marked_dictionary]
    exact hcan
  · unfold originalOrderedMonomialDatum
    rw [originalTerminal_indexed_marked_dictionary]
    exact hr
  · unfold originalOrderedMonomialDatum
    rw [originalTerminal_indexed_marked_dictionary]
    exact hu

/-- The genuine original old-gamma tail is chosen ONLY from its internally generated actual recursion. -/
def originalOrderedGammaTail {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    BlowupTower (originalSeparation hH).D (originalSeparation hH).D :=
  Classical.choose (exists_original_ordered_gamma_tail hH)

/-- The actual internally produced gamma tail has true projection, finite length, OLD canonicality and SAME whole unit endpoint. -/
theorem originalOrderedGammaTail_spec {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (originalOrderedGammaTail hH).proj = id ∧ (originalOrderedGammaTail hH).length ≤ (n-1)*(n-1) ∧
    ResolutionDriver.IsCanonicalSegment (originalOrderedMonomialDatum hH)
      (fun {V} R => MonomialStepAlong.towerInvAlong (originalOrderedMonomialDatum hH) (Y := V) R)
      (originalOrderedGammaTail hH) ∧
    IsGeoResolution (originalOrderedMonomialDatum hH) (originalOrderedGammaTail hH) ∧
    (geoTransformAlong (originalOrderedMonomialDatum hH) (originalOrderedGammaTail hH)).ideal =
      unitIdeal n (originalSeparation hH).D := Classical.choose_spec (exists_original_ordered_gamma_tail hH)

/-- The actual real universal-property original Cartier step is kept separate from the nonempty old-gamma segment. -/
def originalTerminalCartierStep {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    BlowupTower (originalSeparation hH).D (originalSeparation hH).D :=
  .step .refl (strictTransform n (originalSeparation hH).T.proj H) id (originalTerminal_isBlowupAlong_id hH)

/-- The real complete SAME-original resolution includes the actual separation, original Cartier step and actual gamma tail. -/
def originalOrderedMarkedCompletion {H : Set A} (hH : IsNormalCrossingsCarrier (n := n) H) :
    BlowupTower A (originalSeparation hH).D :=
  (originalSeparation hH).T.append ((originalTerminalCartierStep hH).append (originalOrderedGammaTail hH))

/-- The SAME whole original NC datum has a genuine finite marked test resolution. -/
theorem originalOrderedMarkedCompletion_isGeoResolution {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    IsGeoResolution (originalMarkedIdeal H) (originalOrderedMarkedCompletion hH) := by
  apply IsGeoResolution.append _ (originalSeparation_isGeoTestTower hH)
  apply IsGeoResolution.append _ (T := originalTerminalCartierStep hH)
    (S := originalOrderedGammaTail hH)
  · exact ⟨trivial,originalTerminal_isAdmissibleCentre hH⟩
  · exact (originalOrderedGammaTail_spec hH).2.2.2.1

/-- The COMPLETE actual SAME original controlled endpoint ideal is unit. -/
theorem originalOrderedMarkedCompletion_ideal_eq_unit {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (geoTransformAlong (originalMarkedIdeal H) (originalOrderedMarkedCompletion hH)).ideal =
      unitIdeal n (originalSeparation hH).D := by
  rw [originalOrderedMarkedCompletion,geoTransformAlong_append,geoTransformAlong_append]
  exact (originalOrderedGammaTail_spec hH).2.2.2.2

/-- The actual ordered monomial completion preserves the WHOLE real original separation projection. -/
theorem originalOrderedMarkedCompletion_proj {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (originalOrderedMarkedCompletion hH).proj = (originalSeparation hH).T.proj := by
  rw [originalOrderedMarkedCompletion,BlowupTower.proj_append,BlowupTower.proj_append,
    (originalOrderedGammaTail_spec hH).1]
  rfl

/-- The WHOLE bound includes the true prior separation and one actual original Cartier step, distinct from the gamma-tail bound. -/
theorem originalOrderedMarkedCompletion_length_le {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) :
    (originalOrderedMarkedCompletion hH).length ≤ 1+n*(n-1) := by
  rw [originalOrderedMarkedCompletion,BlowupTower.length_append,BlowupTower.length_append]
  change (originalSeparation hH).T.length + (1+(originalOrderedGammaTail hH).length) ≤ _
  have hs := (originalSeparation_geometry hH).1
  have ht := (originalOrderedGammaTail_spec hH).2.1
  cases n with
  | zero => simp only [Nat.zero_sub,Nat.mul_zero] at *; omega
  | succ k =>
    simp only [Nat.add_sub_cancel] at hs ht ⊢
    rw [Nat.add_mul,Nat.one_mul]
    omega

/-- Every literal prefix of the actual WHOLE completion lies in the original marked domain. -/
theorem originalOrderedMarkedCompletion_prefix_domain {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ) :
    ResolutionInvariantSpec.IsInvDomain n (geoTransformAlong (originalMarkedIdeal H)
      (BlowupTowerSplit.head (originalOrderedMarkedCompletion hH) i)) :=
  InvDomainTowerAlong.isInvDomain_geoTransformAlong (isInvDomain_originalMarkedIdeal hH) _
    (((BlowupTowerSplit.isGeoTestTower_iff_head_tail (originalMarkedIdeal H)
      (originalOrderedMarkedCompletion hH) i).mp (originalOrderedMarkedCompletion_isGeoResolution hH).1).1)

/-- True SNC of EVERY actual literal prefix retains all empty and repeated historical entries. -/
theorem originalOrderedMarkedCompletion_prefix_snc {H : Set A}
    (hH : IsNormalCrossingsCarrier (n := n) H) (i : ℕ) :
    IsSNCDivisor n (geoTransformAlong (originalMarkedIdeal H)
      (BlowupTowerSplit.head (originalOrderedMarkedCompletion hH) i)).E :=
  (originalOrderedMarkedCompletion_prefix_domain hH i).isWellFormed.isSNCDivisor

/-- Zero-dimensional true old-gamma completion is reflexive; the real original empty Cartier step is still kept literally. -/
theorem originalOrderedMarkedCompletion_dimension_zero {D : CMfd.{u} 0} {H : Set D}
    (hH : IsNormalCrossingsCarrier (n := 0) H) :
    (originalOrderedGammaTail hH).length = 0 ∧ (originalOrderedMarkedCompletion hH).length = 1 := by
  have hs : (originalSeparation hH).T.length = 0 := Nat.eq_zero_of_le_zero (originalSeparation_geometry hH).1
  have ht : (originalOrderedGammaTail hH).length = 0 := Nat.eq_zero_of_le_zero (originalOrderedGammaTail_spec hH).2.1
  refine ⟨ht,?_⟩
  rw [originalOrderedMarkedCompletion,BlowupTower.length_append,BlowupTower.length_append,hs,ht]
  rfl

end
end Hironaka.HironakaNormalCrossingsOrderedMonomialTail
