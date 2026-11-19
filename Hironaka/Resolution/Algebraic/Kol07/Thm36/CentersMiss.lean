/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Resolution.Algebraic.Kol07.Thm36.CentersOverSupport
import Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCore
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Centres missing a subset of the base, and sequences with empty centres

Clause (b) of Włodarczyk's embedded desingularization theorem [Wlo05, Theorem 1.0.2] says that
all centres are disjoint from the set of points where the subvariety `Y` is smooth. For the
embedded desingularization sequence of `Hironaka.Resolution.Algebraic.Wlo05.Embedded` it is proved
locally, on an affine open of `X` meeting `Y` in one smooth component, by Włodarczyk's remark that
"the generic points would be transformed isomorphically" [Wlo05, 4.6]. This file holds the general
facts about blow-up sequences used in that argument, none of which mentions the loop:

* `CentersMiss S U`: no point of a centre of `S` lies over the set `U ⊆ X`; its rules for `cons`,
  `concat` and `take`, and the case of a sequence of order `≥ 1` whose ideal's support misses `U`
  (`stageMap_mem_support_of_mem_center`);
* `centerContains_take_iff`: the predicate `CenterContains` on a prefix is the predicate on the
  sequence, at indices below the prefix length;
* `exists_mem_center_support_of_eraseEmpty_eq_cons`: a point of the first centre of `S.eraseEmpty`
  is the image of a point of the first nonempty centre of `S`, all earlier centres being empty
  (the deletion of empty blow-ups, [Kol07, 32]);
* the transforms along a sequence all of whose centres are empty: marked and strict transforms
  are the inverse images (`markedTransform_top_left`, `strictTransform_top_left`), the total
  transform of a family with empty members has empty members (`exceptionalDivisor_top`), and the
  stage maps are isomorphisms (`isIso_stageMap_of_center_eq_top`);
* `center_pullback_eq_top_iff`: a centre of the pullback along a flat `h` is empty if and only if
  no point of the centre lies over the image of `h` [Kol07, Definition 30, 30.1];
* `isGenericPoint_of_mem_genericPoints_comap`: the image under an open immersion of a generic point
  of `h⁻¹ V(Z)`, for an irreducible `V(Z)`, is the generic point of `V(Z)`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Resolution

variable {X : Scheme.{u}}

/-! ### Centres missing a subset of the base -/

/-- **No centre of `S` has a point over `U ⊆ X`.** For `U` the set of smooth points of a
subvariety `Y` this is clause (b) of [Wlo05, Theorem 1.0.2]: "all centers are disjoint from
`Reg(Y)`". -/
def CentersMiss (S : BlowUpSequence X) (U : Set X) : Prop :=
  ∀ (i : Fin S.length) (x : S.stage i.castSucc), x ∈ (S.center i).support →
    S.stageMap i.castSucc x ∉ U

/-- `CentersMiss` for the centres of index `< n` only. -/
def CentersMissBefore (S : BlowUpSequence X) (U : Set X) (n : ℕ) : Prop :=
  ∀ (i : Fin S.length), i.val < n → ∀ (x : S.stage i.castSucc), x ∈ (S.center i).support →
    S.stageMap i.castSucc x ∉ U

theorem centersMiss_nil (U : Set X) : CentersMiss (nil X) U := fun i => i.elim0

/-- `CentersMiss` on a `cons`: the first centre misses `U` and the tail misses its preimage under
the first blow-up. -/
theorem centersMiss_cons_iff (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp)
    (U : Set X) :
    CentersMiss (cons X D rest) U ↔
      (∀ x ∈ D.support, x ∉ U) ∧ CentersMiss rest (D.blowUpπ ⁻¹' U) := by
  constructor
  · intro h
    refine ⟨fun x hx => h ⟨0, Nat.succ_pos _⟩ x hx, fun i x hx => ?_⟩
    obtain ⟨i, hi⟩ := i
    exact h ⟨i + 1, Nat.succ_lt_succ hi⟩ x hx
  · rintro ⟨h0, h⟩ ⟨i, hi⟩ x hx
    cases i with
    | zero => exact h0 x hx
    | succ i => exact h ⟨i, Nat.lt_of_succ_lt_succ hi⟩ x hx

/-- `CentersMiss` on a concatenation (the composites `Π_{ij}` of [Kol07, Definition 29]): the first
piece misses `U` and the second misses the preimage of `U` under the composite of the first. -/
theorem centersMiss_concat :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (T : BlowUpSequence S.last) (U : Set X),
      CentersMiss S U → CentersMiss T (S.composite ⁻¹' U) → CentersMiss (S.concat T) U
  | _, nil _, _, _, _, hT => fun i x hx => hT i x hx
  | _, cons X D rest, T, U, hS, hT => by
    rw [concat_cons, centersMiss_cons_iff]
    obtain ⟨h0, hrest⟩ := (centersMiss_cons_iff D rest U).mp hS
    exact ⟨h0, centersMiss_concat rest T (D.blowUpπ ⁻¹' U) hrest hT⟩

/-- The prefix `S.take n` misses `U` when the centres of `S` of index `< n` do. -/
theorem centersMiss_take_of_centersMissBefore :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (U : Set X) (n : ℕ),
      CentersMissBefore S U n → CentersMiss (S.take n) U
  | _, nil _, _, _, _ => fun i => i.elim0
  | _, cons _ _ _, _, 0, _ => fun i => i.elim0
  | _, cons X D rest, U, n + 1, h => by
    rw [take_cons_succ, centersMiss_cons_iff]
    refine ⟨fun x hx => h ⟨0, Nat.succ_pos _⟩ (Nat.succ_pos _) x hx, ?_⟩
    refine centersMiss_take_of_centersMissBefore rest (D.blowUpπ ⁻¹' U) n
      fun i hi x hx => ?_
    exact h ⟨i.val + 1, Nat.succ_lt_succ i.2⟩ (Nat.succ_lt_succ hi) x hx

/-- The centres of a sequence of order `≥ m ≥ 1` for `(I, E)` lie over `V(I)` [Kol07, Definition
60] (`stageMap_mem_support_of_mem_center`), so they miss every set disjoint from `V(I)`. -/
theorem centersMiss_of_isOrderGeSeq {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f] {S : BlowUpSequence X}
    {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ} (hS : S.IsOrderGeSeq f I m E)
    (hm : 1 ≤ m) (U : Set X) (hU : ∀ x ∈ I.support, x ∉ U) : CentersMiss S U :=
  fun i _ hx => hU _ (stageMap_mem_support_of_mem_center f n hS hm i hx)

/-! ### The stop rule on a prefix -/

/-- The predicate `CenterContains` on a `cons` at a positive index is the predicate on the tail for
the strict transform. -/
theorem centerContains_cons_succ_iff (D : X.IdealSheafData) (rest : BlowUpSequence
    D.blowUp)
    (c : X.IdealSheafData) (i : ℕ) :
    CenterContains (cons X D rest) c (i + 1) ↔ CenterContains rest (c.strictTransform D) i :=
  ⟨fun ⟨hi, h⟩ => ⟨Nat.lt_of_succ_lt_succ hi, h⟩, fun ⟨hi, h⟩ => ⟨Nat.succ_lt_succ hi, h⟩⟩

/-- The predicate `CenterContains` at an index below `n` on the prefix `S.take n` is the predicate
on `S`. -/
theorem centerContains_take_iff :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (c : X.IdealSheafData) (n i : ℕ), i < n →
      (CenterContains (S.take n) c i ↔ CenterContains S c i)
  | _, nil _, _, _, _, _ => Iff.rfl
  | _, cons _ _ _, _, 0, _, hi => (Nat.not_lt_zero _ hi).elim
  | _, cons X D rest, c, n + 1, 0, _ => by
    rw [take_cons_succ]
    exact ⟨fun h => ⟨Nat.succ_pos _, h.2⟩, fun h => ⟨Nat.succ_pos _, h.2⟩⟩
  | _, cons X D rest, c, n + 1, i + 1, hi => by
    rw [take_cons_succ]
    exact (centerContains_cons_succ_iff D (rest.take n) c i).trans
      ((centerContains_take_iff rest (c.strictTransform D) n i (Nat.lt_of_succ_lt_succ hi)).trans
        (centerContains_cons_succ_iff D rest c i).symm)

/-! ### The first centre of `eraseEmpty` -/

/-- The deletion of empty blow-ups [Kol07, 32]: a point `q` of the first centre of
`S.eraseEmpty` is the image of a point `q'` of the first nonempty centre of `S`, at an index `n` all
of whose predecessors are empty centres. -/
theorem exists_mem_center_support_of_eraseEmpty_eq_cons :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) {D₀ : X.IdealSheafData}
      {rest₀ : BlowUpSequence D₀.blowUp}, S.eraseEmpty = cons X D₀ rest₀ →
      ∀ {q : X}, q ∈ D₀.support →
      ∃ (n : ℕ) (hn : n < S.length) (q' : S.stage ⟨n, Nat.lt_succ_of_lt hn⟩),
        q' ∈ (S.center ⟨n, hn⟩).support ∧ S.stageMap ⟨n, Nat.lt_succ_of_lt hn⟩ q' = q ∧
          ∀ i (hi : i < n), S.center ⟨i, lt_trans hi hn⟩ = ⊤
  | _, nil X, _, _, h, _, _ => by
    have h0 : (nil X).eraseEmpty = nil X := rfl
    rw [h0] at h
    cases h
  | _, cons X D rest, D₀, rest₀, h, q, hq => by
    classical
    by_cases hD : D = ⊤
    · have := isIso_blowUpπ_of_eq_top hD
      rw [eraseEmpty_cons_of_eq_top rest hD] at h
      obtain ⟨D₁, rest₁, h₁, hD₁⟩ := exists_cons_of_pullback_eq_cons _ _ h
      have hq' : inv D.blowUpπ q ∈ D₁.support := by
        rw [← hD₁, mem_support_comap_iff_apply] at hq
        exact hq
      obtain ⟨n, hn, q', hq'c, hq'm, hbefore⟩ :=
        exists_mem_center_support_of_eraseEmpty_eq_cons rest h₁ hq'
      refine ⟨n + 1, Nat.succ_lt_succ hn, q', hq'c, ?_, ?_⟩
      · change D.blowUpπ (rest.stageMap ⟨n, Nat.lt_succ_of_lt hn⟩ q') = q
        rw [hq'm, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
        rfl
      · intro i hi
        cases i with
        | zero => exact hD
        | succ i => exact hbefore i (Nat.lt_of_succ_lt_succ hi)
    · rw [eraseEmpty_cons_of_ne_top rest hD] at h
      obtain ⟨e, -⟩ := cons_inj h
      subst e
      exact ⟨0, Nat.succ_pos _, q, hq, rfl, fun i hi => (Nat.not_lt_zero _ hi).elim⟩

/-! ### Sequences all of whose centres are empty -/

/-- Along a sequence all of whose centres are empty the marked transform of `K` is its inverse
image under the stage map (`markedTransform_top_left` at every step). -/
theorem markedTransformSeq_eq_comap_of_forall_center_eq_top :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X), (∀ i, S.center i = ⊤) →
      ∀ (K : X.IdealSheafData) (m : ℕ) (i : Fin (S.length + 1)),
        S.markedTransformSeq K m i = K.comap (S.stageMap i)
  | _, nil X, _, K, _, ⟨0, _⟩ => by
    change K = K.comap (𝟙 X)
    simp
  | _, nil _, _, _, _, ⟨j + 1, hj⟩ => absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero j)
  | _, cons X _ _, _, K, _, ⟨0, _⟩ => by
    change K = K.comap (𝟙 X)
    simp
  | _, cons X D rest, h, K, m, ⟨j + 1, hj⟩ => by
    have hD : D = ⊤ := h ⟨0, Nat.succ_pos _⟩
    have ih := markedTransformSeq_eq_comap_of_forall_center_eq_top rest (fun i => h i.succ)
      (K.markedTransform D m) m ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    change rest.markedTransformSeq (K.markedTransform D m) m ⟨j, Nat.lt_of_succ_lt_succ hj⟩ =
      K.comap (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ)
    rw [ih, comap_comp]
    congr 1
    subst hD
    exact markedTransform_top_left K m

/-- Along a sequence all of whose centres are empty the strict transform of `K` is its inverse
image under the stage map (`strictTransform_top_left` at every step). -/
theorem strictTransformSeq_eq_comap_of_forall_center_eq_top :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X), (∀ i, S.center i = ⊤) →
      ∀ (K : X.IdealSheafData) (i : Fin (S.length + 1)),
        S.strictTransformSeq K i = K.comap (S.stageMap i)
  | _, nil X, _, K, ⟨0, _⟩ => by
    change K = K.comap (𝟙 X)
    simp
  | _, nil _, _, _, ⟨j + 1, hj⟩ => absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero j)
  | _, cons X _ _, _, K, ⟨0, _⟩ => by
    change K = K.comap (𝟙 X)
    simp
  | _, cons X D rest, h, K, ⟨j + 1, hj⟩ => by
    have hD : D = ⊤ := h ⟨0, Nat.succ_pos _⟩
    have ih := strictTransformSeq_eq_comap_of_forall_center_eq_top rest (fun i => h i.succ)
      (K.strictTransform D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩
    change rest.strictTransformSeq (K.strictTransform D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩ =
      K.comap (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hj⟩ ≫ D.blowUpπ)
    rw [ih, comap_comp]
    congr 1
    subst hD
    exact strictTransform_top_left K

/-- Along a sequence all of whose centres are empty, the total transform of a family all of whose
members are empty has only empty members (`strictTransform_top_right`, `exceptionalDivisor_top`). -/
theorem totalTransformSeq_component_eq_top_of_forall_center_eq_top :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X), (∀ i, S.center i = ⊤) →
      ∀ (E : DivisorFamily X), (∀ e, E.component e = ⊤) →
        ∀ (i : Fin (S.length + 1)) (e : (S.totalTransformSeq E i).ι),
          (S.totalTransformSeq E i).component e = ⊤
  | _, nil _, _, _, hE, ⟨0, _⟩, e => hE e
  | _, nil _, _, _, _, ⟨j + 1, hj⟩, _ => absurd (Nat.lt_of_succ_lt_succ hj) (Nat.not_lt_zero j)
  | _, cons _ _ _, _, _, hE, ⟨0, _⟩, e => hE e
  | _, cons X D rest, h, E, hE, ⟨j + 1, hj⟩, e => by
    have hD : D = ⊤ := h ⟨0, Nat.succ_pos _⟩
    subst hD
    refine totalTransformSeq_component_eq_top_of_forall_center_eq_top rest (fun i => h i.succ)
      (E.totalTransform ⊤) ?_ ⟨j, Nat.lt_of_succ_lt_succ hj⟩ e
    intro e'
    cases e' with
    | inl j' =>
      change (E.component j').strictTransform ⊤ = ⊤
      rw [hE j']
      exact strictTransform_top_right ⊤
    | inr _ =>
      change (⊤ : X.IdealSheafData).exceptionalDivisor = ⊤
      exact exceptionalDivisor_top

/-! ### Empty centres of a pullback -/

section Pullback

variable {Y : Scheme.{u}}

/-- The pullback of a blow-up sequence [Kol07, Definition 30, 30.1], read pointwise: a centre of the
pullback along a flat `h` is empty if and only if no point of the centre of `S` lies over the image
of `h` (`center_pullback_mk`, `range_pullbackStageHom`). -/
theorem center_pullback_eq_top_iff (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h] (j : ℕ)
    (hj : j < S.length) :
    (S.pullback h).center (S.pullbackCenterIdx h ⟨j, hj⟩) = ⊤ ↔
      ∀ x : S.stage ⟨j, Nat.lt_succ_of_lt hj⟩, x ∈ (S.center ⟨j, hj⟩).support →
        S.stageMap ⟨j, Nat.lt_succ_of_lt hj⟩ x ∉ Set.range h := by
  rw [center_pullback_mk, ← support_eq_bot_iff]
  constructor
  · intro hsup x hx hxr
    have hxr' : x ∈ Set.range (S.pullbackStageHom h ⟨j, Nat.lt_succ_of_lt hj⟩) := by
      rw [range_pullbackStageHom]
      exact hxr
    obtain ⟨y, rfl⟩ := hxr'
    have hy := (mem_support_comap_iff_apply (S.center ⟨j, hj⟩) _ y).mpr hx
    rw [hsup, ← SetLike.mem_coe, Closeds.coe_bot] at hy
    exact hy
  · intro hmiss
    rw [eq_bot_iff]
    intro y hy
    have hx := (mem_support_comap_iff_apply (S.center ⟨j, hj⟩) _ y).mp hy
    refine (hmiss _ hx ?_).elim
    rw [← Scheme.Hom.comp_apply, pullbackStageHom_stageMap_mk,
      Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩

/-- All centres of the pullback along a flat `h` are empty when the centres of `S` miss the image
of `h`. -/
theorem forall_center_pullback_eq_top_of_centersMiss (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (hmiss : CentersMiss S (Set.range h)) : ∀ i, (S.pullback h).center i = ⊤ := by
  intro i
  obtain ⟨j, hj⟩ := i
  have hj' : j < S.length := by rwa [length_pullback] at hj
  have e : (⟨j, hj⟩ : Fin (S.pullback h).length) = S.pullbackCenterIdx h ⟨j, hj'⟩ := Fin.ext rfl
  rw [e, center_pullback_eq_top_iff]
  exact fun x hx => hmiss ⟨j, hj'⟩ x hx

/-- The centres of `S` of index `< n` miss the image of `h` when the corresponding centres of the
pullback are empty. -/
theorem centersMissBefore_of_forall_center_pullback_eq_top (S : BlowUpSequence X) (h : Y ⟶ X)
    [Flat h] (n : ℕ)
    (htop : ∀ i, i < n → ∀ hi' : i < S.length,
      (S.pullback h).center (S.pullbackCenterIdx h ⟨i, hi'⟩) = ⊤) :
    CentersMissBefore S (Set.range h) n := by
  intro i hi x hx
  obtain ⟨j, hj⟩ := i
  exact (center_pullback_eq_top_iff S h j hj).mp (htop j hi hj) x hx

end Pullback

/-! ### Generic points along an open immersion -/

/-- The support of an integral closed subscheme is an irreducible closed subset. -/
theorem isIrreducible_support_of_isIntegral (Z : X.IdealSheafData) [IsIntegral Z.subscheme] :
    IsIrreducible (Z.support : Set X) := by
  have hemb : Topology.IsEmbedding Z.subschemeι.base :=
    Z.subschemeι.isClosedEmbedding.isEmbedding
  suffices h : IrreducibleSpace Z.subscheme by
    rwa [Homeomorph.irreducibleSpace_iff hemb.toHomeomorph, ← isIrreducible_iff_irreducibleSpace,
      range_subschemeι] at h
  infer_instance

/-- The generic point seen on an open [Kol07, Corollary 22, proof]: for an open immersion `j` and an
irreducible `V(Z)`, the image of a generic point of `j⁻¹ V(Z)` (`Closeds.genericPoints`) is the
generic point of `V(Z)`. The generic point `ξ` of `V(Z)` generalises `j w`, so it lies in the open
image of `j`, and an open embedding reflects specialisation. -/
theorem isGenericPoint_of_mem_genericPoints_comap {W : Scheme.{u}} (j : W ⟶ X) [IsOpenImmersion j]
    (Z : X.IdealSheafData) (hirr : IsIrreducible (Z.support : Set X)) {w : W}
    (hw : w ∈ (Z.comap j).support.genericPoints) : IsGenericPoint (j w) (Z.support : Set X) := by
  have hξ : IsGenericPoint hirr.genericPoint (Z.support : Set X) :=
    hirr.isGenericPoint_genericPoint Z.support.isClosed
  have hjw : j w ∈ Z.support := (mem_support_comap_iff_apply Z j w).mp hw.1
  have hspec : hirr.genericPoint ⤳ j w := hξ.specializes hjw
  have hoe : Topology.IsOpenEmbedding j := j.isOpenEmbedding
  obtain ⟨w', hw'⟩ : hirr.genericPoint ∈ Set.range j := hspec.mem_open hoe.isOpen_range ⟨w, rfl⟩
  have h1 : j w' ⤳ j w := by
    rw [hw']
    exact hspec
  have h2 : w' ⤳ w := hoe.toIsEmbedding.toIsInducing.specializes_iff.mp h1
  have hw'mem : w' ∈ (Z.comap j).support := by
    rw [mem_support_comap_iff_apply, hw']
    exact hξ.mem
  have heq : w' = w := hw.2 hw'mem h2
  rw [← heq, hw']
  exact hξ

end Hironaka.Resolution
