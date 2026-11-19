/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces
import Hironaka.Algebra.RegularSmooth.SchemeForms
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransforms
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The nerve of a realising piece family: faces, validity, the centres

The combinatorial layer of the geometric realisation. For a piece family `Φ` realising an snc
boundary `E` (`Realizes E e`) on a smooth `k`-scheme of dimension `≤ n`, the faces of its nerve
are the sets of components with a common point, and they satisfy the six invariants of the
combinatorial state, so that `toState` is defined (`valid_of_realizes`):

* `mem_nerve_iff`: a face is a nonempty set of live components with a common point;
* `injOn_label_of_mem_nerve`: the components of a face have distinct labels, because two pieces
  of one label are disjoint (`Realizes.disjoint`);
* `card_le_of_mem_nerve`: a face has at most `n` elements. Its labels are labels of members
  through a common point `x`, at most `dim 𝒪_{X,x}` of them by the injective assignment of
  coordinates in [Kol07, Definition 24] (3), and `dim 𝒪_{X,x} ≤ n` on a smooth scheme of
  relative dimension `≤ n`;
* `support_faceIdeal`, `support_centerOf`, `centerOf_ne_top`: the centre of a finset of faces
  is the ideal sheaf of the union of their intersections `Z_P`, nonempty for faces of the nerve
  (so the blow-ups of the geometric Step 3 are never the empty blow-ups of [Kol07, 32]);
* `eq_of_mem_faceSet_of_isCenter`: the intersections `Z_P`, `P ∈ S`, of a centre of the state
  are pairwise disjoint. Two faces of a centre through a common point are equal
  (`MonomialState.eq_of_isCenter_of_subset`, the faces of a centre having a common label set).

Not in the sources; these are the facts that connect the combinatorial state to the geometry.
The local structure of the pieces and centres is
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Local.lean`.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Scheme Scheme.IdealSheafData

namespace Hironaka.Monomial.PieceFamily

variable {k : Type u} [Field k] {X : Scheme.{u}} (Φ : PieceFamily X)

/-! ### Faces -/

/-- A face set is nonempty iff the components have a common point. -/
theorem faceSet_ne_bot_iff (T : Finset ℕ) :
    Φ.faceSet T ≠ ⊥ ↔ ∃ x : X, ∀ c ∈ T, x ∈ Φ.piece c := by
  rw [← Closeds.coe_nonempty]
  exact exists_congr fun x => by rw [SetLike.mem_coe, mem_faceSet]

/-- The nerve consists of the nonempty sets of live components with a common point. -/
theorem mem_nerve_iff (T : Finset ℕ) :
    T ∈ Φ.nerve ↔
      T ⊆ Finset.range Φ.nextComp ∧ T.Nonempty ∧ ∃ x : X, ∀ c ∈ T, x ∈ Φ.piece c := by
  rw [mem_nerve, faceSet_ne_bot_iff]

theorem exists_mem_faceSet_of_mem_nerve {T : Finset ℕ} (hT : T ∈ Φ.nerve) :
    ∃ x : X, x ∈ Φ.faceSet T :=
  Closeds.coe_nonempty.mpr (Φ.mem_nerve.mp hT).2.2

theorem lt_nextComp_of_mem_nerve {T : Finset ℕ} (hT : T ∈ Φ.nerve) {c : ℕ} (hc : c ∈ T) :
    c < Φ.nextComp :=
  Finset.mem_range.mp ((Φ.mem_nerve.mp hT).1 hc)

theorem mem_nerve_of_mem_faceSet {T : Finset ℕ} (hT : T ⊆ Finset.range Φ.nextComp)
    (hne : T.Nonempty) {x : X} (hx : x ∈ Φ.faceSet T) : T ∈ Φ.nerve :=
  Φ.mem_nerve.mpr ⟨hT, hne, Closeds.coe_nonempty.mp ⟨x, hx⟩⟩

/-! ### Realising families: labels and the dimension bound -/

variable {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel}

/-- Two distinct pieces of one label have no common point (`Realizes.disjoint`). -/
theorem not_mem_piece_of_label_eq (hΦ : Φ.Realizes E e) {c c' : ℕ} (hc : c < Φ.nextComp)
    (hc' : c' < Φ.nextComp) (hne : c ≠ c') (hlab : Φ.label c = Φ.label c') {x : X}
    (hx : x ∈ Φ.piece c) (hx' : x ∈ Φ.piece c') : False := by
  have hd := hΦ.disjoint c c' hc hc' hne hlab
  have hmem : x ∈ Φ.piece c ⊓ Φ.piece c' := by
    rw [← SetLike.mem_coe, Closeds.coe_inf]
    exact ⟨hx, hx'⟩
  have hbot := hd.le_bot hmem
  rw [← SetLike.mem_coe, Closeds.coe_bot] at hbot
  exact hbot

/-- A face of the nerve has injective labels: its components have a common point, and two
pieces of one label are disjoint. -/
theorem injOn_label_of_mem_nerve (hΦ : Φ.Realizes E e) {T : Finset ℕ} (hT : T ∈ Φ.nerve) :
    Set.InjOn Φ.label ↑T := by
  intro c hc c' hc' hlab
  by_contra hne
  obtain ⟨x, hx⟩ := Φ.exists_mem_faceSet_of_mem_nerve hT
  exact Φ.not_mem_piece_of_label_eq hΦ (Φ.lt_nextComp_of_mem_nerve hT hc)
    (Φ.lt_nextComp_of_mem_nerve hT hc') hne hlab (Φ.mem_faceSet.mp hx c hc)
    (Φ.mem_faceSet.mp hx c' hc')

/-- A point of a piece lies on the member of the piece's label. -/
theorem mem_support_component_of_mem_piece (hΦ : Φ.Realizes E e) {c : ℕ} (hc : c < Φ.nextComp)
    {x : X} (hx : x ∈ Φ.piece c) :
    x ∈ (E.component (e.symm ⟨Φ.label c, Φ.label_lt c hc⟩)).support := by
  classical
  rw [hΦ.support_eq]
  refine Finset.le_sup (f := Φ.piece) (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hc, ?_⟩) hx
  simp

open scoped Classical in
/-- The number of members of an snc boundary through a point is at most the dimension of the
local ring there (the injective assignment of coordinates, [Kol07, Definition 24] (3)), which is
at most the relative dimension of a smooth scheme over a perfect field. -/
theorem card_filter_mem_support_le [PerfectField k] (f : X ⟶ Spec (CommRingCat.of k))
    {n' : ℕ} [SmoothOfRelativeDimension n' f] (hE : E.IsSnc) (x : X) :
    (Finset.univ.filter fun i : E.ι => x ∈ (E.component i).support).card ≤ n' := by
  classical
  obtain ⟨nx, z, ⟨-, hz2⟩, c, hcinj, -⟩ := hE.2 x
  have h2 : (Finset.univ.filter fun i : E.ι => x ∈ (E.component i).support).card ≤ nx := by
    rw [← Fintype.card_subtype, ← Fintype.card_fin nx]
    exact Fintype.card_le_of_injective c hcinj
  have hdim := Scheme.ringKrullDim_stalk_add_trdeg_residueField_of_smoothOfRelativeDimension
    f n' x
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ (n' : WithBot ℕ∞) := by
    rw [← hdim]
    exact le_add_of_nonneg_right (WithBot.coe_nonneg.mpr zero_le)
  rw [← hz2] at hle
  have h3 : nx ≤ n' := by exact_mod_cast hle
  omega

/-- A face of the nerve of a family realising an snc boundary on a scheme of dimension `≤ n` has
at most `n` elements: at most `n = dim X` members pass through a point, by `c(i) ≠ c(i')` in
[Kol07, Definition 24] (3). -/
theorem card_le_of_mem_nerve (f : X ⟶ Spec (CommRingCat.of k)) [PerfectField k] (hE : E.IsSnc)
    (hΦ : Φ.Realizes E e) {n : ℕ} (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f) {T : Finset ℕ}
    (hT : T ∈ Φ.nerve) : T.card ≤ n := by
  classical
  obtain ⟨n', hn'n, hsm⟩ := hn
  obtain ⟨x, hx⟩ := Φ.exists_mem_faceSet_of_mem_nerve hT
  -- the labels of `T` are labels of members through `x`
  have hlab : T.image Φ.label ⊆
      (Finset.univ.filter fun i : E.ι => x ∈ (E.component i).support).image
        fun i => (e i : ℕ) := by
    intro l hl
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hl
    have hlt := Φ.lt_nextComp_of_mem_nerve hT hc
    refine Finset.mem_image.mpr ⟨e.symm ⟨Φ.label c, Φ.label_lt c hlt⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Φ.mem_support_component_of_mem_piece hΦ hlt (Φ.mem_faceSet.mp hx c hc)⟩, by simp⟩
  have h1 : T.card ≤ (Finset.univ.filter fun i : E.ι => x ∈ (E.component i).support).card := by
    rw [← Finset.card_image_of_injOn (Φ.injOn_label_of_mem_nerve hΦ hT)]
    exact (Finset.card_le_card hlab).trans Finset.card_image_le
  exact h1.trans ((card_filter_mem_support_le f hE x).trans hn'n)

/-- Under the geometric hypotheses the family's data are `Valid`: faces are nonempty sets of
live components (`mem_nerve`), labels are below `nextLabel` (`label_lt`), the nerve is
down-closed (a subset of a face has a larger face set, `faceSet_anti`), faces have at most `n`
elements (`card_le_of_mem_nerve`) and injective labels (`injOn_label_of_mem_nerve`). -/
theorem valid_of_realizes (f : X ⟶ Spec (CommRingCat.of k)) [PerfectField k] (hE : E.IsSnc)
    (hΦ : Φ.Realizes E e) {n m : ℕ} (hm : 1 ≤ m) (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f) :
    Φ.IsValid n m := by
  refine ⟨hm, fun T hT => (Φ.mem_nerve.mp hT).2.1,
    fun T hT c hc => Φ.lt_nextComp_of_mem_nerve hT hc, fun c _ hc => Φ.label_lt c hc, ?_,
    fun T hT => Φ.card_le_of_mem_nerve f hE hΦ hn hT, fun T hT => Φ.injOn_label_of_mem_nerve hΦ hT⟩
  intro T hT T' hT' hne
  obtain ⟨hTr, -, hTb⟩ := Φ.mem_nerve.mp hT
  have hsub := Finset.mem_powerset.mp hT'
  exact Φ.mem_nerve.mpr ⟨hsub.trans hTr, hne,
    fun h => hTb (le_bot_iff.mp (h ▸ Φ.faceSet_anti hsub))⟩

/-! ### Centres: supports -/

/-- The support of the ideal of a face is its face set `Z_P`. -/
theorem support_faceIdeal (P : Finset ℕ) : (Φ.faceIdeal P).support = Φ.faceSet P := by
  unfold faceIdeal faceSet
  simp only [IdealSheafData.support_iSup, Hironaka.Sequence.support_vanishingIdeal_eq]
  rw [Finset.inf_eq_iInf]

/-- The support of the center of a finset of faces is the union of their intersections. -/
theorem support_centerOf (S : Finset (Finset ℕ)) :
    (Φ.centerOf S).support = S.sup Φ.faceSet := by
  unfold centerOf
  rw [Hironaka.Sequence.support_finset_prod, Finset.sup_eq_iSup]
  exact iSup_congr fun P => iSup_congr fun _ => Φ.support_faceIdeal P

theorem mem_support_centerOf_iff (S : Finset (Finset ℕ)) (x : X) :
    x ∈ (Φ.centerOf S).support ↔ ∃ P ∈ S, x ∈ Φ.faceSet P := by
  rw [support_centerOf, mem_finset_sup_iff]

theorem faceSet_le_support_centerOf {S : Finset (Finset ℕ)} {P : Finset ℕ} (hP : P ∈ S) :
    Φ.faceSet P ≤ (Φ.centerOf S).support := by
  rw [support_centerOf]
  exact Finset.le_sup (f := Φ.faceSet) hP

/-- The centre of a nonempty finset of faces of the nerve is a nonempty closed subscheme: the
blow-ups of the procedure are not the empty blow-ups of [Kol07, 32]. -/
theorem centerOf_ne_top {S : Finset (Finset ℕ)} (hS : S ⊆ Φ.nerve) (hne : S.Nonempty) :
    Φ.centerOf S ≠ ⊤ := by
  intro h
  obtain ⟨P, hP⟩ := hne
  have hPb : Φ.faceSet P ≠ ⊥ := (Φ.mem_nerve.mp (hS hP)).2.2
  have hle := Φ.faceSet_le_support_centerOf hP
  rw [h, IdealSheafData.support_top] at hle
  exact hPb (le_bot_iff.mp hle)

/-! ### Centres of the state: the faces are pairwise disjoint -/

variable {n m : ℕ} {hV : Φ.IsValid n m}

/-- Two faces of a centre of the state through a common point are equal: their union is a face,
and `MonomialState.eq_of_isCenter_of_subset` applies (the faces of a centre have a common label
set and faces have injective labels). -/
theorem eq_of_mem_faceSet_of_isCenter {S : Finset (Finset ℕ)}
    (hS : (Φ.toState n m hV).IsCenter S) {P Q : Finset ℕ} (hP : P ∈ S) (hQ : Q ∈ S) {x : X}
    (hxP : x ∈ Φ.faceSet P) (hxQ : x ∈ Φ.faceSet Q) : P = Q := by
  have hPN : P ∈ Φ.nerve := hS.1 hP
  have hQN : Q ∈ Φ.nerve := hS.1 hQ
  have hT : P ∪ Q ∈ Φ.nerve := by
    refine Φ.mem_nerve_of_mem_faceSet (Finset.union_subset (Φ.mem_nerve.mp hPN).1
      (Φ.mem_nerve.mp hQN).1) ((Φ.mem_nerve.mp hPN).2.1.mono Finset.subset_union_left) (x := x) ?_
    rw [Φ.mem_faceSet]
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · exact Φ.mem_faceSet.mp hxP c hc
    · exact Φ.mem_faceSet.mp hxQ c hc
  exact MonomialState.eq_of_isCenter_of_subset (st := Φ.toState n m hV) (S := S) hS hP hQ hT
    Finset.subset_union_left Finset.subset_union_right

/-- A point of the centre of a centre of the state lies on exactly one of its faces. -/
theorem existsUnique_mem_faceSet_of_isCenter {S : Finset (Finset ℕ)}
    (hS : (Φ.toState n m hV).IsCenter S) {x : X} (hx : x ∈ (Φ.centerOf S).support) :
    ∃! P, P ∈ S ∧ x ∈ Φ.faceSet P := by
  obtain ⟨P, hP, hxP⟩ := (Φ.mem_support_centerOf_iff S x).mp hx
  exact ⟨P, ⟨hP, hxP⟩, fun Q ⟨hQ, hxQ⟩ => Φ.eq_of_mem_faceSet_of_isCenter hS hQ hP hxQ hxP⟩

end Hironaka.Monomial.PieceFamily
