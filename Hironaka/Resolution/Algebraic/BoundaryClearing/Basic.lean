/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
public import Hironaka.Resolution.Algebraic.Balanced.Basic
import Hironaka.Resolution.Algebraic.Balanced.Order
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.Snc.Dictionary
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The data `BD_{n,m,j}` unfolded, and the closed set `Z_{-1}`

**The data.** `BDData n m j` is a structure; the lemmas here read its fields as
Kollár prints [Kol07, Lemma 102]: the value on a triple of the class is a smooth blow-up sequence
of order `m` starting with `(X, I, E)` (`seq_isOrderSeq`, the functor's own field), it contains no
empty blow-up (`seq_noEmptyCenters`, [Kol07, 32]), and clause (1), `cosupp(I_r, m)` disjoint from
`Π^{-1}_* E^j`, says that at every point of the birational transform of `E^j` the final ideal has
order `< m` (`ord_lt_of_mem_strictTransformSeq`). The three unfolding lemmas of the domain are
definitional.

**The closed set `Z_{-1}`.** `Zminus1 I m D` is the vanishing ideal sheaf of `⨆ η, closure {η}`
over the generic points `η` of `V(D)` with `ord_η I ≥ m`. On a Noetherian space the generic points
are finitely many (`Closeds.genericPoints_finite`, `Hironaka/Scheme/Snc/Dictionary.lean`), so the
`⨆` is a finite union of closures, itself closed, and a point lies on `Z_{-1}` iff some selected
generic point specializes to it (`mem_support_Zminus1_iff`: Kollár's union of the irreducible
components of `E^j` contained in `cosupp(I, m)`; a component is contained in `cosupp(I, m)` iff
its generic point is, since the order can only grow under specialization,
`Hironaka/Scheme/IdealSheaf/Order/Specialization.lean`). Hence `Z_{-1} ⊆ cosupp(I, m)`
(`support_Zminus1_subset_cosupp`) and `Z_{-1} ⊆ E^j` (`support_Zminus1_le_support`;
`support_Zminus1_le` for a triple). With `max-ord I = m` the selected components are exactly those
along which `I` has order `m` (`mem_support_Zminus1_iff_ord_eq`: `ord_η I ≤ max-ord I`).

**The dichotomy of a D-balanced ideal.** Kollár's remark after [Kol07, Definition 83], that a
D-balanced ideal with `max-ord I = m` has order `0` or `m` at every point, is
`IsDBalanced.ord_eq_zero_or_eq` (`Hironaka/Resolution/Algebraic/Balanced/Order.lean`); at the
generic points of the components of `E^j` it is `ord_eq_zero_or_eq_of_mem_genericPoints`.

Used by `Center.lean` and, outside this directory, by
`Hironaka/Resolution/Algebraic/Wlo05/Embedded.lean` and
`Hironaka/Resolution/Algebraic/Wlo05/EmbeddedComponentTools.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme.BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka

/-! ### The domain and the data unfolded -/

section Data

variable {k : Type u} [Field k]

/-- `HasDimLE T n` unfolds to some `HasDim n'` with `n' ≤ n`. -/
theorem _root_.AlgebraicGeometry.Triple.hasDimLE_iff (T : Triple k)
    (n : ℕ) : T.HasDimLE n ↔ ∃ n' ≤ n, T.HasDim n' :=
  Iff.rfl

/-- The domain of `BD_{n,m,j}` unfolds to its three conditions. -/
theorem _root_.AlgebraicGeometry.Triple.bdClass_iff (n m j : ℕ) (T : Triple k) :
    Triple.BDClass n m j T ↔ T.HasDimLE n ∧ T.I.maxOrd ≤ (m : ℕ∞) ∧ j < Fintype.card T.E.ι :=
  Iff.rfl

/-- `E^j` is the component at position `j` of the linear order of the index set. -/
theorem _root_.AlgebraicGeometry.Scheme.DivisorFamily.nth_eq {X : Scheme.{u}}
    (E : Scheme.DivisorFamily X)
    (j : Fin (Fintype.card E.ι)) : E.nth j = E.component (monoEquivOfFin E.ι rfl j) :=
  rfl

variable [CharZero k]

namespace BDData

variable {n m j : ℕ}

/-- The value of the data on a triple of the class is a smooth blow-up sequence of order `m`
starting with `(X, I, E)` ([Kol07, Lemma 102]): the functor's own field. -/
theorem seq_isOrderSeq (B : BDData n m j) (T : Triple k) (hT : Triple.BDClass n m j T) :
    ((B.functor k).seq T hT).IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m :=
  (B.functor k).isOrderSeq T hT

/-- The output contains no empty blow-up ([Kol07, 32]). -/
theorem seq_noEmptyCenters (B : BDData n m j) (T : Triple k) (hT : Triple.BDClass n m j T) :
    ((B.functor k).seq T hT).NoEmptyCenters :=
  (B.functor k).noEmptyCenters T hT

/-- At every point of the birational transform of `E^j` on `X_r` the final induced ideal has order
`< m`: the pointwise form of clause (1) of [Kol07, Lemma 102],
`cosupp(I_r, m) ∩ Π^{-1}_* E^j = ∅`. -/
theorem ord_lt_of_mem_strictTransformSeq (B : BDData n m j) (T : Triple k)
    (hT : Triple.BDClass n m j T) {x : ((B.functor k).seq T hT).stage (Fin.last _)}
    (hx : x ∈ (((B.functor k).seq T hT).strictTransformSeq (T.E.nth ⟨j, hT.2.2⟩)
      (Fin.last _)).support) :
    (((B.functor k).seq T hT).weakTransformSeq T.I (Fin.last _)).ord x < m := by
  by_contra hle
  rw [not_lt] at hle
  exact Set.disjoint_left.mp (B.disjoint_cosupp k T hT) hle hx

end BDData

end Data

end Hironaka

namespace Hironaka.BD

variable {X : Scheme.{u}}

/-! ### The closed set underlying `Z_{-1}` -/

/-- On a Noetherian space the closed set of `Z_{-1}` is the union of the closures of the selected
generic points, finitely many (`Closeds.genericPoints_finite`), so the `⨆` of `Closeds` is the
plain union. -/
theorem coe_support_Zminus1 [NoetherianSpace X] (I : X.IdealSheafData) (m : ℕ)
    (D : X.IdealSheafData) :
    ((Zminus1 I m D).support : Set X) =
      {x | ∃ η ∈ D.support.genericPoints, (m : ℕ∞) ≤ I.ord η ∧ η ⤳ x} := by
  have : Finite {η : X // η ∈ D.support.genericPoints ∧ (m : ℕ∞) ≤ I.ord η} :=
    Finite.of_injective (fun η => (⟨η.1, η.2.1⟩ : D.support.genericPoints)) fun a b hab =>
      Subtype.ext (by simpa using congrArg Subtype.val hab)
  let _ : Fintype {η : X // η ∈ D.support.genericPoints ∧ (m : ℕ∞) ≤ I.ord η} := Fintype.ofFinite _
  rw [Zminus1, Scheme.IdealSheafData.coe_support_vanishingIdeal, ← Finset.sup_univ_eq_iSup,
      Closeds.coe_finset_sup]
  ext x
  simp only [Finset.sup_univ_eq_iSup, Function.comp, Set.iSup_eq_iUnion, Set.mem_iUnion,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨⟨η, hη, hm⟩, hx⟩
    exact ⟨η, hη, hm, specializes_iff_mem_closure.mpr hx⟩
  · rintro ⟨η, hη, hm, hx⟩
    exact ⟨⟨η, hη, hm⟩, specializes_iff_mem_closure.mp hx⟩

/-- `Z_{-1} ⊆ V(D)`: the selected components are components of `V(D)`. -/
theorem support_Zminus1_le_support (I : X.IdealSheafData) (m : ℕ) (D : X.IdealSheafData) :
    (Zminus1 I m D).support ≤ D.support := by
  have hZ : (⨆ η : {η : X // η ∈ D.support.genericPoints ∧ (m : ℕ∞) ≤ I.ord η},
      Closeds.closure {(η : X)}) ≤ D.support :=
    iSup_le fun η => Closeds.closure_le.mpr (Set.singleton_subset_iff.mpr η.2.1.1)
  rw [← SetLike.coe_subset_coe, Zminus1, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact SetLike.coe_subset_coe.mpr hZ

end Hironaka.BD

namespace Hironaka.BD

open Triple

/-- A triple's ambient scheme is a Noetherian space: finite type and quasi-compact over the field
(`Scheme.Hom.isNoetherian_of_field`, `Hironaka/Scheme/IdealSheaf/Order/Constructible.lean`). -/
theorem noetherianSpace_triple {k : Type u} [Field k] (T : Triple k) : NoetherianSpace T.X.left :=
  haveI : IsNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isNoetherian_of_field
  inferInstance

variable {k : Type u} [Field k]

/-- A point lies on `Z_{-1}` iff it lies on the closure of a generic point of `E^j` of order `≥ m`
(Kollár's description of `Z_{-1}` in the proof of [Kol07, Lemma 102]). -/
theorem mem_support_Zminus1_iff (T : Triple k) (m : ℕ) (j : T.E.ι) (x : T.X.left) :
    x ∈ (Zminus1 T.I m (T.E.component j)).support ↔
      ∃ η ∈ (T.E.component j).support.genericPoints, (m : ℕ∞) ≤ T.I.ord η ∧ η ⤳ x := by
  have := noetherianSpace_triple T
  exact Set.ext_iff.mp (coe_support_Zminus1 T.I m (T.E.component j)) x

/-- `Z_{-1} ⊆ cosupp(I, m)`: the order can only grow under specialization. -/
theorem support_Zminus1_subset_cosupp [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι) :
    ((Zminus1 T.I m (T.E.component j)).support : Set T.X.left) ⊆ {x | (m : ℕ∞) ≤ T.I.ord x} := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  intro x hx
  obtain ⟨η, -, hm, hηx⟩ := (mem_support_Zminus1_iff T m j x).mp hx
  exact hm.trans (Scheme.IdealSheafData.ord_le_ord_of_specializes T.I
    (T.X.left ↘ Spec (.of k)) n hηx)

/-- `Z_{-1} ⊆ E^j`. -/
theorem support_Zminus1_le (T : Triple k) (m : ℕ) (j : T.E.ι) :
    (Zminus1 T.I m (T.E.component j)).support ≤ (T.E.component j).support :=
  support_Zminus1_le_support T.I m (T.E.component j)

/-- For D-balanced `I` with `max-ord I = m`, `ord_{E^{jk}} I ∈ {0, m}` for every irreducible
component `E^{jk}` of `E^j` (the remark after [Kol07, Definition 83]). The hypothesis `hη` is part
of the statement so that it reads as Kollár's remark about the components of `E^j`, the order along
a component being the order at its generic point, in the form `Transform.lean` uses; the proof does
not need it, because the dichotomy of a D-balanced ideal (`IsDBalanced.ord_eq_zero_or_eq`) holds
at every point, generic or not. -/
theorem ord_eq_zero_or_eq_of_mem_genericPoints [CharZero k] (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m) {η : T.X.left}
    (_hη : η ∈ (T.E.component j).support.genericPoints) : T.I.ord η = 0 ∨ T.I.ord η = m := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  exact hI.ord_eq_zero_or_eq (T.X.left ↘ Spec (.of k)) n hmax η

/-- With `max-ord I = m`, the components of `E^j` contained in `cosupp(I, m)` are exactly those
along which `I` has order `m`. -/
theorem mem_support_Zminus1_iff_ord_eq (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hmax : T.I.maxOrd = m) (x : T.X.left) :
    x ∈ (Zminus1 T.I m (T.E.component j)).support ↔
      ∃ η ∈ (T.E.component j).support.genericPoints, T.I.ord η = m ∧ η ⤳ x := by
  rw [mem_support_Zminus1_iff]
  constructor
  · rintro ⟨η, hη, hm, hηx⟩
    exact ⟨η, hη, le_antisymm (hmax ▸ T.I.le_maxOrd η) hm, hηx⟩
  · rintro ⟨η, hη, hm, hηx⟩
    exact ⟨η, hη, hm.ge, hηx⟩

end Hironaka.BD
