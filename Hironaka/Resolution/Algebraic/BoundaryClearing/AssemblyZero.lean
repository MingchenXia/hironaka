/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Assembly
import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.BoundaryClearing.FunctorialityBaseChange
import Hironaka.Resolution.Algebraic.BoundaryClearing.Transform
import Hironaka.Scheme.BlowUpSequence.BaseChange
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport
import Hironaka.Scheme.BlowUpSequence.TrivialCenter
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.Snc.AppendEmpty
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Lemma 102 at the mark `m = 0`

On `BDClass n 0 j` the ideal `I` is the unit ideal (`max-ord I ≤ 0`), so `cosupp(I, 0)` is all of
`X` and clause (1) of [Kol07, Lemma 102] asks that the birational transform of `E^j` be EMPTY at the
end. The functor `BD.zeroFunctor` (`Assembly.lean`) is `π_{-1}`, the blow-up of `Z_{-1}`, which at
mark `0` is the union of ALL components of `E^j`, with its empty blow-up deleted. Kollár's marks are
`≥ 1`, so this case is not in the source; this module proves its clauses:

* `eq_top_of_bdClass_zero`: `I = O_X` (`eq_top_of_maxOrd_le_zero`: every point of the support would
  have order `≥ 1`).
* `disjoint_cosupp_zeroFunctor` (clause (1)): every point of `E^j` lies in `Z_{-1}`
  (`support_component_subset_support_Zminus1_zero`: it specializes from a generic point of `E^j`,
  all of which are selected at mark `0`), so the saturation of `E^j` by `Z_{-1}` has empty support
  and the strict transform of `E^j` along `π_{-1}` is the unit ideal (`mem_support_saturate_iff`,
  `strictTransform_eq_comap_saturate` of `Transform.lean`). If `Z_{-1}` itself is the unit ideal
  then so is `E^j`, the blow-up is deleted and the sequence is empty; either way the final strict
  transform of `E^j` is the unit ideal, whose support is empty.
* `zeroFunctor_commutesWithSmooth`, `zeroFunctor_commutesWithBaseChange` (clause (2)): `Z_{-1}`
  pulls back along smooth morphisms and changes of fields (`Zminus1_pullback`,
  `Zminus1_baseChange`, stated for every mark), and deleting empty blow-ups commutes with a flat
  surjective pull-back (`eraseEmpty_pullback_of_flat_surjective`) and is idempotent under any flat
  pull-back (`eraseEmpty_pullback_eraseEmpty'`).
* `bdDataZero`, `exists_bdDataZero`: the assembled `BDData n 0 j`.

Used by `AssemblyTuned.lean`, and outside this directory by
`Hironaka/Resolution/Algebraic/Kol07/Thm35/Principalization/Monomial.lean`,
`Hironaka/Resolution/Algebraic/Hir64/MainTheoremIIN.lean`,
`Hironaka/Resolution/Algebraic/Stage/ClosedEmbeddingHypersurface.lean` and
`Hironaka/Resolution/Algebraic/Stage/Congr.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme IdealSheafData BlowUpSequence
  Scheme.IdealSheafData

namespace Hironaka.BD

variable {k : Type u} [Field k]

/-- An ideal sheaf of maximal order `≤ 0` is the unit ideal. -/
theorem eq_top_of_maxOrd_le_zero {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : I.maxOrd ≤ ((0 : ℕ) : ℕ∞)) : I = ⊤ := by
  have hsup : (I.support : Set X) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have h1 : (1 : ℕ∞) ≤ I.ord x := (one_le_ord_iff I x).mpr hx
    have h2 : I.ord x ≤ 0 := (le_maxOrd I x).trans (by simpa using h)
    exact absurd (h1.trans h2) (not_le.mpr zero_lt_one)
  exact (support_eq_bot_iff I).mp (SetLike.coe_injective (by rw [hsup]; rfl))

/-- On `BDClass n 0 j`, `max-ord I ≤ 0` forces `I` to be the unit ideal; the fact needs no
hypothesis on the characteristic. -/
theorem eq_top_of_bdClass_zero (n j : ℕ) (T : Triple k)
    (hT : Triple.BDClass n 0 j T) : T.I = ⊤ :=
  eq_top_of_maxOrd_le_zero T.I hT.2.1

/-- At mark `0` every component of `E^j` is selected: `E^j ⊆ Z_{-1}` as closed sets. -/
theorem support_component_subset_support_Zminus1_zero (T : Triple k) (i : T.E.ι) :
    ((T.E.component i).support : Set T.X.left) ⊆ (Zminus1 T.I 0 (T.E.component i)).support := by
  have := noetherianSpace_triple T
  intro x hx
  obtain ⟨η, hη, hηx⟩ := Closeds.exists_mem_genericPoints_specializes (T.E.component i).support hx
  exact (Set.ext_iff.mp (coe_support_Zminus1 T.I 0 (T.E.component i)) x).mpr
    ⟨η, hη, by simp, hηx⟩

section Zero

variable [CharZero k] (n j : ℕ)

/-- The value of `BD_{n,0,j}` is `π_{-1}`, the blow-up of `Z_{-1}`, with its empty blow-up deleted
([Kol07, 32]). -/
theorem zeroFunctor_seq (T : Triple k) (hT : Triple.BDClass n 0 j T) :
    (zeroFunctor n j).seq T hT = (piMinusOne T.I 0 (T.E.nth ⟨j, hT.2.2⟩)).eraseEmpty :=
  rfl

omit [CharZero k] in
/-- At mark `0` the strict transform of `E^j` along `π_{-1}` is the unit ideal: the saturation of
`E^j` by `Z_{-1} ⊇ E^j` has empty support (`mem_support_saturate_iff`, `Transform.lean`). -/
theorem strictTransform_Zminus1_zero_eq_top (T : Triple k) (i : T.E.ι) :
    (T.E.component i).strictTransform (Zminus1 T.I 0 (T.E.component i)) = ⊤ := by
  rw [strictTransform_eq_comap_saturate T 0 i]
  have hsat : (T.E.component i).saturate (Zminus1 T.I 0 (T.E.component i)) = ⊤ := by
    have hsup : (((T.E.component i).saturate (Zminus1 T.I 0 (T.E.component i))).support :
        Set T.X.left) = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
      have hx' := (mem_support_saturate_iff T 0 i x).mp hx
      exact hx'.2 (support_component_subset_support_Zminus1_zero T i hx'.1)
    exact (support_eq_bot_iff _).mp (SetLike.coe_injective (by rw [hsup]; rfl))
  rw [hsat, comap_top]

/-- Clause (1) of [Kol07, Lemma 102] at `m = 0`: `cosupp(I_r, 0)` is everything and the birational
transform of `E^j` under the blow-up of `Z_{-1} = E^j` is empty, so the two are disjoint (the form
`BDData.disjoint_cosupp` takes). -/
theorem disjoint_cosupp_zeroFunctor (T : Triple k) (hT : Triple.BDClass n 0 j T) :
    Disjoint
      {x | ((0 : ℕ) : ℕ∞) ≤
        (((zeroFunctor n j).seq T hT).weakTransformSeq T.I (Fin.last _)).ord x}
      ((((zeroFunctor n j).seq T hT).strictTransformSeq (T.E.nth ⟨j, hT.2.2⟩)
        (Fin.last _)).support : Set _) := by
  have key : ((zeroFunctor n j).seq T hT).strictTransformSeq (T.E.nth ⟨j, hT.2.2⟩)
      (Fin.last _) = ⊤ := by
    by_cases hZ : Zminus1 T.I 0 (T.E.component (pos T hT.2.2)) = ⊤
    · have := isIso_blowUpπ_of_eq_top hZ
      refine strictTransformSeq_last_eq_top_of_eq_nil ?_ ?_
      · exact (eraseEmpty_cons_of_eq_top (nil _) hZ).trans rfl
      · have h1 := support_component_subset_support_Zminus1_zero T (pos T hT.2.2)
        rw [hZ, DivisorFamily.support_top_eq_bot] at h1
        exact (support_eq_bot_iff _).mp (SetLike.coe_injective
          ((Set.subset_eq_empty h1 Closeds.coe_bot).trans Closeds.coe_bot.symm))
    · refine strictTransformSeq_last_eq_top_of_eq_cons_nil ?_
        (strictTransform_Zminus1_zero_eq_top T (pos T hT.2.2))
      exact (eraseEmpty_cons_of_ne_top (nil _) hZ).trans rfl
  rw [key, DivisorFamily.support_top_eq_bot, Closeds.coe_bot]
  exact Set.disjoint_empty _

/-- `BD_{n,0,j}` commutes with smooth morphisms ([Kol07, 34.1]; clause (2) of [Kol07, Lemma 102] at
`m = 0`): `Z_{-1}` pulls back (`Zminus1_pullback`) and deleting empty blow-ups commutes with a flat
surjective pull-back. -/
theorem zeroFunctor_commutesWithSmooth : (zeroFunctor (k := k) n j).CommutesWithSmooth := by
  refine ⟨?_, ?_⟩
  · intro T T' g _ hs hpb hT hT'
    change (piMinusOne T'.I 0 (T'.E.nth ⟨j, hT'.2.2⟩)).eraseEmpty =
      (piMinusOne T.I 0 (T.E.nth ⟨j, hT.2.2⟩)).eraseEmpty.pullback g
    rw [← eraseEmpty_pullback_of_flat_surjective _ g hs]
    exact congrArg BlowUpSequence.eraseEmpty
      (cons_nil_congr (Zminus1_pullback hpb 0 j hT.2.2 hT'.2.2))
  · intro T T' g _ hpb hT hT'
    change (piMinusOne T'.I 0 (T'.E.nth ⟨j, hT'.2.2⟩)).eraseEmpty =
      ((piMinusOne T.I 0 (T.E.nth ⟨j, hT.2.2⟩)).eraseEmpty.pullback g).eraseEmpty
    rw [eraseEmpty_pullback_eraseEmpty']
    exact congrArg BlowUpSequence.eraseEmpty
      (cons_nil_congr (Zminus1_pullback hpb 0 j hT.2.2 hT'.2.2))

/-- `BD_{n,0,j}` commutes with change of fields ([Kol07, 34.2]; clause (2) of [Kol07, Lemma 102] at
`m = 0`): `Zminus1_baseChange`. -/
theorem zeroFunctor_commutesWithBaseChange {L : Type u} [Field L] [CharZero L] (σ : k →+* L) :
    (zeroFunctor (k := k) n j).CommutesWithBaseChange (zeroFunctor (k := L) n j) σ := by
  intro T T' p hbc hT hT'
  have : Flat p := flat_of_isPullback_specMap hbc.1
  change (piMinusOne T'.I 0 (T'.E.nth ⟨j, hT'.2.2⟩)).eraseEmpty =
    (piMinusOne T.I 0 (T.E.nth ⟨j, hT.2.2⟩)).eraseEmpty.pullback p
  rw [← eraseEmpty_pullback_of_flat_surjective _ p hbc.surjective]
  exact congrArg BlowUpSequence.eraseEmpty
    (cons_nil_congr (Zminus1_baseChange hbc 0 j hT.2.2 hT'.2.2))

end Zero

/-- **`BD_{n,0,j}` over every field of characteristic zero** (clauses (1)–(2) of [Kol07, Lemma 102]
at `m = 0`), assembled from `zeroFunctor` and its clauses. -/
noncomputable def bdDataZero (n j : ℕ) : BDData.{u} n 0 j where
  functor _ _ _ := zeroFunctor n j
  disjoint_cosupp _ _ _ T hT := disjoint_cosupp_zeroFunctor n j T hT
  commutesWithSmooth _ _ _ := zeroFunctor_commutesWithSmooth n j
  commutesWithBaseChange _ _ _ _ _ _ σ := zeroFunctor_commutesWithBaseChange n j σ

/-- Clauses (1)–(2) of [Kol07, Lemma 102] at the mark `0`: a `BDData n 0 j` whose functor over every
field is `zeroFunctor` (existential form of `bdDataZero`). -/
theorem exists_bdDataZero (n j : ℕ) :
    ∃ D : BDData n 0 j, ∀ (k : Type u) [Field k] [CharZero k] (T : Triple k)
      (hT : Triple.BDClass n 0 j T), (D.functor k).seq T hT = (zeroFunctor n j).seq T hT :=
  ⟨bdDataZero n j, fun _ _ _ _ _ => rfl⟩

end Hironaka.BD
