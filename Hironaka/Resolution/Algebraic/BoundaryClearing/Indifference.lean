/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.AssemblyTuned
public import Hironaka.Resolution.Algebraic.OrderReduction.EmptyIndifferent
public import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyEmbedding
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The data of Lemma 102 are indifferent to empty boundary members

Kollár's convention ignores empty blow-ups ([Kol07, 32]) and reindexes after deleting them (the
second bullet of [Kol07, 34.1]); for the functor data of this library the corresponding property is
`BDFamily.IndifferentToEmptyMembers`
(`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferent.lean`): deleting empty (unit-ideal)
members of the boundary, with the distinguished position carried along, does not change the value.
This module proves it for the data `bdData n m j Dom B (hDom m) hB hsm hbc` of `AssemblyTuned.lean`,
at every mark, GIVEN the same indifference of the inductive input `B` (the marked form
`OrderGeSeqAssignment.IndifferentToEmptyMembers`). The statement is a bookkeeping property of the
construction, not in the sources.

* At the mark `0` (`bdDataZero`, `zeroFunctor`) the value is `π_{-1}` at the distinguished member
  `E^j`, which the position clause identifies with `E'^{j'}` (handled inline in
  `bdData_indifferentToEmptyMembers`).
* At `m + 1` (`dataFunctor`, Lemma 102 through the re-tuning) the value is, on the tuned triple, the
  erased raw sequence of `Output.lean`: `π_{-1}` on `S = E^j` followed by `B` on the restricted
  marked triple `(X_S, I_0|_S, m, E_S)`, pushed forward along `S ↪ X` (`rawSeq`). The restricted
  triple depends on the boundary through the distinguished member `E^j` (the scheme `S`, the
  centre, the push-forward) and through the erased family `E − E^j` (its boundary only). We
  separate the two: `restrictedTripleD T m D F` and `rawSeqD T m D F` of `Restriction.lean` take
  the member `D` and the family `F` as parameters (`restrictedTriple T m j` is
  `restrictedTripleD T m (E^j) (E − E^j)`). The position clause gives `E'^{j'} = E^j`, so the two
  members agree and the dependence on `D` is a substitution (`rawSeqD_congr_D`); the embedding `e`
  restricts to `E' − E'^{j'} ↪o E − E^j` with `⊤` complement (`eraseEmb`, `isTopErasure_erase`),
  preserved by the inverse image along `S ↪ X` and the total transform along `Z_{-1}|_S` (the
  transport lemmas of `IsTopErasure`), so `B`'s indifference identifies the two values on the
  restricted triples (`rawSeqD_congr_F`); the first blow-up, the push-forward and the deletion of
  empty blow-ups are then the same (`functor_seq_indifferent`, `dataFunctor_seq_indifferent`).

Used by `Hironaka/Resolution/Algebraic/OrderReduction/Step3Data.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence
  Hironaka.Sequence Scheme.IdealSheafData IsLocalRing

namespace Hironaka.BD

variable {k : Type u} [Field k] [CharZero k]

section RestrictedD

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
  [IsSeparated f] (I : X.IdealSheafData) (m : ℕ) (D : X.IdealSheafData) (F : DivisorFamily X)
  {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)

omit [CharZero k] [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
/-- Transport of the facts along an equality of members. -/
theorem RestrictedHyps.congr {D₁ D₂ : X.IdealSheafData} (hD : D₂ = D₁)
    (h : RestrictedHyps f I m D₂ F) : RestrictedHyps f I m D₁ F := by
  subst hD
  exact h

omit [CharZero k] in
/-- The raw output depends on the member only through its value (a substitution). -/
theorem rawSeqD_congr_D {D₁ D₂ : X.IdealSheafData} (hD : D₂ = D₁)
    (h₂ : RestrictedHyps f I m D₂ F) (h₁ : RestrictedHyps f I m D₁ F)
    (hdom₂ : Dom (restrictedTripleD f I m D₂ F h₂))
    (hdom₁ : Dom (restrictedTripleD f I m D₁ F h₁)) :
    rawSeqD f I m D₂ F B h₂ hdom₂ = rawSeqD f I m D₁ F B h₁ hdom₁ := by
  subst hD
  rfl

omit [CharZero k] in
/-- The raw output is indifferent to `⊤` members of the erased family: the boundaries of the two
restricted triples differ by a deletion of `⊤` members (the inverse image along `D ↪ X` and the
total transform along `Z_{-1}|_D` of the deletion), so `B`'s indifference identifies `B`'s values;
the first blow-up and the push-forward are the same. -/
theorem rawSeqD_congr_F {F₁ F₂ : DivisorFamily X} (e : F₂.ι ↪o F₁.ι) (he : IsTopErasure F₂ F₁ e)
    (hBind : B.IndifferentToEmptyMembers) (h₁ : RestrictedHyps f I m D F₁)
    (h₂ : RestrictedHyps f I m D F₂) (hdom₁ : Dom (restrictedTripleD f I m D F₁ h₁))
    (hdom₂ : Dom (restrictedTripleD f I m D F₂ h₂)) :
    rawSeqD f I m D F₂ B h₂ hdom₂ = rawSeqD f I m D F₁ B h₁ hdom₁ := by
  have he' := (he.comap D.subschemeι).totalTransform (centerSD I m D)
  have hdom₂' : Dom ({ restrictedTripleD f I m D F₁ h₁ with
      E := (F₂.comap D.subschemeι).totalTransform (centerSD I m D)
      isSnc := h₂.isSnc } : MarkedTriple k) := hdom₂
  have key := hBind (restrictedTripleD f I m D F₁ h₁)
    ((F₂.comap D.subschemeι).totalTransform (centerSD I m D)) h₂.isSnc (sumLexMapEmb e) he'.1 he'.2
    hdom₁ hdom₂'
  exact congrArg (fun R : BlowUpSequence (centerSD I m D).blowUp =>
    (cons D.subscheme (centerSD I m D) R).pushforward D.subschemeι) key.symm

end RestrictedD

section Erase

variable {X : Scheme.{u}}

/-- The restriction of a `⊤`-deletion embedding to the erased families: `E' − E'^{j'} ↪o E − E^j`
when `e j' = j`. -/
noncomputable def eraseEmb {E E' : DivisorFamily X} (e : E'.ι ↪o E.ι) {j : E.ι} {j' : E'.ι}
    (hj : e j' = j) : (E'.erase j').ι ↪o (E.erase j).ι :=
  OrderEmbedding.ofMapLEIff (fun i => ⟨e i.1, fun h => i.2 (e.injective (h.trans hj.symm))⟩)
    fun _ _ => Subtype.mk_le_mk.trans e.le_iff_le

/-- A deletion of `⊤` members restricts to a deletion of `⊤` members of the erased families. -/
theorem isTopErasure_erase {E E' : DivisorFamily X} {e : E'.ι ↪o E.ι} (he : IsTopErasure E' E e)
    {j : E.ι} {j' : E'.ι} (hj : e j' = j) :
    IsTopErasure (E'.erase j') (E.erase j) (eraseEmb e hj) := by
  refine ⟨fun i => he.1 i.1, fun b hb => ?_⟩
  refine he.2 b.1 fun ⟨c, hc⟩ => hb ⟨⟨c, fun hcj => b.2 ?_⟩, Subtype.ext hc⟩
  rw [← hc, hcj, hj]

end Erase

section Functor

variable {n m : ℕ} {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)

/-- The functor of `Output.lean` at position `j` is indifferent to `⊤` members of the boundary
([Kol07, 32]): for a deletion `e` of `⊤` members carrying the position `j'` of `E'` to the position
`j` of `E`, the values at `(X, I, E)` and `(X, I, E')` agree: the distinguished members agree, so
the first blow-up and the push-forward are the same (`rawSeqD_congr_D`), and `B`'s indifference
handles the erased families (`rawSeqD_congr_F`). -/
theorem functor_seq_indifferent
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T')
    (hBind : B.IndifferentToEmptyMembers) (T : Triple k)
    (E' : DivisorFamily T.X.left) (hsnc' : E'.IsSnc) (e : E'.ι ↪o T.E.ι)
    (hc : ∀ i, T.E.component (e i) = E'.component i)
    (ht : ∀ b, b ∉ Set.range e → T.E.component b = ⊤) {j j' : ℕ} (hj : j < Fintype.card T.E.ι)
    (hj' : j' < Fintype.card E'.ι) (hpos : e (E'.nthIdx ⟨j', hj'⟩) = T.E.nthIdx ⟨j, hj⟩)
    (hT : Domain n m j T) (hT' : Domain n m j' ({ T with E := E', isSnc := hsnc' } : Triple k)) :
    (functor n m j B hDom).seq T hT =
      (functor n m j' B hDom).seq ({ T with E := E', isSnc := hsnc' } : Triple k) hT' := by
  have hD : E'.component (E'.nthIdx ⟨j', hj'⟩) = T.E.component (T.E.nthIdx ⟨j, hj⟩) := by
    rw [← hpos]
    exact (hc _).symm
  have he := isTopErasure_erase ⟨hc, ht⟩ hpos
  -- the parametrised forms
  have hyps₂ : RestrictedHyps (T.X.left ↘ Spec (.of k)) T.I m (E'.component (E'.nthIdx ⟨j', hj'⟩))
      (E'.erase (E'.nthIdx ⟨j', hj'⟩)) :=
    restrictedHyps_component ({ T with E := E', isSnc := hsnc' } : Triple k) m
      (E'.nthIdx ⟨j', hj'⟩) hT'.2.1 hT'.2.2.1
  have hyps₁ : RestrictedHyps (T.X.left ↘ Spec (.of k)) T.I m (T.E.component (T.E.nthIdx ⟨j, hj⟩))
      (T.E.erase (T.E.nthIdx ⟨j, hj⟩)) :=
    restrictedHyps_component T m (T.E.nthIdx ⟨j, hj⟩) hT.2.1 hT.2.2.1
  have hyps₂' : RestrictedHyps (T.X.left ↘ Spec (.of k)) T.I m (T.E.component (T.E.nthIdx ⟨j, hj⟩))
      (E'.erase (E'.nthIdx ⟨j', hj'⟩)) := hyps₂.congr _ _ _ _ hD
  have hdom₂ : Dom (restrictedTripleD (T.X.left ↘ Spec (.of k)) T.I m
      (E'.component (E'.nthIdx ⟨j', hj'⟩)) (E'.erase (E'.nthIdx ⟨j', hj'⟩)) hyps₂) :=
    hDom _ (hasDimLE_restrictedTriple ({ T with E := E', isSnc := hsnc' } : Triple k) m
      (E'.nthIdx ⟨j', hj'⟩) hT'.2.1 hT'.2.2.1 hT'.1) rfl
  have hdom₁ : Dom (restrictedTripleD (T.X.left ↘ Spec (.of k)) T.I m
      (T.E.component (T.E.nthIdx ⟨j, hj⟩)) (T.E.erase (T.E.nthIdx ⟨j, hj⟩)) hyps₁) :=
    hDom _ (hasDimLE_restrictedTriple T m (T.E.nthIdx ⟨j, hj⟩) hT.2.1 hT.2.2.1 hT.1) rfl
  have hdom₂' : Dom (restrictedTripleD (T.X.left ↘ Spec (.of k)) T.I m
      (T.E.component (T.E.nthIdx ⟨j, hj⟩)) (E'.erase (E'.nthIdx ⟨j', hj'⟩)) hyps₂') :=
    hDom _ (hasDimLE_restrictedTriple T m (T.E.nthIdx ⟨j, hj⟩) hT.2.1 hT.2.2.1 hT.1) rfl
  -- the raw sequences
  have s₂ : rawSeq ({ T with E := E', isSnc := hsnc' } : Triple k) m
      (monoEquivOfFin E'.ι rfl ⟨j', hT'.2.2.2⟩) hT'.2.1 hT'.2.2.1 hT'.1 B hDom =
      rawSeqD (T.X.left ↘ Spec (.of k)) T.I m (E'.component (E'.nthIdx ⟨j', hj'⟩))
        (E'.erase (E'.nthIdx ⟨j', hj'⟩)) B hyps₂ hdom₂ := rfl
  have s₁ : rawSeq T m (monoEquivOfFin T.E.ι rfl ⟨j, hT.2.2.2⟩) hT.2.1 hT.2.2.1 hT.1 B hDom =
      rawSeqD (T.X.left ↘ Spec (.of k)) T.I m (T.E.component (T.E.nthIdx ⟨j, hj⟩))
        (T.E.erase (T.E.nthIdx ⟨j, hj⟩)) B hyps₁ hdom₁ := rfl
  have s₃ := rawSeqD_congr_D (T.X.left ↘ Spec (.of k)) T.I m _ B hD hyps₂ hyps₂' hdom₂ hdom₂'
  have s₄ := rawSeqD_congr_F (T.X.left ↘ Spec (.of k)) T.I m _ B (eraseEmb e hpos) he hBind hyps₁
    hyps₂' hdom₁ hdom₂'
  change (rawSeq T m (monoEquivOfFin T.E.ι rfl ⟨j, hT.2.2.2⟩) hT.2.1 hT.2.2.1 hT.1 B
      hDom).eraseEmpty =
    (rawSeq ({ T with E := E', isSnc := hsnc' } : Triple k) m
      (monoEquivOfFin E'.ι rfl ⟨j', hT'.2.2.2⟩) hT'.2.1 hT'.2.2.1 hT'.1 B hDom).eraseEmpty
  exact congrArg BlowUpSequence.eraseEmpty (s₁.trans (s₄.symm.trans (s₃.symm.trans s₂.symm)))

/-- The data of [Kol07, Lemma 102] at the mark `m ≥ 1` through the re-tuning (`dataFunctor`) are
indifferent to `⊤` members: both sides tune the same ideal, so both are the functor of `Output.lean`
on the tuned triple, or both are empty below the mark. -/
theorem dataFunctor_seq_indifferent (hm : 1 ≤ m)
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom T')
    (hBind : B.IndifferentToEmptyMembers)
    (T : Triple k) (E' : DivisorFamily T.X.left) (hsnc' : E'.IsSnc) (e : E'.ι ↪o T.E.ι)
    (hc : ∀ i, T.E.component (e i) = E'.component i)
    (ht : ∀ b, b ∉ Set.range e → T.E.component b = ⊤) {j j' : ℕ} (hj : j < Fintype.card T.E.ι)
    (hj' : j' < Fintype.card E'.ι) (hpos : e (E'.nthIdx ⟨j', hj'⟩) = T.E.nthIdx ⟨j, hj⟩)
    (hT : Triple.BDClass n m j T)
    (hT' : Triple.BDClass n m j' ({ T with E := E', isSnc := hsnc' } : Triple k)) :
    (dataFunctor n m j hm B hDom).seq T hT =
      (dataFunctor n m j' hm B hDom).seq ({ T with E := E', isSnc := hsnc' } : Triple k) hT' := by
  by_cases h : T.I.maxOrd = m
  · rw [dataFunctor_seq_of_maxOrd_eq (T := T) (hT := hT) (h := h),
      dataFunctor_seq_of_maxOrd_eq (T := ({ T with E := E', isSnc := hsnc' } : Triple k))
        (hT := hT') (h := h)]
    exact functor_seq_indifferent B hDom hBind (T.tuned m hm) E' hsnc' e hc ht hj hj' hpos
      (domain_tuned hm hT h) (domain_tuned hm hT' h)
  · have hlt : T.I.maxOrd < m := lt_of_le_of_ne hT.2.1 h
    rw [dataFunctor_seq_of_maxOrd_lt (T := T) (hT := hT) (h := hlt),
      dataFunctor_seq_of_maxOrd_lt (T := ({ T with E := E', isSnc := hsnc' } : Triple k))
        (hT := hT') (h := hlt)]

end Functor

/-- The data `bdData` of [Kol07, Lemma 102] are indifferent to empty boundary members at every mark
([Kol07, 32]; the second bullet of [Kol07, 34.1]), given that the inductive data `B` are. -/
theorem bdData_indifferentToEmptyMembers {n : ℕ}
    (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
    (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
    (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
      T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom k T')
    (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
      ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
    (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
    (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
      (B k).CommutesWithBaseChange (B L) σ)
    (hBind : ∀ (k : Type u) [Field k] [CharZero k], (B k).IndifferentToEmptyMembers) (m : ℕ) :
    BDFamily.IndifferentToEmptyMembers
      (fun j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) := by
  intro k _ _ T E' hsnc' e hc ht j j' hj hj' hpos hT hT'
  cases m with
  | zero =>
    change (zeroFunctor n j).seq T hT =
      (zeroFunctor n j').seq ({ T with E := E', isSnc := hsnc' } : Triple k) hT'
    have hnth : T.E.nth ⟨j, hT.2.2⟩ = E'.nth ⟨j', hT'.2.2⟩ := by
      change T.E.component (T.E.nthIdx ⟨j, hT.2.2⟩) = E'.component (E'.nthIdx ⟨j', hT'.2.2⟩)
      rw [← hpos]
      exact hc _
    exact congrArg (fun D : T.X.left.IdealSheafData => (piMinusOne T.I 0 D).eraseEmpty) hnth
  | succ m =>
    exact dataFunctor_seq_indifferent (B k) (Nat.le_add_left 1 m) (hDom (m + 1) k) (hBind k) T E'
      hsnc' e hc ht hj hj' hpos hT hT'

end Hironaka.BD
