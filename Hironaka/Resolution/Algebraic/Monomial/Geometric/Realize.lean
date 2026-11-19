/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces
public import Hironaka.Scheme.BlowUpSequence.Basic
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Input
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Kernel
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The realisation invariant along the fold

The geometric Step 3 is the fold of the combinatorial run `(step3 st).2` into a blow-up
sequence (`PieceFamily.realize` of `Hironaka/Resolution/Algebraic/Monomial/Geometric/Pieces.lean`),
carrying the piece family along. This module proves the *realisation invariant*: at every stage `i`
the stage family is `Valid`, its state is the fold of the first `i` centres into the initial state,
it realises the total transform `E_i`, and the stage is smooth over `k` of relative dimension
`≤ n` with `E_i` snc. The proof is an induction along the list of centres, each step being the
nerve transition of `Hironaka/Resolution/Algebraic/Monomial/Geometric/Kernel.lean`
(`toState_blowUpPieces`, `valid_blowUpPieces`, `realizes_blowUpPieces`) together with the facts that
the total transform of an snc boundary under a blow-up with simple normal crossings is snc
(`AlgebraicGeometry.totalTransform_isSnc` of `Hironaka/Scheme/BlowUpSequence/Triple.lean`) and that
the blow-up of a smooth centre of a smooth scheme is smooth. Not in the sources as a statement; it
is the bookkeeping that lets Kollár's blow-up by blow-up description of [Kol07, 111, Step 3] be
iterated.

* `realizeAux_invariant`: the invariant along an arbitrary run;
* `valid_stagePieces`, `realize_invariant`, `realizes_stagePieces`,
  `isSnc_totalTransformSeq_realize`, `exists_smoothOfRelativeDimension_stageMap_realize`: the
  same on `realize`;
* `exists_center_realize_eq`: the `i`-th centre of the geometric Step 3 is Kollár's choice on
  the stage state;
* `realize_noEmptyCenters`: no centre of the geometric Step 3 is empty, so no deletion of empty
  blow-ups in the sense of [Kol07, 32] is ever needed for Step 3 itself.

The invariant is what `Hironaka/Resolution/Algebraic/Monomial/Geometric/OrderSeq.lean` and
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step3Input.lean` read at every stage.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme BlowUpSequence
  IdealSheafData

namespace Hironaka.Monomial

namespace PieceFamily

variable {k : Type u} [Field k] [CharZero k]

/-! ### The invariant along an arbitrary run -/

/-- *The realisation invariant* along a run of the combinatorial state: at every stage the
total transform is snc, the stage is smooth over `k` of relative dimension `≤ n`, the stage
family is `Valid`, its state is the fold of the centres so far, and it realises the total
transform through the stage label isomorphism. -/
theorem realizeAux_invariant (L : List (Finset (Finset ℕ))) :
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [QuasiCompact f]
      (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel}
      (_hE : E.IsSnc) (_hΦ : Φ.Realizes E e) {n m : ℕ} (hV : Φ.IsValid n m)
      (_hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f) {st' : MonomialState}
      (_hrun : MonomialState.IsRun (Φ.toState n m hV) L st')
      (i : Fin ((realizeAux Φ m L).length + 1)),
      ((realizeAux Φ m L).totalTransformSeq E i).IsSnc ∧
      (∃ n' ≤ n, SmoothOfRelativeDimension n' ((realizeAux Φ m L).stageMap i ≫ f)) ∧
      ∃ hV' : (stagePieces Φ m L i).IsValid n m,
        (stagePieces Φ m L i).toState n m hV' =
          (L.take i).foldl MonomialState.blowUp (Φ.toState n m hV) ∧
        (stagePieces Φ m L i).Realizes ((realizeAux Φ m L).totalTransformSeq E i)
          (stageIso Φ m E e L i) := by
  induction L with
  | nil =>
    intro X f _ _ Φ E e hE hΦ n m hV hn st' _ i
    obtain ⟨n', hn'n, hsm⟩ := hn
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    refine ⟨hE, ⟨n', hn'n, ?_⟩, hV, rfl, hΦ⟩
    change SmoothOfRelativeDimension n' (𝟙 X ≫ f)
    rw [Category.id_comp]
    exact hsm
  | cons S L ih =>
    intro X f _ _ Φ E e hE hΦ n m hV hn st' hrun i
    obtain ⟨n', hn'n, hsm⟩ := hn
    cases hrun with
    | cons r hr hrn hne hL =>
      -- the first centre is Kollár's choice: a centre of the state
      have hS : (Φ.toState n m hV).IsCenter ((Φ.toState n m hV).choice r) :=
        (Φ.toState n m hV).isCenter_choice r
      -- the data at the next stage
      have hE' := totalTransform_isSnc f E _ hE
        (Φ.hasSncWith_centerOf hE hΦ hS)
      have hΦ' := Φ.realizes_blowUpPieces f hE hΦ hS
      have hV' := Φ.valid_blowUpPieces f hE hΦ hS
      have hst' := Φ.toState_blowUpPieces f hE hΦ hV' hS
      have hrun' : MonomialState.IsRun ((Φ.blowUpPieces _ m).toState n m hV') L st' := by
        rw [hst']
        exact hL
      have hsmZ : Smooth ((Φ.centerOf _).subschemeι ≫ f) := Φ.smooth_centerOf f hE hΦ hS
      have hsm' := smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n'
        (Φ.centerOf ((Φ.toState n m hV).choice r))
      have hsmooth' : Smooth ((Φ.centerOf ((Φ.toState n m hV).choice r)).blowUpπ ≫ f) :=
        SmoothOfRelativeDimension.smooth n' _
      have hLN : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
      have hproper := blowUp.isProper_π (Φ.centerOf ((Φ.toState n m hV).choice r))
      have hIH := ih ((Φ.centerOf ((Φ.toState n m hV).choice r)).blowUpπ ≫ f)
        (Φ.blowUpPieces _ m) hE' hΦ' hV' ⟨n', hn'n, hsm'⟩ hrun'
      rcases i with ⟨_ | j, h⟩
      · -- stage `0`: the family itself
        refine ⟨hE, ⟨n', hn'n, ?_⟩, hV, rfl, hΦ⟩
        change SmoothOfRelativeDimension n' (𝟙 X ≫ f)
        rw [Category.id_comp]
        exact hsm
      · -- stage `j + 1`: the invariant at stage `j` of the run on the blow-up
        obtain ⟨h1, ⟨n'', hn'', hsm''⟩, hV'', h2, h3⟩ := hIH ⟨j, Nat.lt_of_succ_lt_succ h⟩
        refine ⟨h1, ⟨n'', hn'', ?_⟩, hV'', ?_, h3⟩
        · change SmoothOfRelativeDimension n''
            (((realizeAux (Φ.blowUpPieces _ m) m L).stageMap ⟨j, Nat.lt_of_succ_lt_succ h⟩ ≫
              (Φ.centerOf ((Φ.toState n m hV).choice r)).blowUpπ) ≫ f)
          rw [Category.assoc]
          exact hsm''
        · change (stagePieces (Φ.blowUpPieces _ m) m L ⟨j, Nat.lt_of_succ_lt_succ h⟩).toState n m
            hV'' = _
          rw [List.take_succ_cons, List.foldl_cons, ← hst']
          exact h2

/-! ### The statements on `realize` -/

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [QuasiCompact f]
  (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel}
  {n m : ℕ}

include f in
/-- The stage-`i` piece family's data are `Valid`. -/
theorem valid_stagePieces (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (hV : Φ.IsValid n m)
    (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f)
    (i : Fin ((Φ.realize n m hV).length + 1)) :
    (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2 i).IsValid n m :=
  (realizeAux_invariant _ f Φ hE hΦ hV hn (MonomialState.step3_isRun _) i).2.2.1

include f in
/-- *The realisation invariant*: the state of the stage-`i` piece family of the fold of the
combinatorial run is the fold of the first `i` centres into the initial state. -/
theorem realize_invariant (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (hV : Φ.IsValid n m)
    (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f)
    (i : Fin ((Φ.realize n m hV).length + 1))
    (hV' : (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2 i).IsValid n m) :
    (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2 i).toState n m hV' =
      ((MonomialState.step3 (Φ.toState n m hV)).2.take i).foldl MonomialState.blowUp
        (Φ.toState n m hV) :=
  (realizeAux_invariant _ f Φ hE hΦ hV hn (MonomialState.step3_isRun _) i).2.2.2.1

include f in
/-- The stage-`i` piece family realises the total transform `E_i` ([Kol07, Definition 65]
iterated) through the stage label isomorphism. -/
theorem realizes_stagePieces (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (hV : Φ.IsValid n m)
    (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f)
    (i : Fin ((Φ.realize n m hV).length + 1)) :
    (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2 i).Realizes
      ((Φ.realize n m hV).totalTransformSeq E i)
      (stageIso Φ m E e (MonomialState.step3 (Φ.toState n m hV)).2 i) :=
  (realizeAux_invariant _ f Φ hE hΦ hV hn (MonomialState.step3_isRun _) i).2.2.2.2

include f in
/-- The total transform at every stage of the geometric Step 3 is snc. -/
theorem isSnc_totalTransformSeq_realize (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (hV : Φ.IsValid n m)
    (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f)
    (i : Fin ((Φ.realize n m hV).length + 1)) :
    ((Φ.realize n m hV).totalTransformSeq E i).IsSnc :=
  (realizeAux_invariant _ f Φ hE hΦ hV hn (MonomialState.step3_isRun _) i).1

include f in
/-- Every stage of the geometric Step 3 is smooth over `k` of relative dimension `≤ n`. -/
theorem exists_smoothOfRelativeDimension_stageMap_realize (hE : E.IsSnc) (hΦ : Φ.Realizes E e)
    (hV : Φ.IsValid n m) (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f)
    (i : Fin ((Φ.realize n m hV).length + 1)) :
    ∃ n' ≤ n, SmoothOfRelativeDimension n' ((Φ.realize n m hV).stageMap i ≫ f) :=
  (realizeAux_invariant _ f Φ hE hΦ hV hn (MonomialState.step3_isRun _) i).2.1

/-- The `i`-th centre of the geometric Step 3, read on the stage family: Kollár's choice on the
stage state, a centre with faces of sum `≥ m`. -/
theorem exists_center_realize_eq (hV : Φ.IsValid n m) (i : Fin (Φ.realize n m hV).length) :
    ∃ r, 1 ≤ r ∧
      ((((MonomialState.step3 (Φ.toState n m hV)).2.take i).foldl MonomialState.blowUp
        (Φ.toState n m hV)).choice r).Nonempty ∧
      (MonomialState.step3 (Φ.toState n m hV)).2.get
        (Fin.cast (realizeAux_length Φ m _) i) =
        (((MonomialState.step3 (Φ.toState n m hV)).2.take i).foldl MonomialState.blowUp
          (Φ.toState n m hV)).choice r := by
  obtain ⟨r, hr, -, hne, hget⟩ :=
    (MonomialState.step3_isRun (Φ.toState n m hV)).exists_get_eq_choice
      (Fin.cast (realizeAux_length Φ m _) i)
  exact ⟨r, hr, hne, hget⟩

include f in
/-- The geometric Step 3 has no empty blow-ups ([Kol07, 32]): each centre is a nonempty set of
faces of the nerve of the stage family. -/
theorem realize_noEmptyCenters (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (hV : Φ.IsValid n m)
    (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f) : (Φ.realize n m hV).NoEmptyCenters := by
  intro i hi
  obtain ⟨r, -, hne, hget⟩ := Φ.exists_center_realize_eq hV i
  have hinv := Φ.realize_invariant f hE hΦ hV hn i.castSucc
    (Φ.valid_stagePieces f hE hΦ hV hn i.castSucc)
  rw [Fin.val_castSucc] at hinv
  have hcenter := realizeAux_center Φ m (MonomialState.step3 (Φ.toState n m hV)).2 i
  change (realizeAux Φ m (MonomialState.step3 (Φ.toState n m hV)).2).center i = ⊤ at hi
  rw [hcenter, hget] at hi
  -- the center is the choice on the stage state, whose nerve is the stage family's
  have hsub : (((MonomialState.step3 (Φ.toState n m hV)).2.take i).foldl MonomialState.blowUp
      (Φ.toState n m hV)).choice r ⊆
      (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2 i.castSucc).nerve := by
    intro T hT
    have := (((MonomialState.step3 (Φ.toState n m hV)).2.take i).foldl MonomialState.blowUp
      (Φ.toState n m hV)).mem_nerve_of_mem_choice hT
    rw [← hinv] at this
    exact this
  exact (stagePieces Φ m _ i.castSucc).centerOf_ne_top hsub hne hi

end PieceFamily

end Hironaka.Monomial
