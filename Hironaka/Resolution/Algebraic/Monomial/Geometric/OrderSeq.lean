/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Exponent
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Input
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Kernel
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Realize
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Transform
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.Triple
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The geometric Step 3 as a blow-up sequence of order `≥ m`

The fold `PieceFamily.realize` of the combinatorial run
(`Hironaka/Resolution/Algebraic/Monomial/Geometric/Pieces.lean`) is a smooth blow-up sequence of
order `≥ m` for the marked monomial ideal in the sense of [Kol07, Definition 66], and its marked
transforms are the monomial ideals of the stage families. Not in the sources as statements; this is
what Kollár's description of Step 3 in [Kol07, 111] amounts to once the blow-ups are performed on
the piece families.

* `markedTransformSeq_realizeAux`, `markedTransformSeq_realize`: *the marked transform at stage
  `i` is the monomial ideal of the stage-`i` family* (`markedTransform_monomial` of
  `Hironaka/Resolution/Algebraic/Monomial/Geometric/Transform.lean` at each step, the centre being
  Kollár's choice on the stage state, of order `≥ m`);
* `isOrderGeSeq_realizeAux`, `realize_isOrderGeSeq`: conditions (2′)–(4′) of
  [Kol07, Definition 66]. Every centre is smooth over `k`, has simple normal crossings with
  `E_i`, and the marked transform has order `≥ m` along it, along an arbitrary run, each centre
  being Kollár's choice on the stage state;
* `realize_maxOrd_lt`: at the end of Step 3 the marked monomial ideal has `max-ord < m`, Kollár's
  "at the end of Step 3.n we are done". Every face of the final nerve has sum `< m`
  (`step3_maxOrd_lt` of `Hironaka/Resolution/Algebraic/Monomial/Step3Phases.lean`), and the order at
  a point is the sum over its face.

These are the properties of the third step of `BMO_{n,m}` that
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step3Input.lean` packages.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Monomial.PieceFamily

variable {k : Type u} [Field k] [CharZero k]

/-! ### The marked transforms along an arbitrary run -/

/-- Along a run: the marked transform of the marked monomial ideal at stage `i` of the fold of
a run is the monomial ideal of the stage-`i` piece family, by `markedTransform_monomial` at
every step, each centre being Kollár's choice on the stage state, of order `≥ m`. -/
theorem markedTransformSeq_realizeAux (L : List (Finset (Finset ℕ))) :
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [QuasiCompact f]
      (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel},
      E.IsSnc → Φ.Realizes E e → ∀ {n m : ℕ} (hV : Φ.IsValid n m),
      (∃ n' ≤ n, SmoothOfRelativeDimension n' f) → ∀ {st' : MonomialState},
      MonomialState.IsRun (Φ.toState n m hV) L st' → ∀ (i : Fin ((realizeAux Φ m L).length + 1)),
      (realizeAux Φ m L).markedTransformSeq (E.monomial Φ.exponentAt) m i =
        ((realizeAux Φ m L).totalTransformSeq E i).monomial (stagePieces Φ m L i).exponentAt := by
  induction L with
  | nil =>
    intro X f _ _ Φ E e _ _ n m hV _ st' _ i
    have hi : i = 0 := Fin.fin_one_eq_zero i
    subst hi
    rfl
  | cons S L ih =>
    intro X f _ _ Φ E e hE hΦ n m hV hn st' hrun i
    obtain ⟨n', hn'n, hsm⟩ := hn
    cases hrun with
    | cons r hr hrn hne hL =>
      have hS : (Φ.toState n m hV).IsCenter ((Φ.toState n m hV).choice r) :=
        (Φ.toState n m hV).isCenter_choice r
      have hge : ∀ P ∈ (Φ.toState n m hV).choice r, m ≤ Φ.total P := fun P hP =>
        (Φ.toState n m hV).m_le_total_of_mem_choice hP
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
      · rfl
      · have hmt := Φ.markedTransform_monomial f hE hΦ hS hge
        change (realizeAux (Φ.blowUpPieces _ m) m L).markedTransformSeq
          ((E.monomial Φ.exponentAt).markedTransform (Φ.centerOf _) m) m
            ⟨j, Nat.lt_of_succ_lt_succ h⟩ = _
        rw [hmt]
        exact hIH ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-! ### The order sequence along an arbitrary run -/

/-- Along a run (conditions (2′)–(4′) of [Kol07, Definition 66]): the fold of a run is a smooth
blow-up sequence of order `≥ m` for the marked monomial ideal. Every centre is Kollár's choice
on the stage state, so it is smooth over `k` (`smooth_centerOf`), has simple normal crossings
with the stage boundary (`hasSncWith_centerOf`), and the stage monomial ideal has order `≥ m`
along it (`leOrdAlong_centerOf`), the stage monomial ideal being the marked transform
(`markedTransform_monomial`). -/
theorem isOrderGeSeq_realizeAux (L : List (Finset (Finset ℕ))) :
    ∀ {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [QuasiCompact f]
      (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel},
      E.IsSnc → Φ.Realizes E e → ∀ {n m : ℕ} (hV : Φ.IsValid n m),
      (∃ n' ≤ n, SmoothOfRelativeDimension n' f) → ∀ {st' : MonomialState},
      MonomialState.IsRun (Φ.toState n m hV) L st' →
      (realizeAux Φ m L).IsOrderGeSeq f (E.monomial Φ.exponentAt) m E := by
  induction L with
  | nil =>
    intro X f _ _ Φ E e _ _ n m hV _ st' _
    exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | cons S L ih =>
    intro X f _ _ Φ E e hE hΦ n m hV hn st' hrun
    obtain ⟨n', hn'n, hsm⟩ := hn
    cases hrun with
    | cons r hr hrn hne hL =>
      have hS : (Φ.toState n m hV).IsCenter ((Φ.toState n m hV).choice r) :=
        (Φ.toState n m hV).isCenter_choice r
      have hge : ∀ P ∈ (Φ.toState n m hV).choice r, m ≤ Φ.total P := fun P hP =>
        (Φ.toState n m hV).m_le_total_of_mem_choice hP
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
      have hmt := Φ.markedTransform_monomial f hE hΦ hS hge
      refine ⟨fun i => ?_, fun i => ⟨?_, ?_⟩⟩
      · rcases i with ⟨_ | j, h⟩
        · change Smooth ((Φ.centerOf _).subschemeι ≫ 𝟙 X ≫ f)
          rw [Category.id_comp]
          exact hsmZ
        · change Smooth (((realizeAux (Φ.blowUpPieces ((Φ.toState n m hV).choice r) m) m L).center
              ⟨j, Nat.lt_of_succ_lt_succ h⟩).subschemeι ≫
            ((realizeAux (Φ.blowUpPieces ((Φ.toState n m hV).choice r) m) m L).stageMap
              ⟨j, Nat.lt_succ_of_lt (Nat.lt_of_succ_lt_succ h)⟩ ≫
              (Φ.centerOf ((Φ.toState n m hV).choice r)).blowUpπ) ≫ f)
          rw [Category.assoc]
          exact hIH.1 ⟨j, Nat.lt_of_succ_lt_succ h⟩
      · rcases i with ⟨_ | j, h⟩
        · exact Φ.hasSncWith_centerOf hE hΦ hS
        · exact (hIH.2 ⟨j, Nat.lt_of_succ_lt_succ h⟩).1
      · rcases i with ⟨_ | j, h⟩
        · exact Φ.leOrdAlong_centerOf f hE hΦ hS hge
        · change ((realizeAux (Φ.blowUpPieces ((Φ.toState n m hV).choice r) m) m
            L).markedTransformSeq
            ((E.monomial Φ.exponentAt).markedTransform (Φ.centerOf ((Φ.toState n m hV).choice r)) m)
              m ⟨j, Nat.lt_succ_of_lt (Nat.lt_of_succ_lt_succ h)⟩).LeOrdAlong _ _
          rw [hmt]
          exact (hIH.2 ⟨j, Nat.lt_of_succ_lt_succ h⟩).2

/-! ### The statements on `realize` -/

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [QuasiCompact f]
  (Φ : PieceFamily X) {E : DivisorFamily X} {e : E.ι ≃o Fin Φ.nextLabel}
  {n m : ℕ}

include f in
/-- *The marked transform at stage `i` of the geometric Step 3 is the monomial ideal of the
stage-`i` piece family*, the recursion (1′) of [Kol07, Definition 66],
`I_{i+1} = (π_i)_*^{-1}(I_i, m)`, computed. -/
theorem markedTransformSeq_realize (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (hV : Φ.IsValid n m)
    (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f)
    (i : Fin ((Φ.realize n m hV).length + 1)) :
    (Φ.realize n m hV).markedTransformSeq (E.monomial Φ.exponentAt) m i =
      ((Φ.realize n m hV).totalTransformSeq E i).monomial
        (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2 i).exponentAt :=
  markedTransformSeq_realizeAux _ f Φ hE hΦ hV hn (MonomialState.step3_isRun _) i

include f in
/-- *The geometric Step 3 is a smooth blow-up sequence of order `≥ m` starting with
`(X, 𝒪_X(−∑ a_D D), m, E)`* ([Kol07, Definition 66], for the run of [Kol07, 111, Step 3]):
every centre is Kollár's choice at its stage, hence smooth with simple normal crossings with
`E_i` and of order `≥ m` for the induced marked ideal. -/
theorem realize_isOrderGeSeq (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (hV : Φ.IsValid n m)
    (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f) :
    (Φ.realize n m hV).IsOrderGeSeq f (E.monomial Φ.exponentAt) m E :=
  isOrderGeSeq_realizeAux _ f Φ hE hΦ hV hn (MonomialState.step3_isRun _)

include f in
/-- *At the end of Step 3 the induced marked monomial ideal has `max-ord < m`*, the conclusion
of [Kol07, 111, Step 3] ("at the end of Step 3.n we are done"): every face of the final nerve
has sum `< m` (`step3_maxOrd_lt`), and the order at a point is the sum over its face
(`ord_monomial_eq_total`); a point off the final boundary has the empty face. -/
theorem realize_maxOrd_lt (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (hV : Φ.IsValid n m)
    (hn : ∃ n' ≤ n, SmoothOfRelativeDimension n' f) :
    ((Φ.realize n m hV).markedTransformSeq (E.monomial Φ.exponentAt) m
      (Fin.last (Φ.realize n m hV).length)).maxOrd < (m : ℕ∞) := by
  have hLN : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
  have hproper : IsProper ((realizeAux Φ m (MonomialState.step3 (Φ.toState n m hV)).2).stageMap
      (Fin.last (Φ.realize n m hV).length)) :=
    isProper_stageMap _ _
  have hsm : Smooth ((realizeAux Φ m (MonomialState.step3 (Φ.toState n m hV)).2).stageMap
      (Fin.last (Φ.realize n m hV).length) ≫ f) := by
    obtain ⟨n', -, h⟩ := Φ.exists_smoothOfRelativeDimension_stageMap_realize f hE hΦ hV hn
      (Fin.last (Φ.realize n m hV).length)
    exact (SmoothOfRelativeDimension.smooth n' _ :
      Smooth ((Φ.realize n m hV).stageMap (Fin.last (Φ.realize n m hV).length) ≫ f))
  have hE' := Φ.isSnc_totalTransformSeq_realize f hE hΦ hV hn (Fin.last (Φ.realize n m hV).length)
  have hΦ' := Φ.realizes_stagePieces f hE hΦ hV hn (Fin.last (Φ.realize n m hV).length)
  have hV' := Φ.valid_stagePieces f hE hΦ hV hn (Fin.last (Φ.realize n m hV).length)
  have hinv := Φ.realize_invariant f hE hΦ hV hn (Fin.last (Φ.realize n m hV).length) hV'
  -- the final family's state is the end state of the combinatorial Step 3
  have hlen : (MonomialState.step3 (Φ.toState n m hV)).2.length ≤
      ((Fin.last (Φ.realize n m hV).length : Fin _) : ℕ) := by
    rw [Fin.val_last]
    exact (realizeAux_length Φ m _).ge
  have hfinal : (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2
      (Fin.last (Φ.realize n m hV).length)).toState n m hV' =
      (MonomialState.step3 (Φ.toState n m hV)).1 := by
    rw [hinv, (MonomialState.step3_isRun (Φ.toState n m hV)).fold, List.take_of_length_le hlen]
  have hm1 : 1 ≤ m := (Φ.toState n m hV).one_le_m
  rw [Φ.markedTransformSeq_realize f hE hΦ hV hn (Fin.last (Φ.realize n m hV).length)]
  refine lt_of_le_of_lt ((maxOrd_le_iff _).mpr fun x => ?_)
    (show ((m - 1 : ℕ) : ℕ∞) < (m : ℕ∞) by exact_mod_cast Nat.sub_lt hm1 one_pos)
  have hord := (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2
    (Fin.last (Φ.realize n m hV).length)).ord_monomial_eq_total
    ((realizeAux Φ m (MonomialState.step3 (Φ.toState n m hV)).2).stageMap
      (Fin.last (Φ.realize n m hV).length) ≫ f) hE' hΦ' x
  have hle : (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2
      (Fin.last (Φ.realize n m hV).length)).total
        ((stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2
          (Fin.last (Φ.realize n m hV).length)).faceAt x) ≤ m - 1 := by
    by_cases hx : x ∈ ((Φ.realize n m hV).totalTransformSeq E
        (Fin.last (Φ.realize n m hV).length)).support
    · -- the face through `x` is a face of the final nerve, of sum `< m`
      have hT := (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2
        (Fin.last (Φ.realize n m hV).length)).faceAt_mem_nerve hΦ' hx
      have hT' : (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2
          (Fin.last (Φ.realize n m hV).length)).faceAt x ∈
          (MonomialState.step3 (Φ.toState n m hV)).1.nerve := by
        rw [← hfinal]
        exact hT
      have hlt := MonomialState.step3_maxOrd_lt (Φ.toState n m hV) hT'
      rw [← hfinal] at hlt
      exact Nat.le_sub_one_of_lt hlt
    · -- no piece passes through `x`: the empty face
      have hface : (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2
          (Fin.last (Φ.realize n m hV).length)).faceAt x = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun c hc => hx ?_
        obtain ⟨hcn, hxc⟩ := (PieceFamily.mem_faceAt _).mp hc
        exact (DivisorFamily.mem_support_iff_exists _ x).mpr
          ⟨_, (stagePieces Φ m (MonomialState.step3 (Φ.toState n m hV)).2
            (Fin.last (Φ.realize n m hV).length)).mem_support_component_of_mem_piece hΦ' hcn hxc⟩
      rw [hface, total, Finset.sum_empty]
      exact Nat.zero_le _
  exact hord.le.trans (by exact_mod_cast hle)

end Hironaka.Monomial.PieceFamily
