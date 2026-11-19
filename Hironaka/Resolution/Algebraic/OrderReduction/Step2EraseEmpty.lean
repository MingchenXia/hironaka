/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step21EraseEmpty
public import Hironaka.Resolution.Algebraic.OrderReduction.Step2Functorial
import Hironaka.Resolution.Algebraic.Kol07.AppendLast
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyEmbedding
import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Kol07.ExceptionalFamilyPullback
import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivSeqFunctor
import Hironaka.Resolution.Algebraic.OrderReduction.Functorial
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Functorial
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Assembly
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Basic
import Hironaka.Resolution.Algebraic.Tuning.Cosupport
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The maximal-contact case of order reduction under an arbitrary smooth morphism

Clause (2) of [Kol07, Theorem 103] with the second clause of [Kol07, 34.1], for the
maximal-contact case: for an arbitrary smooth morphism `h : Y ⟶ X`,
`BO^{h⁻¹H}_{n,m}(Y, h^*I, h⁻¹E)` is the pull-back of `BO^H_{n,m}(X, I, E)` with the empty blow-ups
deleted, under the hypothesis `hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m)` that the
boundary-clearing data of [Kol07, Lemma 102] at every mark are indifferent to empty boundary
members (`Hironaka/Resolution/Algebraic/OrderReduction/EmptyIndifferent.lean`).

* Step 2.1 is `Hironaka/Resolution/Algebraic/OrderReduction/Step21EraseEmpty.lean`.
* Step 2.2 (`step22Seq_eraseEmpty_pullback_aux`): the Step 2.2 triple of the erased pull-back,
  `(X'_r, I'_r, F'_r + H'_r)`, becomes, once its boundary is replaced by the inverse image of
  `F_r + H_r` along the last-stage isomorphism and the last-stage lift (`step22Erased`), an exact
  pull-back of the Step 2.2 triple of `H`; `F'_r + H'_r` is that boundary with the unit-ideal
  members deleted, `H'_r` at the last position on both sides (`exists_embedding_step22Erased`,
  `exceptionalFamily_eraseEmpty_embeds`, `strictTransformSeq_eraseEmpty_last`). The hypothesis
  `hind` at the mark `s(m)` and the second clause of [Kol07, 34.1] for Lemma 102 on the tuned
  exact pull-back give the equality when both maximal orders are `m`; when the pulled-back maximal
  order drops below `m`, the erased pull-back is a smooth blow-up sequence of order `s(m)` for a
  tuned ideal of maximal order `< s(m)` without empty blow-ups, hence empty
  (`eq_nil_of_isOrderSeq_of_maxOrd_lt`, `maxOrd_tuned_lt`).
* `step2Seq_eraseEmpty_pullback` assembles both steps through `pullback_concat` and
  `eraseEmpty_concat`; `maxContactCase_eraseEmpty_pullback` reads the result back through the
  tuning of Step 1, the case `max-ord h^*I < m ≤ max-ord I` by the same emptiness argument.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Hironaka Scheme BlowUpSequence Hironaka.Sequence
  Scheme.IdealSheafData IsLocalRing

namespace Hironaka.BO

variable {k : Type u} [Field k] [CharZero k] {n m : ℕ}

section Tuned

/-- Where the maximal order is below the mark, the maximal coefficient ideal is the unit ideal, of
maximal order `0 < s` (`ord_W_eq_zero_of_ord_lt`). -/
theorem maxOrd_W_lt_of_maxOrd_lt {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (I : X.IdealSheafData) {m : ℕ} (hm : 1 ≤ m)
    (hI : I.maxOrd < m) {s : ℕ} (hs : 1 ≤ s) : (IdealSheafData.W f I m s).maxOrd < s := by
  rw [maxOrd_lt_iff_forall_ord_lt _ hs]
  intro x
  rw [IdealSheafData.ord_W_eq_zero_of_ord_lt f n I m s hm ((I.le_maxOrd x).trans_lt hI)]
  exact_mod_cast hs

/-- The tuned triple of a triple of maximal order below the mark has maximal order below `s(m)`. -/
theorem maxOrd_tuned_lt {T : Triple k} {m : ℕ} (hm : 1 ≤ m) (hI : T.I.maxOrd < m) :
    (T.tuned m hm).I.maxOrd < (tuningParam m : ℕ∞) := by
  obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
  exact maxOrd_W_lt_of_maxOrd_lt (T.X.left ↘ Spec (.of k)) n T.I hm hI (one_le_tuningParam m)

end Tuned

section Step22

variable (T : Triple k) (hn : T.HasDimLE n) (hmax : T.I.maxOrd ≤ m) (bd : ∀ m j : ℕ, BDData.{u} n m
  j)
  (hm : 1 ≤ m)

omit [CharZero k] hn hmax bd hm in
/-- The Step 2.2 boundary of the pulled-back sequence is the inverse image of the Step 2.2 boundary
along the last-stage lift (`exceptionalFamily_pullback`, `strictTransformSeq_pullback_last`). -/
theorem step22Family_pullback_eq {T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) (S₁ : BlowUpSequence T.X.left) (H : T.X.left.IdealSheafData) :
    ((S₁.pullback h).exceptionalFamily T'.E).append
        ((S₁.pullback h).strictTransformSeq (H.comap h) (Fin.last _)) =
      ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).comap
        (S₁.pullbackLastHom h) := by
  have e2 : (S₁.pullback h).exceptionalFamily T'.E =
      (S₁.exceptionalFamily T.E).comap (S₁.pullbackLastHom h) :=
    (congrArg (fun E => (S₁.pullback h).exceptionalFamily E =
      (S₁.exceptionalFamily T.E).comap (S₁.pullbackLastHom h)) hpb.2.2).mpr
      (exceptionalFamily_pullback S₁ h T.E)
  exact (congrArg₂ DivisorFamily.append e2 (strictTransformSeq_pullback_last S₁ h H)).trans
    (DivisorFamily.comap_append _ _ _).symm

omit hn hmax bd hm in
/-- The Step 2.2 boundary of the pulled-back sequence has normal crossings. -/
theorem isSnc_step22Family_pullback {T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) {S₁ : BlowUpSequence T.X.left}
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc) :
    (((S₁.pullback h).exceptionalFamily T'.E).append
      ((S₁.pullback h).strictTransformSeq (H.comap h) (Fin.last _))).IsSnc := by
  rw [step22Family_pullback_eq T h hpb S₁ H]
  have hsm : Smooth (S₁.pullbackLastHom h) := smooth_pullbackLastHom S₁ h
  exact @isSnc_comap_of_smooth _ _ k _ _ ((T.induced S₁ hS₁ (Fin.last _)).X.left ↘ Spec (.of k))
    (T.induced S₁ hS₁ (Fin.last _)).smooth (S₁.pullbackLastHom h) hsm _ hsnc

omit hn hmax bd hm in
/-- The inverse image of the Step 2.2 boundary of the pulled-back sequence along the last-stage
isomorphism has normal crossings. -/
theorem isSnc_step22Erased_E {T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) {S₁ : BlowUpSequence T.X.left}
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hP : (S₁.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc) :
    ((((S₁.pullback h).exceptionalFamily T'.E).append
      ((S₁.pullback h).strictTransformSeq (H.comap h) (Fin.last _))).comap
        (S₁.pullback h).eraseEmptyLastHom).IsSnc := by
  have h₂₀ : Smooth (S₁.pullback h).eraseEmptyLastHom := inferInstance
  exact @isSnc_comap_of_smooth _ _ k _ _
    ((T'.induced (S₁.pullback h) hP (Fin.last _)).X.left ↘ Spec (.of k))
    (T'.induced (S₁.pullback h) hP (Fin.last _)).smooth (S₁.pullback h).eraseEmptyLastHom h₂₀ _
    (isSnc_step22Family_pullback T h hpb hS₁ hsnc)

omit hn hmax bd hm in
/-- The Step 2.2 triple of the erased pull-back with its boundary replaced by the inverse image of
the Step 2.2 boundary of the pull-back along the last-stage isomorphism: the exact pull-back of
the Step 2.2 triple of `H` (`isPullbackOf_step22Erased_comp`). The boundary `F'_r + H'_r` of the
actual Step 2.2 triple is this one with the unit-ideal members deleted
(`exists_embedding_step22Erased`). -/
noncomputable def step22Erased {T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) {S₁ : BlowUpSequence T.X.left}
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hP : (S₁.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S₁.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc) :
    Triple k :=
  { inducedErased (S₁.pullback h) hP hP' with
    E := (((S₁.pullback h).exceptionalFamily T'.E).append
      ((S₁.pullback h).strictTransformSeq (H.comap h) (Fin.last _))).comap
        (S₁.pullback h).eraseEmptyLastHom
    isSnc := isSnc_step22Erased_E T h hpb hS₁ hP hsnc }

omit hn hmax bd hm in
/-- `step22Erased` is the exact pull-back of the Step 2.2 triple of the pulled-back sequence along
the last-stage isomorphism. -/
theorem isPullbackOf_step22Erased {T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) {S₁ : BlowUpSequence T.X.left}
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hP : (S₁.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S₁.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc) :
    (step22Erased T h hpb hS₁ hP hP' hsnc).IsPullbackOf
      (step22TripleOfSeq T' (S₁.pullback h) hP (isSnc_step22Family_pullback T h hpb hS₁ hsnc))
      (S₁.pullback h).eraseEmptyLastHom :=
  ⟨(isPullbackOf_inducedErased hP hP').1, (isPullbackOf_inducedErased hP hP').2.1, rfl⟩

omit hn hmax bd hm in
/-- `step22Erased` is the exact pull-back of the Step 2.2 triple of `H` along the last-stage
isomorphism followed by the last-stage lift of `h`. -/
theorem isPullbackOf_step22Erased_comp {T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) {S₁ : BlowUpSequence T.X.left}
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hP : (S₁.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S₁.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc) :
    (step22Erased T h hpb hS₁ hP hP' hsnc).IsPullbackOf (step22TripleOfSeq T S₁ hS₁ hsnc)
      ((S₁.pullback h).eraseEmptyLastHom ≫ S₁.pullbackLastHom h) :=
  (isPullbackOf_step22TripleOfSeq h hpb hS₁ hP hsnc
    (isSnc_step22Family_pullback T h hpb hS₁ hsnc)).comp
    (isPullbackOf_step22Erased T h hpb hS₁ hP hP' hsnc)

omit hn hmax bd hm in
/-- The structure map of `step22Erased` to the Step 2.2 triple of `H` is smooth. -/
theorem smooth_step22Erased_hom {T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) {S₁ : BlowUpSequence T.X.left}
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hP : (S₁.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S₁.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc) :
    @Smooth (step22Erased T h hpb hS₁ hP hP' hsnc).X.left (step22TripleOfSeq T S₁ hS₁ hsnc).X.left
      ((S₁.pullback h).eraseEmptyLastHom ≫ S₁.pullbackLastHom h) :=
  smooth_eraseEmptyLastHom_comp_pullbackLastHom h hS₁ hP hP'

omit hmax bd hm in
/-- `step22Erased` lies in the boundary-clearing class at every position at which the Step 2.2
triple of `H` does. -/
theorem bdClass_step22Erased {T' : Triple k} (hn' : T'.HasDimLE n)
    (h : T'.X.left ⟶ T.X.left) [Smooth h] (hpb : T'.IsPullbackOf T h) {S₁ : BlowUpSequence T.X.left}
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hP : (S₁.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S₁.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc)
    {j : ℕ} (hT₂ : Triple.BDClass n m j (step22TripleOfSeq T S₁ hS₁ hsnc)) :
    Triple.BDClass n m j (step22Erased T h hpb hS₁ hP hP' hsnc) := by
  have hsm := smooth_step22Erased_hom T h hpb hS₁ hP hP' hsnc
  exact bdClass_of_isPullbackOf _ (isPullbackOf_step22Erased_comp T h hpb hS₁ hP hP' hsnc) hT₂
    (hasDimLE_induced_last T' hn' hP')

omit hn hmax bd in
/-- Restoring the erased boundary in `step22Erased` gives back the Step 2.2 triple of the erased
pullback (structure eta). -/
theorem step22Erased_update_eq {T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) {S₁ : BlowUpSequence T.X.left}
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hP : (S₁.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S₁.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc)
    (hsnc' : (((S₁.pullback h).eraseEmpty.exceptionalFamily T'.E).append
      ((S₁.pullback h).eraseEmpty.strictTransformSeq (H.comap h) (Fin.last _))).IsSnc) :
    ({ (step22Erased T h hpb hS₁ hP hP' hsnc).tuned m hm with
        E := ((S₁.pullback h).eraseEmpty.exceptionalFamily T'.E).append
          ((S₁.pullback h).eraseEmpty.strictTransformSeq (H.comap h) (Fin.last _))
        isSnc := hsnc' } : Triple k) =
      (step22TripleOfSeq T' (S₁.pullback h).eraseEmpty hP' hsnc').tuned m hm := rfl

omit hn hmax bd hm in
/-- The Step 2.2 boundary `F'_r + H'_r` of the erased pull-back embeds into the boundary of
`step22Erased` as a deletion of unit-ideal members, `H'_r ↦ H_r` at the last positions
(`exceptionalFamily_eraseEmpty_embeds`, `strictTransformSeq_eraseEmpty_last`,
`monoEquivOfFin_lex_inr_last`). -/
theorem exists_embedding_step22Erased {T' : Triple k} (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hpb : T'.IsPullbackOf T h) {S₁ : BlowUpSequence T.X.left}
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hP : (S₁.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S₁.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc)
    (hj' : Fintype.card ((S₁.pullback h).eraseEmpty.exceptionalFamily T'.E).ι <
      Fintype.card (((S₁.pullback h).eraseEmpty.exceptionalFamily T'.E).append
        ((S₁.pullback h).eraseEmpty.strictTransformSeq (H.comap h) (Fin.last _))).ι)
    (hj : Fintype.card ((S₁.pullback h).exceptionalFamily T'.E).ι <
      Fintype.card (step22Erased T h hpb hS₁ hP hP' hsnc).E.ι) :
    ∃ e : (((S₁.pullback h).eraseEmpty.exceptionalFamily T'.E).append
        ((S₁.pullback h).eraseEmpty.strictTransformSeq (H.comap h) (Fin.last _))).ι ↪o
        (step22Erased T h hpb hS₁ hP hP' hsnc).E.ι,
      (∀ i, (step22Erased T h hpb hS₁ hP hP' hsnc).E.component (e i) =
        (((S₁.pullback h).eraseEmpty.exceptionalFamily T'.E).append
          ((S₁.pullback h).eraseEmpty.strictTransformSeq (H.comap h) (Fin.last _))).component i) ∧
      (∀ b, b ∉ Set.range e → (step22Erased T h hpb hS₁ hP hP' hsnc).E.component b = ⊤) ∧
      e (DivisorFamily.nthIdx _ ⟨_, hj'⟩) = DivisorFamily.nthIdx _ ⟨_, hj⟩ := by
  obtain ⟨eExc, hcE, htE⟩ := exceptionalFamily_eraseEmpty_embeds (S₁.pullback h) T'.E
  refine ⟨sumLexMapEmb eExc, fun i => ?_, fun b hb => ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := toLex.surjective i
    rcases a with b | u
    · exact hcE b
    · exact (strictTransformSeq_eraseEmpty_last (S₁.pullback h) (H.comap h)).symm
  · obtain ⟨a, rfl⟩ := toLex.surjective b
    rcases a with b₀ | u
    · have hb₀ : b₀ ∉ Set.range eExc := fun ⟨c, hc⟩ =>
        hb ⟨toLex (Sum.inl c), (sumLexMapEmb_apply_inl eExc c).trans (congrArg _ (congrArg _ hc))⟩
      exact htE b₀ hb₀
    · exact (hb ⟨toLex (Sum.inr u), rfl⟩).elim
  · change sumLexMapEmb eExc (monoEquivOfFin
        (((S₁.pullback h).eraseEmpty.exceptionalFamily T'.E).ι ⊕ₗ PUnit.{u + 1}) rfl ⟨_, hj'⟩) =
      monoEquivOfFin (((S₁.pullback h).exceptionalFamily T'.E).ι ⊕ₗ PUnit.{u + 1}) rfl ⟨_, hj⟩
    rw [monoEquivOfFin_lex_inr_last hj', monoEquivOfFin_lex_inr_last hj]
    rfl

/-- Step 2.2 on the erased pull-back is the erased pull-back of Step 2.2, carried along the
last-stage isomorphism ([Kol07, 104, Step 2.3] with the second clause of [Kol07, 34.1]; the
boundary-clearing functor of [Kol07, Lemma 102] at the mark through the re-tuning): the
indifference `hind` at the mark `s(m)`, at the position of `H'_r` against that of `H_r`, the
second clause of [Kol07, 34.1] for the boundary-clearing data on the tuned exact pull-back, and
the emptiness of the erased pull-back when the maximal order of the pull-back drops below `m`. -/
theorem step22Seq_eraseEmpty_pullback_aux {T' : Triple k} (hn' : T'.HasDimLE n)
    (h : T'.X.left ⟶ T.X.left)
    [Smooth h] (hpb : T'.IsPullbackOf T h) (hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m))
    {S₁ : BlowUpSequence T.X.left} (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m)
    (hP : (S₁.pullback h).IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (hP' : (S₁.pullback h).eraseEmpty.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    {H : T.X.left.IdealSheafData}
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq H (Fin.last _))).IsSnc)
    (hsnc' : (((S₁.pullback h).eraseEmpty.exceptionalFamily T'.E).append
      ((S₁.pullback h).eraseEmpty.strictTransformSeq (H.comap h) (Fin.last _))).IsSnc)
    {j j' : ℕ} (hj : j = Fintype.card ((S₁.pullback h).exceptionalFamily T'.E).ι)
    (hj' : j' = Fintype.card ((S₁.pullback h).eraseEmpty.exceptionalFamily T'.E).ι)
    (hT₂ : Triple.BDClass n m j (step22TripleOfSeq T S₁ hS₁ hsnc))
    (hT₂' : Triple.BDClass n m j' (step22TripleOfSeq T' (S₁.pullback h).eraseEmpty hP' hsnc')) :
    (step22Functor bd m j' hm).seq (step22TripleOfSeq T' (S₁.pullback h).eraseEmpty hP' hsnc')
        hT₂' =
      (((step22Functor bd m j hm).seq (step22TripleOfSeq T S₁ hS₁ hsnc) hT₂).pullback
        (S₁.pullbackLastHom h)).eraseEmpty.pullback (S₁.pullback h).eraseEmptyLastHom := by
  subst hj hj'
  have hTb := bdClass_step22Erased T hn' h hpb hS₁ hP hP' hsnc hT₂
  have hpbBig := isPullbackOf_step22Erased_comp T h hpb hS₁ hP hP' hsnc
  have hsm := smooth_step22Erased_hom T h hpb hS₁ hP hP' hsnc
  have hmaxTb : (step22Erased T h hpb hS₁ hP hP' hsnc).I.maxOrd ≤
      (step22TripleOfSeq T S₁ hS₁ hsnc).I.maxOrd := by
    rw [hpbBig.2.1]
    exact maxOrd_comap_le_of_smooth _ _
  by_cases h₂ : (step22TripleOfSeq T S₁ hS₁ hsnc).I.maxOrd = m
  · by_cases h₂' : (step22TripleOfSeq T' (S₁.pullback h).eraseEmpty hP' hsnc').I.maxOrd = m
    · rw [step22Functor_seq_of_maxOrd_eq bd m _ hm _ hT₂ h₂,
        step22Functor_seq_of_maxOrd_eq bd m _ hm _ hT₂' h₂']
      have h₂b : (step22Erased T h hpb hS₁ hP hP' hsnc).I.maxOrd = m := h₂'
      obtain ⟨e, hc, ht, hpos⟩ := exists_embedding_step22Erased T h hpb hS₁ hP hP' hsnc
        (card_lt_card_ι_append _ _) hTb.2.2
      have hTbt := bdClass_tuned hTb h₂b hm
      have hT₂'t := bdClass_tuned hT₂' h₂' hm
      have hT₂'t' : Triple.BDClass n (tuningParam m) _
          ({ (step22Erased T h hpb hS₁ hP hP' hsnc).tuned m hm with
            E := ((S₁.pullback h).eraseEmpty.exceptionalFamily T'.E).append
              ((S₁.pullback h).eraseEmpty.strictTransformSeq (H.comap h) (Fin.last _))
            isSnc := hsnc' } : Triple k) := hT₂'t
      have hpos' : e (DivisorFamily.nthIdx _ ⟨_, hT₂'t.2.2⟩) =
          DivisorFamily.nthIdx ((step22Erased T h hpb hS₁ hP hP' hsnc).tuned m hm).E
            ⟨_, hTbt.2.2⟩ := hpos
      have key := hind (tuningParam m) k ((step22Erased T h hpb hS₁ hP hP' hsnc).tuned m hm) _
        hsnc' e hc ht _ _ hTbt.2.2 hT₂'t.2.2 hpos' hTbt hT₂'t'
      have hsmt : @Smooth ((step22Erased T h hpb hS₁ hP hP' hsnc).tuned m hm).X.left
          ((step22TripleOfSeq T S₁ hS₁ hsnc).tuned m hm).X.left
          ((S₁.pullback h).eraseEmptyLastHom ≫ S₁.pullbackLastHom h) := hsm
      have key₂ := ((bd (tuningParam m) _).commutesWithSmooth k).2
        ((step22TripleOfSeq T S₁ hS₁ hsnc).tuned m hm)
        ((step22Erased T h hpb hS₁ hP hP' hsnc).tuned m hm)
        ((S₁.pullback h).eraseEmptyLastHom ≫ S₁.pullbackLastHom h) (isPullbackOf_tuned hpbBig m hm)
        (bdClass_tuned hT₂ h₂ hm) hTbt
      exact (eq_of_heq (OrderSeqAssignment.seq_congr _
        (step22Erased_update_eq T hm h hpb hS₁ hP hP' hsnc hsnc').symm hT₂'t hT₂'t')).trans
        (key.symm.trans (key₂.trans ((congrArg BlowUpSequence.eraseEmpty
          (pullback_comp _ (S₁.pullback h).eraseEmptyLastHom (S₁.pullbackLastHom h))).trans
          (eraseEmpty_pullback_of_flat_surjective _ (S₁.pullback h).eraseEmptyLastHom
            (surjective_of_isIso _)))))
    · have hlt' : (step22TripleOfSeq T' (S₁.pullback h).eraseEmpty hP' hsnc').I.maxOrd < m :=
        lt_of_le_of_ne hT₂'.2.1 h₂'
      rw [step22Functor_seq_of_maxOrd_lt bd m _ hm _ hT₂' hlt',
        step22Functor_seq_of_maxOrd_eq bd m _ hm _ hT₂ h₂]
      have hsm₁ : Smooth (S₁.pullbackLastHom h) := smooth_pullbackLastHom S₁ h
      have hsm₁' : @Smooth ((step22TripleOfSeq T' (S₁.pullback h) hP
          (isSnc_step22Family_pullback T h hpb hS₁ hsnc)).tuned m hm).X.left
          ((step22TripleOfSeq T S₁ hS₁ hsnc).tuned m hm).X.left (S₁.pullbackLastHom h) := hsm₁
      have hpbP := isPullbackOf_tuned (isPullbackOf_step22TripleOfSeq h hpb hS₁ hP hsnc
        (isSnc_step22Family_pullback T h hpb hS₁ hsnc)) m hm
      have hord := hpbP.isOrderSeq_eraseEmpty_pullback
        (((bd (tuningParam m) _).functor k).isOrderSeq _ (bdClass_tuned hT₂ h₂ hm))
      have hltP : (step22TripleOfSeq T' (S₁.pullback h) hP
          (isSnc_step22Family_pullback T h hpb hS₁ hsnc)).I.maxOrd < m := by
        refine lt_of_le_of_lt ?_ hlt'
        change ((S₁.pullback h).weakTransformSeq T'.I (Fin.last _)).maxOrd ≤
          ((S₁.pullback h).eraseEmpty.weakTransformSeq T'.I (Fin.last _)).maxOrd
        obtain ⟨n', hn'⟩ := T'.smoothOfRelativeDimension
        rw [weakTransformSeq_eraseEmpty_last (S₁.pullback h) (T'.X.left ↘ Spec (.of k))
          n' T'.I T'.E m hP]
        have hsurj : Function.Surjective (S₁.pullback h).eraseEmptyLastHom := surjective_of_isIso _
        exact maxOrd_le_maxOrd_comap_of_surjective _ hsurj _
      have hnil := eq_nil_of_isOrderSeq_of_maxOrd_lt _ hord (noEmptyCenters_eraseEmpty _)
        (maxOrd_tuned_lt hm hltP)
      exact ((congrArg (fun R : BlowUpSequence (S₁.pullback h).last =>
        R.pullback (S₁.pullback h).eraseEmptyLastHom) hnil).trans (pullback_nil _)).symm
  · have hlt : (step22TripleOfSeq T S₁ hS₁ hsnc).I.maxOrd < m := lt_of_le_of_ne hT₂.2.1 h₂
    have hlt' : (step22TripleOfSeq T' (S₁.pullback h).eraseEmpty hP' hsnc').I.maxOrd < m :=
      lt_of_le_of_lt hmaxTb hlt
    rw [step22Functor_seq_of_maxOrd_lt bd m _ hm _ hT₂ hlt,
      step22Functor_seq_of_maxOrd_lt bd m _ hm _ hT₂' hlt']
    rfl

end Step22

section Step2

variable (T : Triple k) (hn : T.HasDimLE n) (hmax : T.I.maxOrd ≤ m) (bd : ∀ m j : ℕ, BDData.{u} n m
  j)
  (hm : 1 ≤ m) {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
  (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H)

/-- Step 2 on the pulled-back data, generalised over its Step 2.1 sequence `S₁'` with
`S₁' = (S₁.pullback h).eraseEmpty`: it is the erased pull-back of Step 2. -/
theorem step2Seq_eraseEmpty_pullback_aux {T' : Triple k} (hn' : T'.HasDimLE n)
    (h : T'.X.left ⟶ T.X.left)
    [Smooth h] (hpb : T'.IsPullbackOf T h) (hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m))
    (S₁' : BlowUpSequence T'.X.left) (hS₁' : S₁'.IsOrderSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.E m)
    (e₁ : S₁' = ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback h).eraseEmpty)
    (hsnc' : ((S₁'.exceptionalFamily T'.E).append
      (S₁'.strictTransformSeq (H.comap h) (Fin.last _))).IsSnc) (j' : ℕ)
    (hj' : j' = Fintype.card (S₁'.exceptionalFamily T'.E).ι)
    (hT₂' : Triple.BDClass n m j' (step22TripleOfSeq T' S₁' hS₁' hsnc')) :
    S₁'.concat ((step22Functor bd m j' hm).seq (step22TripleOfSeq T' S₁' hS₁' hsnc') hT₂') =
      ((step2Seq T hn hmax bd hm hH hle).pullback h).eraseEmpty := by
  subst e₁
  have hP := hpb.isOrderSeq_pullback (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι))
  have hjP : Fintype.card ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily
      T.E).ι = Fintype.card (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback
        h).exceptionalFamily T'.E).ι := by
    have hj2 : Fintype.card (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback
        h).exceptionalFamily T'.E).ι = Fintype.card
        (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback h).exceptionalFamily
          (T.E.comap h)).ι := by
      rw [hpb.2.2]
    have hj3 : Fintype.card (((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback
        h).exceptionalFamily (T.E.comap h)).ι = Fintype.card
        ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.exceptionalFamily T.E).ι :=
      Fintype.card_congr (Equiv.cast (congrArg DivisorFamily.ι
        (exceptionalFamily_pullback _ h T.E)))
    exact (hj2.trans hj3).symm
  refine Eq.trans ?_ ((congrArg BlowUpSequence.eraseEmpty (pullback_concat _ _ h)).trans
    (eraseEmpty_concat _ _)).symm
  refine congrArg _ ?_
  exact step22Seq_eraseEmpty_pullback_aux T bd hm hn' h hpb hind
    (isOrderSeq_step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)) hP hS₁'
    (step22Triple T hn hmax bd hm hH hle).isSnc hsnc' hjP hj'
    (bdClass_step22Triple T hn hmax bd hm hH hle) hT₂'

/-- For an arbitrary smooth morphism `h`, Step 2 on the pulled-back data is the pull-back of Step 2
with the empty blow-ups deleted ([Kol07, 104, Step 2.3] with the second clause of
[Kol07, 34.1]). -/
theorem step2Seq_eraseEmpty_pullback {T' : Triple k} (hn' : T'.HasDimLE n)
    (hmax' : T'.I.maxOrd ≤ m) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hH' : IsSmoothDivisor (H.comap h))
    (hle' : IdealSheafData.IsMaximalContact (T'.X.left ↘ Spec (.of k)) T'.I m (H.comap h))
    (hpb : T'.IsPullbackOf T h) (hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m)) :
    step2Seq T' hn' hmax' bd hm hH' hle' = ((step2Seq T hn hmax bd hm hH hle).pullback
      h).eraseEmpty := by
  have hcard : Fintype.card T'.E.ι = Fintype.card T.E.ι :=
    Fintype.card_congr (Equiv.cast (congrArg DivisorFamily.ι hpb.2.2))
  have e₁ : (step21Seq T' hn' hmax' (bd m) (Fintype.card T'.E.ι)).1 =
      ((step21Seq T hn hmax (bd m) (Fintype.card T.E.ι)).1.pullback h).eraseEmpty := by
    rw [hcard]
    exact step21Seq_eraseEmpty_pullback T hn hmax (bd m) hn' hmax' h hpb (hind m) _
  exact step2Seq_eraseEmpty_pullback_aux T hn hmax bd hm hH hle hn' h hpb hind _
    (isOrderSeq_step21Seq T' hn' hmax' (bd m) (Fintype.card T'.E.ι)) e₁
    (step22Triple T' hn' hmax' bd hm hH' hle').isSnc _ rfl
    (bdClass_step22Triple T' hn' hmax' bd hm hH' hle')

end Step2

section MaxContactCase

variable (T : Triple k) (hT : Triple.BOClass n m T) {H : T.X.left.IdealSheafData}
  (hH : IsSmoothDivisor H)
  (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I m H) (bd : ∀ m j : ℕ,
      BDData.{u} n m j)

/-- **The maximal-contact case of order reduction commutes with arbitrary smooth morphisms**
(clause (2) of [Kol07, Theorem 103] with the second clause of [Kol07, 34.1]): for every smooth
`h`, `BO^{h⁻¹H}_{n,m}(Y, h^*I, h⁻¹E)` is the pull-back of `BO^H_{n,m}(X, I, E)` with its empty
blow-ups deleted, under the hypothesis `hind` that the boundary-clearing data of
[Kol07, Lemma 102] at every mark are indifferent to empty boundary members. -/
theorem maxContactCase_eraseEmpty_pullback (hind : ∀ m, BDFamily.IndifferentToEmptyMembers (bd m))
    {T' : Triple k} (hT' : Triple.BOClass n m T')
    (h : T'.X.left ⟶ T.X.left) [Smooth h] (hpb : T'.IsPullbackOf T h)
    (hH' : IsSmoothDivisor (H.comap h))
    (hle' : IdealSheafData.IsMaximalContact (T'.X.left ↘ Spec (.of k)) T'.I m (H.comap h)) :
    maxContactCase T' hT' hH' hle' bd = ((maxContactCase T hT hH hle bd).pullback h).eraseEmpty :=
      by
  have hle_max : T'.I.maxOrd ≤ T.I.maxOrd := by
    rw [hpb.2.1]
    exact maxOrd_comap_le_of_smooth h _
  by_cases h₁ : T.I.maxOrd = m
  · by_cases h₁' : T'.I.maxOrd = m
    · rw [maxContactCase_of_maxOrd_eq T hT hH hle bd h₁,
        maxContactCase_of_maxOrd_eq T' hT' hH' hle' bd h₁']
      exact step2Seq_eraseEmpty_pullback (T.tuned m hT.1) (hasDimLE_tuned hT.2.1 m hT.1)
        (le_of_eq (maxOrd_tuned h₁ hT.1)) bd (one_le_tuningParam m) hH
        (retune_keeps_maxContact h₁ hT.1 hle) (T' := T'.tuned m hT'.1)
        (hasDimLE_tuned hT'.2.1 m hT'.1) (le_of_eq (maxOrd_tuned h₁' hT'.1)) h hH'
        (retune_keeps_maxContact h₁' hT'.1 hle') (isPullbackOf_tuned hpb m hT.1) hind
    · have hlt' : T'.I.maxOrd < m := lt_of_le_of_ne hT'.2.2 h₁'
      rw [maxContactCase_of_maxOrd_lt T' hT' hH' hle' bd hlt',
        maxContactCase_of_maxOrd_eq T hT hH hle bd h₁]
      have hord := (isPullbackOf_tuned hpb m hT.1).isOrderSeq_eraseEmpty_pullback
        (isOrderSeq_step2Seq (T.tuned m hT.1) (hasDimLE_tuned hT.2.1 m hT.1)
          (le_of_eq (maxOrd_tuned h₁ hT.1)) bd (one_le_tuningParam m) hH
          (retune_keeps_maxContact h₁ hT.1 hle))
      exact (eq_nil_of_isOrderSeq_of_maxOrd_lt _ hord (noEmptyCenters_eraseEmpty _)
        (maxOrd_tuned_lt hT.1 hlt')).symm
  · have hlt : T.I.maxOrd < m := lt_of_le_of_ne hT.2.2 h₁
    rw [maxContactCase_of_maxOrd_lt T hT hH hle bd hlt,
      maxContactCase_of_maxOrd_lt T' hT' hH' hle' bd (lt_of_le_of_lt hle_max hlt)]
    rfl

end MaxContactCase

end Hironaka.BO
