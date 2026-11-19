/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step24ClosedEmbedding
public import Hironaka.Resolution.Algebraic.OrderReduction.Step2Functorial
public import Hironaka.Resolution.Algebraic.BoundaryClearing.AssemblyTuned
public import Hironaka.Resolution.Algebraic.Tuning.Parameter
import Hironaka.Resolution.Algebraic.BoundaryClearing.ClauseThree
import Hironaka.Resolution.Algebraic.Kol07.AppendLast
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Assembly
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 2.4 of order reduction: closed embeddings

Step 2.4 of the proof of [Kol07, Theorem 103] ([Kol07, 104, Step 2.4]) proves clause (3): for a
smooth hypersurface `τ : Y ↪ X` and an ideal sheaf `J ⊂ 𝒪_Y`, nonzero on every irreducible
component of `Y`, with `τ_*(𝒪_Y/J) = 𝒪_X/I`, the ideal `I` contains the local equations of `Y` and
so has order `1`, whence `I = W(I)`; for `E = ∅`, Step 2.1 does nothing and Step 2.2 may take
`H = Y`, so that clause (3) of Theorem 103 follows from clause (3) of [Kol07, Lemma 102].
This module proves that clause for the maximal-contact case,
`BO^Y_{n,1}(X, I, ∅) = τ_* BMO_{n−1,1}(Y, J, 1, ∅)`, in the form
`maxContactCase_bdData_eq_pushforward`, following Kollár's three observations.

**"`I = W(I)`."** At the mark `1`, `BO^Y_{n,1}(X, I, ∅)` is Step 2 on the tuned triple
`(X, W_{s(1)}(I), ∅)` at the mark `s(1)`; since `s(1) = 1` and `W_1(I) = I` (`tuningParam_one`,
`W_tuningParam_one`), it is Step 2 on `(X, I, ∅)` at the mark `1`. The transport
`step2Seq_congr_mark` generalises the mark and the tuned ideal and substitutes
(`maxContactCase_one_eq_step2Seq`).

**"Step 2.1 does nothing."** For `E = ∅` the Step 2.1 sequence is `nil` (`card E.ι = 0`,
`step21Seq_val_eq_nil`), and the whole Step 2.2 data is generalised over a sequence `S₁` with
`S₁ = nil` and substituted (`step22_closedEmbedding_aux`), so that the Step 2.2 triple becomes
`(X, I, ∅ + Y)` with `Y` at position `0` (`card F_r.ι = 0`, `nth_append_last`), and `I = τ_*J`
transports to it through the identification `e` of the position-`0` member with `Y`
(`map_comap_eqToHom`).

**"(103.3) follows from (102.3)."** Step 2.2 at the mark is the boundary-clearing functor at `s(1)`
on the re-tuned triple, again with `s(1) = 1` and `W_1 = id` (`functor_seq_congr_mark`); for the
boundary-clearing data `Hironaka.BD.bdData` at the mark `1` that is `Hironaka.BD.dataFunctor`,
whose clause (3) is `Hironaka.BD.eq_pushforward_of_quotient`: `τ_* B(Y, J, 1, (F − Y)|_Y + ⊤)` on
the Step 2.2 triple. Below the mark (`max-ord I = 0`, so `I = 𝒪_X`) both sides are empty:
`maxContactCase` is `nil` by the remark after [Kol07, Theorem 68] and the Step 2.2 functor is `nil`
(`step22Functor_seq_of_maxOrd_lt`), while clause (3) of Lemma 102 still identifies the pushforward
with the empty value.

The globalised form of clause (3), for `BO_{n,1}` itself, is assembled in
`Hironaka/Resolution/Algebraic/Stage/ClosedEmbeddingHypersurface.lean`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme IdealSheafData BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.Local IsLocalRing

namespace Hironaka.BO

section Transports

variable {k : Type u} [Field k] [CharZero k] {n : ℕ}

/-- Transport of Step 2 along the identification of the mark and of the tuned ideal at `m = 1`:
`s(1) = 1` and `W_1(I) = I` are propositional equalities, so the mark and the ideal are generalised
and substituted (structure eta identifies `{T with I := T.I}` with `T`). -/
theorem step2Seq_congr_mark (T : Triple k) (hn : T.HasDimLE n) (bd : ∀ m j : ℕ, BDData.{u} n m j)
    {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H) (s : ℕ) (hs : s = 1)
    (I' : T.X.left.IdealSheafData) (hI' : I' = T.I) (hne' : IsNonzeroEverywhere I')
    (hn' : ({ T with I := I', isNonzeroEverywhere := hne' } : Triple k).HasDimLE n)
    (hmax' : I'.maxOrd ≤ s) (hs1 : 1 ≤ s) (hle' : IsMaximalContact (T.X.left ↘ Spec (.of k)) I' s H)
    (hmax : T.I.maxOrd ≤ ((1 : ℕ) : ℕ∞))
    (hle : IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I 1 H) :
    step2Seq ({ T with I := I', isNonzeroEverywhere := hne' } : Triple k) hn' hmax' bd hs1 hH hle' =
      step2Seq T hn hmax bd le_rfl hH hle := by
  subst hs
  subst hI'
  rfl

/-- At the mark `1`, `BO^H_{n,1}(X, I, E)` is Step 2 on `(X, I, E)` itself ([Kol07, 104, Step 2.4]:
"in particular, `I = W(I)`"): the tuning `W_{s(1)}(I) = W_1(I) = I` is the identity
(`tuningParam_one`, `W_tuningParam_one`). -/
theorem maxContactCase_one_eq_step2Seq (T : Triple k) (hT : Triple.BOClass n 1 T)
    {H : T.X.left.IdealSheafData} (hH : IsSmoothDivisor H)
    (hle : IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I 1 H) (bd : ∀ m j : ℕ, BDData.{u} n m j)
    (h1 : T.I.maxOrd = ((1 : ℕ) : ℕ∞)) :
    maxContactCase T hT hH hle bd = step2Seq T hT.2.1 hT.2.2 bd le_rfl hH hle := by
  rw [maxContactCase_of_maxOrd_eq T hT hH hle bd h1]
  exact step2Seq_congr_mark T hT.2.1 bd hH (tuningParam 1) tuningParam_one _
    (W_tuningParam_one (T.X.left ↘ Spec (.of k)) T.I) _ _ _ _ _ hT.2.2 hle

/-- Transport of the boundary-clearing functor's value along the identification of the mark and of
the tuned ideal at `m = 1` (the re-tuning inside Step 2.2). -/
theorem functor_seq_congr_mark (bd : ∀ m j : ℕ, BDData.{u} n m j) (j : ℕ) (T₂ : Triple k) (s : ℕ)
    (hs : s = 1) (I' : T₂.X.left.IdealSheafData) (hI' : I' = T₂.I) (hne' : IsNonzeroEverywhere I')
    (hT' : Triple.BDClass n s j ({ T₂ with I := I', isNonzeroEverywhere := hne' } : Triple k))
    (hT : Triple.BDClass n 1 j T₂) :
    ((bd s j).functor k).seq ({ T₂ with I := I', isNonzeroEverywhere := hne' } : Triple k) hT' =
      ((bd 1 j).functor k).seq T₂ hT := by
  subst hs
  subst hI'
  rfl

/-- `I = τ_*J` transported along an identification of the hypersurface: for `A = B` and `J` on
`V(B)`, `(J ∘ eqToHom)` on `V(A)` pushes forward to the same ideal. -/
theorem map_comap_eqToHom {X : Scheme.{u}} {A B : X.IdealSheafData} (e : A = B)
    (J : B.subscheme.IdealSheafData) :
    (J.comap (eqToHom (congrArg Scheme.IdealSheafData.subscheme e))).map A.subschemeι =
      J.map B.subschemeι := by
  subst e
  change (J.comap (𝟙 _)).map A.subschemeι = J.map A.subschemeι
  rw [Scheme.IdealSheafData.comap_id]

end Transports

section ClosedEmbeddingProof

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} (T : Triple k) (hn : T.HasDimLE n)
  (hmax : T.I.maxOrd ≤ ((1 : ℕ) : ℕ∞)) {Y : T.X.left.IdealSheafData} (hY : IsSmoothDivisor Y)
  (hle : IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I 1 Y) (hE : IsEmpty T.E.ι)
  (J : Y.subscheme.IdealSheafData) (hJ : IsNonzeroEverywhere J) (hIJ : T.I = J.map Y.subschemeι)

include hE in
/-- For an empty boundary the Step 2.1 sequence is empty ([Kol07, 104, Step 2.4]: "if `E = ∅` then
Step 2.1 does nothing"). -/
theorem step21Seq_val_eq_nil {m : ℕ} (hmax : T.I.maxOrd ≤ m) (bd : ∀ j : ℕ, BDData.{u} n m j) :
    (step21Seq T hn hmax bd (Fintype.card T.E.ι)).1 = BlowUpSequence.nil T.X.left := by
  have hc : Fintype.card T.E.ι = 0 := @Fintype.card_eq_zero _ _ hE
  exact hc ▸ rfl

variable (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
  (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
  (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
    T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom k T')
  (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
    ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
  (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
  (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
    (B k).CommutesWithBaseChange (B L) σ)

include hE hIJ in
/-- Generalised over the Step 2.1 sequence: for `S₁ = nil`, Step 2.2 with the boundary-clearing
data at the mark `1` on the Step 2.2 triple of `Y` is the pushforward
`τ_* B(Y_r, J, 1, (F_r − Y_r)|_{Y_r} + ⊤)` of clause (3) of [Kol07, Lemma 102]
([Kol07, 104, Step 2.4]: "in Step 2.2 we can choose `H = Y`; thus (103.3) follows from (102.3)"):
at the mark through the re-tuning identity (`functor_seq_congr_mark`) and
`Hironaka.BD.eq_pushforward_of_quotient`; below the mark both sides are empty. -/
theorem step22_closedEmbedding_aux (S₁ : BlowUpSequence T.X.left)
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E 1)
    (e₀ : S₁ = BlowUpSequence.nil T.X.left)
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq Y (Fin.last _))).IsSnc)
    (j₂ : ℕ) (hj₂ : j₂ = 0)
    (hT₂ : Triple.BDClass n 1 j₂ (step22TripleOfSeq T S₁ hS₁ hsnc))
    (h₀ : 0 < Fintype.card (step22TripleOfSeq T S₁ hS₁ hsnc).E.ι)
    (e : ((step22TripleOfSeq T S₁ hS₁ hsnc).E.nth ⟨0, h₀⟩).subscheme = Y.subscheme)
    (hdim : (Hironaka.BD.hypersurfaceTriple (step22TripleOfSeq T S₁ hS₁ hsnc) h₀
      (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)).toTriple.HasDimLE (n - 1)) :
    (step22Functor (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) 1 j₂ le_rfl).seq
        (step22TripleOfSeq T S₁ hS₁ hsnc) hT₂ =
      BlowUpSequence.pushforward (X := (step22TripleOfSeq T S₁ hS₁ hsnc).X.left)
        (Y := ((step22TripleOfSeq T S₁ hS₁ hsnc).E.nth ⟨0, h₀⟩).subscheme)
        ((B k).seq (Hironaka.BD.hypersurfaceTriple (step22TripleOfSeq T S₁ hS₁ hsnc) h₀
            (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ))
          (hDom 1 k _ hdim tuningParam_one.symm))
        ((step22TripleOfSeq T S₁ hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι := by
  subst e₀
  subst hj₂
  -- the member at position `0` is `Y`
  have hFcard : Fintype.card ((BlowUpSequence.nil T.X.left).exceptionalFamily T.E).ι = 0 :=
    @Fintype.card_eq_zero _ _ ⟨fun a => hE.elim a.1⟩
  have eY : (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩ = Y := by
    have h1 := nth_append_last ((BlowUpSequence.nil T.X.left).exceptionalFamily T.E)
      ((BlowUpSequence.nil T.X.left).strictTransformSeq Y (Fin.last _)) (card_lt_card_ι_append _ _)
    have hidx : (⟨0, h₀⟩ :
        Fin (Fintype.card (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).E.ι)) =
        ⟨Fintype.card ((BlowUpSequence.nil T.X.left).exceptionalFamily T.E).ι,
          card_lt_card_ι_append _ _⟩ :=
      Fin.ext hFcard.symm
    rw [hidx]
    exact h1
  -- `I = τ_*J` on the Step 2.2 triple, through the identification
  have hIJ' : (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).I =
      (J.comap (eqToHom e)).map
        ((step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).E.nth ⟨0,
          h₀⟩).subschemeι := by
    change T.I = _
    rw [hIJ]
    exact (map_comap_eqToHom eY J).symm
  have key := Hironaka.BD.eq_pushforward_of_quotient
    (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc) h₀ (J.comap (eqToHom e))
    (isNonzeroEverywhere_comap_eqToHom e J hJ) hIJ' hT₂.1 (B k) (hDom 1 k) (hsm k).1
  by_cases h₂ : (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).I.maxOrd =
    ((1 : ℕ) : ℕ∞)
  · rw [step22Functor_seq_of_maxOrd_eq _ 1 0 le_rfl _ hT₂ h₂]
    refine Eq.trans (functor_seq_congr_mark
      (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) 0
      (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc) (tuningParam 1) tuningParam_one _
      (W_tuningParam_one _ _) _ _ hT₂) ?_
    exact key
  · have hlt : (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).I.maxOrd <
      ((1 : ℕ) : ℕ∞) :=
      lt_of_le_of_ne hT₂.2.1 h₂
    rw [step22Functor_seq_of_maxOrd_lt _ 1 0 le_rfl _ hT₂ hlt, ← key,
      Hironaka.BD.dataFunctor_seq_of_maxOrd_lt n 1 0 le_rfl (B k) (hDom 1 k) _ _ hlt]

/-- Step 2 is empty below the mark for an empty boundary: Step 2.1 is `nil` and Step 2.2 is `nil`
by the remark after [Kol07, Theorem 68]. -/
theorem step2Seq_eq_nil_aux (bd : ∀ m j : ℕ, BDData.{u} n m j) (S₁ : BlowUpSequence T.X.left)
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E 1)
    (e₀ : S₁ = BlowUpSequence.nil T.X.left)
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq Y (Fin.last _))).IsSnc)
    (j₂ : ℕ) (hT₂ : Triple.BDClass n 1 j₂ (step22TripleOfSeq T S₁ hS₁ hsnc))
    (hlt : T.I.maxOrd < ((1 : ℕ) : ℕ∞)) :
    S₁.concat ((step22Functor bd 1 j₂ le_rfl).seq (step22TripleOfSeq T S₁ hS₁ hsnc) hT₂) =
      BlowUpSequence.nil T.X.left := by
  subst e₀
  rw [step22Functor_seq_of_maxOrd_lt _ 1 j₂ le_rfl _ hT₂ hlt]
  rfl

end ClosedEmbeddingProof

section Main

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} (T : Triple k) {Y : T.X.left.IdealSheafData}
  (hY : IsSmoothDivisor Y) (J : Y.subscheme.IdealSheafData) (hJ : IsNonzeroEverywhere J)
  (hIJ : T.I = J.map Y.subschemeι) (hn : T.HasDimLE n) (hE : IsEmpty T.E.ι)
  (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
  (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
  (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
    T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom k T')
  (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
    ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
  (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
  (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
    (B k).CommutesWithBaseChange (B L) σ)

/-- The boundary-clearing data `Hironaka.BD.bdData` at every mark, built from the inductive input
`B`. -/
local notation "bdD" => (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc)

/-- The boundary-clearing data at the mark `1`. -/
local notation "bdD₁" => (fun j => Hironaka.BD.bdData n 1 j Dom B (hDom 1) hB hsm hbc)

include hIJ in
/-- **Clause (3) of [Kol07, Theorem 103] in the maximal-contact case** ([Kol07, 104, Step 2.4];
clause (3) of [Kol07, Lemma 102]): for the boundary-clearing data `bdData` built from the inductive
input `B`, `E = ∅` and `I = τ_*J`, `BO^Y_{n,1}(X, I, ∅) = τ_* B(Y_r, J, 1, (F_r − Y_r)|_{Y_r} + ⊤)`,
the marked triple of clause (3) on the Step 2.2 triple of `Y` at the mark `1`, `Y_r` at position
`0`, `J` transported, preceded by the empty Step 2.1 sequence. -/
theorem maxContactCase_bdData_eq_pushforward :
    maxContactCase T (bOClass_one_of_eq_map T hn hY hIJ) hY
        (isMaximalContact_one_of_eq_map T J hIJ)
        (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) =
      (step21Seq T hn (maxOrd_le_one_of_eq_map_smoothDivisor T hY hIJ)
          (fun j => Hironaka.BD.bdData n 1 j Dom B (hDom 1) hB hsm hbc)
          (Fintype.card T.E.ι)).1.concat
        (BlowUpSequence.pushforward
          (X := (step22Triple T hn (maxOrd_le_one_of_eq_map_smoothDivisor T hY hIJ)
              (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) le_rfl hY
              (isMaximalContact_one_of_eq_map T J hIJ)).X.left)
          (Y := ((step22Triple T hn (maxOrd_le_one_of_eq_map_smoothDivisor T hY hIJ)
              (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) le_rfl hY
              (isMaximalContact_one_of_eq_map T J hIJ)).E.nth
            ⟨0, zero_lt_card_step22Triple T hn (maxOrd_le_one_of_eq_map_smoothDivisor T hY hIJ)
              (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) le_rfl hY
              (isMaximalContact_one_of_eq_map T J hIJ)⟩).subscheme)
          ((B k).seq
            (closedEmbeddingTriple T hn (maxOrd_le_one_of_eq_map_smoothDivisor T hY hIJ)
              (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) hY
              (isMaximalContact_one_of_eq_map T J hIJ) hE J hJ)
            (hDom 1 k _
              (hasDimLE_closedEmbeddingTriple T hn (maxOrd_le_one_of_eq_map_smoothDivisor T hY hIJ)
                (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) hY
                (isMaximalContact_one_of_eq_map T J hIJ) hE J hJ)
              tuningParam_one.symm))
          ((step22Triple T hn (maxOrd_le_one_of_eq_map_smoothDivisor T hY hIJ)
              (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) le_rfl hY
              (isMaximalContact_one_of_eq_map T J hIJ)).E.nth
            ⟨0, zero_lt_card_step22Triple T hn (maxOrd_le_one_of_eq_map_smoothDivisor T hY hIJ)
              (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) le_rfl hY
              (isMaximalContact_one_of_eq_map T J hIJ)⟩).subschemeι) := by
  have hmax₁ := maxOrd_le_one_of_eq_map_smoothDivisor T hY hIJ
  have hle₁ := isMaximalContact_one_of_eq_map T J hIJ
  have e₀ := step21Seq_val_eq_nil T hn hE hmax₁ bdD₁
  have hF0 : Fintype.card ((step21Seq T hn hmax₁ bdD₁
      (Fintype.card T.E.ι)).1.exceptionalFamily T.E).ι = 0 := by
    rw [e₀]
    exact @Fintype.card_eq_zero _ _ ⟨fun a => hE.elim a.1⟩
  have aux := step22_closedEmbedding_aux T hE J hJ hIJ Dom B hDom hB hsm hbc
    (step21Seq T hn hmax₁ bdD₁ (Fintype.card T.E.ι)).1
    (isOrderSeq_step21Seq T hn hmax₁ bdD₁ (Fintype.card T.E.ι)) e₀
    (step22Triple T hn hmax₁ bdD le_rfl hY hle₁).isSnc
    (Fintype.card ((step21Seq T hn hmax₁ bdD₁ (Fintype.card T.E.ι)).1.exceptionalFamily T.E).ι) hF0
    (bdClass_step22Triple T hn hmax₁ bdD le_rfl hY hle₁)
    (zero_lt_card_step22Triple T hn hmax₁ bdD le_rfl hY hle₁)
    (subscheme_nth_zero_step22Triple T hn hmax₁ bdD le_rfl hY hle₁ hE)
    (hasDimLE_closedEmbeddingTriple T hn hmax₁ bdD hY hle₁ hE J hJ)
  have hB : step2Seq T hn hmax₁ bdD le_rfl hY hle₁ =
      (step21Seq T hn hmax₁ bdD₁ (Fintype.card T.E.ι)).1.concat
        ((step22Functor bdD 1 _ le_rfl).seq (step22Triple T hn hmax₁ bdD le_rfl hY hle₁)
          (bdClass_step22Triple T hn hmax₁ bdD le_rfl hY hle₁)) := rfl
  have hC := congrArg (step21Seq T hn hmax₁ bdD₁ (Fintype.card T.E.ι)).1.concat aux
  by_cases h1 : T.I.maxOrd = ((1 : ℕ) : ℕ∞)
  · have hA := maxContactCase_one_eq_step2Seq T (bOClass_one_of_eq_map T hn hY hIJ) hY hle₁ bdD h1
    exact hA.trans (hB.trans hC)
  · have hlt : T.I.maxOrd < ((1 : ℕ) : ℕ∞) := lt_of_le_of_ne hmax₁ h1
    have hA := maxContactCase_of_maxOrd_lt T (bOClass_one_of_eq_map T hn hY hIJ) hY hle₁ bdD hlt
    have hN := step2Seq_eq_nil_aux T bdD (step21Seq T hn hmax₁ bdD₁ (Fintype.card T.E.ι)).1
      (isOrderSeq_step21Seq T hn hmax₁ bdD₁ (Fintype.card T.E.ι)) e₀
      (step22Triple T hn hmax₁ bdD le_rfl hY hle₁).isSnc _
      (bdClass_step22Triple T hn hmax₁ bdD le_rfl hY hle₁) hlt
    exact hA.trans (hN.symm.trans hC)

end Main

end Hironaka.BO
