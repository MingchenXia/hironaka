/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.OrderReduction.Step2Functorial
public import Hironaka.Resolution.Algebraic.BoundaryClearing.AssemblyTuned
import Hironaka.Resolution.Algebraic.BoundaryClearing.Composite
import Hironaka.Resolution.Algebraic.Kol07.AppendLast
import Hironaka.Resolution.Algebraic.OrderReduction.ClosedEmbedding
import Hironaka.Resolution.Algebraic.OrderReduction.Step22Basic
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The first centre of Step 2 when the hypersurface has an absorbed component

Step 2 of the proof of [Kol07, Theorem 103] on a triple `(X, I, ∅)` with `max-ord I = 1` and a
smooth hypersurface `Y` of maximal contact is [Kol07, Lemma 102] at the position of `Y` (Step 2.1
being empty for an empty boundary): its FIRST blow-up is `π_{-1}`, the blow-up of `Z_{-1}(I, 1, Y)`,
the union of the irreducible components of `Y` along which `I` has order `≥ 1` — when there is one
(`Z_{-1} ≠ 𝒪_X`), the deletion of empty blow-ups [Kol07, 32] keeps it:

* `dataFunctor_seq_eq_cons_of_Zminus1_ne_top`: at the level of `BD_{n,1,j}` (`dataFunctor`, through
  the tuning identity at the mark `1`);
* `maxContactCase_bdData_eq_cons_of_Zminus1_ne_top`: at the level of Step 2 with the data of
  Lemma 102 (the unfolding of `maxContactCase` for `E = ∅`; [Kol07, 104, Step 2.4]: "If `E = ∅`
  then Step 2.1 does nothing").

This is the complementary case to `maxContactCase_bdData_eq_pushforward` (`Z_{-1} = 𝒪_X`, the
descent along the closed embedding). Used by the core lemma of the smooth case
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilCore`): the generic point of an absorbed component
of `Y` is a generic point of `V(I)` lying in the first centre.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka
  BlowUpSequence Scheme.IdealSheafData Hironaka.Sequence Hironaka.Local IsLocalRing Hironaka.BO
  Hironaka.BD

namespace Hironaka.Resolution

variable {k : Type u} [Field k] [CharZero k]

section BD

variable {n : ℕ} {Dom : MarkedTriple k → Prop} (B : OrderGeSeqAssignment k Dom)

/-- On the standing class of [Kol07, Lemma 102], when some component of `E^j` carries `I` of order
`≥ m` (`Z_{-1} ≠ 𝒪_X`), the output with its empty blow-ups deleted starts with `π_{-1}` — the
blow-up of `Z_{-1}` (`map_centerS`), kept by the deletion since it is nonempty (the proof of
Lemma 102). -/
theorem rawSeq_eraseEmpty_eq_cons_of_Zminus1_ne_top (T : Triple k) (m : ℕ) (j : T.E.ι)
    (hI : T.I.IsDBalanced (T.X.left ↘ Spec (.of k)) m) (hmax : T.I.maxOrd = m) (hn : T.HasDimLE n)
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = m → Dom T')
    (hZ : Zminus1 T.I m (T.E.component j) ≠ ⊤) :
    ∃ (D : T.X.left.IdealSheafData) (rest : BlowUpSequence D.blowUp),
      (rawSeq T m j hI hmax hn B hDom).eraseEmpty = BlowUpSequence.cons T.X.left D rest ∧
        D = Zminus1 T.I m (T.E.component j) := by
  have hraw : rawSeq T m j hI hmax hn B hDom =
      BlowUpSequence.cons T.X.left ((centerS T m j).map (T.E.component j).subschemeι)
        (tailSeq T m j hI hmax hn B hDom) := rfl
  have hne : (centerS T m j).map (T.E.component j).subschemeι ≠ ⊤ := by
    rw [map_centerS]
    exact hZ
  rw [hraw, eraseEmpty_cons_of_ne_top _ hne]
  exact ⟨_, _, rfl, map_centerS T m j⟩

/-- At the mark `1`, on a triple of `BDClass n 1 j` with `max-ord I = 1` whose `j`-th member `E^j`
has a component along which `I` has order `≥ 1` (`Z_{-1} ≠ 𝒪_X`), `BD_{n,1,j}` starts with the
blow-up of `Z_{-1}` — the tuning at the mark `1` is the identity (`W_tuningParam_one`,
`tuningParam_one`). -/
theorem dataFunctor_seq_eq_cons_of_Zminus1_ne_top (T : Triple k) {j : ℕ}
    (hj : j < Fintype.card T.E.ι)
    (hDom : ∀ T' : MarkedTriple k, T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam 1 → Dom T')
    (hT : Triple.BDClass n 1 j T) (h1 : T.I.maxOrd = ((1 : ℕ) : ℕ∞))
    (hZ : Zminus1 T.I 1 (T.E.nth ⟨j, hj⟩) ≠ ⊤) :
    ∃ (D : T.X.left.IdealSheafData) (rest : BlowUpSequence D.blowUp),
      (dataFunctor n 1 j le_rfl B hDom).seq T hT = BlowUpSequence.cons T.X.left D rest ∧
        D = Zminus1 T.I 1 (T.E.nth ⟨j, hj⟩) := by
  obtain ⟨hn', hI', hmax', hj'⟩ := domain_tuned le_rfl hT h1
  have hc : Zminus1 (T.tuned 1 le_rfl).I (tuningParam 1)
      ((T.tuned 1 le_rfl).E.component (monoEquivOfFin (T.tuned 1 le_rfl).E.ι rfl ⟨j, hj'⟩)) =
      Zminus1 T.I 1 (T.E.nth ⟨j, hj⟩) := by
    change Zminus1 (IdealSheafData.W (T.X.left ↘ Spec (.of k)) T.I 1 (tuningParam 1))
      (tuningParam 1) (T.E.component (monoEquivOfFin T.E.ι rfl ⟨j, hj'⟩)) = _
    rw [IdealSheafData.W_tuningParam_one (T.X.left ↘ Spec (.of k)) T.I, tuningParam_one]
    rfl
  obtain ⟨D, rest, hD, hDZ⟩ := rawSeq_eraseEmpty_eq_cons_of_Zminus1_ne_top B (T.tuned 1 le_rfl)
    (tuningParam 1) (monoEquivOfFin (T.tuned 1 le_rfl).E.ι rfl ⟨j, hj'⟩) hI' hmax' hn' hDom
    (by rw [hc]; exact hZ)
  rw [dataFunctor_seq_of_maxOrd_eq n 1 j le_rfl B hDom T hT h1]
  exact ⟨D, rest, hD, hDZ.trans hc⟩

end BD

section Step2

variable {n : ℕ} (T : Triple k) {Y : T.X.left.IdealSheafData} (hY : IsSmoothDivisor Y)
  (hle : IdealSheafData.IsMaximalContact (T.X.left ↘ Spec (.of k)) T.I 1 Y) (hE : IsEmpty T.E.ι)
  (Dom : ∀ (k : Type u) [Field k] [CharZero k], MarkedTriple k → Prop)
  (B : ∀ (k : Type u) [Field k] [CharZero k], OrderGeSeqAssignment k (Dom k))
  (hDom : ∀ (m : ℕ) (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k),
    T'.toTriple.HasDimLE (n - 1) → T'.m = tuningParam m → Dom k T')
  (hB : ∀ (k : Type u) [Field k] [CharZero k] (T' : MarkedTriple k) (hT' : Dom k T'),
    ((B k).endTriple T' hT').I.maxOrd < (T'.m : ℕ∞))
  (hsm : ∀ (k : Type u) [Field k] [CharZero k], (B k).CommutesWithSmooth)
  (hbc : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L] (σ : k →+* L),
    (B k).CommutesWithBaseChange (B L) σ)

include hE in
/-- [Kol07, 104, Step 2.4] ("If `E = ∅` then Step 2.1 does nothing"), generalised over the Step 2.1
sequence as `step22_closedEmbedding_aux`: for `S₁ = nil`, Step 2.2 with the data at the mark `1`
on the Step 2.2 triple of `Y` starts with the blow-up of `Z_{-1}(I, 1, Y)` when the latter is not
the unit ideal. -/
theorem step22_eq_cons_of_Zminus1_ne_top_aux (S₁ : BlowUpSequence T.X.left)
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E 1)
    (e₀ : S₁ = BlowUpSequence.nil T.X.left)
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq Y (Fin.last _))).IsSnc)
    (j₂ : ℕ) (hj₂ : j₂ = 0) (hT₂ : Triple.BDClass n 1 j₂ (step22TripleOfSeq T S₁ hS₁ hsnc))
    (h1 : T.I.maxOrd = ((1 : ℕ) : ℕ∞)) (hZ : Zminus1 T.I 1 Y ≠ ⊤) :
    ∃ (D : T.X.left.IdealSheafData) (rest : BlowUpSequence D.blowUp),
      S₁.concat ((step22Functor (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) 1 j₂
        le_rfl).seq (step22TripleOfSeq T S₁ hS₁ hsnc) hT₂) = BlowUpSequence.cons T.X.left D rest ∧
        D = Zminus1 T.I 1 Y := by
  subst e₀
  subst hj₂
  have h₀ : 0 < Fintype.card (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).E.ι :=
    hT₂.2.2
  have hFcard : Fintype.card ((BlowUpSequence.nil T.X.left).exceptionalFamily T.E).ι = 0 :=
    @Fintype.card_eq_zero _ _ ⟨fun a => hE.elim a.1⟩
  have eY : (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩ = Y := by
    have h1' := nth_append_last ((BlowUpSequence.nil T.X.left).exceptionalFamily T.E)
      ((BlowUpSequence.nil T.X.left).strictTransformSeq Y (Fin.last _)) (card_lt_card_ι_append _ _)
    have hidx : (⟨0, h₀⟩ :
        Fin (Fintype.card (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).E.ι)) =
        ⟨Fintype.card ((BlowUpSequence.nil T.X.left).exceptionalFamily T.E).ι,
          card_lt_card_ι_append _ _⟩ :=
      Fin.ext hFcard.symm
    rw [hidx]
    exact h1'
  have h₂ : (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).I.maxOrd =
    ((1 : ℕ) : ℕ∞) := by
    change T.I.maxOrd = _
    exact h1
  have hZ₂ : Zminus1 (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).I 1
      ((step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩) ≠ ⊤ := by
    rw [eY]
    exact hZ
  obtain ⟨D, rest, hD, hDZ⟩ := dataFunctor_seq_eq_cons_of_Zminus1_ne_top (B k)
    (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc) h₀ (hDom 1 k) hT₂ h₂ hZ₂
  change ∃ (D : T.X.left.IdealSheafData) (rest : BlowUpSequence D.blowUp),
    (step22Functor (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) 1 0 le_rfl).seq
      (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc) hT₂ =
        BlowUpSequence.cons T.X.left D rest ∧
      D = Zminus1 T.I 1 Y
  rw [step22Functor_seq_of_maxOrd_eq _ 1 0 le_rfl _ hT₂ h₂]
  refine ⟨D, rest, Eq.trans (functor_seq_congr_mark
    (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) 0
    (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc) (tuningParam 1) tuningParam_one _
    (IdealSheafData.W_tuningParam_one _ _) _ _ hT₂) hD, hDZ.trans (congrArg
    (fun H => Zminus1 (step22TripleOfSeq T (BlowUpSequence.nil T.X.left) hS₁ hsnc).I 1 H) eY)⟩

include hE in
/-- Step 2 of the proof of [Kol07, Theorem 103] with the proof of [Kol07, Lemma 102]: on a triple
`(X, I, ∅)` with `max-ord I = 1` and a smooth hypersurface `Y` of maximal contact along which some
component of `Y` has `I` of order `≥ 1` (`Z_{-1}(I, 1, Y) ≠ 𝒪_X`), `BO^Y_{n,1}(X, I, ∅)` with the
data of Lemma 102 starts with the blow-up of `Z_{-1}(I, 1, Y)`. The complementary case is
`maxContactCase_bdData_eq_pushforward`. -/
theorem maxContactCase_bdData_eq_cons_of_Zminus1_ne_top (hT : Triple.BOClass n 1 T)
    (h1 : T.I.maxOrd = ((1 : ℕ) : ℕ∞)) (hZ : Zminus1 T.I 1 Y ≠ ⊤) :
    ∃ (D : T.X.left.IdealSheafData) (rest : BlowUpSequence D.blowUp),
      maxContactCase T hT hY hle (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) =
        BlowUpSequence.cons T.X.left D rest ∧ D = Zminus1 T.I 1 Y := by
  have hmax₁ : T.I.maxOrd ≤ ((1 : ℕ) : ℕ∞) := hT.2.2
  have e₀ := step21Seq_val_eq_nil T hT.2.1 hE hmax₁
    (fun j => Hironaka.BD.bdData n 1 j Dom B (hDom 1) hB hsm hbc)
  have hF0 : Fintype.card ((step21Seq T hT.2.1 hmax₁
      (fun j => Hironaka.BD.bdData n 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).1.exceptionalFamily T.E).ι = 0 := by
    rw [e₀]
    exact @Fintype.card_eq_zero _ _ ⟨fun a => hE.elim a.1⟩
  obtain ⟨D, rest, haux, hDZ⟩ := step22_eq_cons_of_Zminus1_ne_top_aux T hE Dom B hDom hB hsm hbc
    (step21Seq T hT.2.1 hmax₁ (fun j => Hironaka.BD.bdData n 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).1
    (isOrderSeq_step21Seq T hT.2.1 hmax₁
      (fun j => Hironaka.BD.bdData n 1 j Dom B (hDom 1) hB hsm hbc) (Fintype.card T.E.ι)) e₀
    (step22Triple T hT.2.1 hmax₁ (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc)
      le_rfl hY hle).isSnc
    (Fintype.card ((step21Seq T hT.2.1 hmax₁
      (fun j => Hironaka.BD.bdData n 1 j Dom B (hDom 1) hB hsm hbc)
      (Fintype.card T.E.ι)).1.exceptionalFamily T.E).ι) hF0
    (bdClass_step22Triple T hT.2.1 hmax₁
      (fun m j => Hironaka.BD.bdData n m j Dom B (hDom m) hB hsm hbc) le_rfl hY hle) h1 hZ
  refine ⟨D, rest, ?_, hDZ⟩
  rw [maxContactCase_one_eq_step2Seq T hT hY hle _ h1]
  exact haux

end Step2

end Hironaka.Resolution
