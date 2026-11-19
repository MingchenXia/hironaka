/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Transform
import Hironaka.Scheme.BlowUpSequence.InducedData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Two marked ideals with the same nonmonomial part keep it along a common sequence

In Step 2 of the proof of [Kol07, Theorem 107] ([Kol07, 111, Step 2]) a round of order reduction
for `N(I)^m + I^s` is at once a smooth blow-up sequence of order `≥ s` for `(N(I), s)` and of order
`≥ m` for `(I, m)`; after it, "we stop when `cosupp(I_r, m) ∩ cosupp(N(I_r), s) = ∅`", which
compares the nonmonomial part `N(I_r)` of the new marked ideal with the marked transform
`N_r := Π^{-1}_*(N(I), s)` of the old one. The comparison is the invariant proved here, not in the
sources as such: for two marked ideals `(I, m)` and `(J, s)` on the same triple with `N(I) = N(J)`,
along a smooth blow-up sequence of order `≥ m` for the first and `≥ s` for the second, the
nonmonomial parts of the two induced marked ideals agree at the end. One blow-up is the identity
`N(π^{-1}_*(I, m)) = N(π^* N(I))` of
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Transform.lean`
(`nonmonomialPart_markedTransform`), applied to both marked triples: `N(I_{i+1}) = N(π^* N(I_i)) =
N(π^* N(J_i)) = N(J_{i+1})`. The variant with the second sequence unmarked at the exact order, used
for the rounds of Step 1, is `nonmonomialPart_markedTransformSeq_last_eq` in
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step1NonmonomialPart.lean`.

* `nonmonomialPart_markedTransformSeq_eq_of_isOrderGeSeq`: the invariant at the end of the
  sequence, through `nonmonomialPart_markedTransformSeq_eq_of_isOrderGeSeq_aux` by induction on the
  length (the marked triples advance to `blowUpTriple`, so the induction is on the length, not
  structural on a sequence over a fixed scheme).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Hironaka Scheme BlowUpSequence

namespace Hironaka.BMO

variable {k : Type u} [Field k] [CharZero k]

/-- The recursion behind `nonmonomialPart_markedTransformSeq_eq_of_isOrderGeSeq`, by induction on
the length of the sequence. -/
theorem nonmonomialPart_markedTransformSeq_eq_of_isOrderGeSeq_aux (l : ℕ) :
    ∀ (T : MarkedTriple k) (S : BlowUpSequence T.X.left), S.length = l →
      ∀ {J : T.X.left.IdealSheafData}, IsNonzeroEverywhere J → ∀ {s : ℕ},
        S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) J s T.E →
        S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E →
        nonmonomialPart T.I T.E = nonmonomialPart J T.E →
        nonmonomialPart (S.markedTransformSeq T.I T.m (Fin.last _))
            (S.totalTransformSeq T.E (Fin.last _)) =
          nonmonomialPart (S.markedTransformSeq J s (Fin.last _))
            (S.totalTransformSeq T.E (Fin.last _)) := by
  induction l with
  | zero =>
    intro T S hl J hJ s hS hge hN
    cases S with
    | nil => exact hN
    | cons _ D rest => exact absurd hl (Nat.succ_ne_zero _)
  | succ l ih =>
    intro T S hl J hJ s hS hge hN
    cases S with
    | nil => exact absurd hl (Nat.zero_ne_add_one _)
    | cons _ D rest =>
      obtain ⟨⟨hD, hsnc, hleJ⟩, ht⟩ := (isOrderGeSeq_cons_iff _ J T.E s D rest).1 hS
      obtain ⟨⟨-, -, hle⟩, hget⟩ := (isOrderGeSeq_cons_iff _ T.I T.E T.m D rest).1 hge
      have hZ : T.IsOrderGeBlowUp D := ⟨hD, hsnc, hle⟩
      let Tj : MarkedTriple k := { T with I := J, isNonzeroEverywhere := hJ, m := s }
      have hZj : Tj.IsOrderGeBlowUp D := ⟨hD, hsnc, hleJ⟩
      have hJ' : IsNonzeroEverywhere (J.markedTransform D s) :=
        isNonzeroEverywhere_markedTransform (T.X.left ↘ Spec (.of k)) D hD J hJ s hleJ
      have e : ((blowUpTriple T D hZ).X.left ↘ Spec (.of k)) =
          D.blowUpπ ≫ (T.X.left ↘ Spec (.of k)) := by
        change (𝟙 _ ≫ D.blowUpπ) ≫ _ = _
        rw [Category.id_comp]
      have hS' : rest.IsOrderGeSeq ((blowUpTriple T D hZ).X.left ↘ Spec (.of k))
          (J.markedTransform D s) s (blowUpTriple T D hZ).E := by
        rw [e]
        exact ht
      have hge' : rest.IsOrderGeSeq ((blowUpTriple T D hZ).X.left ↘ Spec (.of k))
          (blowUpTriple T D hZ).I (blowUpTriple T D hZ).m (blowUpTriple T D hZ).E := by
        rw [e]
        exact hget
      have hN' : nonmonomialPart (blowUpTriple T D hZ).I (blowUpTriple T D hZ).E =
          nonmonomialPart (J.markedTransform D s) (blowUpTriple T D hZ).E := by
        have h1 := nonmonomialPart_markedTransform T D hZ
        have h2 := nonmonomialPart_markedTransform Tj D hZj
        change nonmonomialPart (T.I.markedTransform D T.m) (T.E.totalTransform D) =
          nonmonomialPart (J.markedTransform D s) (T.E.totalTransform D)
        rw [h1, hN]
        exact h2.symm
      exact ih (blowUpTriple T D hZ) rest (Nat.succ.inj hl) hJ' hS' hge' hN'

/-- For two marked ideals `(I, m)` and `(J, s)` on the same triple with `N(I) = N(J)`, along a
smooth blow-up sequence of order `≥ m` for `(I, m)` and of order `≥ s` for `(J, s)`, the
nonmonomial parts of the induced marked ideals agree at the end, with respect to the induced
boundary: `nonmonomialPart_markedTransform` applied to both marked triples at every stage (the
identity "`N((Π_1)^{-1}_*(I, m)) = (Π_1)^{-1}_* N(I)`" of [Kol07, 111, Step 1], read modulo `N`).
Step 2 of the proof of Theorem 107 uses it at `J = N(I)` and `s` the separation order:
`N(I_r) = N(Π^{-1}_*(N(I), s))`. Not in the sources as such. -/
theorem nonmonomialPart_markedTransformSeq_eq_of_isOrderGeSeq (T : MarkedTriple k)
    (S : BlowUpSequence T.X.left) {J : T.X.left.IdealSheafData} (hJ : IsNonzeroEverywhere J) {s : ℕ}
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) J s T.E)
    (hge : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E)
    (hN : nonmonomialPart T.I T.E = nonmonomialPart J T.E) :
    nonmonomialPart (S.markedTransformSeq T.I T.m (Fin.last _))
        (S.totalTransformSeq T.E (Fin.last _)) =
      nonmonomialPart (S.markedTransformSeq J s (Fin.last _))
        (S.totalTransformSeq T.E (Fin.last _)) :=
  nonmonomialPart_markedTransformSeq_eq_of_isOrderGeSeq_aux S.length T S rfl hJ hS hge hN

end Hironaka.BMO
