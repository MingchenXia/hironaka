/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.BlowUp.Composite
public import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
public import Hironaka.Scheme.Snc.TotalTransformSmoothBlowUp
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# The transforms of a triple and the triples induced along a sequence

Kollár's Definition 65 transforms a triple `(X, I, E)` under a smooth blow-up of order `m` with
center `Z` into `(B_Z X, π_*^{-1} I, π_tot^{-1}(E))`, and Definition 66 iterates this along a
smooth blow-up sequence of order `m` into `(X_i, I_i, E_i)`; likewise for marked triples
[Kol07, Definitions 65 and 66]. The underlying data are the recursions `weakTransform`,
`markedTransform`, `totalTransform` and their sequence versions; this module proves that they
satisfy the conditions of [Kol07, Notation 64] and packages them as the triples
`Triple.transform`, `MarkedTriple.transform`, `Triple.induced` and `MarkedTriple.induced`.

**The conditions, one by one.** Finite type, quasi-compactness and separatedness of
`B_Z X → Spec k` come from the properness of the blow-up over a locally Noetherian `X` (finite
type over a field), composed with those of `X`; along a sequence every `Π_i` is proper, by
induction (`isProper_stageMap`, `BlowUpSequence.isProper_composite`). Smoothness and
equidimensionality are Kollár's Notation 19 for a smooth center of any shape
(`Hironaka/Scheme/BlowUpSequence/SmoothCenter.lean`), along a sequence by
`IsSmooth.smoothOfRelativeDimension_stageMap`. Nonvanishing on the components is preserved
(`Hironaka/Scheme/BlowUpSequence/InducedData.lean`). The total transform of a simple normal crossing
family under a blow-up whose center has simple normal crossings with it is again a simple normal
crossing family ([Kol07, Definition 25]; [Hau14, Proposition 5.3]), assembled here from the local
normal crossing data at the points of the exceptional divisor and off it and from the smoothness
of every member (`Hironaka/Scheme/Snc/TotalTransformSnc.lean`, `TotalTransformOffCentre.lean`);
along a sequence by induction with condition (3) of Definition 66 at every stage.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing Ideal Scheme
  BlowUpSequence IdealSheafData

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-! ### The total transform of a simple normal crossing family is simple normal crossing -/

/-! ### Properness of the stage maps, snc of the induced families -/

/-- Every composite `Π_i` of a blow-up sequence on a locally Noetherian scheme is proper (the
blow-up of a locally Noetherian scheme is proper, and proper morphisms compose). -/
theorem isProper_stageMap (S : BlowUpSequence X) [hX : IsLocallyNoetherian X]
    (i : Fin (S.length + 1)) : IsProper (S.stageMap i) := by
  revert hX i
  induction S with
  | nil Y =>
    intro _ i
    change IsProper (𝟙 Y)
    infer_instance
  | cons Y D rest ih =>
    intro hY i
    have : IsLocallyNoetherian D.blowUp := blowUp.isLocallyNoetherian D
    have : IsProper D.blowUpπ := blowUp.isProper_π D
    rcases i with ⟨_ | j, hi⟩
    · change IsProper (𝟙 Y)
      infer_instance
    · change IsProper (rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ)
      have := ih ⟨j, Nat.lt_of_succ_lt_succ hi⟩
      infer_instance

/-- The composite `Π : X_r ⟶ X` of a blow-up sequence on a locally Noetherian scheme is proper
(`isProper_stageMap` at the last index); for `X` of finite type over a field this is the
properness of a resolution [Kol07, (2)]. -/
theorem Scheme.BlowUpSequence.isProper_composite (S : BlowUpSequence X) [IsLocallyNoetherian X] :
    IsProper S.composite :=
  isProper_stageMap S (Fin.last _)

section IsSnc

variable [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
  {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ} {S : BlowUpSequence X}

include n

/-- Along a smooth blow-up sequence of order `m` starting with `(X, I, E)`, every induced family
`E_i` is simple normal crossing: condition (3) of [Kol07, Definition 66] iterated with
`AlgebraicGeometry.totalTransform_isSnc`. -/
theorem IsOrderSeq.isSnc_totalTransformSeq (h : S.IsOrderSeq f I E m) (hE : E.IsSnc)
    (i : Fin (S.length + 1)) : (S.totalTransformSeq E i).IsSnc := by
  induction S with
  | nil Y => exact hE
  | cons Y D rest ih =>
    obtain ⟨⟨hD, hsnc, -⟩, ht⟩ := (isOrderSeq_cons_iff f I E m D rest).1 h
    have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
      have := hD
      exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | j, hi⟩
    · exact hE
    · exact ih (D.blowUpπ ≫ f) ht (totalTransform_isSnc f E D hE hsnc)
        ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- Along a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`, every induced
family `E_i` is simple normal crossing: condition (3′) of [Kol07, Definition 66] iterated. -/
theorem IsOrderGeSeq.isSnc_totalTransformSeq (h : S.IsOrderGeSeq f I m E) (hE : E.IsSnc)
    (i : Fin (S.length + 1)) : (S.totalTransformSeq E i).IsSnc := by
  induction S with
  | nil Y => exact hE
  | cons Y D rest ih =>
    obtain ⟨⟨hD, hsnc, -⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 h
    have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
      have := hD
      exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | j, hi⟩
    · exact hE
    · exact ih (D.blowUpπ ≫ f) ht (totalTransform_isSnc f E D hE hsnc)
        ⟨j, Nat.lt_of_succ_lt_succ hi⟩

end IsSnc

end AlgebraicGeometry

/-! ### The transformed and the induced triples -/

namespace Hironaka

open Scheme IdealSheafData

open AlgebraicGeometry

variable {k : Type u} [Field k] [CharZero k]

/-- The birational transform `π_*^{-1}(X, I, E) = (B_Z X, π_*^{-1} I, π_tot^{-1}(E))` of a triple
under a smooth blow-up of order `m` with center `Z` [Kol07, Definition 65]. -/
noncomputable def _root_.AlgebraicGeometry.Triple.transform (T : Triple k)
    (Z : T.X.left.IdealSheafData) {m : ℕ} (h : T.IsOrderBlowUp Z m) : Triple k where
  X := .ofHom (Z.blowUpπ ≫ (T.X.left ↘ Spec (.of k)))
    (by
      have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
      have : IsProper Z.blowUpπ := blowUp.isProper_π Z
      exact inferInstanceAs (FiniteType (Z.blowUpπ ≫ (T.X.left ↘ Spec (.of k)))))
    (by
      have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
      have : IsProper Z.blowUpπ := blowUp.isProper_π Z
      exact inferInstanceAs (IsSeparated (Z.blowUpπ ≫ (T.X.left ↘ Spec (.of k)))))
  smoothOfRelativeDimension := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    have := h.1
    exact ⟨n, smoothOfRelativeDimension_blowUpπ_comp_of_smooth (T.X.left ↘ Spec (.of k)) n Z⟩
  I := T.I.weakTransform Z
  isNonzeroEverywhere :=
    isNonzeroEverywhere_weakTransform (T.X.left ↘ Spec (.of k)) Z h.1 T.I T.isNonzeroEverywhere
  E := T.E.totalTransform Z
  isSnc := totalTransform_isSnc (T.X.left ↘ Spec (.of k)) T.E Z T.isSnc h.2.1

/-- The birational transform `π_*^{-1}(X, I, m, E) = (B_Z X, π_*^{-1}(I, m), π_tot^{-1}(E))` of a
marked triple under a smooth blow-up with center `Z` and `ord_Z I ≥ m` [Kol07, Definition 65]. -/
noncomputable def MarkedTriple.transform (T : MarkedTriple k) (Z : T.X.left.IdealSheafData)
    (h : T.IsOrderGeBlowUp Z) : MarkedTriple k where
  X := .ofHom (Z.blowUpπ ≫ (T.X.left ↘ Spec (.of k)))
    (by
      have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
      have : IsProper Z.blowUpπ := blowUp.isProper_π Z
      exact inferInstanceAs (FiniteType (Z.blowUpπ ≫ (T.X.left ↘ Spec (.of k)))))
    (by
      have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
      have : IsProper Z.blowUpπ := blowUp.isProper_π Z
      exact inferInstanceAs (IsSeparated (Z.blowUpπ ≫ (T.X.left ↘ Spec (.of k)))))
  smoothOfRelativeDimension := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    have := h.1
    exact ⟨n, smoothOfRelativeDimension_blowUpπ_comp_of_smooth (T.X.left ↘ Spec (.of k)) n Z⟩
  I := T.I.markedTransform Z T.m
  isNonzeroEverywhere :=
    isNonzeroEverywhere_markedTransform (T.X.left ↘ Spec (.of k)) Z h.1 T.I
      T.isNonzeroEverywhere T.m h.2.2
  E := T.E.totalTransform Z
  isSnc := totalTransform_isSnc (T.X.left ↘ Spec (.of k)) T.E Z T.isSnc h.2.1
  m := T.m

/-- The triple `(X_i, I_i, E_i)` induced at stage `i` of a smooth blow-up sequence of order `m`
starting with `T` [Kol07, Definition 66, condition (1)]; Kollár's `Π_*^{-1}(X, I, E)` is its value
at `Fin.last S.length`. -/
noncomputable def _root_.AlgebraicGeometry.Triple.induced (T : Triple k)
    (S : BlowUpSequence T.X.left) {m : ℕ}
    (h : S.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E m) (i : Fin (S.length + 1)) : Triple k where
  X := .ofHom (S.stageMap i ≫ (T.X.left ↘ Spec (.of k)))
    (by
      have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
      have := isProper_stageMap S i
      exact inferInstanceAs (FiniteType (S.stageMap i ≫ (T.X.left ↘ Spec (.of k)))))
    (by
      have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
      have := isProper_stageMap S i
      exact inferInstanceAs (IsSeparated (S.stageMap i ≫ (T.X.left ↘ Spec (.of k)))))
  smoothOfRelativeDimension := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    exact ⟨n, IsSmooth.smoothOfRelativeDimension_stageMap (n := n) (IsOrderSeq.isSmooth h) i⟩
  I := S.weakTransformSeq T.I i
  isNonzeroEverywhere := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    exact IsOrderSeq.isNonzeroEverywhere_weakTransformSeq (T.X.left ↘ Spec (.of k)) n h
      T.isNonzeroEverywhere i
  E := S.totalTransformSeq T.E i
  isSnc := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    exact IsOrderSeq.isSnc_totalTransformSeq (T.X.left ↘ Spec (.of k)) n h T.isSnc i

/-- The marked triple `(X_i, I_i, m, E_i)` induced at stage `i` of a smooth blow-up sequence of
order `≥ m` starting with `T` [Kol07, Definition 66, condition (1′)]. -/
noncomputable def MarkedTriple.induced (T : MarkedTriple k) (S : BlowUpSequence T.X.left)
    (h : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E) (i : Fin (S.length + 1)) :
    MarkedTriple k where
  X := .ofHom (S.stageMap i ≫ (T.X.left ↘ Spec (.of k)))
    (by
      have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
      have := isProper_stageMap S i
      exact inferInstanceAs (FiniteType (S.stageMap i ≫ (T.X.left ↘ Spec (.of k)))))
    (by
      have : IsLocallyNoetherian T.X.left := (T.X.left ↘ Spec (.of k)).isLocallyNoetherian_of_field
      have := isProper_stageMap S i
      exact inferInstanceAs (IsSeparated (S.stageMap i ≫ (T.X.left ↘ Spec (.of k)))))
  smoothOfRelativeDimension := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    exact ⟨n, IsSmooth.smoothOfRelativeDimension_stageMap (n := n) (IsOrderGeSeq.isSmooth h) i⟩
  I := S.markedTransformSeq T.I T.m i
  isNonzeroEverywhere := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    exact IsOrderGeSeq.isNonzeroEverywhere_markedTransformSeq (T.X.left ↘ Spec (.of k)) n h
      T.isNonzeroEverywhere i
  E := S.totalTransformSeq T.E i
  isSnc := by
    obtain ⟨n, hn⟩ := T.smoothOfRelativeDimension
    exact IsOrderGeSeq.isSnc_totalTransformSeq (T.X.left ↘ Spec (.of k)) n h T.isSnc i
  m := T.m

end Hironaka
