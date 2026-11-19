/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Transform
public import Hironaka.Scheme.BlowUpSequence.Defs
public import Hironaka.Scheme.Snc.Basic
import Hironaka.Scheme.BlowUpSequence.PullbackEraseEmpty
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The blow-up of a center equal to the unit ideal

The facts about the empty blow-up are stated elsewhere for the center written as `⊤`
(`markedTransform_top_left`, `strictTransform_top_left`, `exceptionalDivisor_top`,
`eraseEmpty_cons_top`). The proof of clause (3) of [Kol07, Lemma 102] meets a center `Z` that is
provably the unit ideal (Kollár's "`Z_{-1} = ∅`") but is not written as `⊤`, and the schemes
`Z.blowUp` in the types prevent a rewrite. This module restates the facts for a center `Z` with
a proof `hZ : Z = ⊤` (each by substitution), together with the identification of the total
transform along the trivial blow-up with the pull-back of the family with an appended empty member
([Kol07, Definition 25]: the exceptional divisor of the unit ideal is the unit ideal), and a few
congruence lemmas along an equality of sequences.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence
  Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The marked transform along the blow-up of a center provably equal to the unit ideal is the
pull-back of the ideal (`markedTransform_top_left` for such a center). -/
theorem markedTransform_of_eq_top (I : X.IdealSheafData) (m : ℕ) {Z : X.IdealSheafData}
    (hZ : Z = ⊤) : I.markedTransform Z m = I.comap Z.blowUpπ := by
  subst hZ
  exact markedTransform_top_left I m

/-- The total transform of [Kol07, Definition 25] along the trivial blow-up: the total transform
of a family along the blow-up of the unit ideal is the pull-back of the family with an appended
empty member (the strict transform of each member is its pull-back, the exceptional divisor is
the unit ideal). -/
theorem totalTransform_of_eq_top (F : DivisorFamily X) {Z : X.IdealSheafData} (hZ : Z = ⊤) :
    F.totalTransform Z = (F.append ⊤).comap Z.blowUpπ := by
  subst hZ
  unfold DivisorFamily.totalTransform DivisorFamily.append DivisorFamily.comap
  congr 1
  funext i
  rcases i with a | u
  · exact strictTransform_top_left _
  · exact exceptionalDivisor_top.trans (comap_top _).symm

/-- Two one-step sequences with equal centers are equal. -/
theorem cons_nil_congr {Z Z' : X.IdealSheafData} (h : Z = Z') :
    cons X Z (nil _) = cons X Z' (nil _) := by
  subst h
  rfl

/-- The last strict transform along a sequence equal to the empty one is the ideal itself. -/
theorem strictTransformSeq_last_eq_top_of_eq_nil {S : BlowUpSequence X} (hS : S = nil X)
    {D : X.IdealSheafData} (hD : D = ⊤) : S.strictTransformSeq D (Fin.last _) = ⊤ := by
  subst hS
  exact hD

/-- The last strict transform along a one-step sequence is the strict transform along its center. -/
theorem strictTransformSeq_last_eq_top_of_eq_cons_nil {S : BlowUpSequence X}
    {Z : X.IdealSheafData} (hS : S = cons X Z (nil _)) {D : X.IdealSheafData}
    (hD : D.strictTransform Z = ⊤) : S.strictTransformSeq D (Fin.last _) = ⊤ := by
  subst hS
  exact hD

/-- Congruence of the disjointness of [Kol07, Lemma 102, conclusion (1)] along an equality of
sequences (the index `Fin.last _` depends on the sequence, so this is stated once and used in
place of `rw`). -/
theorem disjoint_cosupp_congr {S S' : BlowUpSequence X} (e : S = S') (I D : X.IdealSheafData)
    (m : ℕ) :
    Disjoint {x | (m : ℕ∞) ≤ (S.weakTransformSeq I (Fin.last _)).ord x}
        ((S.strictTransformSeq D (Fin.last _)).support : Set _) ↔
      Disjoint {x | (m : ℕ∞) ≤ (S'.weakTransformSeq I (Fin.last _)).ord x}
        ((S'.strictTransformSeq D (Fin.last _)).support : Set _) := by
  subst e
  rfl

end AlgebraicGeometry
