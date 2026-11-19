/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.SncGlobalSubfamily
public import Hironaka.Scheme.BlowUpSequence.ConcatPullback
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.EraseEmptyTransport
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The exceptional sub-family under pull-back

`exceptionalFamily S E` (`Hironaka/Resolution/Algebraic/Kol07/SncGlobalSubfamily.lean`) is the
sub-family of the total transform `E_r` consisting of the members that are not transforms of
original members (`originalIdx`): the exceptional divisors of the sequence, in the sense of the
total exceptional set of [Kol07, Definition 25]. Along a flat `h : Y ⟶ X` the total transform of the
pulled-back family is the pull-back of the total transform (`totalTransformSeq_pullback`), and the
original members correspond: the sub-family avoiding the transforms of a chosen set of original
members pulls back to the corresponding sub-family (`subfamily_originalIdx_pullback`, by recursion
on the sequence with the chosen set carried through the first blow-up as `toLex ∘ Sum.inl`; the
pulled-back total transform of a `cons` differs from the pull-back of the total transform only by
`totalTransform_comap_of_flat`, transported by `subfamily_originalIdx_congr`). At the last stage
this is `exceptionalFamily_pullback`, with the index identification `pullbackStageIdx_last`
absorbed into the last-stage lift `pullbackLastHom` (`subfamily_totalTransformSeq_eq_idx`). It is
used for the functoriality of the boundary-clearing sequence of [Kol07, 104, Step 2.2].
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Transport of the sub-family avoiding the transforms of marked original members along an
equality of the starting families (whose index types agree definitionally in every use). -/
theorem subfamily_originalIdx_congr (S : BlowUpSequence X) (F₁ F₂ : DivisorFamily X) (e : F₁ = F₂)
    (i : Fin (S.length + 1)) {T : Type u} (x₁ : T → F₁.ι) (x₂ : T → F₂.ι) (hx : HEq x₁ x₂) :
    (S.totalTransformSeq F₁ i).subfamily (fun b => ∀ t, b ≠ S.originalIdx F₁ i (x₁ t)) =
      (S.totalTransformSeq F₂ i).subfamily (fun b => ∀ t, b ≠ S.originalIdx F₂ i (x₂ t)) := by
  subst e
  cases hx
  rfl

/-- Along a flat `h`, the sub-family of the total transform at stage `⟨j, hj⟩` avoiding the
transforms of the original members `g t` pulls back to the corresponding sub-family of the
pulled-back sequence, by recursion on the sequence, the chosen members carried through the first
blow-up as `toLex (Sum.inl (g t))`. -/
theorem subfamily_originalIdx_pullback :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) {Y : Scheme.{u}} (h : Y ⟶ X) [Flat h]
      (E : DivisorFamily X) (j : ℕ) (hj : j < S.length + 1) {T : Type u} (g : T → E.ι),
      ((S.pullback h).totalTransformSeq (E.comap h) (S.pullbackStageIdx h ⟨j, hj⟩)).subfamily
          (fun b => ∀ t, b ≠ (S.pullback h).originalIdx (E.comap h) (S.pullbackStageIdx h ⟨j, hj⟩)
            (g t)) =
        ((S.totalTransformSeq E ⟨j, hj⟩).subfamily
          (fun b => ∀ t, b ≠ S.originalIdx E ⟨j, hj⟩ (g t))).comap (S.pullbackStageHom h ⟨j, hj⟩)
  | _, nil _, _, _, _, _, _, _, _, _ => rfl
  | _, cons _ _ _, _, _, _, _, 0, _, _, _ => rfl
  | _, cons X D rest, Y, h, _, E, j + 1, hj, T, g => by
    have hflat : Flat (Scheme.Hom.blowUpMap h D) := flat_blowUpMap h D
    exact (subfamily_originalIdx_congr (rest.pullback (Scheme.Hom.blowUpMap h D))
      ((E.comap h).totalTransform (D.comap h)) ((E.totalTransform D).comap
          (Scheme.Hom.blowUpMap h D))
      (totalTransform_comap_of_flat h D E)
      (rest.pullbackStageIdx (Scheme.Hom.blowUpMap h D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩)
      (fun t => toLex (Sum.inl (g t))) (fun t => toLex (Sum.inl (g t))) HEq.rfl).trans
      (subfamily_originalIdx_pullback rest (Scheme.Hom.blowUpMap h D) (E.totalTransform D) j
        (Nat.lt_of_succ_lt_succ hj) (fun t => toLex (Sum.inl (g t))))

/-- Transport of a sub-family of the total transform along an equality of stage indices: the
`eqToHom` of the stage identification is absorbed. -/
theorem subfamily_totalTransformSeq_eq_idx (S : BlowUpSequence X) (E : DivisorFamily X)
    {i j : Fin (S.length + 1)} (e : i = j) (P : ∀ i : Fin (S.length + 1),
      (S.totalTransformSeq E i).ι → Prop) :
    (S.totalTransformSeq E j).subfamily (P j) =
      ((S.totalTransformSeq E i).subfamily (P i)).comap (eqToHom (congrArg S.stage e.symm)) := by
  cases e
  change _ = ((S.totalTransformSeq E i).subfamily (P i)).comap (𝟙 _)
  simp

/-- The exceptional sub-family of the pulled-back sequence is the inverse image of the exceptional
sub-family along the last-stage lift (`originalIdx` commutes with pull-back, and so does the total
transform, `totalTransformSeq_pullback`). -/
theorem exceptionalFamily_pullback (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (E : DivisorFamily X) :
    (S.pullback h).exceptionalFamily (E.comap h) =
      (S.exceptionalFamily E).comap (S.pullbackLastHom h) := by
  have key := subfamily_originalIdx_pullback S h E S.length (Nat.lt_succ_self _) (fun a : E.ι => a)
  refine (subfamily_totalTransformSeq_eq_idx (S.pullback h) (E.comap h) (pullbackStageIdx_last S h)
    (fun i b => ∀ a, b ≠ (S.pullback h).originalIdx (E.comap h) i a)).trans ?_
  refine Eq.trans (congrArg (fun F : DivisorFamily _ =>
    F.comap (eqToHom (congrArg (S.pullback h).stage (pullbackStageIdx_last S h).symm))) key) ?_
  exact (DivisorFamily.comap_comp _ _ _).symm

end Hironaka.Sequence
