/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyEmbedding
import Hironaka.Resolution.Algebraic.Kol07.ComponentwiseTransport
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Blow-up sequences all of whose centers are empty

A blow-up sequence all of whose centers are the unit ideal, every blow-up being the trivial one,
an isomorphism [Kol07, Warning 20], erases to the empty sequence under the empty blow-up convention
[Kol07, 32] (`eraseEmpty_eq_nil`); its composite is an isomorphism
(`isIso_stageMap_of_center_eq_top`); the weak transform at its end is the inverse image of the
starting ideal along the composite (the exceptional factor is the unit ideal at each stage,
`weakTransform_top_left`); and the boundary at its end is the inverse image of the starting
boundary with the (unit) exceptional members appended, a deletion of `⊤` members (`IsTopErasure`,
`Hironaka/Resolution/Algebraic/Kol07/EraseEmptyEmbedding.lean`), assembled stage by stage from
`isTopErasure_inlEmb_top`. These are the four facts needed about a round of the order reduction
functor whose pull-back along a smooth morphism has no point of order `≥ d` and is therefore
skipped (the second clause of functoriality for smooth morphisms, [Kol07, 34.1]). -/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Sequence

/-- When every center is the unit ideal, the weak transform at the end is the inverse image of the
starting ideal along the composite: at each stage the exceptional factor is the unit ideal
(`weakTransform_top_left`; [Kol07, Warning 20] along a sequence). -/
theorem weakTransformSeq_last_eq_comap_composite_of_center_eq_top {X : Scheme.{u}}
    (S : BlowUpSequence X) (I : X.IdealSheafData) (hc : ∀ i, S.center i = ⊤) :
    S.weakTransformSeq I (Fin.last _) = I.comap S.composite := by
  induction S with
  | nil X => exact (Scheme.IdealSheafData.comap_id I).symm
  | cons X D rest ih =>
    have hD : D = ⊤ := hc ⟨0, Nat.succ_pos _⟩
    have ih' := ih (I.weakTransform D) (fun i => hc i.succ)
    subst hD
    change rest.weakTransformSeq (I.weakTransform ⊤) (Fin.last _) =
      I.comap (rest.composite ≫ (⊤ : X.IdealSheafData).blowUpπ)
    rw [ih', weakTransform_top_left, Scheme.IdealSheafData.comap_comp]

/-- When every center is the unit ideal, the boundary at the end of the sequence is the inverse
image of the starting boundary along the composite with unit members appended (`IsTopErasure`):
stage by stage, the total transform under the trivial blow-up is the inverse image of the family
extended by the (unit) exceptional member (`isTopErasure_inlEmb_top`; [Kol07, 32]). -/
theorem exists_isTopErasure_totalTransformSeq_of_center_eq_top {X : Scheme.{u}}
    (S : BlowUpSequence X) (E : DivisorFamily X) (hc : ∀ i, S.center i = ⊤) :
    ∃ e : (E.comap S.composite).ι ↪o (S.totalTransformSeq E (Fin.last _)).ι,
      IsTopErasure (E.comap S.composite) (S.totalTransformSeq E (Fin.last _)) e := by
  induction S with
  | nil X =>
    exact ⟨(OrderIso.refl E.ι).toOrderEmbedding, fun i => (Scheme.IdealSheafData.comap_id _).symm,
      fun b hb => (hb ⟨b, rfl⟩).elim⟩
  | cons X D rest ih =>
    have hD : D = ⊤ := hc ⟨0, Nat.succ_pos _⟩
    obtain ⟨e₁, h₁⟩ := ih (E.totalTransform D) (fun i => hc i.succ)
    subst hD
    obtain ⟨hh1, hh2⟩ := ((isTopErasure_inlEmb_top E).comap rest.composite).trans h₁
    refine ⟨(inlEmb E ⊤).trans e₁, fun i => (hh1 i).trans ?_, hh2⟩
    exact (Scheme.IdealSheafData.comap_comp (E.component i) rest.composite
        (⊤ : X.IdealSheafData).blowUpπ).symm

/-- When every center is the unit ideal, the composite of the sequence is an isomorphism
[Kol07, Warning 20]. -/
theorem isIso_composite_of_center_eq_top {X : Scheme.{u}} (S : BlowUpSequence X)
    (hc : ∀ i, S.center i = ⊤) : IsIso S.composite :=
  isIso_stageMap_of_center_eq_top S (Fin.last _) fun j _ => hc j

end Hironaka.Sequence
