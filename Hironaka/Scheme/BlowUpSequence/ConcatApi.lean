/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Concat
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.BlowUpSequence.InducedData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Composites, transforms and order conditions along a concatenation

Kollár's `Π_{ij}` bookkeeping [Kol07, Definition 29] for the concatenation `S.concat T` of
`Hironaka/Scheme/BlowUpSequence/Concat.lean`: the end result is that of `T` (`last_concat`), the
composite is `Π_T ≫ Π_S` (`composite_concat`), the weak transforms and boundaries after the whole
sequence are those of `T` computed from those of `S` (`weakTransformSeq_concat_last`,
`boundarySeq_concat_last`), a predicate holding on every center of `S` and of `T` holds on every
center of `S.concat T` (`forall_center_concat`), and a smooth blow-up sequence of order `d`
followed by one of order `d` for the induced triple is one of order `d` (`isOrderSeq_concat`,
[Kol07, Definition 66]). The transport statements carry the identification
`eqToHom (last_concat S T)` of the end results, an identity up to the definitional unfolding of
`last`.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.BlowUpSequence

open IdealSheafData

variable {X : Scheme.{u}}

/-- The end result of a concatenation is the end result of the second sequence. -/
theorem last_concat (S : BlowUpSequence X) (T : BlowUpSequence S.last) :
    (S.concat T).last = T.last := by
  induction S with
  | nil X => rfl
  | cons X D rest ih => exact ih T

/-- The composite of a concatenation, `Π_{S ++ T} = Π_T ≫ Π_S` [Kol07, Definition 29]. -/
theorem composite_concat (S : BlowUpSequence X) (T : BlowUpSequence S.last) :
    (S.concat T).composite = eqToHom (last_concat S T) ≫ T.composite ≫ S.composite := by
  induction S with
  | nil X =>
    have h0 : eqToHom (last_concat (nil X) T) = 𝟙 T.last := eqToHom_refl _ _
    change T.composite = eqToHom (last_concat (nil X) T) ≫ T.composite ≫ 𝟙 X
    erw [h0, Category.id_comp, Category.comp_id]
  | cons X D rest ih =>
    change (rest.concat T).composite ≫ D.blowUpπ =
      eqToHom _ ≫ T.composite ≫ rest.composite ≫ D.blowUpπ
    rw [ih T, Category.assoc, Category.assoc]
    exact rfl

/-- The weak transform at the end of a concatenation is the weak transform along `T` of the weak
transform along `S`. -/
theorem weakTransformSeq_concat_last (S : BlowUpSequence X) (T : BlowUpSequence S.last)
    (J : X.IdealSheafData) :
    (S.concat T).weakTransformSeq J (Fin.last _) =
      (T.weakTransformSeq (S.weakTransformSeq J (Fin.last _)) (Fin.last _)).comap
        (eqToHom (last_concat S T)) := by
  induction S with
  | nil X =>
    have h0 : eqToHom (last_concat (nil X) T) = 𝟙 T.last := eqToHom_refl _ _
    change T.weakTransformSeq (J : (nil X).last.IdealSheafData) (Fin.last _) =
      (T.weakTransformSeq (J : (nil X).last.IdealSheafData) (Fin.last _)).comap
        (eqToHom (last_concat (nil X) T))
    erw [h0, comap_id]
  | cons X D rest ih =>
    change (rest.concat T).weakTransformSeq (J.weakTransform D) (Fin.last _) =
      (T.weakTransformSeq (rest.weakTransformSeq (J.weakTransform D) (Fin.last _))
        (Fin.last _)).comap (eqToHom _)
    exact ih T (J.weakTransform D)

/-- The boundary (the reduced total transform of the boundary divisor) at the end of a
concatenation is the boundary along `T` of the boundary along `S`. -/
theorem boundarySeq_concat_last (S : BlowUpSequence X) (T : BlowUpSequence S.last)
    (E₀ : X.IdealSheafData) :
    (S.concat T).boundarySeq E₀ (Fin.last _) =
      (T.boundarySeq (S.boundarySeq E₀ (Fin.last _)) (Fin.last _)).comap
        (eqToHom (last_concat S T)) := by
  induction S with
  | nil X =>
    have h0 : eqToHom (last_concat (nil X) T) = 𝟙 T.last := eqToHom_refl _ _
    change T.boundarySeq (E₀ : (nil X).last.IdealSheafData) (Fin.last _) =
      (T.boundarySeq (E₀ : (nil X).last.IdealSheafData) (Fin.last _)).comap
        (eqToHom (last_concat (nil X) T))
    erw [h0, comap_id]
  | cons X D rest ih =>
    change (rest.concat T).boundarySeq (E₀.reducedTransform D) (Fin.last _) =
      (T.boundarySeq (rest.boundarySeq (E₀.reducedTransform D) (Fin.last _))
        (Fin.last _)).comap (eqToHom _)
    exact ih T (E₀.reducedTransform D)

/-- A predicate on closed subschemes that holds on every centre of `S` and of `T` holds on every
centre of `S.concat T`. -/
theorem forall_center_concat (P : ∀ {Y : Scheme.{u}}, Y.IdealSheafData → Prop)
    (S : BlowUpSequence X) (T : BlowUpSequence S.last) (hS : ∀ i, P (S.center i))
    (hT : ∀ j, P (T.center j)) : ∀ i, P ((S.concat T).center i) := by
  induction S with
  | nil X => exact hT
  | cons X D rest ih =>
    intro i
    rcases i with ⟨_ | j, hj⟩
    · exact hS ⟨0, Nat.succ_pos _⟩
    · exact ih T (fun i => hS i.succ) hT ⟨j, Nat.lt_of_succ_lt_succ hj⟩

end AlgebraicGeometry.Scheme.BlowUpSequence

namespace AlgebraicGeometry

variable {X : Scheme.{u}} {k : Type u} [Field k]

/-- A smooth blow-up sequence of order `d` for `(X, J, E)` followed by one of order `d` for the
induced triple at its end result is a smooth blow-up sequence of order `d` for `(X, J, E)`
[Kol07, Definition 66]. -/
theorem isOrderSeq_concat (f : X ⟶ Spec (.of k)) (S : BlowUpSequence X) (T : BlowUpSequence S.last)
    {J : X.IdealSheafData} {E : DivisorFamily X} {d : ℕ} (hS : S.IsOrderSeq f J E d)
    (hT : T.IsOrderSeq (S.composite ≫ f) (S.weakTransformSeq J (Fin.last _))
      (S.totalTransformSeq E (Fin.last _)) d) :
    (S.concat T).IsOrderSeq f J E d := by
  induction S with
  | nil X =>
    have h : (nil X).composite ≫ f = f := Category.id_comp f
    rw [h] at hT
    exact hT
  | cons X D rest ih =>
    obtain ⟨hhead, ht⟩ := (isOrderSeq_cons_iff f J E d D rest).1 hS
    refine (isOrderSeq_cons_iff f J E d D (rest.concat T)).2 ⟨hhead, ?_⟩
    have h : (cons X D rest).composite ≫ f = rest.composite ≫ D.blowUpπ ≫ f :=
      Category.assoc _ _ _
    rw [h] at hT
    exact ih (D.blowUpπ ≫ f) T ht hT

end AlgebraicGeometry
