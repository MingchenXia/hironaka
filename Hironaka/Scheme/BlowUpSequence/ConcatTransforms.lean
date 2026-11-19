/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.ConcatApi
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Concatenation of blow-up sequences: empty centers, strict transforms, disjointness at the end

The empty blow-up convention of [Kol07, 32] along a concatenation: a concatenation of two
sequences without empty centers has none. The boundary-clearing sequence of
[Kol07, 104, Step 2.1] is a concatenation of values of the functors `BD_{n,m,j}` of
[Kol07, Lemma 102], each without empty centers, and this lemma places the induced triple in the
class of Lemma 102 again. The module also transports the strict transform of an ideal sheaf
through a concatenation (`strictTransformSeq_concat_last`) and the disjointness of Lemma 102 (1),
between the points of order `≥ m` of the weak transform and the strict transform of a divisor,
at the end of a concatenation (`disjoint_cosupp_concat_iff`).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The empty blow-up convention [Kol07, 32] through a concatenation: no empty center on either
part, none on the whole. -/
theorem noEmptyCenters_concat (S : BlowUpSequence X) (T : BlowUpSequence S.last)
    (hS : S.NoEmptyCenters) (hT : T.NoEmptyCenters) : (S.concat T).NoEmptyCenters := by
  induction S with
  | nil X => exact hT
  | cons X D rest ih =>
    rw [concat_cons, noEmptyCenters_cons_iff]
    rw [noEmptyCenters_cons_iff] at hS
    exact ⟨hS.1, ih T hS.2 hT⟩

/-- The strict transform along a concatenation is the strict transform along the second part of
the strict transform along the first; the analogue of `weakTransformSeq_concat_last` for strict
transforms. -/
theorem strictTransformSeq_concat_last (S : BlowUpSequence X) (T : BlowUpSequence S.last)
    (D : X.IdealSheafData) :
    (S.concat T).strictTransformSeq D (Fin.last _) =
      (T.strictTransformSeq (S.strictTransformSeq D (Fin.last _)) (Fin.last _)).comap
        (eqToHom (last_concat S T)) := by
  induction S with
  | nil X =>
    have h0 : eqToHom (last_concat (nil X) T) = 𝟙 T.last := eqToHom_refl _ _
    change T.strictTransformSeq (D : (nil X).last.IdealSheafData) (Fin.last _) =
      (T.strictTransformSeq (D : (nil X).last.IdealSheafData) (Fin.last _)).comap
        (eqToHom (last_concat (nil X) T))
    erw [h0, Scheme.IdealSheafData.comap_id]
  | cons X D₀ rest ih =>
    change (rest.concat T).strictTransformSeq (D.strictTransform D₀) (Fin.last _) =
      (T.strictTransformSeq (rest.strictTransformSeq (D.strictTransform D₀) (Fin.last _))
        (Fin.last _)).comap (eqToHom _)
    exact ih T (D.strictTransform D₀)

/-- The disjointness of [Kol07, Lemma 102, conclusion (1)] (the points of order `≥ m` of the weak
transform against the strict transform of a divisor) at the end of a concatenation is the
disjointness at the end of the second part for the transforms along the first, by the same
induction as the transport lemmas, without the `eqToHom` of `last_concat`. -/
theorem disjoint_cosupp_concat_iff : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (T : BlowUpSequence S.last) (J D : X.IdealSheafData) (m : ℕ),
    (Disjoint {x | (m : ℕ∞) ≤ ((S.concat T).weakTransformSeq J (Fin.last _)).ord x}
        (((S.concat T).strictTransformSeq D (Fin.last _)).support : Set _) ↔
      Disjoint
        {x | (m : ℕ∞) ≤ (T.weakTransformSeq (S.weakTransformSeq J (Fin.last _)) (Fin.last _)).ord x}
        ((T.strictTransformSeq (S.strictTransformSeq D (Fin.last _)) (Fin.last _)).support : Set _))
  | _, nil _, _, _, _, _ => Iff.rfl
  | _, cons _ D₀ rest, T, J, D, m =>
    disjoint_cosupp_concat_iff rest T (J.weakTransform D₀) (D.strictTransform D₀) m

end AlgebraicGeometry
