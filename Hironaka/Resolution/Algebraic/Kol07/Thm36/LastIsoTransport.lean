/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.EraseEmptyInduced
import Hironaka.Resolution.Algebraic.Kol07.Thm36.SncPreimageSingular
import Hironaka.Scheme.BlowUpSequence.ConcatApi
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transport of the end-result clauses along an isomorphism of last stages

Clauses (1)–(3) of [Kol07, Theorem 36] speak about the end result `X_r` of a blow-up sequence and
its composite `Π : X_r → X`: the end result is smooth, `Π` is an isomorphism over the smooth
locus, `Π⁻¹(Sing X)` is the support of a simple normal crossing family. The resolution functor
deletes the empty blow-ups of the affine resolution ([Kol07, 32] and the second bullet of
[Kol07, 34.1]), a harmless change of the sequence that leaves the composite unchanged up to an
isomorphism of the last stages. This module records the isomorphism and the transport of the three
clauses:

* `eraseEmptyLastIso S : S.eraseEmpty.last ≅ S.last` with
  `(eraseEmptyLastIso S).hom ≫ S.composite = S.eraseEmpty.composite` (from `eraseEmptyLastHom` of
  `Hironaka/Scheme/BlowUpSequence/EraseEmptyConcat.lean`, an isomorphism by
  `isIso_eraseEmptyLastHom`);
* for an isomorphism `e : S'.last ≅ S.last` with `e.hom ≫ S.composite = S'.composite`:
  `smooth_composite_of_lastIso`, `isIso_composite_restrict_of_lastIso`,
  `exists_isSnc_support_eq_preimage_of_lastIso`: clauses (1), (2), (3) pass from `S` to `S'` (the
  simple normal crossing family is pulled back along the isomorphism, `isSnc_comap_of_smooth`);
* the same three clauses pass between two sequences with the same erasure.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence

namespace Hironaka.Sequence

variable {X : Scheme.{u}}

/-! ### The isomorphism of last stages -/

/-- The last stage of the sequence with its empty blow-ups deleted is isomorphic to the last stage
of the sequence (`eraseEmptyLastHom` is an isomorphism). -/
noncomputable def eraseEmptyLastIso (S : BlowUpSequence X) : S.eraseEmpty.last ≅ S.last :=
  asIso S.eraseEmptyLastHom

theorem eraseEmptyLastIso_hom_comp_composite (S : BlowUpSequence X) :
    (eraseEmptyLastIso S).hom ≫ S.composite = S.eraseEmpty.composite :=
  eraseEmptyLastHom_comp_composite S

/-! ### Transport of the three clauses -/

section Transport

variable {S S' : BlowUpSequence X} (e : S'.last ≅ S.last) (he : e.hom ≫ S.composite = S'.composite)
include he

/-- Clause (1) along an isomorphism of last stages: the end result stays smooth. -/
theorem smooth_composite_of_lastIso {Z : Scheme.{u}} (f : X ⟶ Z) [Smooth (S.composite ≫ f)] :
    Smooth (S'.composite ≫ f) := by
  rw [← he, Category.assoc]
  infer_instance

/-- Clause (2) along an isomorphism of last stages: the composite stays an isomorphism over an
open `W` of the base. -/
theorem isIso_composite_restrict_of_lastIso (W : X.Opens) [IsIso (S.composite ∣_ W)] :
    IsIso (S'.composite ∣_ W) := by
  -- the domains `(e.hom ≫ S.composite) ⁻¹ᵁ W` and `e.hom ⁻¹ᵁ (S.composite ⁻¹ᵁ W)` agree only
  -- definitionally, so the composition instance is applied by an explicit term
  have hiso : IsIso ((e.hom ≫ S.composite) ∣_ W) := by
    rw [morphismRestrict_comp]
    exact @IsIso.comp_isIso Scheme.{u} _ _ _ _ (e.hom ∣_ (S.composite ⁻¹ᵁ W)) (S.composite ∣_ W)
      inferInstance inferInstance
  rw [he] at hiso
  exact hiso

/-- Clause (3) along an isomorphism of last stages: an snc family whose support is the preimage of
a set `W` of the base pulls back to one on the other last stage (`isSnc_comap_of_smooth` along the
isomorphism, which is smooth; the end result is smooth over `k` by clause (1)). -/
theorem exists_isSnc_support_eq_preimage_of_lastIso {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth (S.composite ≫ f)] (W : Set X)
    (h : ∃ F : DivisorFamily S.last, F.IsSnc ∧ (F.support : Set S.last) = S.composite ⁻¹' W) :
    ∃ F' : DivisorFamily S'.last, F'.IsSnc ∧ (F'.support : Set S'.last) = S'.composite ⁻¹' W := by
  obtain ⟨F, hF, hsupp⟩ := h
  refine ⟨F.comap e.hom, isSnc_comap_of_smooth (S.composite ≫ f) e.hom hF, ?_⟩
  ext y
  rw [SetLike.mem_coe, DivisorFamily.mem_comap_support_iff, ← SetLike.mem_coe,
    hsupp, Set.mem_preimage, Set.mem_preimage, ← he, Scheme.Hom.comp_apply]

end Transport

/-! ### Two sequences with the same erasure -/

/-- Clause (1) passes between two sequences with the same erasure. -/
theorem smooth_composite_of_eraseEmpty_eq {S S' : BlowUpSequence X}
    (h : S.eraseEmpty = S'.eraseEmpty) {Z : Scheme.{u}} (f : X ⟶ Z)
    [Smooth (S.composite ≫ f)] : Smooth (S'.composite ≫ f) := by
  have h1 : Smooth (S.eraseEmpty.composite ≫ f) :=
    smooth_composite_of_lastIso (eraseEmptyLastIso S) (eraseEmptyLastIso_hom_comp_composite S) f
  rw [h] at h1
  exact smooth_composite_of_lastIso (eraseEmptyLastIso S').symm
    (by rw [Iso.symm_hom, ← eraseEmptyLastIso_hom_comp_composite, Iso.inv_hom_id_assoc]) f

/-- Clause (2) passes between two sequences with the same erasure. -/
theorem isIso_composite_restrict_of_eraseEmpty_eq {S S' : BlowUpSequence X}
    (h : S.eraseEmpty = S'.eraseEmpty) (W : X.Opens) [IsIso (S.composite ∣_ W)] :
    IsIso (S'.composite ∣_ W) := by
  have h1 : IsIso (S.eraseEmpty.composite ∣_ W) :=
    isIso_composite_restrict_of_lastIso (eraseEmptyLastIso S)
      (eraseEmptyLastIso_hom_comp_composite S) W
  rw [h] at h1
  exact isIso_composite_restrict_of_lastIso (eraseEmptyLastIso S').symm
    (by rw [Iso.symm_hom, ← eraseEmptyLastIso_hom_comp_composite, Iso.inv_hom_id_assoc]) W

/-- Clause (3) passes between two sequences with the same erasure. -/
theorem exists_isSnc_support_eq_preimage_of_eraseEmpty_eq {S S' : BlowUpSequence X}
    (h : S.eraseEmpty = S'.eraseEmpty) {k : Type u} [Field k] [CharZero k]
    (f : X ⟶ Spec (CommRingCat.of k))
    [Smooth (S.composite ≫ f)] (W : Set X)
    (hF : ∃ F : DivisorFamily S.last, F.IsSnc ∧ (F.support : Set S.last) = S.composite ⁻¹' W) :
    ∃ F' : DivisorFamily S'.last, F'.IsSnc ∧ (F'.support : Set S'.last) = S'.composite ⁻¹' W := by
  have hsm : Smooth (S.eraseEmpty.composite ≫ f) :=
    smooth_composite_of_lastIso (eraseEmptyLastIso S) (eraseEmptyLastIso_hom_comp_composite S) f
  have h1 := exists_isSnc_support_eq_preimage_of_lastIso (eraseEmptyLastIso S)
    (eraseEmptyLastIso_hom_comp_composite S) f W hF
  rw [h] at h1 hsm
  exact exists_isSnc_support_eq_preimage_of_lastIso (eraseEmptyLastIso S').symm
    (by rw [Iso.symm_hom, ← eraseEmptyLastIso_hom_comp_composite, Iso.inv_hom_id_assoc]) f W h1

end Hironaka.Sequence
