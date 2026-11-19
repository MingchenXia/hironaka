/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.Defs
public import Hironaka.Scheme.Smooth.EtaleCoordinatesDefs
import Hironaka.Scheme.BlowUp.Glue.RestrictOpen
import Hironaka.Scheme.BlowUp.Glue.Trivial
import Hironaka.Scheme.Smooth.BlowUpSmoothChart
import Hironaka.Scheme.Smooth.EtaleCoordinatesAdapted
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.RingTheory.FiniteLength

/-!
# The blow-up of a smooth center in a smooth scheme is smooth

`k` a perfect field, `f : X ⟶ Spec k` smooth of relative dimension `n`, `Z` an ideal sheaf whose
closed subscheme `V(Z)` is smooth over `k` of relative dimension `n − r` (`r ≤ n`). Kollár's
"if `π_{Z,X}` is a smooth blow-up, then … `B_Z X` [is] smooth" [Kol07, Notation 19], proved here
in the form `B_Z X → Spec k` is smooth of relative dimension `n`
(`smoothOfRelativeDimension_blowUpπ_comp`).

The argument. Smoothness of relative dimension `n` is Zariski-local on the source
(`IsZariskiLocalAtSource.of_iSup_eq_top`); `B_Z X` is covered by `π⁻¹(U)` for the charts `U` of
étale coordinates adapted to `Z` at the closed points of `V(Z)` (`EtaleCoordinatesAdapted`),
where `π⁻¹(U) ≅ B_{Z∩U} U` (`blowUp.restrictIso`) is smooth by the chart computation of
`Hironaka/Scheme/Smooth/BlowUpSmoothChart.lean`, and by `π⁻¹(X ∖ V(Z))`, where `π` is an isomorphism
(`isIso_π_restrict_compl_support`). These opens cover `X` because `X` is a Jacobson space
(locally of finite type over a field, `LocallyOfFiniteType.jacobsonSpace`): the complement of
their union is a closed subset of `X` without closed points, hence empty
(`nonempty_inter_closedPoints`, `iSup_eq_top_of_forall_isClosed`). Forgetting the relative
dimension, `B_Z X` is smooth over `k` (`smooth_blowUpπ_comp`). Every morphism out of an empty
scheme is smooth (`smooth_of_isEmpty`), as for the empty center `Z = ∅` of [Kol07, Warning 20].

This is the step that keeps the ambient scheme smooth along a sequence of smooth blow-ups
(`Hironaka/Scheme/BlowUpSequence/Basic.lean`, `Hironaka/Scheme/BlowUpSequence/SmoothCenter.lean`).
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

open AlgebraicGeometry Scheme.IdealSheafData

variable {k : Type u} [Field k] {X : Scheme.{u}}

section Pieces

/-- Over the complement of the center the blow-up is an isomorphism
(`isIso_π_restrict_compl_support`), so `π ≫ f` restricted there is smooth of relative dimension
`n` when `f` is. -/
theorem smoothOfRelativeDimension_restrict_compl_support (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] (Z : X.IdealSheafData) :
    SmoothOfRelativeDimension n
      ((blowUpπ Z ∣_ Z.support.compl) ≫ Scheme.Opens.ι Z.support.compl ≫ f) := by
  have := blowUp.isIso_π_restrict_compl_support Z
  have : SmoothOfRelativeDimension (0 + (0 + n))
      ((blowUpπ Z ∣_ Z.support.compl) ≫ Scheme.Opens.ι Z.support.compl ≫ f) := inferInstance
  rwa [zero_add, zero_add] at this

/-- Over a chart `U` of étale coordinates adapted to `Z`, `π⁻¹(U) ≅ B_{Z∩U} U`
(`preimageToRestrict`) is smooth of relative dimension `n` over `k`
(`smoothOfRelativeDimension_blowUpπ_comap`). -/
theorem smoothOfRelativeDimension_restrict_of_etaleCoordinates {f : X ⟶ Spec (.of k)} {n r : ℕ}
    {Z : X.IdealSheafData} {x : X} (E : EtaleCoordinatesAdapted f n r Z x) :
    SmoothOfRelativeDimension n ((blowUpπ Z ∣_ E.U.1) ≫ E.U.1.ι ≫ f) := by
  have := smoothOfRelativeDimension_blowUpπ_comap E
  have : IsIso (preimageToRestrict Z E.U.1) :=
    ⟨⟨restrictHomToPreimage Z E.U.1, preimageToRestrict_restrictHomToPreimage Z E.U.1,
      restrictHomToPreimage_preimageToRestrict Z E.U.1⟩⟩
  rw [← preimageToRestrict_π Z E.U.1, Category.assoc]
  have : SmoothOfRelativeDimension (0 + n)
      (preimageToRestrict Z E.U.1 ≫ blowUpπ (Z.comap E.U.1.ι) ≫ E.U.1.ι ≫ f) := inferInstance
  rwa [zero_add] at this

/-- Opens `U x ∋ x` given at every closed point `x` of `V(Z)`, together with the complement of
`V(Z)`, cover the Jacobson space `X`: the complement of their union is a closed set without
closed points, hence empty. -/
theorem iSup_eq_top_of_forall_isClosed [JacobsonSpace X] (Z : X.IdealSheafData)
    (U : {x : X // IsClosed ({x} : Set X) ∧ x ∈ Z.support} → X.Opens) (hU : ∀ x, x.1 ∈ U x) :
    (⨆ x, U x) ⊔ Z.support.compl = ⊤ := by
  set O : X.Opens := (⨆ x, U x) ⊔ Z.support.compl with hO
  by_contra h
  have hne : ((O : Set X)ᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    intro hO'
    exact h (Opens.ext hO')
  obtain ⟨c, hcC, hc⟩ := nonempty_inter_closedPoints hne O.isOpen.isClosed_compl.isLocallyClosed
  have hcZ : c ∈ Z.support := by
    by_contra hcZ
    exact hcC (Opens.mem_sup.mpr (Or.inr hcZ))
  exact hcC (Opens.mem_sup.mpr (Or.inl (Opens.mem_iSup.mpr ⟨⟨c, hc, hcZ⟩, hU _⟩)))

/-- Every morphism out of an empty scheme is smooth (the empty open cover). -/
theorem smooth_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (g : Y ⟶ X) : Smooth g := by
  have hloc : IsZariskiLocalAtSource @Smooth :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) (fun _ : PEmpty.{u + 1} => ⊥) ?_
    fun i => i.elim
  ext y
  exact isEmptyElim y

end Pieces

section Main

variable [PerfectField k] (f : X ⟶ Spec (.of k)) (n r : ℕ) [SmoothOfRelativeDimension n f]
  (Z : X.IdealSheafData) [SmoothOfRelativeDimension (n - r) (Z.subschemeι ≫ f)] (hrn : r ≤ n)

include n r hrn

/-- **The blow-up of a smooth center in a smooth scheme is smooth** [Kol07, Notation 19]: for `X`
smooth over the perfect field `k` of relative dimension `n` and `V(Z)` smooth of relative
dimension `n − r`, `B_Z X → Spec k` is smooth of relative dimension `n`. Glued from the chart
computation over the charts of adapted étale coordinates at the closed points of `V(Z)` and the
complement of `V(Z)`, which cover `X` because `X` is Jacobson. -/
theorem smoothOfRelativeDimension_blowUpπ_comp :
    SmoothOfRelativeDimension n (blowUpπ Z ≫ f) := by
  classical
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{u} n) :=
    @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  have : IsJacobsonRing k := inferInstance
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  let E : ∀ x : {x : X // IsClosed ({x} : Set X) ∧ x ∈ Z.support},
      EtaleCoordinatesAdapted f n r Z x.1 :=
    fun x => Classical.choice (nonempty_etaleCoordinatesAdapted f n r Z hrn x.2.2 x.2.1)
  let V : Option {x : X // IsClosed ({x} : Set X) ∧ x ∈ Z.support} → X.Opens :=
    fun o => o.elim Z.support.compl fun x => (E x).U.1
  have hV : iSup V = ⊤ := by
    rw [← iSup_eq_top_of_forall_isClosed Z (fun x => (E x).U.1) fun x => (E x).mem]
    apply le_antisymm
    · refine iSup_le fun o => ?_
      cases o with
      | none => exact le_sup_right
      | some x => exact (le_iSup (fun x => (E x).U.1) x).trans le_sup_left
    · exact sup_le (iSup_le fun x => le_iSup V (some x)) (le_iSup V none)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{u} n)
    (fun o => blowUpπ Z ⁻¹ᵁ V o) ?_ fun o => ?_
  · rw [← Scheme.Hom.preimage_iSup, hV, Scheme.Hom.preimage_top]
  · rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    cases o with
    | none => exact smoothOfRelativeDimension_restrict_compl_support f n Z
    | some x => exact smoothOfRelativeDimension_restrict_of_etaleCoordinates (E x)

/-- In Kollár's words [Kol07, Notation 19]: `B_Z X` is smooth over `k`. -/
theorem smooth_blowUpπ_comp : Smooth (blowUpπ Z ≫ f) := by
  have := smoothOfRelativeDimension_blowUpπ_comp f n r Z hrn
  exact SmoothOfRelativeDimension.smooth n _

end Main

end AlgebraicGeometry
