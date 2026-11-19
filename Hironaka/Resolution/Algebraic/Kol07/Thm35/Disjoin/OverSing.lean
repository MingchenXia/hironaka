/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.MeetLocus
import Hironaka.Scheme.Snc.TotalTransformSnc
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The disjoining centers lie over `Sing E`

Clause (3) of the principalization theorem as proved in this library
(`exists_functorial_principalization`) says that `Π` is an isomorphism over `X ∖ (cosupp I ∪ Sing
E)`, where `Sing E` is the locus where two components of `E` meet, rather than over `X ∖ cosupp I`
as printed in [Kol07, Theorem 35 (3)]: the disjoining sequence of [Kol07, 72] blows up the
intersections of the components of `E` regardless of `I`. The fact behind this form of the clause is
that every center of the disjoining sequence lies over `Sing E`: a center is a locus where at least
two birational transforms of components meet, and a birational transform lies over its component.

* `support_center_disjoinSeqAux_le`: the invariant form: members lying over distinct components of
  a family `E₀` through a morphism `π` have all their disjoining centers over `Sing E₀`.
* `support_center_disjoinSeq_le`: the statement for the disjoining sequence.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Scheme IdealSheafData
  BlowUpSequence Scheme.IdealSheafData

namespace Hironaka.Sequence

/-- Two members through a point, lying over distinct components, put the image in `Sing E₀`. -/
theorem mem_sing_of_mem_meetLocus_two {X X₀ : Scheme.{u}} {ι : Type*} [Fintype ι]
    {G : ι → X.IdealSheafData} (π : X ⟶ X₀) (E₀ : DivisorFamily X₀) (e : ι → E₀.ι)
    (he : Function.Injective e)
    (hover : ∀ i, ∀ x ∈ (G i).support, π x ∈ (E₀.component (e i)).support) {x : X} {m : ℕ}
    (hm : 2 ≤ m) (hx : x ∈ meetLocus G m) : π x ∈ E₀.singularLocus := by
  obtain ⟨s, hs, hxs⟩ := (mem_meetLocus_iff G m x).mp hx
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  exact le_iSup₂_of_le
    (f := fun i j => ⨆ (_ : i ≠ j), (E₀.component i).support ⊓ (E₀.component j).support)
    (e i) (e j) (le_iSup_of_le (he.ne hij) le_rfl) ⟨hover i x (hxs i hi), hover j x (hxs j hj)⟩

/-- Every center of the disjoining steps lies over `Sing E₀` when the members lie over distinct
components of `E₀`. -/
theorem support_center_disjoinSeqAux_le : ∀ (m : ℕ) {X X₀ : Scheme.{u}} {ι : Type*} [Fintype ι]
    (G : ι → X.IdealSheafData) (π : X ⟶ X₀) (E₀ : DivisorFamily X₀) (e : ι → E₀.ι)
    (_ : Function.Injective e) (_ : ∀ i, ∀ x ∈ (G i).support, π x ∈ (E₀.component (e i)).support)
    (i : Fin (disjoinSeqAux m G).length), ∀ x ∈ ((disjoinSeqAux m G).center i).support,
      ((disjoinSeqAux m G).stageMap i.castSucc ≫ π) x ∈ E₀.singularLocus
  | 0, _, _, _, _, _, _, _, _, _, _, i => i.elim0
  | 1, _, _, _, _, _, _, _, _, _, _, i => i.elim0
  | m + 2, X, X₀, ι, _, G, π, E₀, e, he, hover, ⟨0, _⟩ => fun x hx => by
    change x ∈ (disjoinCenter G (m + 2)).support at hx
    rw [support_disjoinCenter] at hx
    change (𝟙 X ≫ π) x ∈ E₀.singularLocus
    rw [Category.id_comp]
    exact mem_sing_of_mem_meetLocus_two π E₀ e he hover (by omega) hx
  | m + 2, X, X₀, ι, _, G, π, E₀, e, he, hover, ⟨j + 1, h⟩ => fun x hx => by
    have hover' : ∀ i, ∀ x' ∈ ((G i).strictTransform (disjoinCenter G (m + 2))).support,
        ((disjoinCenter G (m + 2)).blowUpπ ≫ π) x' ∈ (E₀.component (e i)).support :=
      fun i x' hx' => by
        rw [Scheme.Hom.comp_apply]
        exact hover i _ (π_mem_support_of_mem_support_strictTransformAlong _ _ x' hx')
    have key := support_center_disjoinSeqAux_le (m + 1) _ ((disjoinCenter G (m + 2)).blowUpπ ≫ π)
      E₀ e he hover' ⟨j, Nat.lt_of_succ_lt_succ h⟩ x hx
    rwa [← Category.assoc] at key

/-- Every center of the disjoining sequence lies over `Sing E`: it is a locus where at least two
birational transforms of components of `E` meet. This is why clause (3) of the principalization
theorem excludes `Sing E` together with `cosupp I`. -/
theorem support_center_disjoinSeq_le {X : Scheme.{u}} (E : DivisorFamily X)
    (i : Fin (disjoinSeq E).length) :
    ((disjoinSeq E).center i).support ≤
      E.singularLocus.preimage ((disjoinSeq E).stageMap i.castSucc).continuous := by
  intro x hx
  rw [← SetLike.mem_coe, Closeds.coe_preimage, Set.mem_preimage, SetLike.mem_coe]
  have key := support_center_disjoinSeqAux_le (Fintype.card E.ι) E.component (𝟙 X) E id
    Function.injective_id (fun i x hx => by simpa using hx) i x hx
  rwa [Category.comp_id] at key

end Hironaka.Sequence
