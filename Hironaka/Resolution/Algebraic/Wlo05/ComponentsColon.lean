/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Defs
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Resolution.Algebraic.Wlo05.ColonCoprime
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Products of pairwise disjoint components and their colons

For a finite set `C` of ideal sheaves with pairwise disjoint supports:

* any two sub-products over disjoint index sets are comaximal (`prod_sup_prod_eq_top`);
* the product over a finset is the intersection (`prod_eq_inf_of_pairwise_disjoint`), so for
  vanishing ideals the vanishing ideal of the union of the supports of a subset `A ⊆ C` is the
  product over `A` (`vanishingIdeal_iSup_support_eq_prod`);
* the colon of the full product by the product over `A` is the product over the complement
  (`colon_prod_filter`: `(∏_C c) : (∏_A c) = ∏_{C ∖ A} c`).

The comaximality tools are those of `Hironaka.Resolution.Algebraic.Wlo05.ColonCoprime`. In
Włodarczyk's embedded desingularization (`Hironaka.Resolution.Algebraic.Wlo05.Embedded`) these
describe the isolated ideal when `Y` is smooth: the components of a smooth `Y` are pairwise
disjoint, the ideal of `Y` is the product of their reduced ideals, and the colon by the reduced
ideal of the absorbed components is the ideal of the remaining ones
(`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedNilInvariant`). The vanishing ideal of a union of
disjoint components as a product is also used in
`Hironaka.Resolution.Algebraic.Wlo05.EmbeddedCP2Entry` and
`Hironaka.Resolution.Algebraic.Wlo05.StrictTransformReduced`.
-/

public section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The support of a product over a finset, as a `Finset.sup` of the supports. -/
theorem support_finset_prod_eq_sup {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) :
    (∏ j ∈ s, I j).support = s.sup fun j => (I j).support := by
  rw [Hironaka.Sequence.support_finset_prod, Finset.sup_eq_iSup]

/-- Sub-products of a family with pairwise disjoint supports over disjoint index sets are
comaximal. -/
theorem prod_sup_prod_eq_top {ι : Type*} (I : ι → X.IdealSheafData) (A B : Finset ι)
    (hdisj : ∀ a ∈ A, ∀ b ∈ B, Disjoint (I a).support (I b).support) :
    (∏ j ∈ A, I j) ⊔ (∏ j ∈ B, I j) = ⊤ := by
  apply sup_eq_top_of_disjoint_support
  rw [support_finset_prod_eq_sup, support_finset_prod_eq_sup, Finset.disjoint_sup_left]
  intro a ha
  rw [Finset.disjoint_sup_right]
  intro b hb
  exact hdisj a ha b hb

/-- The product over a finset of a family with pairwise disjoint supports is the intersection. -/
theorem prod_eq_inf_of_pairwise_disjoint {ι : Type*} (I : ι → X.IdealSheafData)
    (A : Finset ι) (hdisj : (A : Set ι).Pairwise fun a b => Disjoint (I a).support (I b).support) :
    ∏ j ∈ A, I j = A.inf I := by
  classical
  induction A using Finset.induction_on with
  | empty => simp
  | insert a A haA ih =>
    rw [Finset.prod_insert haA, Finset.inf_insert, ← ih
      (hdisj.mono (Finset.coe_subset.mpr (Finset.subset_insert a A)))]
    apply mul_eq_inf_of_sup_eq_top
    apply sup_eq_top_of_disjoint_support
    rw [support_finset_prod_eq_sup, Finset.disjoint_sup_right]
    intro b hb
    exact hdisj (Finset.mem_insert_self a A) (Finset.mem_insert_of_mem hb) (fun h => haA (h ▸ hb))

/-- For vanishing ideals with pairwise disjoint supports, the vanishing ideal of the union of the
supports over a finset is the product over the finset. -/
theorem vanishingIdeal_iSup_support_eq_prod {ι : Type*}
    (I : ι → X.IdealSheafData) (A : Finset ι)
    (hrad : ∀ a ∈ A, vanishingIdeal (I a).support = I a)
    (hdisj : (A : Set ι).Pairwise fun a b => Disjoint (I a).support (I b).support) :
    vanishingIdeal (⨆ j ∈ A, (I j).support) = ∏ j ∈ A, I j := by
  rw [prod_eq_inf_of_pairwise_disjoint I A hdisj, Finset.inf_eq_iInf]
  simp only [vanishingIdeal_iSup]
  exact iInf_congr fun j => iInf_congr fun hj => hrad j hj

/-- The colon by the absorbed components: for a finset `C` of vanishing ideals with pairwise
disjoint supports and a predicate `P` on it, the colon of the product over `C` by the vanishing
ideal of the union of the supports over `C.filter P` is the product over `C.filter (¬ P)`. -/
theorem colon_prod_filter {ι : Type*} (I : ι → X.IdealSheafData) (C : Finset ι)
    (P : ι → Prop) [DecidablePred P]
    (hrad : ∀ a ∈ C, vanishingIdeal (I a).support = I a)
    (hdisj : (C : Set ι).Pairwise fun a b => Disjoint (I a).support (I b).support) :
    (∏ j ∈ C, I j).colon (vanishingIdeal (⨆ j ∈ C.filter P, (I j).support)) =
      ∏ j ∈ C.filter (fun j => ¬ P j), I j := by
  rw [vanishingIdeal_iSup_support_eq_prod I (C.filter P)
    (fun a ha => hrad a (Finset.mem_filter.mp ha).1)
    (hdisj.mono (Finset.coe_subset.mpr (Finset.filter_subset P C)))]
  rw [← Finset.prod_filter_mul_prod_filter_not C P I]
  apply colon_mul_left_of_sup_eq_top
  apply prod_sup_prod_eq_top
  intro a ha b hb
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  exact hdisj ha'.1 hb'.1 (fun h => hb'.2 (h ▸ ha'.2))

end AlgebraicGeometry.Scheme.IdealSheafData
