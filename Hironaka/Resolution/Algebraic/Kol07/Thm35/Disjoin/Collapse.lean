/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.MeetLocus
import Hironaka.Resolution.Algebraic.Snc.DictionaryBoundary
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.HasSncWith
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Declaring pairwise disjoint components a single divisor

If the irreducible components of `E` happen to be disjoint, "we can just declare that `E` is a
single divisor", since Theorem 68 allows the components of `E` to be reducible [Kol07, 72].
The single divisor is `E_1 + ⋯ + E_k`, with ideal sheaf `∏_i E_i`; at a point `x` at most one
`E_i` passes, and the stalk of the product is the stalk of that one component (the others
contribute the unit ideal), so conditions (1)–(3) of [Kol07, Definition 24] hold for the
one-component family with the same coordinates, and the divisor is regular because each `E_i` is.

The same argument applies to any set of pairwise disjoint components of an snc family `F`
collapsed into one component (`DivisorFamily.collapse`), which is how Kollár's ordered family
`E^0 < E^1 < ⋯ < E^{k-1}` is assembled: the general statement is `isSnc_collapse`; the
one-component family is `asSingle_isSnc`.

* `mem_support_finset_prod_iff`: supports of finite products (the stalks are
  `stalkIdeal_finset_prod`, `Hironaka/Scheme/IdealSheaf/StalkLe.lean`).
* `exists_stalkIdeal_prod_eq_of_disjoint`: at a point of the union of pairwise disjoint closed
  subschemes, the stalk of the product is the stalk of the unique member through the point.
* `isSncAt_of_stalk_injection`: conditions (1)–(3) of Definition 24 transport along a
  stalk-matching injection of the components through a point.
* `isSnc_collapse`, `asSingle_isSnc`: the collapsed families are snc.
-/

public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing Ideal Scheme
  Scheme.IdealSheafData

namespace Hironaka.Sequence

variable {X : Scheme.{u}}

/-- A point lies on a finite product of ideal sheaves iff it lies on one of the factors. -/
theorem mem_support_finset_prod_iff {σ : Type*} (S : Finset σ) (J : σ → X.IdealSheafData)
    (x : X) : x ∈ (∏ s ∈ S, J s).support ↔ ∃ s ∈ S, x ∈ (J s).support := by
  rw [support_finset_prod, Closeds.mem_biSup_finset]

section Disjoint

variable {κ : Type*} [Fintype κ] {G : κ → X.IdealSheafData}

/-- At a point of the union of pairwise disjoint closed subschemes, the stalk of their product is
the stalk of the unique member through the point (the others contribute the unit ideal). -/
theorem exists_stalkIdeal_prod_eq_of_disjoint
    (hdisj : ∀ (x : X) (j j' : κ), x ∈ (G j).support → x ∈ (G j').support → j = j') {x : X}
    (hx : x ∈ (∏ j, G j).support) :
    ∃ j : κ, x ∈ (G j).support ∧ (∏ j, G j).stalkIdeal x = (G j).stalkIdeal x := by
  obtain ⟨j, -, hj⟩ := (mem_support_finset_prod_iff _ _ _).mp hx
  refine ⟨j, hj, ?_⟩
  rw [IdealSheafData.stalkIdeal_finset_prod, Finset.prod_eq_single j]
  · intro j' _ hj'
    rw [Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support _
      fun h => hj' (hdisj x j' j h hj)]
    exact Ideal.one_eq_top.symm
  · intro h
    exact absurd (Finset.mem_univ j) h

end Disjoint

/-- Bookkeeping: Kollár's conditions (1)–(3) at `x` transport along an injection of the components
of `F'` through `x` into those of `F` through `x` that matches the stalks at `x`. -/
theorem isSncAt_of_stalk_injection {F F' : DivisorFamily X} {x : X} {n : ℕ}
    {z : Fin n → X.presheaf.stalk x} (h : F.IsSncAt x z)
    (θ : {i : F'.ι // x ∈ (F'.component i).support} → {a : F.ι // x ∈ (F.component a).support})
    (hθ : Function.Injective θ)
    (hst : ∀ i, (F'.component i.1).stalkIdeal x = (F.component (θ i).1).stalkIdeal x) :
    F'.IsSncAt x z := by
  obtain ⟨hrs, c, hcinj, hc⟩ := h
  exact ⟨hrs, c ∘ θ, hcinj.comp hθ, fun i => (hst i).trans (hc (θ i))⟩

/-- At a point of a smooth `k`-scheme, the quotient of the stalk by a coordinate of a regular
system of parameters is a regular local ring. -/
theorem isRegularLocalRing_quotient_span_singleton_of_isSncAt {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [Smooth f] {x : X} {n : ℕ} {z : Fin n → X.presheaf.stalk x}
    (hrs : IsRegularSystemOfParameters z) (j : Fin n) :
    IsRegularLocalRing (X.presheaf.stalk x ⧸ span {z j}) := by
  have := isRegularLocalRing_stalk f x
  have h := isRegularLocalRing_quotient_span_image_finset hrs.1.symm hrs.2 {j}
  rwa [Finset.coe_singleton, Set.image_singleton] at h

section Collapse

variable {F : DivisorFamily X} {p : F.ι → Prop}

/-- The members to collapse are pairwise disjoint, as a family over the collapsed indices. -/
theorem collapse_disjoint
    (hp : ∀ (x : X) (a b : F.ι), p a → p b → x ∈ (F.component a).support →
      x ∈ (F.component b).support → a = b) (x : X) (j j' : {a : F.ι // p a})
    (hj : x ∈ (F.component j.1).support) (hj' : x ∈ (F.component j'.1).support) : j = j' :=
  Subtype.ext (hp x j.1 j'.1 j.2 j'.2 hj hj')

variable (p) [DecidablePred p]

/-- The collapsed component is the product of the collapsed members. -/
theorem collapse_component_bot :
    (F.collapse p).component (⊥ : WithBot _) = ∏ a : {a : F.ι // p a}, F.component a.1 := rfl

/-- The other components are unchanged. -/
theorem collapse_component_coe (a : {a : F.ι // ¬ p a}) :
    (F.collapse p).component (a : WithBot {a : F.ι // ¬ p a}) = F.component a.1 := rfl

variable {p}

/-- Collapsing a pairwise disjoint set of components of an snc family into one component gives an
snc family ("in (68) we allow the components of `E` to be reducible", [Kol07, 72]). -/
theorem isSnc_collapse {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [Smooth f] (hF : F.IsSnc)
    (hp : ∀ (x : X) (a b : F.ι), p a → p b → x ∈ (F.component a).support →
      x ∈ (F.component b).support → a = b) :
    (F.collapse p).IsSnc := by
  classical
  have hdisj := collapse_disjoint hp
  refine ⟨fun i => ?_, fun x => ?_⟩
  · induction i using WithBot.recBotCoe with
    | bot =>
      refine isRegular_subscheme_of_isRegularLocalRing_quotient _ fun w hw => ?_
      obtain ⟨j, hwj, heq⟩ :=
        exists_stalkIdeal_prod_eq_of_disjoint (G := fun a : {a : F.ι // p a} => F.component a.1)
          hdisj hw
      obtain ⟨n, z, hrs, c, -, hc⟩ := hF.2 w
      rw [collapse_component_bot, heq, hc ⟨j.1, hwj⟩]
      exact isRegularLocalRing_quotient_span_singleton_of_isSncAt f hrs _
    | coe a => exact hF.1 a.1
  · obtain ⟨n, z, hz⟩ := hF.2 x
    refine ⟨n, z, isSncAt_of_stalk_injection hz (fun i => ?_) ?_ ?_⟩
    · -- the member of `F` through `x` carrying the component `i` of the collapse
      refine WithBot.recBotCoe (C := fun w => x ∈ ((F.collapse p).component w).support →
        {a : F.ι // x ∈ (F.component a).support}) (fun hx => ?_) (fun a hx => ⟨a.1, hx⟩) i.1 i.2
      exact ⟨(Classical.choose (exists_stalkIdeal_prod_eq_of_disjoint
        (G := fun a : {a : F.ι // p a} => F.component a.1) hdisj hx)).1,
        (Classical.choose_spec (exists_stalkIdeal_prod_eq_of_disjoint
          (G := fun a : {a : F.ι // p a} => F.component a.1) hdisj hx)).1⟩
    · rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ h
      induction i₁ using WithBot.recBotCoe with
      | bot =>
        induction i₂ using WithBot.recBotCoe with
        | bot => rfl
        | coe b =>
          exfalso
          simp only [WithBot.recBotCoe_bot, WithBot.recBotCoe_coe] at h
          have h' := Subtype.ext_iff.mp h
          exact b.2 (h' ▸ (Classical.choose (exists_stalkIdeal_prod_eq_of_disjoint
            (G := fun a : {a : F.ι // p a} => F.component a.1) hdisj h₁)).2)
      | coe a =>
        induction i₂ using WithBot.recBotCoe with
        | bot =>
          exfalso
          simp only [WithBot.recBotCoe_bot, WithBot.recBotCoe_coe] at h
          have h' := Subtype.ext_iff.mp h
          exact a.2 (h'.symm ▸ (Classical.choose (exists_stalkIdeal_prod_eq_of_disjoint
            (G := fun a : {a : F.ι // p a} => F.component a.1) hdisj h₂)).2)
        | coe b =>
          simp only [WithBot.recBotCoe_coe] at h
          have h' : a.1 = b.1 := (Subtype.ext_iff.mp h :)
          exact Subtype.ext
            (congrArg (fun c : {a : F.ι // ¬ p a} => (c : WithBot {a : F.ι // ¬ p a}))
              (Subtype.ext h'))
    · rintro ⟨i, hi⟩
      induction i using WithBot.recBotCoe with
      | bot =>
        simp only [WithBot.recBotCoe_bot]
        exact (Classical.choose_spec (exists_stalkIdeal_prod_eq_of_disjoint
          (G := fun a : {a : F.ι // p a} => F.component a.1) hdisj hi)).2
      | coe a => rfl

end Collapse

section AsSingle

/-- The single divisor is `E_1 + ⋯ + E_k`, with ideal sheaf `∏_i E_i` [Kol07, 72]. -/
theorem asSingle_component (E : DivisorFamily X) :
    E.asSingle.component PUnit.unit = ∏ i, E.component i := rfl

/-- The single divisor has the support of `E`. -/
theorem support_asSingle (E : DivisorFamily X) : E.asSingle.support = E.support := by
  change (⨆ _ : PUnit, (∏ i, E.component i).support) = ⨆ i, (E.component i).support
  rw [iSup_const, support_finset_prod]
  simp only [Finset.mem_univ, iSup_true]

/-- Pairwise disjoint components: `Sing E = ∅` means that no point lies on two components. -/
theorem eq_of_mem_support_of_sing_eq_bot {E : DivisorFamily X} (hsing : E.singularLocus = ⊥) {x : X}
    {i j : E.ι} (hi : x ∈ (E.component i).support) (hj : x ∈ (E.component j).support) : i = j := by
  by_contra hij
  have hx : x ∈ E.singularLocus :=
    le_iSup₂_of_le
      (f := fun i j => ⨆ (_ : i ≠ j), (E.component i).support ⊓ (E.component j).support)
      i j (le_iSup_of_le hij le_rfl) ⟨hi, hj⟩
  rw [hsing] at hx
  exact hx

/-- If the components of the snc divisor `E` are pairwise disjoint, then `E` declared a single
(reducible) divisor is an snc family [Kol07, 72], a legal input for [Kol07, Theorems 68 and 69]. -/
theorem asSingle_isSnc {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [Smooth f]
    (E : DivisorFamily X) (hE : E.IsSnc) (hsing : E.singularLocus = ⊥) : E.asSingle.IsSnc := by
  have hdisj : ∀ (x : X) (j j' : E.ι), x ∈ (E.component j).support →
      x ∈ (E.component j').support → j = j' :=
    fun x j j' hj hj' => eq_of_mem_support_of_sing_eq_bot hsing hj hj'
  refine ⟨fun _ => ?_, fun x => ?_⟩
  · refine isRegular_subscheme_of_isRegularLocalRing_quotient _ fun w hw => ?_
    obtain ⟨j, hwj, heq⟩ := exists_stalkIdeal_prod_eq_of_disjoint hdisj hw
    obtain ⟨n, z, hrs, c, -, hc⟩ := hE.2 w
    change IsRegularLocalRing (X.presheaf.stalk w ⧸ (∏ i, E.component i).stalkIdeal w)
    rw [heq, hc ⟨j, hwj⟩]
    exact isRegularLocalRing_quotient_span_singleton_of_isSncAt f hrs _
  · obtain ⟨n, z, hz⟩ := hE.2 x
    refine ⟨n, z, isSncAt_of_stalk_injection hz
      (fun i => ⟨Classical.choose (exists_stalkIdeal_prod_eq_of_disjoint hdisj i.2),
        (Classical.choose_spec (exists_stalkIdeal_prod_eq_of_disjoint hdisj i.2)).1⟩)
      (fun i₁ i₂ _ => Subtype.ext (@Subsingleton.elim _ (inferInstanceAs (Subsingleton PUnit)) _ _))
      fun i =>
        (Classical.choose_spec (exists_stalkIdeal_prod_eq_of_disjoint hdisj i.2)).2⟩

end AsSingle

end Hironaka.Sequence
