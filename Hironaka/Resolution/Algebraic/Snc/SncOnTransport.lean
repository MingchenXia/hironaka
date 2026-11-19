/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.SncOn
public import Hironaka.Scheme.Snc.Basic
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Resolution.Algebraic.Kol07.Thm35.Disjoin.Collapse
import Hironaka.Scheme.Smooth.AdaptedCoordinates
import Hironaka.Scheme.Snc.RestrictHypersurface
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Transport of simple normal crossings along reindexings

[Kol07, Definition 24] at a point (`IsSncAt`) is a statement about the members THROUGH the point: it
transfers along any injection of index sets that matches the members (`isSncAt_of_stalk_injection`,
restated here for a global injection with equal members, `isSncAt_of_injective_components`), hence
to sub-families (`isSncOn_subfamily_append_mono`) and along the reindexing that the induction of
`Hironaka.Resolution.Algebraic.Kol07.SncGlobalSubfamily` (Step 2.1 of [Kol07, 104]) needs at each
blow-up: the members of `((E.totalTransform D).subfamily (extendPred p)).append (strictTransform D
H)` — the selected members of the total transform, the new exceptional divisor, the birational
transform of `H` — are those of `((E.subfamily p).append H).totalTransform D` (`stepIdx`,
`component_stepIdx`, `stepIdx_injective`). The base of that induction, a smooth divisor alone, is
`isSnc_append_empty_of_isSmoothDivisor` of `Hironaka.Scheme.Snc.RestrictHypersurface` read on the
empty sub-family (`isSncOn_subfamily_false_append`).

Sources: [Kol07, Definition 24; Definition 25; 104] (Step 2.1).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData IsLocalRing

namespace Hironaka.Snc

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Definition 24 at a point transfers along an injection of index sets matching the members. -/
theorem isSncAt_of_injective_components {F F' : DivisorFamily X} (θ : F'.ι → F.ι)
    (hθ : Function.Injective θ) (hcomp : ∀ i, F'.component i = F.component (θ i)) {x : X}
    {n : ℕ} {z : Fin n → X.presheaf.stalk x} (h : F.IsSncAt x z) : F'.IsSncAt x z :=
  Hironaka.Sequence.isSncAt_of_stalk_injection h
    (fun i => ⟨θ i.1, by rw [← hcomp]; exact i.2⟩)
    (fun i₁ i₂ h12 => Subtype.ext (hθ (congrArg Subtype.val h12)))
    (fun i => congrArg (fun J : X.IdealSheafData => J.stalkIdeal x) (hcomp i.1))

/-- Snc along a set transfers along an injection of index sets matching the members. -/
theorem isSncOn_of_injective_components {F F' : DivisorFamily X} (θ : F'.ι → F.ι)
    (hθ : Function.Injective θ) (hcomp : ∀ i, F'.component i = F.component (θ i)) {s : Set X}
    (h : F.IsSncOn s) : F'.IsSncOn s := fun x hx =>
  let ⟨n, z, hz⟩ := h x hx
  ⟨n, z, isSncAt_of_injective_components θ hθ hcomp hz⟩

/-- A sub-family of a family with an appended member: shrinking the selected set keeps snc along a
set. -/
theorem isSncOn_subfamily_append_mono {E : DivisorFamily X} {p q : E.ι → Prop}
    (hpq : ∀ i, p i → q i) (H : X.IdealSheafData) {s : Set X}
    (h : ((E.subfamily q).append H).IsSncOn s) : ((E.subfamily p).append H).IsSncOn s := by
  have hf : Function.Injective
      (fun a : {a : E.ι // p a} => (⟨a.1, hpq a.1 a.2⟩ : {a : E.ι // q a})) :=
    fun a₁ a₂ h12 => Subtype.ext (Subtype.mk.inj h12)
  refine isSncOn_of_injective_components
    (toLex ∘ Sum.map (fun a : {a : E.ι // p a} => (⟨a.1, hpq a.1 a.2⟩ : {a : E.ι // q a})) id ∘
      ofLex) (toLex.injective.comp ((hf.sumMap Function.injective_id).comp ofLex.injective))
    ?_ h
  intro i
  rcases i with a | u
  · rfl
  · rfl

/-- Extend a predicate on the members of `E` to the members of `E.totalTransform D`: the new
exceptional member is selected. -/
def extendPred {ι : Type u} (p : ι → Prop) : ι ⊕ₗ PUnit.{u + 1} → Prop :=
  fun i => Sum.elim p (fun _ => True) (ofLex i)

/-- The reindexing of the induction step of
`Hironaka.Resolution.Algebraic.Kol07.SncGlobalSubfamily`: the members of `((E.totalTransform
D).subfamily (extendPred p)).append (strictTransform D H)` among those of `((E.subfamily p).append
H).totalTransform D`. -/
def stepIdx (E : DivisorFamily X) (p : E.ι → Prop) :
    ({i : E.ι ⊕ₗ PUnit.{u + 1} // extendPred p i} ⊕ₗ PUnit.{u + 1}) →
      (({a : E.ι // p a} ⊕ₗ PUnit.{u + 1}) ⊕ₗ PUnit.{u + 1}) := fun i =>
  Sum.elim
    (fun j : {j : E.ι ⊕ₗ PUnit.{u + 1} // extendPred p j} =>
      (Sum.rec (motive := fun s => Sum.elim p (fun _ => True) s →
          (({a : E.ι // p a} ⊕ₗ PUnit.{u + 1}) ⊕ₗ PUnit.{u + 1}))
        (fun a ha => toLex (Sum.inl (toLex (Sum.inl ⟨a, ha⟩))))
        (fun u _ => toLex (Sum.inr u)) (ofLex j.1)) j.2)
    (fun u => toLex (Sum.inl (toLex (Sum.inr u)))) (ofLex i)

/-- `stepIdx` matches the members. -/
theorem component_stepIdx (E : DivisorFamily X) (p : E.ι → Prop) (D H : X.IdealSheafData) (i) :
    (((E.totalTransform D).subfamily (extendPred p)).append (H.strictTransform D)).component i =
      (((E.subfamily p).append H).totalTransform D).component (stepIdx E p i) := by
  rcases i with ⟨j, hj⟩ | u
  · rcases j with a | v
    · rfl
    · rfl
  · rfl

/-- The left inverse of `stepIdx`. -/
def stepIdxInv (E : DivisorFamily X) (p : E.ι → Prop) :
    (({a : E.ι // p a} ⊕ₗ PUnit.{u + 1}) ⊕ₗ PUnit.{u + 1}) →
      ({i : E.ι ⊕ₗ PUnit.{u + 1} // extendPred p i} ⊕ₗ PUnit.{u + 1}) := fun i =>
  Sum.elim
    (fun j => Sum.elim (fun a : {a : E.ι // p a} => toLex (Sum.inl ⟨toLex (Sum.inl a.1), a.2⟩))
      (fun u => toLex (Sum.inr u)) (ofLex j))
    (fun u => toLex (Sum.inl ⟨toLex (Sum.inr u), trivial⟩)) (ofLex i)

theorem stepIdxInv_stepIdx (E : DivisorFamily X) (p : E.ι → Prop) (i) :
    stepIdxInv E p (stepIdx E p i) = i := by
  rcases i with ⟨j, hj⟩ | u
  · rcases j with a | v
    · rfl
    · rfl
  · rfl

/-- `stepIdx` is injective. -/
theorem stepIdx_injective (E : DivisorFamily X) (p : E.ι → Prop) :
    Function.Injective (stepIdx E p) :=
  Function.LeftInverse.injective (stepIdxInv_stepIdx E p)

/-- Definition 24 at a point for a family with an appended member, from the sub-family of the
members selected by `p`, when every member through the point is selected (the final step of the
induction: at a point of the cosupport every member of `E_r` is exceptional). -/
theorem isSncAt_append_of_subfamily {E : DivisorFamily X} {p : E.ι → Prop} {H : X.IdealSheafData}
    {x : X} (hP : ∀ i, x ∈ (E.component i).support → p i) {n : ℕ} {z : Fin n → X.presheaf.stalk x}
    (h : ((E.subfamily p).append H).IsSncAt x z) : (E.append H).IsSncAt x z := by
  obtain ⟨hrs, c, hcinj, hc⟩ := h
  let θ : {i : (E.append H).ι // x ∈ ((E.append H).component i).support} →
      {i : ((E.subfamily p).append H).ι // x ∈ (((E.subfamily p).append H).component i).support} :=
    fun i => Sum.rec
      (motive := fun s => x ∈ ((E.append H).component (toLex s)).support →
        {i : ((E.subfamily p).append H).ι // x ∈ (((E.subfamily p).append H).component i).support})
      (fun a ha => ⟨toLex (Sum.inl ⟨a, hP a ha⟩), ha⟩) (fun u hu => ⟨toLex (Sum.inr u), hu⟩)
      (ofLex i.1) i.2
  refine ⟨hrs, fun i => c (θ i), ?_, ?_⟩
  · intro i₁ i₂ h12
    have h12' := hcinj h12
    obtain ⟨i₁, hi₁⟩ := i₁
    obtain ⟨i₂, hi₂⟩ := i₂
    rcases i₁ with a₁ | u₁ <;> rcases i₂ with a₂ | u₂
    · have h0 : (⟨a₁, hP a₁ hi₁⟩ : {a : E.ι // p a}) = ⟨a₂, hP a₂ hi₂⟩ :=
        Sum.inl_injective (toLex.injective (Subtype.mk.inj h12'))
      have h1 : a₁ = a₂ := Subtype.mk.inj h0
      subst h1
      rfl
    · exact absurd (toLex.injective (Subtype.mk.inj h12')) Sum.inl_ne_inr
    · exact absurd (toLex.injective (Subtype.mk.inj h12')) Sum.inr_ne_inl
    · cases u₁; cases u₂; rfl
  · intro i
    obtain ⟨i, hi⟩ := i
    rcases i with a | u
    · exact hc (θ ⟨Sum.inl a, hi⟩)
    · exact hc (θ ⟨Sum.inr u, hi⟩)

variable {k : Type u} [Field k]

/-- `isSnc_append_empty_of_isSmoothDivisor` of `Hironaka.Scheme.Snc.RestrictHypersurface` on the
empty sub-family: a smooth divisor alone has simple normal crossings along every set. -/
theorem isSncOn_subfamily_false_append (f : X ⟶ Spec (.of k)) [Smooth f] (E : DivisorFamily X)
    {H : X.IdealSheafData} (hH : IsSmoothDivisor H) (s : Set X) :
    ((E.subfamily fun _ => False).append H).IsSncOn s := by
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) :=
    fun x => isRegularLocalRing_stalk f x
  have h := (isSnc_append_empty_of_isSmoothDivisor hreg hH).isSncOn s
  have hf : Function.Injective (fun a : {a : E.ι // False} => (a.2.elim : PEmpty.{u + 1})) :=
    fun a _ _ => a.2.elim
  refine isSncOn_of_injective_components
    (toLex ∘ Sum.map (fun a : {a : E.ι // False} => (a.2.elim : PEmpty.{u + 1})) id ∘ ofLex)
    (toLex.injective.comp ((hf.sumMap Function.injective_id).comp ofLex.injective)) ?_ h
  intro i
  rcases i with a | u
  · exact a.2.elim
  · rfl

end Hironaka.Snc
