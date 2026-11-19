/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.Basic
public import Hironaka.Scheme.Snc.SmoothDivisor
import Hironaka.Algebra.Local.PolynomialOrder
import Hironaka.Scheme.BlowUp.ExceptionalSetSmooth
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Remark33Exceptional
import Hironaka.Scheme.IdealSheaf.Derivative.Pullback
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.IdealSheaf.Order.Invariance
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Maximal contact under restriction to open subschemes

Kollár's proof of [Kol07, Theorem 80 (1)] opens with the remark that being a hypersurface of
maximal contact is a local question, so that one may assume `L = 𝒪_X`, and [Kol07, Definition 78]
quantifies over every open `X⁰ ⊆ X` with the restricted data `(X⁰, I|_{X⁰})` and `H⁰ = H ∩ X⁰`.
This file supplies the two restriction facts those steps use.

* **The maximal contact ideal restricts** ([Kol07, Lemma 74 (4)]): for a smooth `g : Y ⟶ X`, in
  particular an open immersion, `MC(g^* I) = g^*(MC(I))`, because derivatives commute with smooth
  pull-back (`derivativeIter_comap_of_smooth`); hence the static form `𝒪_X(−H) ⊆ MC(I)` restricts
  to `g^*`: `𝒪_Y(−g^*H) ⊆ MC(g^* I)` (`IsMaximalContact.comap`).
* **A smooth hypersurface restricts to a smooth hypersurface of an open subscheme** (Kollár's
  tacit `H⁰ := H ∩ X⁰`): the closed subscheme of `g^* H` is an open subscheme of that of `H`
  (`isOpenImmersion_subschemeMap_of_comap`), so its stalks are regular; and the stalk of `g^* H`
  at `y` is the image of the stalk of `H` at `g y` under the isomorphism of stalks of an open
  immersion, whose generator still has order one, since the order of an ideal sheaf is invariant
  under open immersions (`ord_comap_of_isOpenImmersion`) and an element of a regular local ring
  has order one exactly when it lies in `𝔪 ∖ 𝔪²` (`ordElem_eq_one_iff`).
* **The static form is local**: `𝒪_X(−H) ⊆ MC(I)` holds iff it holds on the members of an open
  cover; (⇒) by restriction, (⇐) because an inclusion of ideal sheaves descends along a jointly
  surjective family of open immersions (`le_of_comap_le_of_forall_exists`), `MC` commuting with
  the restrictions. This is the precise content of the reduction to `L = 𝒪_X`: a section
  `h ∈ H⁰(X, L ⊗ MC(I))` with zero divisor `H` is the inclusion `𝒪_X(−H) ⊆ MC(I)` on every open
  trivializing `L`, and the inclusion glues.

These facts are used throughout `Hironaka/Resolution/Algebraic/MaximalContact/` (the local
existence, the transform of a hypersurface through the centre, going down) and in
`Hironaka/Resolution/Algebraic/Snc/SmoothDivisorLocal.lean`. -/

public section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k))
variable [CharZero k] (n : ℕ) [SmoothOfRelativeDimension n f]

omit [CharZero k] in
include n in
/-- [Kol07, Lemma 74 (4)] iterated: the maximal contact ideal commutes with smooth pull-back, in
particular with restriction to an open subscheme. -/
theorem MC_comap_of_smooth (g : Y ⟶ X) [Smooth g] (I : X.IdealSheafData) (m : ℕ) :
    MC (g ≫ f) (I.comap g) m = (MC f I m).comap g := by
  have : Smooth f := SmoothOfRelativeDimension.smooth n f
  exact derivativeIter_comap_of_smooth f g (m - 1) I

omit [CharZero k] in
include n in
/-- The static form `𝒪_X(−H) ⊆ MC(I)` restricts along every smooth `g`, in particular to every open
subscheme, as the restricted data of [Kol07, Definition 78] require. -/
theorem IsMaximalContact.comap {I H : X.IdealSheafData} {m : ℕ} (h : IsMaximalContact f I m H)
    (g : Y ⟶ X) [Smooth g] : IsMaximalContact (g ≫ f) (I.comap g) m (H.comap g) := by
  unfold IsMaximalContact at h ⊢
  rw [MC_comap_of_smooth f n g I m]
  exact comap_mono g h

omit [CharZero k] in
include n in
/-- The reduction "we may assume that `L = 𝒪_X`" opening the proof of [Kol07, Theorem 80]: the
static form is local, `𝒪_X(−H) ⊆ MC(I)` iff it holds on every member of an open cover. (⇒) is
`IsMaximalContact.comap`; (⇐) descends the inclusion along the covering open immersions
(`le_of_comap_le_of_forall_exists`), `MC` commuting with them. -/
theorem isMaximalContact_iff_forall_opens (I : X.IdealSheafData) (m : ℕ) (H : X.IdealSheafData)
    {ι : Type*} (U : ι → X.Opens) (hU : iSup U = ⊤) :
    IsMaximalContact f I m H ↔
      ∀ α, IsMaximalContact ((U α).ι ≫ f) (I.comap (U α).ι) m (H.comap (U α).ι) := by
  refine ⟨fun h α => h.comap f n (U α).ι, fun h => ?_⟩
  refine Remark33.le_of_comap_le_of_forall_exists (fun α => (U α).ι) ?_
    fun α => ?_
  · intro x
    have hx : x ∈ iSup U := by
      rw [hU]
      exact TopologicalSpace.Opens.mem_top _
    obtain ⟨α, hα⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨α, ⟨x, hα⟩, rfl⟩
  · have := h α
    unfold IsMaximalContact at this
    rwa [MC_comap_of_smooth f n (U α).ι I m] at this

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Kollár's `H⁰ := H ∩ X⁰` in [Kol07, Definition 78]: a smooth hypersurface restricts to a smooth
hypersurface of every open subscheme. The closed subscheme of the
restriction is an open subscheme of `V(H)`, hence regular; the stalk at `y` is the isomorphic image
of the stalk at `g y`, and its generator has order one because the order is invariant under open
immersions. -/
theorem IsSmoothDivisor.comap_of_isOpenImmersion {H : X.IdealSheafData} (hH : IsSmoothDivisor H)
    (g : Y ⟶ X) [IsOpenImmersion g] : IsSmoothDivisor (H.comap g) := by
  have hle : H ≤ (H.comap g).map g := Scheme.IdealSheafData.le_map_comap H g
  have hφ : IsOpenImmersion (Scheme.IdealSheafData.subschemeMap (H.comap g) H g hle) :=
    Scheme.IdealSheafData.isOpenImmersion_subschemeMap_of_comap g H (H.comap g) rfl hle
  refine ⟨⟨fun y => ?_⟩, fun y hy => ?_⟩
  · set φ := Scheme.IdealSheafData.subschemeMap (H.comap g) H g hle
    have : IsRegularLocalRing (H.subscheme.presheaf.stalk (φ y)) := hH.1.isRegularAt (φ y)
    exact IsRegularLocalRing.of_ringEquiv (asIso (φ.stalkMap y)).commRingCatIsoToRingEquiv
  · have hgy : g y ∈ H.support := (mem_support_comap_iff_apply H g y).mp hy
    obtain ⟨a, ha, ha2, hspan⟩ := hH.2 (g y) hgy
    have hspan' : (H.comap g).stalkIdeal y = Ideal.span {(g.stalkMap y).hom a} := by
      rw [Scheme.IdealSheafData.stalkIdeal_comap, hspan, Ideal.map_span, Set.image_singleton]
    have hord : ordElem ((g.stalkMap y).hom a) = 1 := by
      have h1 : (H.comap g).ord y = 1 := by
        rw [Scheme.IdealSheafData.ord_comap_of_isOpenImmersion,
          Scheme.IdealSheafData.ord_eq_ord_stalkIdeal, hspan, ord_span_singleton]
        exact ordElem_eq_one_iff.mpr ⟨ha, ha2⟩
      rwa [Scheme.IdealSheafData.ord_eq_ord_stalkIdeal, hspan', ord_span_singleton] at h1
    obtain ⟨hb, hb2⟩ := ordElem_eq_one_iff.mp hord
    exact ⟨_, hb, hb2, hspan'⟩

end AlgebraicGeometry
