/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.RefineFamily
import Hironaka.Resolution.Algebraic.Kol07.CosuppTransport
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Semicontinuity
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Hironaka.Scheme.IdealSheaf.StalkLe
import Hironaka.Scheme.Snc.DictionaryOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Subdivisions along a set, and the order condition along the cosupport

`Subdivides F G` (`Hironaka/Resolution/Algebraic/Kol07/RefineFamily.lean`), the relation "at every
point the members of `F` through the point are assigned injectively to members of `G` with the same
stalks", transports the order condition of [Kol07, Definition 66] from `G` to `F`
(`isOrderSeq_of_subdivides`), because simple normal crossings with a center
[Kol07, Definition 24 (4)] only see the members through a point and their stalks. The restriction
to the hypersurface of maximal contact in the proof of Theorem 103 [Kol07, 104, Step 2.2] needs
the same transport when the assignment exists only along a set `s` containing every center:
`SubdividesOn F G s`. Every center of a smooth blow-up sequence of order `m` lies in
`cosupp(I, m)` (condition (4) of Definition 66, `le_ord_of_mem_center`), and the cosupport of the
weak transform maps into the cosupport (`le_ord_of_le_ord_weakTransform`), so an assignment along
`cosupp(I, m)` transports stage by stage exactly as a global one does
(`subdividesOn_totalTransformAlong`), and a smooth blow-up sequence of order `m` for `(I, G)` is
one for `(I, F)` (`isOrderSeq_of_subdividesOn_cosupp`).

This is the lemma by which the sequence of Step 2.2, a sequence of order `m` for
`(I_r, F_r + H_r)` with `F_r` the exceptional sub-family, is one for the original `(I_r, E_r)`:
the transforms of the original members of `E` are disjoint from the cosupport, so along the
cosupport every member of `E_r` is a member of `F_r`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme BlowUpSequence
  Scheme.IdealSheafData IdealSheafData

namespace AlgebraicGeometry.Scheme.DivisorFamily

variable {X : Scheme.{u}}

/-- `F` subdivides `G` along `s` (`Subdivides` restricted to a set): at every point of `s`, the
members of `F` through the point are assigned injectively to members of `G` with the same
stalks. -/
def SubdividesOn (F G : DivisorFamily X) (s : Set X) : Prop :=
  ∀ x ∈ s, ∃ q : F.ι → Option G.ι,
    (∀ j j', x ∈ (F.component j).support → x ∈ (F.component j').support → q j = q j' → j = j') ∧
    ∀ j, x ∈ (F.component j).support →
      ∃ i, q j = some i ∧ (F.component j).stalkIdeal x = (G.component i).stalkIdeal x

/-- A subdivision along `t` is one along every `s ⊆ t`. -/
theorem SubdividesOn.mono {F G : DivisorFamily X} {s t : Set X} (h : F.SubdividesOn G t)
    (hst : s ⊆ t) : F.SubdividesOn G s :=
  fun x hx => h x (hst hx)

/-- A subdivision everywhere is one along every set. -/
theorem Subdivides.subdividesOn {F G : DivisorFamily X} (h : F.Subdivides G) (s : Set X) :
    F.SubdividesOn G s :=
  fun x _ => h x

end AlgebraicGeometry.Scheme.DivisorFamily

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Simple normal crossings with `Z` pass from `G` to `F` when `F` subdivides `G` along a set
containing `V(Z)` (`hasSncWith_of_subdivides` along a set). -/
theorem hasSncWith_of_subdividesOn {F G : DivisorFamily X} {s : Set X} (h : F.SubdividesOn G s)
    {Z : X.IdealSheafData} (hZs : ∀ x ∈ Z.support, x ∈ s) (hZ : G.HasSncWith Z) :
    F.HasSncWith Z := by
  intro x hx
  obtain ⟨n, z, ⟨hz, c, hc, hcz⟩, s', hs'⟩ := hZ x hx
  obtain ⟨q, hq, hs⟩ := h x (hZs x hx)
  choose i hi hsi using hs
  have hmem : ∀ j : {j : F.ι // x ∈ (F.component j).support},
      x ∈ (G.component (i j.1 j.2)).support :=
    fun j => mem_support_of_stalkIdeal_eq j.2 (hsi j.1 j.2)
  let c' : {j : F.ι // x ∈ (F.component j).support} → Fin n := fun j => c ⟨i j.1 j.2, hmem j⟩
  have hc' : Function.Injective c' := by
    intro j j' heq
    have h2 : i j.1 j.2 = i j'.1 j'.2 := congrArg Subtype.val (hc heq)
    have h3 : q j.1 = q j'.1 := by rw [hi j.1 j.2, hi j'.1 j'.2, h2]
    exact Subtype.ext (hq j.1 j'.1 j.2 j'.2 h3)
  refine ⟨n, z, ⟨hz, c', hc', fun j => ?_⟩, s', hs'⟩
  exact (hsi j.1 j.2).trans (hcz ⟨i j.1 j.2, hmem j⟩)

/-- A subdivision along `s` is preserved by the total transform along `π` with an invertible
distinguished divisor, along the preimage of `s` (`subdivides_totalTransformAlong` along a
set). -/
theorem subdividesOn_totalTransformAlong {F G : DivisorFamily X} {s : Set X}
    (h : F.SubdividesOn G s) {B : Scheme.{u}} (π : B ⟶ X) {K : B.IdealSheafData}
    (hK : K.IsInvertible) :
    (F.totalTransformAlong π K).SubdividesOn (G.totalTransformAlong π K) (π ⁻¹' s) := by
  intro y hy
  obtain ⟨q, hq, hs⟩ := h (π y) hy
  have hmem : ∀ j : F.ι, y ∈ ((F.component j).strictTransformAlong π K).support →
      π y ∈ (F.component j).support := by
    intro j hj
    by_contra hn
    refine notMem_support_of_stalkIdeal_eq_top ?_ hj
    rw [strictTransformAlong, stalkIdeal_saturate_of_isInvertible _ hK, stalkIdeal_comap,
      stalkIdeal_eq_top_of_notMem_support _ hn, Ideal.map_top]
    simp only [Submodule.top_colon, iSup_const]
  have hstalk : ∀ (j : F.ι) (i : G.ι),
      (F.component j).stalkIdeal (π y) = (G.component i).stalkIdeal (π y) →
      ((F.component j).strictTransformAlong π K).stalkIdeal y =
        ((G.component i).strictTransformAlong π K).stalkIdeal y := by
    intro j i hji
    rw [strictTransformAlong, strictTransformAlong, stalkIdeal_saturate_of_isInvertible _ hK,
      stalkIdeal_saturate_of_isInvertible _ hK, stalkIdeal_comap, stalkIdeal_comap, hji]
  refine ⟨fun j' => Sum.elim (fun j => (q j).map fun i => toLex (Sum.inl i))
    (fun _ => some (toLex (Sum.inr PUnit.unit))) (ofLex j'), ?_, ?_⟩
  · rintro (j | u) (j' | u') hj hj' heq
    · change y ∈ ((F.component j).strictTransformAlong π K).support at hj
      change y ∈ ((F.component j').strictTransformAlong π K).support at hj'
      change (q j).map _ = (q j').map _ at heq
      obtain ⟨i, hi, -⟩ := hs j (hmem j hj)
      obtain ⟨i', hi', -⟩ := hs j' (hmem j' hj')
      rw [hi, hi'] at heq
      have hii : i = i' := Sum.inl.inj (Option.some_injective _ heq)
      have hjj : j = j' := hq j j' (hmem j hj) (hmem j' hj') (hi.trans (by rw [hii, hi']))
      exact congrArg (fun j => (toLex (Sum.inl j) : (F.totalTransformAlong π K).ι)) hjj
    · change y ∈ ((F.component j).strictTransformAlong π K).support at hj
      change (q j).map _ = some _ at heq
      obtain ⟨i, hi, -⟩ := hs j (hmem j hj)
      rw [hi] at heq
      exact absurd (Option.some_injective _ heq) Sum.inl_ne_inr
    · change y ∈ ((F.component j').strictTransformAlong π K).support at hj'
      change some _ = (q j').map _ at heq
      obtain ⟨i', hi', -⟩ := hs j' (hmem j' hj')
      rw [hi'] at heq
      exact absurd (Option.some_injective _ heq) Sum.inr_ne_inl
    · exact congrArg (fun u => (toLex (Sum.inr u) : (F.totalTransformAlong π K).ι))
        (Subsingleton.elim u u')
  · rintro (j | u) hj
    · change y ∈ ((F.component j).strictTransformAlong π K).support at hj
      obtain ⟨i, hi, hsi⟩ := hs j (hmem j hj)
      refine ⟨toLex (Sum.inl i), ?_, hstalk j i hsi⟩
      change (q j).map _ = some _
      rw [hi]
      rfl
    · exact ⟨toLex (Sum.inr PUnit.unit), rfl, rfl⟩

/-- A subdivision along `s` is preserved by the total transform under a blow-up, along the
preimage of `s` (`subdivides_totalTransform` along a set). -/
theorem subdividesOn_totalTransform {F G : DivisorFamily X} {s : Set X} (h : F.SubdividesOn G s)
    (D : X.IdealSheafData) :
    (F.totalTransform D).SubdividesOn (G.totalTransform D) (D.blowUpπ ⁻¹' s) :=
  subdividesOn_totalTransformAlong h D.blowUpπ (blowUp.isInvertible_comap_π D)

variable {k : Type u} [Field k] [CharZero k]

/-- A smooth blow-up sequence of order `m` for `(J, G)` is one for `(J, F)` when `F` subdivides
`G` along `cosupp(J, m)` ([Kol07, Definition 66]; used in [Kol07, 104, Step 2.2]): every center
lies in the cosupport (condition (4) of Definition 66) and the cosupport of the weak transform
maps into the cosupport, so the subdivision transports stage by stage
(`isOrderSeq_of_subdivides` along the cosupport). -/
theorem isOrderSeq_of_subdividesOn_cosupp (n : ℕ) : ∀ {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [SmoothOfRelativeDimension n f] (S : BlowUpSequence X)
    {J : X.IdealSheafData} {G F : DivisorFamily X} {m : ℕ},
    F.SubdividesOn G {x | (m : ℕ∞) ≤ J.ord x} → S.IsOrderSeq f J G m → S.IsOrderSeq f J F m
  | _, _, _, nil _, _, _, _, _, _, hS => ⟨hS.1, fun i => i.elim0⟩
  | X, f, _, cons _ D₀ rest, J, G, F, m, hFG, hS => by
    obtain ⟨hhead, ht⟩ := (isOrderSeq_cons_iff f J G m D₀ rest).1 hS
    have hsm : Smooth (D₀.subschemeι ≫ f) := hhead.1
    have : SmoothOfRelativeDimension n (D₀.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D₀
    have hf : Smooth f := SmoothOfRelativeDimension.smooth n f
    have : IsLocallyNoetherian X := f.isLocallyNoetherian_of_field
    have hZc : ∀ x ∈ D₀.support, (m : ℕ∞) ≤ J.ord x := fun x hx =>
      IsOrderSeq.le_ord_of_mem_center f n hS ⟨0, Nat.succ_pos _⟩ hx
    refine (isOrderSeq_cons_iff f J F m D₀ rest).2
      ⟨⟨hhead.1, hasSncWith_of_subdividesOn hFG hZc hhead.2.1, hhead.2.2⟩, ?_⟩
    refine isOrderSeq_of_subdividesOn_cosupp n (D₀.blowUpπ ≫ f) rest ?_ ht
    exact (subdividesOn_totalTransform hFG D₀).mono fun x' hx' =>
      le_ord_of_le_ord_weakTransform D₀ J hZc x' hx'

end Hironaka.Sequence
