/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Order.OrderIsoNat
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.ENat.Lattice
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Upper semicontinuous resolution invariants: maxima, maximum loci, termination

Sources: Bierstone--Milman 2008 §7 (the invariant whose maximum locus is the next centre), Encinas--Hauser 2002
("Resolution of mobiles": an invariant with values in a well-ordered set that drops under the blowup of its top
locus gives termination).

A resolution invariant is upper semicontinuous in the sense used by the algorithm: every point has a
neighbourhood on which the invariant is at most its value at the point (`IsInvUSCOn`).  No topology on the set of
values is needed.

## Main results

* `IsInvUSCOn.exists_isMaxOn`: on a nonempty compact set such an invariant attains its maximum (finitely many
  neighbourhoods cover);
* `IsInvUSCOn.mono`: restriction to a subset and pullback along a continuous map (restriction to open sets and
  transport along biholomorphisms in the algorithm);
-/

open Set Filter
open scoped Topology

namespace Hironaka.ResolutionInvariantOrder

section USC

variable {X Y Λ : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Upper semicontinuity of a resolution invariant** on `s`: every point of `s` has a neighbourhood whose points in
`s` have values at most the value at the point. -/
def IsInvUSCOn [Preorder Λ] (f : X → Λ) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ᶠ y in 𝓝 x, y ∈ s → f y ≤ f x

variable {f : X → Λ} {s t : Set X}

/-- Restriction to a subset. -/
theorem IsInvUSCOn.mono [Preorder Λ] (hf : IsInvUSCOn f s) (hts : t ⊆ s) : IsInvUSCOn f t :=
  fun x hx => (hf x (hts hx)).mono fun _ hy hyt => hy (hts hyt)

/-- **The maximum exists on a nonempty compact set.** -/
theorem IsInvUSCOn.exists_isMaxOn [LinearOrder Λ] (hf : IsInvUSCOn f s) (hs : IsCompact s)
    (hne : s.Nonempty) : ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x := by
  classical
  obtain ⟨t, hcover⟩ := hs.elim_nhds_subcover' (fun x _ => {y | y ∈ s → f y ≤ f x})
    (fun x hx => hf x hx)
  have htne : t.Nonempty := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.mp (hcover hy)
    exact ⟨i, hi⟩
  obtain ⟨x₀, hx₀t, hmax⟩ := t.exists_max_image (fun x => f x) htne
  refine ⟨x₀, x₀.2, fun y hy => ?_⟩
  obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp (hcover hy)
  exact (hyi hy).trans (hmax i hi)

end USC

end Hironaka.ResolutionInvariantOrder
