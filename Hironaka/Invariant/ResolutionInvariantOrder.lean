import Mathlib.Data.DFinsupp.WellFounded
import Mathlib.Order.OrderIsoNat
import Mathlib.Topology.Compactness.Compact
import Mathlib.Data.ENat.Lattice

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Upper semicontinuous resolution invariants: maxima, maximum loci, termination

Blueprint `hir:invariant-order` (`blueprint/src/hironaka.tex`, Hironaka phase H4).  Sources: Bierstone--Milman 2008 §7 (the
invariant whose maximum locus is the next centre), Encinas--Hauser 2002 ("Resolution of mobiles": an invariant with
values in a well-ordered set that drops under the blowup of its top locus gives termination).

A resolution invariant is upper semicontinuous in the sense used by the algorithm: every point has a
neighbourhood on which the invariant is at most its value at the point (`IsInvUSCOn`).  No topology on the set of
values is needed.

## Main results

* `IsInvUSCOn.exists_isMaxOn`: on a nonempty compact set such an invariant attains its maximum (finitely many
  neighbourhoods cover);
* `IsInvUSCOn.isClosed_superlevel`, `IsInvUSCOn.isClosed_maxLocus`: superlevel sets and the maximum locus are closed when
  the domain is closed;
* `IsInvUSCOn.mono`, `IsInvUSCOn.comp`: restriction to a subset and pullback along a continuous map (restriction to
  open sets and transport along biholomorphisms in the algorithm);
* `maxLocus_inter_eq`: on a set `W` on which the invariant is `≤ λ`, the points of value `λ` are the trace on `W` of the
  superlevel set;
* termination: `exists_not_of_lt_succ` -- if, as long as a property `P i` holds (e.g. "the cosupport at stage `i` is
  nonempty"), the maxima `m i` strictly decrease in a well-founded order, then `P` fails at some stage;
  `wellFoundedLT_lex` -- lexicographically ordered tuples `Fin k → Λ` of a well-ordered `Λ` (e.g. `ℕ∞`) are well-founded.

Import discipline (Hironaka phase): mathlib only; in particular this module does not import
`Hironaka.RelativePrincipalization` or `Hironaka.EmbeddedResolution`.

Sorry-free.
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

/-- Pullback along a continuous map. -/
theorem IsInvUSCOn.comp [Preorder Λ] (hf : IsInvUSCOn f s) {φ : Y → X} (hφ : Continuous φ) :
    IsInvUSCOn (f ∘ φ) (φ ⁻¹' s) :=
  fun y hy => (hφ.tendsto y).eventually (hf (φ y) hy)

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

/-- **Superlevel sets are closed** (for a closed domain). -/
theorem IsInvUSCOn.isClosed_superlevel [LinearOrder Λ] (hf : IsInvUSCOn f s) (hs : IsClosed s) (l : Λ) :
    IsClosed {x | x ∈ s ∧ l ≤ f x} := by
  refine isOpen_compl_iff.mp (isOpen_iff_mem_nhds.mpr fun y hy => ?_)
  by_cases hys : y ∈ s
  · have hlt : f y < l := lt_of_not_ge fun h => hy ⟨hys, h⟩
    filter_upwards [hf y hys] with z hz hzmem
    exact absurd ((hz hzmem.1).trans_lt hlt) (not_lt.mpr hzmem.2)
  · filter_upwards [hs.isOpen_compl.mem_nhds hys] with z hz hzmem
    exact hz hzmem.1

/-- **The maximum locus is closed** (for a closed domain): the points of `s` whose value is the maximum. -/
theorem IsInvUSCOn.isClosed_maxLocus [LinearOrder Λ] (hf : IsInvUSCOn f s) (hs : IsClosed s) {x₀ : X}
    (hmax : ∀ y ∈ s, f y ≤ f x₀) : IsClosed {x | x ∈ s ∧ f x = f x₀} := by
  have : {x | x ∈ s ∧ f x = f x₀} = {x | x ∈ s ∧ f x₀ ≤ f x} := by
    ext x
    exact ⟨fun h => ⟨h.1, h.2.ge⟩, fun h => ⟨h.1, le_antisymm (hmax x h.1) h.2⟩⟩
  rw [this]
  exact hf.isClosed_superlevel hs _

/-- On a set `W` on which the invariant is at most `l`, the points of value `l` are the trace on `W` of the superlevel
set `{l ≤ f}` (this is how a maximum locus restricts to an open set). -/
theorem maxLocus_inter_eq [PartialOrder Λ] {W : Set X} {l : Λ} (hW : ∀ x ∈ W ∩ s, f x ≤ l) :
    {x | x ∈ W ∩ s ∧ f x = l} = W ∩ {x | x ∈ s ∧ l ≤ f x} := by
  ext x
  constructor
  · rintro ⟨⟨hxW, hxs⟩, hx⟩
    exact ⟨hxW, hxs, hx.ge⟩
  · rintro ⟨hxW, hxs, hx⟩
    exact ⟨⟨hxW, hxs⟩, le_antisymm (hW x ⟨hxW, hxs⟩) hx⟩

end USC

section Termination

variable {Λ : Type*}

/-- **Termination by a well-founded invariant**: if, as long as `P i` holds, the values `m i` strictly decrease
(`m (i + 1) < m i` whenever `P i` and `P (i + 1)`), then `P` fails at some stage. -/
theorem exists_not_of_lt_succ [Preorder Λ] [WellFoundedLT Λ] (P : ℕ → Prop) (m : ℕ → Λ)
    (hdec : ∀ i, P i → P (i + 1) → m (i + 1) < m i) : ∃ i, ¬ P i := by
  by_contra! hall
  exact not_strictAnti_of_wellFoundedLT m (strictAnti_nat_of_succ_lt fun i => hdec i (hall i) (hall (i + 1)))

/-- **Lexicographic tuples of a well-ordered set are well-founded** (e.g. invariant values in `Lex (Fin k → ℕ∞)`). -/
theorem wellFoundedLT_lex (k : ℕ) [LinearOrder Λ] [WellFoundedLT Λ] : WellFoundedLT (Lex (Fin k → Λ)) :=
  inferInstance

/-- The invariant values of Encinas--Hauser type: lexicographic tuples of `ℕ∞` are well-founded. -/
example (k : ℕ) : WellFoundedLT (Lex (Fin k → ℕ∞)) := wellFoundedLT_lex k

end Termination

end Hironaka.ResolutionInvariantOrder
