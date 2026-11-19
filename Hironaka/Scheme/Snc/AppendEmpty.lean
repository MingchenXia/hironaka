/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.Basic
/-!
# Appending an empty member to a simple normal crossing family

The total transform of a divisor family appends the exceptional divisor as a last member
[Kol07, Definition 25], which under a trivial blow-up is EMPTY (the unit ideal); the restricted
marked triple of the boundary-clearing step carries such a member, and
clause (3) of [Kol07, Lemma 102] compares it with Kollár's `(E − E^j)|_{E^j}`, which has none. This
module holds the one fact that comparison needs: appending the unit ideal as a member keeps a family
snc (`isSnc_append_top`) — the new member passes through no point, so the coordinates of
[Kol07, Definition 24] at every point are unchanged, and the empty subscheme is regular vacuously.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.DivisorFamily

variable {X : Scheme.{u}}

/-- The unit ideal has empty support. -/
theorem support_top_eq_bot : (⊤ : X.IdealSheafData).support = ⊥ :=
  (Scheme.IdealSheafData.support_eq_bot_iff (I := (⊤ : X.IdealSheafData))).mpr rfl

/-- Appending the unit ideal — an empty member — to an snc family keeps it snc
[Kol07, Definition 24]: the empty subscheme is regular vacuously, and the new member passes through
no point, so the coordinates and the injection of Definition 24 at each point are those of the old
family. -/
theorem isSnc_append_top (E : DivisorFamily X) (hE : E.IsSnc) : (E.append ⊤).IsSnc := by
  classical
  refine ⟨fun i => ?_, fun x => ?_⟩
  · rcases i with i | u
    · exact hE.1 i
    · have hemp : IsEmpty (⊤ : X.IdealSheafData).subscheme := inferInstance
      exact ⟨fun p => hemp.elim p⟩
  · obtain ⟨n, z, hz⟩ := hE.2 x
    obtain ⟨hrsp, c, hcinj, hc⟩ := hz
    have hnot : ∀ u : PUnit.{u + 1},
        x ∉ ((E.append ⊤).component (toLex (Sum.inr u))).support := by
      intro u hu
      change x ∈ (⊤ : X.IdealSheafData).support at hu
      rw [support_top_eq_bot] at hu
      exact hu
    -- every member through `x` is an old member
    have key : ∀ i : {i : (E.append ⊤).ι // x ∈ ((E.append ⊤).component i).support},
        ∃ a : {a : E.ι // x ∈ (E.component a).support}, i.1 = toLex (Sum.inl a.1) := by
      rintro ⟨i, hi⟩
      rcases i with a | u
      · exact ⟨⟨a, hi⟩, rfl⟩
      · exact (hnot u hi).elim
    choose lift hlift using key
    refine ⟨n, z, hrsp, fun i => c (lift i), ?_, ?_⟩
    · intro i₁ i₂ h
      have h' := hcinj h
      apply Subtype.ext
      rw [hlift i₁, hlift i₂, h']
    · intro i
      have h1 := hc (lift i)
      have h2 : ((E.append ⊤).component i.1) = E.component (lift i).1 :=
        congrArg (E.append ⊤).component (hlift i)
      rw [h2]
      exact h1

end AlgebraicGeometry.Scheme.DivisorFamily
