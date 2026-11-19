/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.Defs
/-!
# Simple normal crossings along a set; sub-families

Step 2.1 of [Kol07, 104] ends with the divisor `H_{r(s)} + E_{r(s)}` having "simple normal crossing
along `cosupp(I_{r(s)}, m)`": the pointwise condition of [Kol07, Definition 24] (`IsSncAt`) at every
point of a set, not on the whole scheme — the transforms of the original components of `E` may still
meet `H_{r(s)}` badly away from the cosupport. This module holds that predicate
(`DivisorFamily.IsSncOn`) and the sub-family of a family on a subset of its index set
(`DivisorFamily.subfamily`; `erase E j` of `Hironaka.Scheme.Snc.EraseFamily` is the case `p := (· ≠
j)`), which the induction of `Hironaka.Resolution.Algebraic.Kol07.SncGlobalSubfamily` uses for the
exceptional members of the boundary. The global `IsSnc` is the regularity of the members together
with `IsSncOn` on the whole scheme (`isSnc_iff_isSncOn_univ`).

Sources: [Kol07, Definition 24]; [Kol07, 104] (Step 2.1); [Kol07, Notation 64 (3)] (the ordered
index set).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.DivisorFamily

variable {X : Scheme.{u}}

/-- The family `E` has **simple normal crossings along the set `s`** — the local coordinates of
[Kol07, Definition 24] exist at every point of `s` (`IsSncAt`); Kollár's "has simple normal crossing
along `cosupp(I_{r(s)}, m)`", Step 2.1 of [Kol07, 104]. -/
def IsSncOn (E : DivisorFamily X) (s : Set X) : Prop :=
  ∀ x ∈ s, ∃ (n : ℕ) (z : Fin n → X.presheaf.stalk x), E.IsSncAt x z

/-- The **sub-family** of `E` on the indices satisfying `p`, with the induced order (the boundary is
an ordered set of divisors, [Kol07, Notation 64 (3)]). `erase E j` of
`Hironaka.Scheme.Snc.EraseFamily` is the case `p := (· ≠ j)`. -/
noncomputable def subfamily (E : DivisorFamily X) (p : E.ι → Prop) : DivisorFamily X where
  ι := {a : E.ι // p a}
  fintype := by classical exact Subtype.fintype p
  component := fun a => E.component a.1

/-- The members of a sub-family are the members of the family at the selected indices. -/
theorem subfamily_component (E : DivisorFamily X) (p : E.ι → Prop) (a : {a : E.ι // p a}) :
    (E.subfamily p).component a = E.component a.1 :=
  rfl

/-- A simple normal crossing family has simple normal crossings along every set. -/
theorem IsSnc.isSncOn {E : DivisorFamily X} (hE : E.IsSnc) (s : Set X) : E.IsSncOn s :=
  fun x _ => hE.2 x

/-- `IsSnc` is the regularity of the members together with `IsSncOn` on the whole scheme
([Kol07, Definition 24 (1)–(3)]): the new predicate is the old one relativised to a set. -/
theorem isSnc_iff_isSncOn_univ (E : DivisorFamily X) :
    E.IsSnc ↔ (∀ i, IsRegular (E.component i).subscheme) ∧ E.IsSncOn Set.univ :=
  ⟨fun h => ⟨h.1, fun x _ => h.2 x⟩, fun h => ⟨h.1, fun x => h.2 x trivial⟩⟩

end AlgebraicGeometry.Scheme.DivisorFamily
