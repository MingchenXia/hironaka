/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Defs
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The universal property of the blow-up as a predicate

A morphism `π : B ⟶ X` is *a blow-up of `X` along the ideal sheaf `I`* [Hau14, Definition 4.4] if
(i) the inverse image `I·𝒪_B = I.comap π` of the centre is an effective Cartier divisor — `π` is
*admissible* for `I` — and (ii) `π` is universal for this property: every admissible `f : Y ⟶ X`
(every `f` with `I.comap f` invertible) factors through `π` by a unique `g : Y ⟶ B`.  Equivalently,
the blow-up is a final object of the category of `X`-schemes on which the inverse image of the
centre is an effective Cartier divisor [Sta, Tag 0806].

`IsBlowUp I π` records exactly these two clauses.  Every theorem of the blow-up calculus that the
sources derive "from the universal property" — the trivial blow-up, flat base change, the product
formula and the composite of blow-ups — is proved once for an arbitrary `π` with `IsBlowUp I π`
(`HironakaExamples.BlowUp.TrivialBlowUp`, `Hironaka.Scheme.BlowUp.FlatBaseChange`,
`Hironaka.Scheme.BlowUp.ProductCenter`) and instantiated at the blow-up through `blowUp.isBlowUp`
(`Hironaka.Scheme.BlowUp.Glue.Global`).  The predicate is `Prop`-valued (no data).
-/

@[expose] public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory

universe u

/-- `π : B ⟶ X` is a blow-up of `X` along `I` [Hau14, Definition 4.4]; [Sta, Tag 0806] if `π` is
admissible for `I` (the inverse image ideal `I.comap π` is invertible) and every admissible
`f : Y ⟶ X` factors uniquely through `π`. -/
structure IsBlowUp {X B : Scheme.{u}} (I : X.IdealSheafData) (π : B ⟶ X) : Prop where
  /-- Clause (i): the inverse image of the centre is an effective Cartier divisor. -/
  admissible : (I.comap π).IsInvertible
  /-- Clause (ii): unique factorization of every admissible morphism. -/
  existsUnique_lift : ∀ {Y : Scheme.{u}} (f : Y ⟶ X), (I.comap f).IsInvertible →
    ∃! g : Y ⟶ B, g ≫ π = f

namespace IsBlowUp

variable {X B : Scheme.{u}} {I : X.IdealSheafData} {π : B ⟶ X}

/-- Existence half of the universal property. -/
theorem exists_lift (h : IsBlowUp I π) {Y : Scheme.{u}} (f : Y ⟶ X)
    (hf : (I.comap f).IsInvertible) : ∃ g : Y ⟶ B, g ≫ π = f :=
  (h.existsUnique_lift f hf).exists

/-- Uniqueness half of the universal property: two lifts of an admissible morphism coincide. -/
theorem hom_ext (h : IsBlowUp I π) {Y : Scheme.{u}} (f : Y ⟶ X) (hf : (I.comap f).IsInvertible)
    (g g' : Y ⟶ B) (e : g ≫ π = f) (e' : g' ≫ π = f) : g = g' := by
  obtain ⟨g₀, -, huniq⟩ := h.existsUnique_lift f hf
  exact (huniq g e).trans (huniq g' e').symm

/-- Admissibility of `π` composed with any morphism into `X` for which `I` pulls back to an
invertible ideal sheaf on the blow-up: `I.comap (π ≫ g) = (I.comap g).comap π`. -/
theorem comap_comp_isInvertible_iff {Z : Scheme.{u}} (g : X ⟶ Z) (J : Z.IdealSheafData) :
    (J.comap (π ≫ g)).IsInvertible ↔ ((J.comap g).comap π).IsInvertible := by
  rw [Scheme.IdealSheafData.comap_comp]

end IsBlowUp

end AlgebraicGeometry
