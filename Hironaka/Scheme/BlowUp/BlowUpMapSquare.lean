/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Consequences of a cartesian square of schemes

The stages of a blow-up sequence pulled back along a morphism `h : Y → X` are the fibre products
`Xᵢ ×_X Y` [Kol07, Definition 30, 30.1], and for flat `h` the base-change square of the induced
morphism of blow-ups is cartesian [Sta, Tag 0805]; this is used to transfer properties of `h` to
its lifts (étale, smooth, flat, image `= π⁻¹(im h)`).  The two transfers are pure pullback
bookkeeping and are stated here for an arbitrary cartesian square of schemes
`IsPullback fst snd f g` (`fst ≫ f = snd ≫ g`):

* `range_fst_of_isPullback`: the image of `fst` is `f⁻¹(im g)` — Mathlib's
  `Scheme.Pullback.range_fst` for the chosen pullback, transported along the comparison
  isomorphism;
* `property_of_isPullback`: a property stable under base change passes from `g` to `fst`
  (Mathlib's `MorphismProperty.IsStableUnderBaseChange`).

They are applied to the square `IsPullback (blowUpMap h D) π_Y π_X h` of `isPullback_blowUpMap`
and to the base change of blow-up sequences.
-/

public section

namespace AlgebraicGeometry

open AlgebraicGeometry CategoryTheory Limits

universe u

variable {P X Y Z : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- In a cartesian square of schemes the image of `fst` is the preimage under `f` of the image of
`g` (Mathlib's `Scheme.Pullback.range_fst`). -/
theorem range_fst_of_isPullback (H : IsPullback fst snd f g) :
    Set.range fst = f ⁻¹' Set.range g := by
  have hsurj : Function.Surjective H.isoPullback.hom := by
    intro y
    obtain ⟨p, hp⟩ := (Scheme.homeoOfIso H.isoPullback).surjective y
    exact ⟨p, by rw [← Scheme.homeoOfIso_apply]; exact hp⟩
  have hcomp : ⇑(H.isoPullback.hom ≫ Limits.pullback.fst f g) =
      ⇑(Limits.pullback.fst f g) ∘ ⇑H.isoPullback.hom :=
    funext fun p => Scheme.Hom.comp_apply _ _ p
  rw [← H.isoPullback_hom_fst, hcomp, Set.range_comp, Set.range_eq_univ.mpr hsurj,
    Set.image_univ, Scheme.Pullback.range_fst]

/-- A property of morphisms stable under base change passes from `g` to `fst` in a cartesian
square (Mathlib's `MorphismProperty.IsStableUnderBaseChange`). -/
theorem property_of_isPullback (Q : MorphismProperty Scheme.{u}) [Q.IsStableUnderBaseChange]
    (H : IsPullback fst snd f g) (hg : Q g) : Q fst :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback H.flip hg

end AlgebraicGeometry
