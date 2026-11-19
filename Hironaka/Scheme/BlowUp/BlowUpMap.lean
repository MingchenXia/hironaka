/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.BlowUpMap.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Hironaka.Scheme.BlowUp.FlatBaseChange
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The morphism of blow-ups induced by a morphism of the base

The universal property of the blow-up [Sta, Tag 0806] lifts every admissible `f : Y ⟶ X` (one along
which `I` becomes invertible) to `blowUp.lift I f hf : Y ⟶ blowUp I`, the only morphism over `f`
(`blowUp.lift_π`, `blowUp.eq_lift`). For a morphism `h : Y ⟶ X` and an ideal sheaf `D` on `X`, the
composite `π_Y ≫ h : B_{D·𝒪_Y} Y ⟶ X` of the blow-up of `Y` along the inverse image ideal
`D.comap h` with `h` is admissible for `D`: its inverse image of `D` is `(D.comap h).comap π_Y`, the
exceptional ideal of `B_{D·𝒪_Y} Y`, which is invertible. Its lift is the morphism of blow-ups

  `blowUpMap h D : blowUp (D.comap h) ⟶ blowUp D` with `blowUpMap h D ≫ π_X = π_Y ≫ h`

(`blowUpMap_π`), the morphism `h^*π` of the pull-back of a blow-up sequence along `h`
[Kol07, Definition 30, 30.1] and the top arrow of the cartesian diagram of blow-ups under flat base
change [Sta, Tag 0805]: for flat `h` the square is cartesian (`isPullback_blowUpMap`).

The flat square uses that the blow-up satisfies the universal property in the form of the
predicate `IsBlowUp` (`blowUp.isBlowUp`, `Hironaka.Scheme.BlowUp.Glue.Global`), through which the
theorems of the blow-up calculus proved for an abstract `IsBlowUp`
(`Hironaka.Scheme.BlowUp.FlatBaseChange`, `Hironaka.Scheme.BlowUp.ProductCenter`,
`Hironaka.Scheme.BlowUp.Transform.StrictTransform`) instantiate at the blow-up.
-/

public section

namespace AlgebraicGeometry

open Scheme.IdealSheafData Scheme.Hom

open AlgebraicGeometry CategoryTheory Scheme.IdealSheafData

universe u

section Lift

variable {X : Scheme.{u}} (I : X.IdealSheafData) {Y : Scheme.{u}} (f : Y ⟶ X)

@[reassoc (attr := simp)]
theorem Scheme.IdealSheafData.blowUp.lift_π (hf : (I.comap f).IsInvertible) :
    blowUp.lift I f hf ≫ blowUpπ I = f :=
  (blowUp.exists_lift I f hf).choose_spec

theorem Scheme.IdealSheafData.blowUp.eq_lift (hf : (I.comap f).IsInvertible) (g : Y ⟶ blowUp I)
    (hg : g ≫ blowUpπ I = f) : g = blowUp.lift I f hf :=
  blowUp.hom_ext I f hf g _ hg (blowUp.lift_π I f hf)

end Lift

variable {X Y : Scheme.{u}} (h : Y ⟶ X) (D : X.IdealSheafData)

/-- The defining equation: `blowUpMap h D` lies over `h`. -/
@[reassoc (attr := simp)]
theorem blowUpMap_π : blowUpMap h D ≫ blowUpπ D = blowUpπ (D.comap h) ≫ h :=
  blowUp.lift_π D _ _

/-- Transport of the projection along an equality of centres. -/
@[reassoc]
theorem eqToHom_comp_blowUpπ {I J : X.IdealSheafData} (e : I = J) :
    eqToHom (congrArg blowUp e) ≫ blowUpπ J = blowUpπ I := by
  subst e
  rw [eqToHom_refl, Category.id_comp]

/-- Points of a blow-up transport along an equality of centres `e : I = J`: every point of
`blowUp J` is the image of a point of `blowUp I` under the `eqToHom` of `eqToHom_comp_blowUpπ`. -/
theorem exists_eqToHom_apply_eq {I J : X.IdealSheafData} (e : I = J) (t : blowUp J) :
    ∃ s, eqToHom (congrArg blowUp e) s = t := by
  subst e
  exact ⟨t, by simp⟩

/-- `blowUpMap h D` is the only morphism over `h`. -/
theorem eq_blowUpMap (g : blowUp (D.comap h) ⟶ blowUp D)
    (hg : g ≫ blowUpπ D = blowUpπ (D.comap h) ≫ h) : g = blowUpMap h D :=
  blowUp.eq_lift D _ _ g hg

/-- For flat `h` the square of `blowUpMap h D` over `h` is cartesian,
`B_{D·𝒪_Y} Y = Y ×_X B_D X` [Sta, Tag 0805] (from `IsBlowUp.exists_isPullback_of_flat`). -/
theorem isPullback_blowUpMap [Flat h] :
    IsPullback (blowUpMap h D) (blowUpπ (D.comap h)) (blowUpπ D) h := by
  obtain ⟨φ, H⟩ := (blowUp.isBlowUp D).exists_isPullback_of_flat h (blowUp.isBlowUp (D.comap h))
  rw [eq_blowUpMap h D φ H.w] at H
  exact H

end AlgebraicGeometry
