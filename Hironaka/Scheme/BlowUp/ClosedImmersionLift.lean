/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.BlowUpMap.Defs
public import Hironaka.Scheme.BlowUp.Transform.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Lifts of closed immersions to blow-ups

For a closed subscheme `j : S ↪ X` and a centre `Z ⊆ X`, the blow-up `B_{Z ∩ S} S` is naturally
identified with the strict transform `π⁻¹_* S ⊂ B_Z X`, and conversely a centre `Z ⊆ S` pushed
forward to `X` gives the closed immersion `B_Z S ↪ B_{j_* Z} X` [Kol07, Definition 30, 30.2 and
30.3].  This module holds the blow-up calculus behind both, in a form the vocabulary of the main
theorems can use (`AlgebraicGeometry.Scheme.Hom.pushforwardBlowUp`, the morphism
`B_Z S ⟶ B_{j_* Z} X` built from `(Z.map j).comap j = Z`, `comap_map_of_isClosedImmersion`):

* `isClosedImmersion_blowUpMap`, `ker_blowUpMap_subschemeι`: for `j = J.subschemeι` the lift
  `blowUpMap j D : B_{D ∩ V(J)} V(J) ⟶ B_D X` is a closed immersion with kernel the strict transform
  of `V(J)` (the identification of `B_{D ∩ V(J)} V(J)` with the strict transform,
  `exists_iso_strictTransform_subscheme`, and the uniqueness of lifts).
* `isIso_blowUpMap_of_isIso`, `isClosedImmersion_blowUpMap_of_isClosedImmersion`,
  `ker_blowUpMap_of_isClosedImmersion`: the same for any closed immersion `j`, through its
  scheme-theoretic image `j = j.toImage ≫ j.ker.subschemeι` (`blowUpMap` of an isomorphism is an
  isomorphism, the top arrow of the flat base-change square); hence `pushforwardBlowUp j Z` is a
  closed immersion (the instance `Scheme.instIsClosedImmersionPushforwardBlowUp`).
* Cartesian squares: pushing forward along a closed immersion commutes with pulling back along a
  flat morphism, and the induced square of blow-ups over a cartesian square of the bases is
  cartesian (`comap_map_of_isPullback`, `isPullback_blowUpMap_of_isPullback`).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.IdealSheafData Scheme.Hom

variable {X Y : Scheme.{u}}

/-- For a closed subscheme `V(J) ⊆ X` and a centre `D`, the induced morphism of blow-ups
`blowUpMap J.subschemeι D : B_{D ∩ V(J)} V(J) ⟶ B_D X` is a closed immersion — the isomorphism of
`B_{D ∩ V(J)} V(J)` onto the strict transform of `V(J)` (`exists_iso_strictTransform_subscheme`)
followed by the strict transform's inclusion, by the uniqueness of lifts
[Kol07, Definition 30, 30.2]. -/
theorem isClosedImmersion_blowUpMap (J D : X.IdealSheafData) :
    IsClosedImmersion (blowUpMap J.subschemeι D) := by
  obtain ⟨e, he⟩ := exists_iso_strictTransform_subscheme (blowUp.isBlowUp D)
    (blowUp.isBlowUp (D.comap J.subschemeι))
  have h := eq_blowUpMap J.subschemeι D
    (e.hom ≫ (J.strictTransformAlong (blowUpπ D) (D.comap (blowUpπ D))).subschemeι)
    (by rw [Category.assoc]; exact he)
  rw [← h]
  infer_instance

/-- The lift `blowUpMap J.subschemeι D` has kernel the strict transform of `V(J)`: its image is
`π⁻¹_* V(J)`. -/
theorem ker_blowUpMap_subschemeι (J D : X.IdealSheafData) :
    (blowUpMap J.subschemeι D).ker =
      J.strictTransformAlong (blowUpπ D) (D.comap (blowUpπ D)) := by
  obtain ⟨e, he⟩ := exists_iso_strictTransform_subscheme (blowUp.isBlowUp D)
    (blowUp.isBlowUp (D.comap J.subschemeι))
  have h := eq_blowUpMap J.subschemeι D
    (e.hom ≫ (J.strictTransformAlong (blowUpπ D) (D.comap (blowUpπ D))).subschemeι)
    (by rw [Category.assoc]; exact he)
  rw [← h, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

/-- The lift along an isomorphism is an isomorphism: the top arrow of the flat base-change square
`isPullback_blowUpMap`. -/
theorem isIso_blowUpMap_of_isIso (e : Y ⟶ X) [IsIso e] (D : X.IdealSheafData) :
    IsIso (blowUpMap e D) :=
  (isPullback_blowUpMap e D).isIso_fst_of_isIso

/-- The lift along a composite factors through the lifts of the factors (the uniqueness clause of
the universal property). -/
theorem blowUpMap_comp_eq {Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) (D : X.IdealSheafData) :
    blowUpMap (f ≫ g) D =
      eqToHom (congrArg (blowUp (X := Z)) (D.comap_comp f g)) ≫ blowUpMap f (D.comap g) ≫
        blowUpMap g D := by
  symm
  apply eq_blowUpMap
  simp only [Category.assoc, blowUpMap_π, blowUpMap_π_assoc]
  rw [← Category.assoc, eqToHom_comp_blowUpπ (D.comap_comp f g)]

/-- One step for any closed immersion `j : Y ⟶ X`, written `j = e ≫ J.subschemeι` with `e` an
isomorphism (its scheme-theoretic image): the lift `blowUpMap j D` is a closed immersion. -/
theorem isClosedImmersion_blowUpMap_of_factor (J : X.IdealSheafData) (e : Y ⟶ J.subscheme)
    [IsIso e] (j : Y ⟶ X) (hj : e ≫ J.subschemeι = j) (D : X.IdealSheafData) :
    IsClosedImmersion (blowUpMap j D) := by
  subst hj
  rw [blowUpMap_comp_eq]
  have := isIso_blowUpMap_of_isIso e (D.comap J.subschemeι)
  have := isClosedImmersion_blowUpMap J D
  infer_instance

/-- One step for any closed immersion written `j = e ≫ J.subschemeι`: the kernel of the lift is the
strict transform of `V(J)`. -/
theorem ker_blowUpMap_of_factor (J : X.IdealSheafData) (e : Y ⟶ J.subscheme) [IsIso e]
    (j : Y ⟶ X) (hj : e ≫ J.subschemeι = j) (D : X.IdealSheafData) :
    (blowUpMap j D).ker = J.strictTransformAlong (blowUpπ D) (D.comap (blowUpπ D)) := by
  subst hj
  rw [blowUpMap_comp_eq]
  have := isIso_blowUpMap_of_isIso e (D.comap J.subschemeι)
  rw [Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp_of_isIso, ker_blowUpMap_subschemeι]

/-- For any closed immersion `j`, `blowUpMap j D` is a closed immersion. -/
theorem isClosedImmersion_blowUpMap_of_isClosedImmersion (j : Y ⟶ X) [IsClosedImmersion j]
    (D : X.IdealSheafData) : IsClosedImmersion (blowUpMap j D) :=
  isClosedImmersion_blowUpMap_of_factor j.ker j.toImage j j.toImage_imageι D

/-- For any closed immersion `j`, the kernel of `blowUpMap j D` is the strict transform of the
image of `j`. -/
theorem ker_blowUpMap_of_isClosedImmersion (j : Y ⟶ X) [IsClosedImmersion j]
    (D : X.IdealSheafData) :
    (blowUpMap j D).ker = j.ker.strictTransformAlong (blowUpπ D) (D.comap (blowUpπ D)) :=
  ker_blowUpMap_of_factor j.ker j.toImage j j.toImage_imageι D

/-- The induced morphism of blow-ups along a closed immersion is a closed immersion
(`AlgebraicGeometry.isClosedImmersion_blowUpMap_of_isClosedImmersion`). -/
instance Scheme.instIsClosedImmersionPushforwardBlowUp (j : Y ⟶ X) [IsClosedImmersion j]
    (Z : Y.IdealSheafData) : IsClosedImmersion (pushforwardBlowUp j Z) := by
  unfold pushforwardBlowUp
  have := isClosedImmersion_blowUpMap_of_isClosedImmersion j (Z.map j)
  infer_instance

/-! ### Cartesian squares: ideal sheaves and blow-ups over a base change -/

/-- Transport of a cartesian square along equalities of its four objects and heterogeneous
equalities of its four morphisms (bookkeeping for the `eqToHom` identifications of blow-up
sources). -/
theorem isPullback_of_heq {C : Type*} [Category C] {P X Y Z P' X' Y' Z' : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'}
    {g' : Y' ⟶ Z'} (hP : P = P') (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (h₁ : HEq fst fst')
    (h₂ : HEq snd snd') (h₃ : HEq f f') (h₄ : HEq g g') (sq : IsPullback fst snd f g) :
    IsPullback fst' snd' f' g' := by
  subst hP hX hY hZ
  cases h₁
  cases h₂
  cases h₃
  cases h₄
  exact sq

/-- The inverse image along a commutative square: `(I.comap h).comap j' = (I.comap j).comap hS`
when `j' ≫ h = hS ≫ j` (`comap_comp` twice) — pulling back by `h` and then restricting gives the
same result as restricting and then pulling back, as in the proof of [Kol07, Lemma 102]. -/
theorem comap_comap_eq_of_comm {X' Y' : Scheme.{u}} (I : X.IdealSheafData) (j : Y ⟶ X)
    (h : X' ⟶ X) (j' : Y' ⟶ X') (hS : Y' ⟶ Y) (w : j' ≫ h = hS ≫ j) :
    (I.comap h).comap j' = (I.comap j).comap hS := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, w]

/-- The square of a closed subscheme `V(Z)` and its inverse image `V(Z.comap f)` is cartesian,
with Mathlib's `subschemeMap` as the induced map (`isPullback_of_isClosedImmersion`; the kernels
are `Z` and `Z.comap f` by `ker_subschemeι`). -/
theorem isPullback_subschemeι_comap (Z : X.IdealSheafData) (f : Y ⟶ X) :
    IsPullback (Z.comap f).subschemeι
      (Scheme.IdealSheafData.subschemeMap (Z.comap f) Z f (Scheme.IdealSheafData.le_map_comap Z f))
      f Z.subschemeι :=
  isPullback_of_isClosedImmersion _ _ _ _
    (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _).symm
    (by rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι])

/-- On a cartesian square `j' ≫ h = hS ≫ j` with `j` a closed immersion, pushing forward along
`j` then pulling back along `h` is pulling back along `hS` then pushing forward along `j'`:
`(Z.map j).comap h = (Z.comap hS).map j'` — both are the ideal of `Z ×_X X' = (Z ×_Y Y')` in `X'`
(pasting `isPullback_subschemeι_comap` with the square, `ker_fst_of_isClosedImmersion`). -/
theorem comap_map_of_isPullback {X' Y' : Scheme.{u}} {j : Y ⟶ X} [IsClosedImmersion j]
    {h : X' ⟶ X} {j' : Y' ⟶ X'} {hS : Y' ⟶ Y} (sq : IsPullback j' hS h j)
    (Z : Y.IdealSheafData) : (Z.map j).comap h = (Z.comap hS).map j' := by
  have hsq : IsPullback ((Z.comap hS).subschemeι ≫ j')
      (Scheme.IdealSheafData.subschemeMap (Z.comap hS) Z hS
        (Scheme.IdealSheafData.le_map_comap Z hS)) h (Z.subschemeι ≫ j) :=
    (isPullback_subschemeι_comap Z hS).paste_horiz sq
  calc (Z.map j).comap h = (Z.subschemeι ≫ j).ker.comap h := rfl
    _ = (pullback.fst h (Z.subschemeι ≫ j)).ker :=
        (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion _ h).symm
    _ = (hsq.isoPullback.hom ≫ pullback.fst h (Z.subschemeι ≫ j)).ker :=
        (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = ((Z.comap hS).subschemeι ≫ j').ker := by rw [hsq.isoPullback_hom_fst]
    _ = (Z.comap hS).map j' := rfl

/-- For `h` flat and a cartesian square `j' ≫ h = hS ≫ j`, the induced square of the blow-ups
along `D`, `D.comap h`, `D.comap j` and `(D.comap h).comap j' = (D.comap j).comap hS` is cartesian
(flat base change [Sta, Tag 0805] over a cartesian square):
`B_{D'} Y' = Y' ×_Y B_{D_Y} Y = (X' ×_X Y) ×_Y B_{D_Y} Y = B_{D_Y} Y ×_{B_D X} (X' ×_X B_D X)`, by
pasting the flat base-change squares (`isPullback_blowUpMap`, for `h` and for its base change
`hS`) with the given square and cancelling (`IsPullback.of_right`); the commutativity of the
blow-up square is the uniqueness clause of the universal property (`blowUp.hom_ext`). -/
theorem isPullback_blowUpMap_of_isPullback {X' Y' : Scheme.{u}} {j : Y ⟶ X} {h : X' ⟶ X}
    [Flat h] {j' : Y' ⟶ X'} {hS : Y' ⟶ Y} (sq : IsPullback j' hS h j) (D : X.IdealSheafData) :
    IsPullback (blowUpMap j' (D.comap h))
      (eqToHom (congrArg (blowUp (X := Y')) (comap_comap_eq_of_comm D j h j' hS sq.w)) ≫
        blowUpMap hS (D.comap j))
      (blowUpMap h D) (blowUpMap j D) := by
  have : Flat hS :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) sq inferInstance
  have s₀ : IsPullback (blowUpπ ((D.comap h).comap j'))
      (eqToHom (congrArg (blowUp (X := Y')) (comap_comap_eq_of_comm D j h j' hS sq.w))) (𝟙 Y')
      (blowUpπ ((D.comap j).comap hS)) :=
    IsPullback.of_vert_isIso
      ⟨by rw [Category.comp_id,
        eqToHom_comp_blowUpπ (comap_comap_eq_of_comm D j h j' hS sq.w)]⟩
  have s₁ := s₀.paste_vert (isPullback_blowUpMap hS (D.comap j)).flip
  rw [Category.id_comp] at s₁
  have R := s₁.paste_horiz sq
  rw [← blowUpMap_π j' (D.comap h), ← blowUpMap_π j D] at R
  refine IsPullback.of_right R ?_ (isPullback_blowUpMap h D).flip
  refine blowUp.hom_ext D (blowUpπ ((D.comap h).comap j') ≫ j' ≫ h) ?_ _ _ ?_ ?_
  · rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
    exact blowUp.isInvertible_comap_π _
  · simp only [Category.assoc, blowUpMap_π, blowUpMap_π_assoc]
  · simp only [Category.assoc, blowUpMap_π, blowUpMap_π_assoc]
    rw [← Category.assoc,
      eqToHom_comp_blowUpπ (comap_comap_eq_of_comm D j h j' hS sq.w), sq.w]

end AlgebraicGeometry
