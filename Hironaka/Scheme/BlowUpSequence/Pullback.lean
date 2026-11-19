/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Basic
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUp.Descent
import Hironaka.Scheme.IdealSheaf.StalkIdeal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
/-!
# Pullback of a blow-up sequence along a morphism: the stage lifts

The recursion `AlgebraicGeometry.Scheme.BlowUpSequence.pullback` pulls a sequence back center by
center, `(cons X D rest).pullback h = cons Y (D.comap h) (rest.pullback (blowUpMap h D))`, the tail
being pulled back along the morphism of blow-ups `blowUpMap h D : blowUp (D.comap h) ⟶ blowUp D`
that lies over `h` (the universal property of the blow-up). For a smooth `h : Y → X` this is the
pull-back `h^* B` of [Kol07, 30.1]: the sequence of fibre products `X_i ×_X Y` with centers
`Z_i ×_X Y`, together with the induced maps `h_i : X_i ×_X Y → X_i`. This module defines

* `pullbackStageIdx`, `pullbackCenterIdx`: the index transports along the length identity
  `length_pullback` (`Fin.cast`, reducible), so that the stages and centers of `S.pullback h` are
  indexed by those of `S`;
* `pullbackStageHom S h i : (S.pullback h).stage _ ⟶ S.stage i`: Kollár's `h_i`, by recursion on
  the sequence: `h` at stage `0`, and at stage `i + 1` the lift `blowUpMap h_i (S.center i)` of
  `h_i` to the blow-ups;
* `CentersInRange S h`: every center `|Z_i|` lies in the image of `h_i` (automatic for a
  surjective flat `h`),

and proves the basic facts about them: the commuting squares `h_i ≫ Π_i = Π'_i ≫ h`, the centers
`(S.pullback h).center i = (S.center i).comap h_i`, the cartesian stage squares for flat `h`, with
smoothness, flatness and surjectivity of the `h_i` by base change (and that the `h_i` of an open
immersion are open immersions, used for the locality of maximal contact), the functoriality of
the pullback in `h` (`pullback_comp`, `pullback_id`), and the injectivity of the pullback along a
flat morphism whose stage lifts cover the centers (`pullback_injective`; Kollár's "if `h` is
surjective then `h^* B` determines `B` uniquely"). The pullback of a smooth sequence is smooth
(`Hironaka/Scheme/BlowUpSequence/PullbackSmooth.lean`), and the induced ideals and divisors pull
back (`Hironaka/Scheme/BlowUpSequence/PullbackInduced.lean`); see also [Wlo05, Proposition 2.4.2].
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme BlowUpSequence

namespace AlgebraicGeometry.Scheme.BlowUpSequence

variable {X : Scheme.{u}}

/-- The index transport of stages along `length_pullback`: a stage index of `S` read as a stage
index of `S.pullback h`. Reducible, so that `(S.pullback h).stage (S.pullbackStageIdx h ⟨j, _⟩)`
unfolds on the constructor shapes. -/
noncomputable abbrev pullbackStageIdx (S : BlowUpSequence X) {Y : Scheme.{u}} (h : Y ⟶ X)
    (i : Fin (S.length + 1)) : Fin ((S.pullback h).length + 1) :=
  Fin.cast (congrArg (· + 1) (length_pullback S h).symm) i

/-- The index transport of centers along `length_pullback`. -/
noncomputable abbrev pullbackCenterIdx (S : BlowUpSequence X) {Y : Scheme.{u}} (h : Y ⟶ X)
    (i : Fin S.length) : Fin (S.pullback h).length :=
  Fin.cast (length_pullback S h).symm i

/-- **The stage lifts of `h` along the pulled-back sequence**: `h_0 = h` and
`h_{i+1} = blowUpMap h_i (Z_i)`, the morphism of blow-ups over `h_i` given by the universal
property. These are the maps `h_i : X_i ×_X Y → X_i` of [Kol07, 30.1] and the lifts `φ_i` of
[Wlo05, Proposition 2.4.2 (1)]: for flat `h` the stages of `S.pullback h` are the fibre products
`X_i ×_X Y` and the `h_i` their projections (`isPullback_pullbackStageHom`). -/
noncomputable def pullbackStageHom : {X : Scheme.{u}} → (S : BlowUpSequence X) → {Y : Scheme.{u}} →
    (h : Y ⟶ X) → (i : Fin (S.length + 1)) → ((S.pullback h).stage (S.pullbackStageIdx h i) ⟶
    S.stage i)
  | _, nil _, _, h, _ => h
  | _, cons _ _ _, _, h, ⟨0, _⟩ => h
  | _, cons _ D rest, _, h, ⟨j + 1, hj⟩ =>
      rest.pullbackStageHom (Scheme.Hom.blowUpMap h D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩

/-- **The centers of `S` lie in the images of the stage lifts**, `|Z_i| ⊆ h_i(X_i ×_X Y)` for every
`i`. This is the hypothesis under which a flat pullback determines the sequence
(`pullback_injective`); it is automatic when `h` is surjective and flat
(`centersInRange_of_surjective`). Compare [Kol07, 30.1]: if `h` is surjective then `h^* B`
determines `B` uniquely, while otherwise "we lose information about the centers living above
`X ∖ h(Y)`". -/
def CentersInRange (S : BlowUpSequence X) {Y : Scheme.{u}} (h : Y ⟶ X) : Prop :=
  ∀ i : Fin S.length,
    ((S.center i).support : Set (S.stage i.castSucc)) ⊆ Set.range (S.pullbackStageHom h i.castSucc)

end AlgebraicGeometry.Scheme.BlowUpSequence

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### The recursion on the constructor shapes -/

/-- The pullback of the empty sequence (definitional). -/
@[simp]
theorem pullback_nil (h : Y ⟶ X) : (nil X).pullback h = nil Y := rfl

/-- The pullback of a `cons` (definitional). -/
@[simp]
theorem pullback_cons (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp) (h : Y ⟶ X) :
    (cons X D rest).pullback h = cons Y (D.comap h) (rest.pullback
        (Scheme.Hom.blowUpMap h D)) := rfl

/-- The stage lift on the empty sequence is `h` (definitional). -/
theorem pullbackStageHom_nil (h : Y ⟶ X) (i : Fin ((nil X).length + 1)) :
    (nil X).pullbackStageHom h i = h := rfl

/-- The stage lift at index `0` of a `cons` is `h` (definitional). -/
theorem pullbackStageHom_cons_zero (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp)
    (h : Y ⟶ X) : (cons X D rest).pullbackStageHom h ⟨0, Nat.succ_pos _⟩ = h := rfl

/-- The stage lift at index `j + 1` of a `cons` is the tail's (definitional). -/
theorem pullbackStageHom_cons_succ (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp)
    (h : Y ⟶ X) (j : ℕ) (hj : j + 1 < (cons X D rest).length + 1) :
    (cons X D rest).pullbackStageHom h ⟨j + 1, hj⟩ =
      rest.pullbackStageHom (Scheme.Hom.blowUpMap h D) ⟨j, Nat.lt_of_succ_lt_succ hj⟩ := rfl

/-- The stage lifts lie over `h`, in the `⟨j, hj⟩` form of the indices in which the recursions
unfold. -/
theorem pullbackStageHom_stageMap_mk (S : BlowUpSequence X) (h : Y ⟶ X) (j : ℕ)
    (hj : j < S.length + 1) :
    S.pullbackStageHom h ⟨j, hj⟩ ≫ S.stageMap ⟨j, hj⟩ =
      (S.pullback h).stageMap (S.pullbackStageIdx h ⟨j, hj⟩) ≫ h := by
  induction S generalizing Y j with
  | nil X =>
    change h ≫ 𝟙 X = 𝟙 Y ≫ h
    simp
  | cons X D rest ih =>
    cases j with
    | zero =>
      change h ≫ 𝟙 X = 𝟙 Y ≫ h
      simp
    | succ j =>
      have hj' : j < rest.length + 1 := Nat.lt_of_succ_lt_succ hj
      change rest.pullbackStageHom (Scheme.Hom.blowUpMap h D) ⟨j, hj'⟩ ≫
          (rest.stageMap ⟨j, hj'⟩ ≫ D.blowUpπ) =
        ((rest.pullback (Scheme.Hom.blowUpMap h D)).stageMap
          (rest.pullbackStageIdx (Scheme.Hom.blowUpMap h D) ⟨j, hj'⟩) ≫ (D.comap h).blowUpπ) ≫ h
      rw [← Category.assoc, ih (Scheme.Hom.blowUpMap h D) j hj', Category.assoc, Category.assoc]
      congr 1
      exact blowUpMap_π h D

/-- The stage lifts lie over `h`: `h_i ≫ Π_i = Π'_i ≫ h` [Kol07, 30.1]. -/
theorem pullbackStageHom_stageMap (S : BlowUpSequence X) (h : Y ⟶ X) (i : Fin (S.length + 1)) :
    S.pullbackStageHom h i ≫ S.stageMap i =
      (S.pullback h).stageMap (S.pullbackStageIdx h i) ≫ h := by
  obtain ⟨j, hj⟩ := i
  exact pullbackStageHom_stageMap_mk S h j hj

/-- The centers of the pullback are the inverse images of the centers, in the `⟨j, hj⟩` form. -/
theorem center_pullback_mk (S : BlowUpSequence X) (h : Y ⟶ X) (j : ℕ) (hj : j < S.length) :
    (S.pullback h).center (S.pullbackCenterIdx h ⟨j, hj⟩) =
      (S.center ⟨j, hj⟩).comap (S.pullbackStageHom h ⟨j, Nat.lt_succ_of_lt hj⟩) := by
  induction S generalizing Y j with
  | nil X => exact (Nat.not_lt_zero _ hj).elim
  | cons X D rest ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih (Scheme.Hom.blowUpMap h D) j (Nat.lt_of_succ_lt_succ hj)

/-- The `i`-th center of the pullback is the inverse image of `Z_i` under the stage lift `h_i`
(the center `Z_i ×_X Y` of [Kol07, 30.1]). -/
theorem center_pullback (S : BlowUpSequence X) (h : Y ⟶ X) (i : Fin S.length) :
    (S.pullback h).center (S.pullbackCenterIdx h i) =
      (S.center i).comap (S.pullbackStageHom h i.castSucc) := by
  obtain ⟨j, hj⟩ := i
  exact center_pullback_mk S h j hj

/-- The `j`-th blow-up of the pullback lies over the `j`-th blow-up of `S`, in the `⟨j, hj⟩`
form. -/
theorem step_pullback_mk (S : BlowUpSequence X) (h : Y ⟶ X) (j : ℕ) (hj : j < S.length) :
    (S.pullback h).step (S.pullbackCenterIdx h ⟨j, hj⟩) ≫
        S.pullbackStageHom h ⟨j, Nat.lt_succ_of_lt hj⟩ =
      S.pullbackStageHom h ⟨j + 1, Nat.succ_lt_succ hj⟩ ≫ S.step ⟨j, hj⟩ := by
  induction S generalizing Y j with
  | nil X => exact (Nat.not_lt_zero _ hj).elim
  | cons X D rest ih =>
    cases j with
    | zero =>
      cases rest with
      | nil _ =>
        change (eqToHom rfl ≫ (D.comap h).blowUpπ) ≫ h =
          Scheme.Hom.blowUpMap h D ≫ (eqToHom rfl ≫ D.blowUpπ)
        simp [blowUpMap_π]
      | cons _ D' rest' =>
        change (eqToHom rfl ≫ (D.comap h).blowUpπ) ≫ h =
          Scheme.Hom.blowUpMap h D ≫ (eqToHom rfl ≫ D.blowUpπ)
        simp [blowUpMap_π]
    | succ j => exact ih (Scheme.Hom.blowUpMap h D) j (Nat.lt_of_succ_lt_succ hj)

/-- The `i`-th blow-up of the pullback lies over the `i`-th blow-up of `S`: the square of
`h^* π_i` over `π_i` in [Kol07, 30.1]. -/
theorem step_pullback (S : BlowUpSequence X) (h : Y ⟶ X) (i : Fin S.length) :
    (S.pullback h).step (S.pullbackCenterIdx h i) ≫ S.pullbackStageHom h i.castSucc =
      S.pullbackStageHom h i.succ ≫ S.step i := by
  obtain ⟨j, hj⟩ := i
  exact step_pullback_mk S h j hj

/-- The exceptional divisor of the `i`-th blow-up of the pullback is the inverse image of
`F_{i+1}` under `h_{i+1}`, for every `h` [Wlo05, Proposition 2.4.2, proof]. -/
theorem exceptionalAt_pullback (S : BlowUpSequence X) (h : Y ⟶ X) (i : Fin S.length) :
    (S.pullback h).exceptionalAt (S.pullbackCenterIdx h i) =
      (S.exceptionalAt i).comap (S.pullbackStageHom h i.succ) := by
  unfold exceptionalAt
  rw [center_pullback, ← Scheme.IdealSheafData.comap_comp, step_pullback,
    Scheme.IdealSheafData.comap_comp]

/-! ### The fibre-product squares (flat base change) -/

/-- The stage squares of a flat pullback are cartesian, in the `⟨j, hj⟩` form: the pullback
square of one blow-up map (`AlgebraicGeometry.isPullback_blowUpMap`) pasted stage by stage. -/
theorem isPullback_pullbackStageHom_mk (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h] (j : ℕ)
    (hj : j < S.length + 1) :
    IsPullback (S.pullbackStageHom h ⟨j, hj⟩)
      ((S.pullback h).stageMap (S.pullbackStageIdx h ⟨j, hj⟩)) (S.stageMap ⟨j, hj⟩) h := by
  induction S generalizing Y j with
  | nil X =>
    change IsPullback h (𝟙 Y) (𝟙 X) h
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  | cons X D rest ih =>
    cases j with
    | zero =>
      change IsPullback h (𝟙 Y) (𝟙 X) h
      exact IsPullback.of_vert_isIso ⟨by simp⟩
    | succ j =>
      have hj' : j < rest.length + 1 := Nat.lt_of_succ_lt_succ hj
      have : Flat (Scheme.Hom.blowUpMap h D) :=
        property_of_isPullback _ (isPullback_blowUpMap h D)
          inferInstance
      exact (ih (Scheme.Hom.blowUpMap h D) j hj').paste_vert (isPullback_blowUpMap h D)

/-- For flat `h` the stage squares are cartesian: the stages of the pullback are the fibre
products `X_i ×_X Y` of [Kol07, 30.1]. -/
theorem isPullback_pullbackStageHom (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (i : Fin (S.length + 1)) :
    IsPullback (S.pullbackStageHom h i) ((S.pullback h).stageMap (S.pullbackStageIdx h i))
      (S.stageMap i) h := by
  obtain ⟨j, hj⟩ := i
  exact isPullback_pullbackStageHom_mk S h j hj

/-- The stage lifts of a flat `h` are flat. -/
theorem flat_pullbackStageHom (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (i : Fin (S.length + 1)) : Flat (S.pullbackStageHom h i) :=
  property_of_isPullback _ (isPullback_pullbackStageHom S h i) inferInstance

/-- The stage lifts of a smooth `h` are smooth [Kol07, 30.1]. -/
theorem smooth_pullbackStageHom (S : BlowUpSequence X) (h : Y ⟶ X) [Smooth h]
    (i : Fin (S.length + 1)) : Smooth (S.pullbackStageHom h i) :=
  property_of_isPullback _ (isPullback_pullbackStageHom S h i) inferInstance

/-- The stage lifts of an open immersion `h` are open immersions: base change along the cartesian
squares `isPullback_pullbackStageHom` (open immersions are flat, so the squares are cartesian).
Used for the locality of maximal contact. -/
theorem isOpenImmersion_pullbackStageHom (S : BlowUpSequence X) (h : Y ⟶ X) [IsOpenImmersion h]
    (i : Fin (S.length + 1)) : IsOpenImmersion (S.pullbackStageHom h i) :=
  property_of_isPullback _ (isPullback_pullbackStageHom S h i) inferInstance

/-- The image of the stage lift is the preimage under `Π_i` of the image of `h`. -/
theorem range_pullbackStageHom (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (i : Fin (S.length + 1)) :
    Set.range (S.pullbackStageHom h i) = S.stageMap i ⁻¹' Set.range h :=
  range_fst_of_isPullback (isPullback_pullbackStageHom S h i)

/-- The stage lifts of a surjective flat `h` are surjective. -/
theorem surjective_pullbackStageHom (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (hs : Function.Surjective h) (i : Fin (S.length + 1)) :
    Function.Surjective (S.pullbackStageHom h i) := by
  rw [← Set.range_eq_univ, range_pullbackStageHom, Set.range_eq_univ.mpr hs, Set.preimage_univ]

/-! ### Transport lemmas: equality of sequences, functoriality of the pullback -/

/-- Equality of two `cons` terms is equality of the centers and, after substitution, of the
tails. -/
theorem cons_inj {D D' : X.IdealSheafData} {r : BlowUpSequence D.blowUp}
    {r' : BlowUpSequence D'.blowUp} (hc : cons X D r = cons X D' r') :
    ∃ e : D = D', (e ▸ r : BlowUpSequence D'.blowUp) = r' := by
  obtain ⟨e, hr⟩ := BlowUpSequence.cons.inj hc
  subst e
  exact ⟨rfl, eq_of_heq hr⟩

/-- The converse direction used by the transport proofs: `cons` of equal centers and
heterogeneously equal tails are equal. -/
theorem cons_congr {D D' : X.IdealSheafData} {r : BlowUpSequence D.blowUp}
    {r' : BlowUpSequence D'.blowUp} (e : D = D') (hr : HEq r r') :
    cons X D r = cons X D' r' := by
  subst e
  cases hr
  rfl

/-- Pulling back along `eqToHom e ≫ h` is pulling back along `h`, up to the transport of the base
along `e`. -/
theorem pullback_eqToHom_comp (S : BlowUpSequence X) {Y' : Scheme.{u}} (e : Y' = Y) (h : Y ⟶ X) :
    HEq (S.pullback (eqToHom e ≫ h)) (S.pullback h) := by
  subst e
  rw [eqToHom_refl, Category.id_comp]

/-- The transport of the blow-up projection along an equality of centers. -/
theorem blowUpπ_eqToHom {I I' : X.IdealSheafData} (e : I = I') :
    eqToHom (congrArg Scheme.IdealSheafData.blowUp e) ≫ I'.blowUpπ = I.blowUpπ :=
  eqToHom_comp_blowUpπ e

/-- The coherence of the morphisms of blow-ups under composition, by the uniqueness clause of the
universal property (`AlgebraicGeometry.blowUpMap_comp_eq`, restated on the abbreviations of the
sequence vocabulary). -/
theorem blowUpMap_comp {Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) (D : X.IdealSheafData) :
    Scheme.Hom.blowUpMap (f ≫ g) D =
      eqToHom (congrArg Scheme.IdealSheafData.blowUp
          (D.comap_comp f g)) ≫ Scheme.Hom.blowUpMap f (D.comap g) ≫
        Scheme.Hom.blowUpMap g D :=
  blowUpMap_comp_eq f g D

/-- The morphism of blow-ups over the identity is the transport along `comap_id`. -/
theorem blowUpMap_id (D : X.IdealSheafData) :
    Scheme.Hom.blowUpMap (𝟙 X) D = eqToHom (congrArg Scheme.IdealSheafData.blowUp D.comap_id) := by
  symm
  apply eq_blowUpMap
  rw [Category.comp_id, blowUpπ_eqToHom D.comap_id]

/-- The pullback is functorial: `(f ≫ g)^* S = f^* (g^* S)`. -/
theorem pullback_comp (S : BlowUpSequence X) {Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X) :
    S.pullback (f ≫ g) = (S.pullback g).pullback f := by
  induction S generalizing Y Z with
  | nil X => rfl
  | cons X D rest ih =>
    change cons Z (D.comap (f ≫ g)) (rest.pullback (Scheme.Hom.blowUpMap (f ≫ g) D)) =
      cons Z ((D.comap g).comap f)
        ((rest.pullback (Scheme.Hom.blowUpMap g D)).pullback (Scheme.Hom.blowUpMap f (D.comap g)))
    apply cons_congr (D.comap_comp f g)
    rw [blowUpMap_comp]
    exact (pullback_eqToHom_comp rest _ _).trans (heq_of_eq (ih _ _))

/-- Pulling back along the identity is the identity. -/
@[simp]
theorem pullback_id (S : BlowUpSequence X) : S.pullback (𝟙 X) = S := by
  induction S with
  | nil X => rfl
  | cons X D rest ih =>
    change cons X (D.comap (𝟙 X)) (rest.pullback (Scheme.Hom.blowUpMap (𝟙 X) D)) = cons X D rest
    apply cons_congr D.comap_id
    rw [blowUpMap_id, ← Category.comp_id (eqToHom _)]
    exact (pullback_eqToHom_comp rest _ _).trans (heq_of_eq ih)

/-- The stalk map of the identity is an isomorphism (Mathlib's `stalkMap_id`). -/
theorem isIso_stalkMap_id (Y : Scheme.{u}) (x : Y) : IsIso ((𝟙 Y : Y ⟶ Y).stalkMap x) := by
  rw [Scheme.Hom.stalkMap_id]
  exact IsIso.id _

open Scheme.IdealSheafData in
/-- The stalk of the inverse image along the identity is the stalk. -/
theorem stalkIdeal_comap_id (I : X.IdealSheafData) (x : X) :
    (I.comap (𝟙 X)).stalkIdeal x = I.stalkIdeal x := by
  rw [stalkIdeal_comap, Scheme.Hom.stalkMap_id]
  exact Ideal.map_id _

/-- The index transport sends the last stage to the last stage. -/
theorem pullbackStageIdx_last (S : BlowUpSequence X) (h : Y ⟶ X) :
    S.pullbackStageIdx h (Fin.last S.length) = Fin.last (S.pullback h).length :=
  Fin.ext (by simp)

/-! ### A flat pullback covering the centers determines the sequence -/

/-- A surjective flat `h` covers every center. -/
theorem centersInRange_of_surjective (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (hs : Function.Surjective h) : S.CentersInRange h := fun i => by
  rw [Set.range_eq_univ.mpr (surjective_pullbackStageHom S h hs _)]
  exact Set.subset_univ _

/-- Two sequences whose centers lie in the images of the stage lifts of a flat `h`, and whose
pullbacks along `h` agree, are equal [Kol07, 30.1]: by induction on the sequence, an ideal sheaf
whose support lies in the image of a flat morphism being determined by its inverse image
(`Scheme.IdealSheafData.eq_of_comap_eq_of_flat`) at each stage. -/
theorem pullback_injective {S S' : BlowUpSequence X} (h : Y ⟶ X) [Flat h]
    (hr : S.CentersInRange h) (hr' : S'.CentersInRange h) (heq : S.pullback h = S'.pullback h) :
    S = S' := by
  induction S generalizing Y with
  | nil X =>
    cases S' with
    | nil _ => rfl
    | cons _ D' r' =>
      have hl := congrArg BlowUpSequence.length heq
      rw [length_pullback, length_pullback] at hl
      exact absurd hl (by simp [BlowUpSequence.length])
  | cons X D r ih =>
    cases S' with
    | nil _ =>
      have hl := congrArg BlowUpSequence.length heq
      rw [length_pullback, length_pullback] at hl
      exact absurd hl (by simp [BlowUpSequence.length])
    | cons _ D' r' =>
      obtain ⟨e, hr₂⟩ := BlowUpSequence.cons.inj heq
      have hD : D = D' :=
        Scheme.IdealSheafData.eq_of_comap_eq_of_flat h D D' (hr ⟨0, Nat.succ_pos _⟩)
          (hr' ⟨0, Nat.succ_pos _⟩) e
      subst hD
      have : Flat (Scheme.Hom.blowUpMap h D) :=
        property_of_isPullback _ (isPullback_blowUpMap h D)
          inferInstance
      exact congrArg (cons X D)
        (ih (Scheme.Hom.blowUpMap h D) (fun i => hr ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
          (fun i => hr' ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩) (eq_of_heq hr₂))

/-- A surjective flat pullback is injective on sequences: "if `h` is surjective then `h^* B`
determines `B` uniquely" [Kol07, 30.1]. -/
theorem pullback_injective_of_surjective {S S' : BlowUpSequence X} (h : Y ⟶ X) [Flat h]
    (hs : Function.Surjective h) (heq : S.pullback h = S'.pullback h) : S = S' :=
  pullback_injective h (centersInRange_of_surjective S h hs)
    (centersInRange_of_surjective S' h hs) heq

/-- An isomorphism of schemes is surjective on points. -/
theorem surjective_of_isIso {Z W : Scheme.{u}} (e : Z ⟶ W) [IsIso e] : Function.Surjective e :=
  fun w => ⟨inv e w, by
    change (inv e ≫ e) w = w
    rw [IsIso.inv_hom_id]
    rfl⟩

end AlgebraicGeometry
