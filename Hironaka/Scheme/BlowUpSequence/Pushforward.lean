/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUp.BlowUpMapSquare
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.Restrict
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# Push-forward of a blow-up sequence from a closed subscheme

For a closed subscheme `j : S ↪ X` and a blow-up sequence `B(S)` with centers `Z_i^S ⊂ S_i`, the
push-forward `j_* B` of [Kol07, 30.3] is the sequence starting with `X` whose centers are
`Z_i^X := (j_i)_* Z_i^S`, the `j_i : S_i ↪ X_i` being the natural inclusions built inductively
(`S_{i+1} = B_{Z_i^S} S_i ↪ B_{Z_i^X} X_i = X_{i+1}`); "for all practical purposes
`Z_i^X = Z_i^S`", and the push-forward of a smooth blow-up sequence is smooth. The recursion is
`AlgebraicGeometry.Scheme.BlowUpSequence.pushforward`
(`cons X (Z.map j) (rest.pushforward (pushforwardBlowUp j Z))`), with
`pushforwardBlowUp j Z : Z.blowUp ⟶ (Z.map j).blowUp` the morphism of blow-ups over `j` on
`Z.blowUp = blowUp Y ((Z.map j).comap j)`.

This module defines the stage inclusions
`pushforwardStageHom j S i : S.stage i ⟶ (S.pushforward j).stage _` (`j` at stage `0`,
`pushforwardBlowUp` at stage `i + 1`, the pattern of `pullbackStageHom`) with the index transports
`pushforwardStageIdx`, `pushforwardCenterIdx`, and proves: the push-forward has the length of the
sequence; the stage inclusions are closed immersions over `j` whose images are the strict
transforms of `S`, and the centers of `j_* B` are the pushed centers; the push-forward of a smooth
sequence is smooth; restriction and push-forward are inverse to each other (`pullback_pushforward`,
`pushforward_pullback_of_strictTransformSeq_le`), which is the injectivity of [Kol07, 51.1] and
the correspondence of [Kol07, Corollary 85]; the push-forward commutes with flat pullback along a
cartesian square (used in the proof of [Kol07, Lemma 102]) and is functorial in the closed
embedding ([Kol07, 34.3]). The last section gives the descent of the identity `B(X) = j_* B(Y)`
along a smooth surjection, used for the closed-embedding clause [Kol07, Claim 71.2].
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.Hom Scheme Hironaka BlowUpSequence
open AlgebraicGeometry (comap_map_of_isClosedImmersion eqToHom_comp_blowUpπ
    ker_blowUpMap_of_isClosedImmersion isClosedImmersion_blowUpMap_of_isClosedImmersion blowUpMap_π
    comap_map_of_isPullback isPullback_blowUpMap_of_isPullback isPullback_of_heq
    comap_comap_eq_of_comm property_of_isPullback isPullback_blowUpMap)
open IdealSheafData (strictTransformAlong)

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- Pushing forward a sequence does not change its length. -/
theorem length_pushforward (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j] :
    (S.pushforward j).length = S.length := by
  induction S generalizing X with
  | nil _ => rfl
  | cons Y Z rest ih => exact congrArg (· + 1) (ih (pushforwardBlowUp j Z))

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.BlowUpSequence

variable {X Y : Scheme.{u}}

/-- The index transport of stages along `length_pushforward`. -/
noncomputable abbrev pushforwardStageIdx (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (i : Fin (S.length + 1)) : Fin ((S.pushforward j).length + 1) :=
  Fin.cast (by rw [length_pushforward]) i

/-- The index transport of centers along `length_pushforward`. -/
noncomputable abbrev pushforwardCenterIdx (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (i : Fin S.length) : Fin (S.pushforward j).length :=
  Fin.cast (length_pushforward S j).symm i

/-- **The stage inclusions of a pushed-forward sequence**, `j_0 = j` and
`j_{i+1} = pushforwardBlowUp j_i Z_i`, the closed immersion `B_{Z_i} S_i ↪ B_{(j_i)_* Z_i} X_i`
given by the universal property of the blow-up: "the `j_i : S_i ↪ X_i` are the natural
inclusions" [Kol07, 30.3]. -/
noncomputable def pushforwardStageHom : {Y : Scheme.{u}} → (S : BlowUpSequence Y) →
    {X : Scheme.{u}} → (j : Y ⟶ X) → [IsClosedImmersion j] → (i : Fin (S.length + 1)) →
    (S.stage i ⟶ (S.pushforward j).stage (S.pushforwardStageIdx j i))
  | _, nil _, _, j, _, _ => j
  | _, cons _ _ _, _, j, _, ⟨0, _⟩ => j
  | _, cons _ Z rest, _, j, _, ⟨n + 1, hn⟩ =>
      rest.pushforwardStageHom (pushforwardBlowUp j Z) ⟨n, Nat.lt_of_succ_lt_succ hn⟩

end AlgebraicGeometry.Scheme.BlowUpSequence

namespace AlgebraicGeometry

open Hironaka

variable {X Y : Scheme.{u}}

/-! ### The recursion, the square over `j`, closed immersions, centers, kernels -/

/-- The push-forward of the empty sequence. -/
theorem pushforward_nil (j : Y ⟶ X) [IsClosedImmersion j] : (nil Y).pushforward j = nil X := rfl

/-- The recursion of `pushforward` on a `cons`. -/
theorem pushforward_cons (Z : Y.IdealSheafData) (rest : BlowUpSequence Z.blowUp)
    (j : Y ⟶ X)
    [IsClosedImmersion j] :
    (cons Y Z rest).pushforward j =
      cons X (Z.map j) (rest.pushforward (pushforwardBlowUp j Z)) := rfl

/-- The one-step inclusion `B_Z S ↪ B_{j_* Z} X` lies over `j` (`blowUpMap_π` after the transport
`AlgebraicGeometry.eqToHom_comp_blowUpπ`). -/
theorem pushforwardBlowUp_π (j : Y ⟶ X) [IsClosedImmersion j] (Z : Y.IdealSheafData) :
    pushforwardBlowUp j Z ≫ (Z.map j).blowUpπ = Z.blowUpπ ≫ j := by
  unfold pushforwardBlowUp
  rw [Category.assoc]
  rw [blowUpMap_π, ← Category.assoc,
    eqToHom_comp_blowUpπ (comap_map_of_isClosedImmersion j Z).symm]

/-- The kernel of the one-step inclusion is the strict transform of the image of `j` under the
blow-up of `X` along `j_* Z` (`Scheme.Hom.ker_comp_of_isIso` for the transport). -/
theorem ker_pushforwardBlowUp (j : Y ⟶ X) [IsClosedImmersion j] (Z : Y.IdealSheafData) :
    (pushforwardBlowUp j Z).ker =
      j.ker.strictTransformAlong (Z.map j).blowUpπ ((Z.map j).comap (Z.map j).blowUpπ) := by
  unfold pushforwardBlowUp
  exact (Scheme.Hom.ker_comp_of_isIso _ _).trans (ker_blowUpMap_of_isClosedImmersion j (Z.map j))

/-- The stage inclusions lie over `j`, in the `⟨n, hn⟩` form of the indices. -/
theorem pushforwardStageHom_stageMap_mk (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (n : ℕ) (hn : n < S.length + 1) :
    S.pushforwardStageHom j ⟨n, hn⟩ ≫
        (S.pushforward j).stageMap (S.pushforwardStageIdx j ⟨n, hn⟩) =
      S.stageMap ⟨n, hn⟩ ≫ j := by
  induction S generalizing X n with
  | nil Y =>
    change j ≫ 𝟙 X = 𝟙 Y ≫ j
    simp
  | cons Y Z rest ih =>
    cases n with
    | zero =>
      change j ≫ 𝟙 X = 𝟙 Y ≫ j
      simp
    | succ n =>
      have hn' : n < rest.length + 1 := Nat.lt_of_succ_lt_succ hn
      change rest.pushforwardStageHom (pushforwardBlowUp j Z) ⟨n, hn'⟩ ≫
          ((rest.pushforward (pushforwardBlowUp j Z)).stageMap
            (rest.pushforwardStageIdx (pushforwardBlowUp j Z) ⟨n, hn'⟩) ≫ (Z.map j).blowUpπ) =
        (rest.stageMap ⟨n, hn'⟩ ≫ Z.blowUpπ) ≫ j
      rw [← Category.assoc, ih (pushforwardBlowUp j Z) n hn', Category.assoc, Category.assoc]
      congr 1
      exact pushforwardBlowUp_π j Z

/-- The stage inclusions `j_i : S_i ↪ X_i` lie over `j` [Kol07, 30.3]. -/
theorem pushforwardStageHom_stageMap (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (i : Fin (S.length + 1)) :
    S.pushforwardStageHom j i ≫ (S.pushforward j).stageMap (S.pushforwardStageIdx j i) =
      S.stageMap i ≫ j := by
  obtain ⟨n, hn⟩ := i
  exact pushforwardStageHom_stageMap_mk S j n hn

/-- The stage inclusions are closed immersions, in the `⟨n, hn⟩` form of the indices. -/
theorem isClosedImmersion_pushforwardStageHom_mk (S : BlowUpSequence Y) (j : Y ⟶ X)
    [IsClosedImmersion j] (n : ℕ) (hn : n < S.length + 1) :
    IsClosedImmersion (S.pushforwardStageHom j ⟨n, hn⟩) := by
  induction S generalizing X n with
  | nil Y => exact ‹IsClosedImmersion j›
  | cons Y Z rest ih =>
    cases n with
    | zero => exact ‹IsClosedImmersion j›
    | succ n => exact ih (pushforwardBlowUp j Z) n (Nat.lt_of_succ_lt_succ hn)

/-- Every stage inclusion is a closed immersion [Kol07, 30.3]. -/
theorem isClosedImmersion_pushforwardStageHom (S : BlowUpSequence Y) (j : Y ⟶ X)
    [IsClosedImmersion j] (i : Fin (S.length + 1)) :
    IsClosedImmersion (S.pushforwardStageHom j i) := by
  obtain ⟨n, hn⟩ := i
  exact isClosedImmersion_pushforwardStageHom_mk S j n hn

/-- The centers of the push-forward are the pushed centers, in the `⟨n, hn⟩` form. -/
theorem center_pushforward_mk (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j] (n : ℕ)
    (hn : n < S.length) :
    (S.pushforward j).center (S.pushforwardCenterIdx j ⟨n, hn⟩) =
      (S.center ⟨n, hn⟩).map (S.pushforwardStageHom j ⟨n, Nat.lt_succ_of_lt hn⟩) := by
  induction S generalizing X n with
  | nil Y => exact (Nat.not_lt_zero _ hn).elim
  | cons Y Z rest ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih (pushforwardBlowUp j Z) n (Nat.lt_of_succ_lt_succ hn)

/-- The centers of the push-forward are the pushed centers, along the stage inclusions:
"`Z_i^X := (j_i)_* Z_i^S`" [Kol07, 30.3]. -/
theorem center_pushforward (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (i : Fin S.length) :
    (S.pushforward j).center (S.pushforwardCenterIdx j i) =
      (S.center i).map (S.pushforwardStageHom j i.castSucc) := by
  obtain ⟨n, hn⟩ := i
  exact center_pushforward_mk S j n hn

/-- The kernel of the `n`-th stage inclusion is the `n`-th strict transform of the image of `j`
under the pushed-forward sequence, in the `⟨n, hn⟩` form. -/
theorem ker_pushforwardStageHom_mk (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (n : ℕ) (hn : n < S.length + 1) :
    (S.pushforwardStageHom j ⟨n, hn⟩).ker =
      (S.pushforward j).strictTransformSeq j.ker (S.pushforwardStageIdx j ⟨n, hn⟩) := by
  induction S generalizing X n with
  | nil Y => rfl
  | cons Y Z rest ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have h := ih (pushforwardBlowUp j Z) n (Nat.lt_of_succ_lt_succ hn)
      rw [ker_pushforwardBlowUp] at h
      exact h

/-- The image of the stage inclusion `j_i : S_i ↪ X_i` is the strict transform of `S` (the
identification of [Kol07, 30.2] on the push-forward side). -/
theorem ker_pushforwardStageHom (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (i : Fin (S.length + 1)) :
    (S.pushforwardStageHom j i).ker =
      (S.pushforward j).strictTransformSeq j.ker (S.pushforwardStageIdx j i) := by
  obtain ⟨n, hn⟩ := i
  exact ker_pushforwardStageHom_mk S j n hn

/-! ### The push-forward of a smooth blow-up sequence is smooth -/

/-- "If `B` is a smooth blow-up sequence, then so is `j_* B`" [Kol07, 30.3]: a smooth closed
subscheme of `S_i` is a smooth closed subscheme of `X_i`, the center `(j_i)_* Z_i^S` having
subscheme isomorphic to that of `Z_i^S` (`Scheme.Hom.toImage` of the closed immersion
`Z_i^S ↪ S_i ↪ X_i`), over the same structure morphism by `pushforwardStageHom_stageMap`;
`Smooth` respects isomorphisms. -/
theorem IsSmooth.pushforward {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (j : Y ⟶ X)
    [IsClosedImmersion j] {S : BlowUpSequence Y} (hS : S.IsSmooth (j ≫ f)) :
    (S.pushforward j).IsSmooth f := by
  intro i'
  obtain ⟨i, rfl⟩ : ∃ i : Fin S.length, i' = S.pushforwardCenterIdx j i :=
    ⟨Fin.cast (length_pushforward S j) i', Fin.ext rfl⟩
  rw [center_pushforward]
  have hci := isClosedImmersion_pushforwardStageHom S j i.castSucc
  have hst : S.pushforwardStageHom j i.castSucc ≫
      (S.pushforward j).stageMap (S.pushforwardCenterIdx j i).castSucc =
        S.stageMap i.castSucc ≫ j :=
    pushforwardStageHom_stageMap S j i.castSucc
  have : MorphismProperty.RespectsIso (@Smooth) :=
    MorphismProperty.respectsIso_of_isStableUnderComposition fun _ _ e he => by
      have : IsIso e := he
      infer_instance
  change Smooth (((S.center i).subschemeι ≫ S.pushforwardStageHom j i.castSucc).imageι ≫
    (S.pushforward j).stageMap (S.pushforwardCenterIdx j i).castSucc ≫ f)
  rw [← MorphismProperty.cancel_left_of_respectsIso (@Smooth)
    ((S.center i).subschemeι ≫ S.pushforwardStageHom j i.castSucc).toImage, ← Category.assoc,
    Scheme.Hom.toImage_imageι]
  simp only [Category.assoc]
  rw [← Category.assoc (S.pushforwardStageHom j i.castSucc), hst]
  simpa only [Category.assoc] using hS i

/-! ### Restriction and push-forward are inverse to each other -/

/-- Transport of the pushforward along an equality of targets and of the closed immersions
(bookkeeping for `cons_congr`). -/
theorem pushforward_heq {Y₁ X₁ X₂ : Scheme.{u}} (T : BlowUpSequence Y₁) (j₁ : Y₁ ⟶ X₁)
    (j₂ : Y₁ ⟶ X₂) [IsClosedImmersion j₁] [IsClosedImmersion j₂] (hX : X₁ = X₂)
    (hj : HEq j₁ j₂) : HEq (T.pushforward j₁) (T.pushforward j₂) := by
  subst hX
  cases hj
  rfl

/-- The one-step inclusion `pushforwardBlowUp j Z` is `blowUpMap j D` up to the identification of
its source, whenever `Z.map j = D` (the transport `eqToHom` of its body is heterogeneously
trivial, `eqToHom_comp_heq`). -/
theorem pushforwardBlowUp_heq (j : Y ⟶ X) [IsClosedImmersion j] {Z : Y.IdealSheafData}
    {D : X.IdealSheafData} (hD : Z.map j = D) :
        HEq (pushforwardBlowUp j Z) (Scheme.Hom.blowUpMap j D) := by
  subst hD
  exact eqToHom_comp_heq _ _

/-- `j^* j_* B = B`: the first center comes back by `comap_map_of_isClosedImmersion`, and the rest
by induction along the inclusion `pushforwardBlowUp j Z`, the transport of its source being
invisible to `pullback` (`pullback_eqToHom_comp`). One half of the correspondence of
[Kol07, 51.1]. -/
theorem pullback_pushforward (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j] :
    (S.pushforward j).pullback j = S := by
  induction S generalizing X with
  | nil _ => rfl
  | cons Y Z rest ih =>
    change cons Y ((Z.map j).comap j)
      ((rest.pushforward (pushforwardBlowUp j Z)).pullback (Scheme.Hom.blowUpMap j (Z.map j))) =
          cons Y Z rest
    refine cons_congr (comap_map_of_isClosedImmersion j Z) ?_
    have h2 : HEq ((rest.pushforward (pushforwardBlowUp j Z)).pullback (pushforwardBlowUp j Z))
        ((rest.pushforward (pushforwardBlowUp j Z)).pullback (Scheme.Hom.blowUpMap j (Z.map j))) :=
      pullback_eqToHom_comp (rest.pushforward (pushforwardBlowUp j Z))
        (congrArg Scheme.IdealSheafData.blowUp (comap_map_of_isClosedImmersion j Z).symm)
            (Scheme.Hom.blowUpMap j (Z.map j))
    exact h2.symm.trans (heq_of_eq (ih (pushforwardBlowUp j Z)))

/-- `j_* j^* B = B` when every center lies in the strict transform of `S`: the first center by
`map_comap_of_ker_le`, the rest by induction along `blowUpMap j D` (whose kernel is the strict
transform), the inclusion `pushforwardBlowUp j (D.comap j)` being `blowUpMap j D` up to
`pushforwardBlowUp_heq`. The other half of the correspondence of [Kol07, 51.1]. -/
theorem pushforward_pullback_of_strictTransformSeq_le (S : BlowUpSequence X) (j : Y ⟶ X)
    [IsClosedImmersion j]
    (hZ : ∀ i : Fin S.length, S.strictTransformSeq j.ker i.castSucc ≤ S.center i) :
    (S.pullback j).pushforward j = S := by
  induction S generalizing Y with
  | nil _ => rfl
  | cons X D rest ih =>
    have h0 : j.ker ≤ D := hZ ⟨0, Nat.succ_pos _⟩
    have hD : (D.comap j).map j = D := map_comap_of_ker_le j D h0
    have hci := isClosedImmersion_blowUpMap_of_isClosedImmersion j D
    have hZ' : ∀ i : Fin rest.length,
        rest.strictTransformSeq (Scheme.Hom.blowUpMap j D).ker i.castSucc ≤ rest.center i := by
      intro ⟨n, hn⟩
      have h1 := hZ ⟨n + 1, Nat.succ_lt_succ hn⟩
      rw [ker_blowUpMap_of_isClosedImmersion]
      exact h1
    have ih' := ih (Scheme.Hom.blowUpMap j D) hZ'
    change cons X ((D.comap j).map j)
      ((rest.pullback (Scheme.Hom.blowUpMap j D)).pushforward (pushforwardBlowUp j (D.comap j))) =
        cons X D rest
    refine cons_congr hD ?_
    refine HEq.trans ?_ (heq_of_eq ih')
    exact pushforward_heq (rest.pullback (Scheme.Hom.blowUpMap j D)) (pushforwardBlowUp j
        (D.comap j))
      (Scheme.Hom.blowUpMap j D) (congrArg Scheme.IdealSheafData.blowUp hD) (pushforwardBlowUp_heq j
          hD)

/-- The centers of `j_* B` lie in the strict transforms of `S`: `ker j_i ≤ Z.map j_i` (`map_bot`,
`map_mono`) read through `ker_pushforwardStageHom` and `center_pushforward`. -/
theorem strictTransformSeq_le_center_pushforward (S : BlowUpSequence Y) (j : Y ⟶ X)
    [IsClosedImmersion j] (i : Fin S.length) :
    (S.pushforward j).strictTransformSeq j.ker (S.pushforwardCenterIdx j i).castSucc ≤
      (S.pushforward j).center (S.pushforwardCenterIdx j i) := by
  rw [center_pushforward]
  have hk : (S.pushforward j).strictTransformSeq j.ker (S.pushforwardCenterIdx j i).castSucc =
      (S.pushforwardStageHom j i.castSucc).ker := (ker_pushforwardStageHom S j i.castSucc).symm
  rw [hk, ← Scheme.IdealSheafData.map_bot]
  exact Scheme.IdealSheafData.map_mono _ bot_le

/-- `j_*` is injective, with `pullback · j` as a left inverse ("gives an injection",
[Kol07, 51.1]). -/
theorem pushforward_injective {S S' : BlowUpSequence Y} (j : Y ⟶ X) [IsClosedImmersion j]
    (heq : S.pushforward j = S'.pushforward j) : S = S' := by
  rw [← pullback_pushforward S j, heq, pullback_pushforward]

/-! ### Push-forward commutes with smooth (flat) pullback -/

/-- Transport of the one-step blow-up morphism along an equality of centers (bookkeeping). -/
theorem blowUpMap_heq (g : Y ⟶ X) {D D' : X.IdealSheafData} (hD : D = D') :
    HEq (Scheme.Hom.blowUpMap g D) (Scheme.Hom.blowUpMap g D') := by
  subst hD
  rfl

/-- For `h` flat and a cartesian square `j' ≫ h = hS ≫ j` with `j`, `j'` closed immersions,
`h^*(j_* B) = (j')_*(hS^* B)` (the flat form of the compatibility used in the proof of
[Kol07, Lemma 102]). Induction on `B`: the first centers agree by `comap_map_of_isPullback`; the
square of the next stage, the inclusions `pushforwardBlowUp` over the flat base changes
`blowUpMap`, is again cartesian by `isPullback_blowUpMap_of_isPullback`, transported along the
identifications of the sources (`comap_map_of_isClosedImmersion`, `comap_comap_eq_of_comm`) by
`isPullback_of_heq`; the rest follows by the hypothesis and `pushforward_heq`. -/
theorem pullback_pushforward_of_isPullback_of_flat {X' Y' : Scheme.{u}} (S : BlowUpSequence Y)
    (j : Y ⟶ X) [IsClosedImmersion j] (h : X' ⟶ X) [Flat h] (j' : Y' ⟶ X') [IsClosedImmersion j']
    (hS : Y' ⟶ Y) (sq : IsPullback j' hS h j) :
    (S.pushforward j).pullback h = (S.pullback hS).pushforward j' := by
  induction S generalizing X X' Y' with
  | nil _ => rfl
  | cons Y Z rest ih =>
    have hc : (Z.map j).comap h = (Z.comap hS).map j' := comap_map_of_isPullback sq Z
    change cons X' ((Z.map j).comap h)
        ((rest.pushforward (pushforwardBlowUp j Z)).pullback (Scheme.Hom.blowUpMap h (Z.map j))) =
      cons X' ((Z.comap hS).map j')
        ((rest.pullback (Scheme.Hom.blowUpMap hS Z)).pushforward
            (pushforwardBlowUp j' (Z.comap hS)))
    refine cons_congr hc ?_
    have hflat : Flat (Scheme.Hom.blowUpMap h (Z.map j)) :=
      property_of_isPullback (@Flat) (isPullback_blowUpMap h (Z.map j)) inferInstance
    have hci : IsClosedImmersion
        (pushforwardBlowUp j' (Z.comap hS) ≫ eqToHom
            (congrArg Scheme.IdealSheafData.blowUp hc.symm)) :=
      inferInstance
    have hP : (((Z.map j).comap h).comap j').blowUp = (Z.comap hS).blowUp :=
      congrArg Scheme.IdealSheafData.blowUp
        (by rw [comap_comap_eq_of_comm (Z.map j) j h j' hS sq.w, comap_map_of_isClosedImmersion])
    have hY : ((Z.map j).comap j).blowUp = Z.blowUp :=
      congrArg Scheme.IdealSheafData.blowUp (comap_map_of_isClosedImmersion j Z)
    have sq₁ : IsPullback
        (pushforwardBlowUp j' (Z.comap hS) ≫ eqToHom (congrArg
          Scheme.IdealSheafData.blowUp hc.symm))
        (Scheme.Hom.blowUpMap hS Z) (Scheme.Hom.blowUpMap h (Z.map j)) (pushforwardBlowUp j Z) :=
      isPullback_of_heq hP rfl hY rfl
        ((comp_eqToHom_heq _ _).trans (pushforwardBlowUp_heq j' hc.symm)).symm
        ((eqToHom_comp_heq _ _).trans (blowUpMap_heq hS (comap_map_of_isClosedImmersion j Z)))
        HEq.rfl (pushforwardBlowUp_heq j rfl).symm
        (isPullback_blowUpMap_of_isPullback sq (Z.map j))
    have ih' := ih (pushforwardBlowUp j Z) (Scheme.Hom.blowUpMap h (Z.map j))
      (pushforwardBlowUp j' (Z.comap hS) ≫ eqToHom (congrArg Scheme.IdealSheafData.blowUp hc.symm))
      (Scheme.Hom.blowUpMap hS Z) sq₁
    exact (heq_of_eq ih').trans (pushforward_heq (rest.pullback (Scheme.Hom.blowUpMap hS Z)) _ _
      (congrArg Scheme.IdealSheafData.blowUp hc) (comp_eqToHom_heq _ _))

/-- For `h : X' → X` smooth and the cartesian square `j' ≫ h = hS ≫ j` (`S' = h⁻¹(S)`,
`hS = h|_{S'}`), pulling back the push-forward along `h` is pushing forward the pullback along
`hS`: `h^*(j_* B) = (j')_*(hS^* B)` (pulling back and restricting commute, "we get the same result"
either way, [Kol07, Lemma 102, proof]). The flat form,
smooth morphisms being flat. -/
theorem pullback_pushforward_of_isPullback {X' Y' : Scheme.{u}} (S : BlowUpSequence Y) (j : Y ⟶ X)
    [IsClosedImmersion j] (h : X' ⟶ X) [Smooth h] (j' : Y' ⟶ X') [IsClosedImmersion j']
    (hS : Y' ⟶ Y) (sq : IsPullback j' hS h j) :
    (S.pushforward j).pullback h = (S.pullback hS).pushforward j' :=
  pullback_pushforward_of_isPullback_of_flat S j h j' hS sq

/-- `pullback_pushforward_of_isPullback` for the closed subscheme `V(J)`: `S' = V(J.comap h)` with
`hS = subschemeMap (J.comap h) J h` (the square is cartesian by
`AlgebraicGeometry.isPullback_subschemeι_comap`). -/
theorem pullback_pushforward_subschemeι {X' : Scheme.{u}} (J : X.IdealSheafData)
    (S : BlowUpSequence J.subscheme) (h : X' ⟶ X) [Smooth h] :
    (S.pushforward J.subschemeι).pullback h =
      (S.pullback (Scheme.IdealSheafData.subschemeMap (J.comap h) J h
        (Scheme.IdealSheafData.le_map_comap J h))).pushforward (J.comap h).subschemeι :=
  pullback_pushforward_of_isPullback S J.subschemeι h (J.comap h).subschemeι _
    (isPullback_subschemeι_comap J h)

/-- The inverse images of a divisor family match on a commutative square,
`h⁻¹(E)|_{S'} = hS⁻¹(E|_S)`: `DivisorFamily.comap_comp` twice. -/
theorem divisorFamily_comap_comap_eq_of_comm {X' Y' : Scheme.{u}} (E : DivisorFamily X)
    (j : Y ⟶ X) (h : X' ⟶ X) (j' : Y' ⟶ X') (hS : Y' ⟶ Y) (w : j' ≫ h = hS ≫ j) :
    (E.comap h).comap j' = (E.comap j).comap hS := by
  rw [← DivisorFamily.comap_comp, ← DivisorFamily.comap_comp, w]

/-! ### Functoriality of the push-forward in the closed embedding -/

/-- The one-step inclusions of a composite `Z ↪ Y ↪ X` compose: both sides are lifts over
`π_D ≫ j' ≫ j` to the blow-up of `X` along `(D.map j').map j = D.map (j' ≫ j)`
(`blowUp.hom_ext`). -/
theorem pushforwardBlowUp_comp {Z : Scheme.{u}} (j' : Z ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion j']
    [IsClosedImmersion j] (D : Z.IdealSheafData) :
    pushforwardBlowUp j' D ≫ pushforwardBlowUp j (D.map j') =
      pushforwardBlowUp (j' ≫ j) D ≫
        eqToHom (congrArg Scheme.IdealSheafData.blowUp
            (Scheme.IdealSheafData.map_comp D j' j)) := by
  have e1 : pushforwardBlowUp j (D.map j') ≫ IdealSheafData.blowUpπ ((D.map j').map j) =
      IdealSheafData.blowUpπ (D.map j') ≫ j := pushforwardBlowUp_π j (D.map j')
  have e2 : pushforwardBlowUp j' D ≫ IdealSheafData.blowUpπ (D.map j') =
      IdealSheafData.blowUpπ D ≫ j' := pushforwardBlowUp_π j' D
  have e3 : pushforwardBlowUp (j' ≫ j) D ≫ IdealSheafData.blowUpπ (D.map (j' ≫ j)) =
      IdealSheafData.blowUpπ D ≫ (j' ≫ j) := pushforwardBlowUp_π (j' ≫ j) D
  refine IdealSheafData.blowUp.hom_ext ((D.map j').map j)
    (IdealSheafData.blowUpπ D ≫ j' ≫ j) ?_ _ _ ?_ ?_
  · rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
      comap_map_of_isClosedImmersion, comap_map_of_isClosedImmersion]
    exact IdealSheafData.blowUp.isInvertible_comap_π D
  · rw [Category.assoc, e1, ← Category.assoc, e2, Category.assoc]
  · rw [Category.assoc,
      eqToHom_comp_blowUpπ (Scheme.IdealSheafData.map_comp D j' j), e3]

/-- The push-forward is functorial in the closed embedding, `j_* j'_* B = (j' ≫ j)_* B` (the
independence from further embeddings `Z ↪ Y ↪ X` of [Kol07, 34.3]): the centers agree by
`map_comp` and the one-step inclusions by `pushforwardBlowUp_comp`, transported by
`pushforward_heq`. -/
theorem pushforward_comp {Z : Scheme.{u}} (S : BlowUpSequence Z) (j' : Z ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion j'] [IsClosedImmersion j] :
    (S.pushforward j').pushforward j = S.pushforward (j' ≫ j) := by
  induction S generalizing X Y with
  | nil _ => rfl
  | cons Z D rest ih =>
    change cons X ((D.map j').map j)
        ((rest.pushforward (pushforwardBlowUp j' D)).pushforward (pushforwardBlowUp j (D.map j'))) =
      cons X (D.map (j' ≫ j)) (rest.pushforward (pushforwardBlowUp (j' ≫ j) D))
    refine cons_congr (Scheme.IdealSheafData.map_comp D j' j).symm ?_
    rw [ih (pushforwardBlowUp j' D) (pushforwardBlowUp j (D.map j'))]
    exact pushforward_heq rest _ _
      (congrArg Scheme.IdealSheafData.blowUp (Scheme.IdealSheafData.map_comp D j' j)).symm
      ((heq_of_eq (pushforwardBlowUp_comp j' j D)).trans (comp_eqToHom_heq _ _))

end AlgebraicGeometry

/-! ### Push-forwards along isomorphisms; descent of the closed-embedding identity along a
smooth surjection -/

namespace AlgebraicGeometry

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The push-forward depends on the closed immersion only through its value: two equal closed
immersions give equal push-forwards (the instance is a proof). -/
theorem pushforward_congr (S : BlowUpSequence Y) {j₁ j₂ : Y ⟶ X} [IsClosedImmersion j₁]
    [IsClosedImmersion j₂] (h : j₁ = j₂) : S.pushforward j₁ = S.pushforward j₂ := by
  subst h
  rfl

/-- Pushing forward along an isomorphism the pullback along it gives the sequence back: pulling
back along the isomorphism (flat and surjective, `surjective_of_isIso`) is injective
(`pullback_injective_of_surjective`) and inverts the push-forward (`pullback_pushforward`). -/
theorem pushforward_pullback_of_isIso (e : Y ⟶ X) [IsIso e] (S : BlowUpSequence X) :
    (S.pullback e).pushforward e = S :=
  pullback_injective_of_surjective e (surjective_of_isIso e)
    (pullback_pushforward (S.pullback e) e)

/-- A marked blow-up sequence functor commuting with smooth surjections ([Kol07, 34.1], first
clause) takes, at a triple carrying the pullback data along an isomorphism, the pullback of its
value. Stated on an abstract morphism so that the surjectivity of the isomorphism
(`surjective_of_isIso`) is checked on it. -/
theorem seq_eq_pullback_of_isIso {k : Type u} [Field k] {Dom : MarkedTriple k → Prop}
    {B : OrderGeSeqAssignment k Dom} (hB : B.CommutesWithSmoothSurjections) {T T' : MarkedTriple k}
    (h : T'.X.left ⟶ T.X.left) [IsIso h] (hpb : T'.IsPullbackOf T h) (hT : Dom T) (hT' : Dom T') :
    B.seq T' hT' = (B.seq T hT).pullback h :=
  hB T T' h (surjective_of_isIso h) hpb hT hT'

variable {k : Type u} [Field k]

/-- **The identity of [Kol07, Claim 71.2] descends along a smooth surjection** ("the claimed
identity in (71.2) is a local question on `X`", [Kol07, 108]). For `g : X' → X` smooth and
surjective, the closed immersion `j : Y → X`, and a cartesian square `j' ≫ g = h_S ≫ j` with `h_S`
smooth and surjective, if the marked triples of `X'` and `Y'` carry the pullback data of those of
`X` and `Y` and `B(X') = j'_* B(Y')`, then `B(X) = j_* B(Y)`: both sides of the latter pull back
along `g` to the two sides of the former (the first clause of [Kol07, 34.1] and
`pullback_pushforward_of_isPullback`), and pullback along the flat surjection `g` is injective. -/
theorem seq_eq_pushforward_of_cover {Dom : MarkedTriple k → Prop} {B : OrderGeSeqAssignment k Dom}
    (hB : B.CommutesWithSmoothSurjections) {TX TY TX' TY' : MarkedTriple k}
    (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j] (g : TX'.X.left ⟶ TX.X.left) [Smooth g]
    (hg : Function.Surjective g) (j' : TY'.X.left ⟶ TX'.X.left) [IsClosedImmersion j']
    (hS : TY'.X.left ⟶ TY.X.left)
    [Smooth hS] (hgS : Function.Surjective hS) (sq : IsPullback j' hS g j)
    (hX' : TX'.IsPullbackOf TX g) (hY' : TY'.IsPullbackOf TY hS) (hTX : Dom TX) (hTY : Dom TY)
    (hTX' : Dom TX') (hTY' : Dom TY') (h' : B.seq TX' hTX' = (B.seq TY' hTY').pushforward j') :
    B.seq TX hTX = (B.seq TY hTY).pushforward j := by
  refine pullback_injective_of_surjective g hg ?_
  calc (B.seq TX hTX).pullback g = B.seq TX' hTX' := (hB TX TX' g hg hX' hTX hTX').symm
    _ = (B.seq TY' hTY').pushforward j' := h'
    _ = ((B.seq TY hTY).pullback hS).pushforward j' := by rw [hB TY TY' hS hgS hY' hTY hTY']
    _ = ((B.seq TY hTY).pushforward j).pullback g :=
        (pullback_pushforward_of_isPullback_of_flat _ j g j' hS sq).symm

end AlgebraicGeometry
