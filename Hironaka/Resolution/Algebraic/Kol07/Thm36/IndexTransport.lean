/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Kol07.Thm36.Affine
import Hironaka.Scheme.BlowUp.BlowUpMap
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.RestrictedCenters
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The first-centre index along pushforwards and isomorphisms

Kollár reduces the independence of the resolution of an affine scheme from its embedding to
embeddings into affine spaces, using that the principalization functor commutes with closed
embeddings and with isomorphisms [Kol07, Theorem 36, proof; Theorem 35 (4), (5)]. This file
proves the bookkeeping behind that reduction: the index `firstCenterIndex` is invariant under the
pushforward of a blow-up sequence along a closed immersion and under the pullback along an
isomorphism, because the predicate `CenterContains` transports exactly.

* Along a closed immersion `j : Y ⟶ X`, the centres of `S.pushforward j` are the images of the
  centres, and the strict transform of `I.map j` along the pushforward is the image of the strict
  transform of `I` along `S` (`strictTransformSeq_pushforward`; one step is `strictTransform_map`,
  which identifies the strict transform of the image of a closed immersion with the kernel of the
  lift of that immersion to the blow-up). Taking images along a closed immersion is an order
  embedding, so `CenterContains` and the index transport (`firstCenterIndex_pushforward`).
* Along an isomorphism `φ`, the centres and strict transforms of `S.pullback φ` are the inverse
  images of those of `S`, again an order embedding (`firstCenterIndex_pullback_of_isIso`).
* `BR_affine_comp_eq_of_BP_eq_pushforward` and `BR_affine_eq_of_BP_eq_pullback`: `BR_affine`
  is unchanged along a closed embedding, respectively an isomorphism, of the ambient triples,
  granted the corresponding identity for `BP` (which
  `Hironaka.Resolution.Algebraic.Kol07.Thm36.Assembly` supplies from the functoriality of the
  principalization sequence).
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData Scheme.Hom Hironaka
  BlowUpSequence
open AlgebraicGeometry (comap_map_of_isClosedImmersion ker_blowUpMap_of_isClosedImmersion)

namespace Hironaka.Resolution

variable {X Y : Scheme.{u}}

/-! ### The strict transform of a pushed-forward ideal -/

/-- The strict transform under the blow-up of `D` of the kernel of a closed immersion `f` is the
kernel of the lift `blowUpMap f D` of `f` to the blow-ups. -/
theorem strictTransform_ker (f : Y ⟶ X) [IsClosedImmersion f] (D : X.IdealSheafData) :
    f.ker.strictTransform D = (Scheme.Hom.blowUpMap f D).ker :=
  (ker_blowUpMap_of_isClosedImmersion f D).symm

/-- The inverse image of `Z.map j` under `ι ≫ j`, for a closed immersion `j`, is the inverse image
of `Z` under `ι`. -/
theorem comap_map_comp {W : Scheme.{u}} (ι : W ⟶ Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (Z : Y.IdealSheafData) : (Z.map j).comap (ι ≫ j) = Z.comap ι := by
  rw [Scheme.IdealSheafData.comap_comp, comap_map_of_isClosedImmersion]

/-- The lift of a composite `ι ≫ j`, with `j` a closed immersion, to the blow-up of the image
`Z.map j` is the lift of `ι` to the blow-up of `Z` followed by the inclusion of blow-ups
`pushforwardBlowUp j Z`, up to the identification of the sources [Kol07, Definition 30, 30.3]. -/
theorem blowUpMap_comp_pushforwardBlowUp {W : Scheme.{u}} (ι : W ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion j] (Z : Y.IdealSheafData) :
    Scheme.Hom.blowUpMap (ι ≫ j) (Z.map j) =
      eqToHom (congrArg Scheme.IdealSheafData.blowUp (comap_map_comp ι j Z)) ≫
        Scheme.Hom.blowUpMap ι Z ≫ pushforwardBlowUp j Z := by
  symm
  apply eq_blowUpMap
  rw [Category.assoc, Category.assoc, pushforwardBlowUp_π, ← Category.assoc
      (Scheme.Hom.blowUpMap ι Z),
    blowUpMap_π, Category.assoc, ← Category.assoc,
    blowUpπ_eqToHom (comap_map_comp ι j Z)]

/-- One step of [Kol07, Definition 30, 30.2–30.3]: the strict transform of the image `I.map j`
under the blow-up of the image centre `Z.map j`, for a closed immersion `j`, is the image, along
the inclusion `pushforwardBlowUp j Z` of the blow-ups, of the strict transform of `I` under the
blow-up of `Z`. -/
theorem strictTransform_map (j : Y ⟶ X) [IsClosedImmersion j] (Z I : Y.IdealSheafData) :
    (I.map j).strictTransform (Z.map j) = (I.strictTransform Z).map (pushforwardBlowUp j Z) := by
  have h1 : I.map j = (I.subschemeι ≫ j).ker := rfl
  have h2 : I.strictTransform Z = (Scheme.Hom.blowUpMap I.subschemeι Z).ker := by
    rw [← strictTransform_ker, Scheme.IdealSheafData.ker_subschemeι]
  rw [h1, strictTransform_ker, h2, Scheme.IdealSheafData.map_ker,
    blowUpMap_comp_pushforwardBlowUp, Scheme.Hom.ker_comp_of_isIso]

/-- Along the pushforward of a sequence `S` along a closed immersion `j`, the strict transform of
`I.map j` is the image, along the stage inclusion, of the strict transform of `I` along `S`
[Kol07, Definition 30, 30.2–30.3]; the indices are given as `⟨n, hn⟩`. By induction on the
sequence, with `strictTransform_map` at the head. -/
theorem strictTransformSeq_pushforward_mk (S : BlowUpSequence Y) (j : Y ⟶ X)
    [IsClosedImmersion j] (I : Y.IdealSheafData) (n : ℕ) (hn : n < S.length + 1) :
    (S.pushforward j).strictTransformSeq (I.map j) (S.pushforwardStageIdx j ⟨n, hn⟩) =
      (S.strictTransformSeq I ⟨n, hn⟩).map (S.pushforwardStageHom j ⟨n, hn⟩) := by
  induction S generalizing X n with
  | nil Y => rfl
  | cons Y Z rest ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have := ih (pushforwardBlowUp j Z) (I.strictTransform Z) n (Nat.lt_of_succ_lt_succ hn)
      rw [← strictTransform_map] at this
      exact this

/-- The strict transform of a pushed-forward ideal sheaf along the pushed-forward sequence is the
image of the strict transform along the stage inclusion [Kol07, Definition 30, 30.2–30.3]. -/
theorem strictTransformSeq_pushforward (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (I : Y.IdealSheafData) (i : Fin (S.length + 1)) :
    (S.pushforward j).strictTransformSeq (I.map j) (S.pushforwardStageIdx j i) =
      (S.strictTransformSeq I i).map (S.pushforwardStageHom j i) := by
  obtain ⟨n, hn⟩ := i
  exact strictTransformSeq_pushforward_mk S j I n hn

/-! ### Order embeddings -/

/-- `map` along a closed immersion reflects and preserves inclusions
(`comap_map_of_isClosedImmersion`). -/
theorem map_le_map_iff_of_isClosedImmersion (j : Y ⟶ X) [IsClosedImmersion j]
    {A B : Y.IdealSheafData} : A.map j ≤ B.map j ↔ A ≤ B := by
  refine ⟨fun h => ?_, fun h => Scheme.IdealSheafData.map_mono j h⟩
  have := Scheme.IdealSheafData.comap_mono j h
  dsimp only at this
  rwa [comap_map_of_isClosedImmersion, comap_map_of_isClosedImmersion] at this

/-- `comap` along an isomorphism reflects and preserves inclusions. -/
theorem comap_le_comap_iff_of_isIso (φ : Y ⟶ X) [IsIso φ] {A B : X.IdealSheafData} :
    A.comap φ ≤ B.comap φ ↔ A ≤ B := by
  refine ⟨fun h => ?_, fun h => Scheme.IdealSheafData.comap_mono φ h⟩
  have := Scheme.IdealSheafData.comap_mono (inv φ) h
  dsimp only at this
  rwa [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id] at this

/-! ### The first-centre index along a pushforward -/

/-- The predicate "the `n`-th centre contains the strict transform" transports exactly along the
pushforward of a sequence along a closed immersion: the centres and strict transforms of the
pushforward are the images of those of `S`, and taking images is an order embedding. -/
theorem centerContains_pushforward_iff (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (I : Y.IdealSheafData) (n : ℕ) :
    CenterContains (S.pushforward j) (I.map j) n ↔ CenterContains S I n := by
  constructor
  · rintro ⟨hn, h⟩
    have hn' : n < S.length := by rwa [length_pushforward] at hn
    refine ⟨hn', ?_⟩
    have e1 : (S.pushforward j).center ⟨n, hn⟩ =
        (S.center ⟨n, hn'⟩).map (S.pushforwardStageHom j ⟨n, Nat.lt_succ_of_lt hn'⟩) :=
      center_pushforward_mk S j n hn'
    have e2 : (S.pushforward j).strictTransformSeq (I.map j) ⟨n, Nat.lt_succ_of_lt hn⟩ =
        (S.strictTransformSeq I ⟨n, Nat.lt_succ_of_lt hn'⟩).map
          (S.pushforwardStageHom j ⟨n, Nat.lt_succ_of_lt hn'⟩) :=
      strictTransformSeq_pushforward_mk S j I n (Nat.lt_succ_of_lt hn')
    rw [e1, e2] at h
    have := isClosedImmersion_pushforwardStageHom S j ⟨n, Nat.lt_succ_of_lt hn'⟩
    exact (map_le_map_iff_of_isClosedImmersion _).mp h
  · rintro ⟨hn, h⟩
    have hn' : n < (S.pushforward j).length := by rwa [length_pushforward]
    refine ⟨hn', ?_⟩
    have e1 : (S.pushforward j).center ⟨n, hn'⟩ =
        (S.center ⟨n, hn⟩).map (S.pushforwardStageHom j ⟨n, Nat.lt_succ_of_lt hn⟩) :=
      center_pushforward_mk S j n hn
    have e2 : (S.pushforward j).strictTransformSeq (I.map j) ⟨n, Nat.lt_succ_of_lt hn'⟩ =
        (S.strictTransformSeq I ⟨n, Nat.lt_succ_of_lt hn⟩).map
          (S.pushforwardStageHom j ⟨n, Nat.lt_succ_of_lt hn⟩) :=
      strictTransformSeq_pushforward_mk S j I n (Nat.lt_succ_of_lt hn)
    rw [e1, e2]
    have := isClosedImmersion_pushforwardStageHom S j ⟨n, Nat.lt_succ_of_lt hn⟩
    exact (map_le_map_iff_of_isClosedImmersion _).mpr h

/-- The first-centre index of the pushed-forward sequence for the pushed-forward ideal sheaf is
the first-centre index of the original. -/
theorem firstCenterIndex_pushforward (S : BlowUpSequence Y) (j : Y ⟶ X) [IsClosedImmersion j]
    (I : Y.IdealSheafData) :
    firstCenterIndex (S.pushforward j) (I.map j) = firstCenterIndex S I := by
  have hp : CenterContains (S.pushforward j) (I.map j) = CenterContains S I :=
    funext fun n => propext (centerContains_pushforward_iff S j I n)
  unfold firstCenterIndex
  rw [hp, length_pushforward]

/-! ### The first-centre index along an isomorphism -/

/-- The stage lifts of the pullback of a sequence along an isomorphism are isomorphisms (each is
the lift of an isomorphism to the blow-ups, `isIso_blowUpMap_of_isIso`). -/
theorem isIso_pullbackStageHom_mk (S : BlowUpSequence X) (φ : Y ⟶ X) [IsIso φ] (n : ℕ)
    (hn : n < S.length + 1) : IsIso (S.pullbackStageHom φ ⟨n, hn⟩) := by
  induction S generalizing Y n with
  | nil X => exact inferInstanceAs (IsIso φ)
  | cons X D rest ih =>
    cases n with
    | zero => exact inferInstanceAs (IsIso φ)
    | succ n =>
      have := isIso_blowUpMap_of_isIso φ D
      exact ih (Scheme.Hom.blowUpMap φ D) n (Nat.lt_of_succ_lt_succ hn)

/-- The predicate "the `n`-th centre contains the strict transform" transports exactly along the
pullback of a sequence along an isomorphism `φ`: centres and strict transforms of the pullback are
the inverse images of those of `S`, and inverse image along `φ` is an order embedding. -/
theorem centerContains_pullback_iff_of_isIso (S : BlowUpSequence X) (φ : Y ⟶ X) [IsIso φ]
    (I : X.IdealSheafData) (n : ℕ) :
    CenterContains (S.pullback φ) (I.comap φ) n ↔ CenterContains S I n := by
  have hflat : Flat φ := inferInstance
  constructor
  · rintro ⟨hn, h⟩
    have hn' : n < S.length := by rwa [length_pullback] at hn
    refine ⟨hn', ?_⟩
    have e1 : (S.pullback φ).center ⟨n, hn⟩ =
        (S.center ⟨n, hn'⟩).comap (S.pullbackStageHom φ ⟨n, Nat.lt_succ_of_lt hn'⟩) :=
      center_pullback_mk S φ n hn'
    have e2 : (S.pullback φ).strictTransformSeq (I.comap φ) ⟨n, Nat.lt_succ_of_lt hn⟩ =
        (S.strictTransformSeq I ⟨n, Nat.lt_succ_of_lt hn'⟩).comap
          (S.pullbackStageHom φ ⟨n, Nat.lt_succ_of_lt hn'⟩) :=
      strictTransformSeq_pullback_mk S φ I n (Nat.lt_succ_of_lt hn')
    rw [e1, e2] at h
    have := isIso_pullbackStageHom_mk S φ n (Nat.lt_succ_of_lt hn')
    exact (comap_le_comap_iff_of_isIso _).mp h
  · rintro ⟨hn, h⟩
    have hn' : n < (S.pullback φ).length := by rwa [length_pullback]
    refine ⟨hn', ?_⟩
    have e1 : (S.pullback φ).center ⟨n, hn'⟩ =
        (S.center ⟨n, hn⟩).comap (S.pullbackStageHom φ ⟨n, Nat.lt_succ_of_lt hn⟩) :=
      center_pullback_mk S φ n hn
    have e2 : (S.pullback φ).strictTransformSeq (I.comap φ) ⟨n, Nat.lt_succ_of_lt hn'⟩ =
        (S.strictTransformSeq I ⟨n, Nat.lt_succ_of_lt hn⟩).comap
          (S.pullbackStageHom φ ⟨n, Nat.lt_succ_of_lt hn⟩) :=
      strictTransformSeq_pullback_mk S φ I n (Nat.lt_succ_of_lt hn)
    rw [e1, e2]
    have := isIso_pullbackStageHom_mk S φ n (Nat.lt_succ_of_lt hn)
    exact (comap_le_comap_iff_of_isIso _).mpr h

/-- The first-centre index of the pullback of a sequence along an isomorphism, for the pulled-back
ideal sheaf, is the first-centre index of the original (the case of an automorphism of the
ambient space in the proof of [Kol07, Theorem 36]). -/
theorem firstCenterIndex_pullback_of_isIso (S : BlowUpSequence X) (φ : Y ⟶ X) [IsIso φ]
    (I : X.IdealSheafData) :
    firstCenterIndex (S.pullback φ) (I.comap φ) = firstCenterIndex S I := by
  have hp : CenterContains (S.pullback φ) (I.comap φ) = CenterContains S I :=
    funext fun n => propext (centerContains_pullback_iff_of_isIso S φ I n)
  unfold firstCenterIndex
  rw [hp, length_pullback]

/-! ### `BR_affine` along a closed embedding and along an isomorphism of the ambient triples -/

section BRAffine

variable {k : Type u} [Field k] [CharZero k]

/-- `BR_affine` is unchanged along a closed embedding of the ambient triples, granted that the
principalization sequences correspond: if `BP TA' = (BP TA).pushforward j` for a closed immersion
`j` of the ambients and `TA'.I = TA.I.map j`, then `BR_affine` built through `TA'` from the
embedding `emb ≫ j` equals `BR_affine` built in `TA` from `emb`. The first-centre index is the
same (`firstCenterIndex_pushforward`), truncation commutes with the pushforward, and restricting
a pushed-forward sequence to `X` gives back the restriction of the original. The hypothesis is
[Kol07, Theorem 35 (5)], supplied in `Hironaka.Resolution.Algebraic.Kol07.Thm36.Assembly`. -/
theorem BR_affine_comp_eq_of_BP_eq_pushforward (TA TA' : Triple k) (j : TA.X.left ⟶ TA'.X.left)
    [IsClosedImmersion j] (hBP : Hironaka.Sequence.BP TA' = (Hironaka.Sequence.BP TA).pushforward j)
    (hI : TA'.I = TA.I.map j) {X : Scheme.{u}} (emb : X ⟶ TA.X.left) :
    BR_affine TA' (emb ≫ j) = BR_affine TA emb := by
  unfold BR_affine
  rw [hBP, hI, firstCenterIndex_pushforward, ← pushforward_take, pullback_comp,
    pullback_pushforward]

/-- `BR_affine` is unchanged along an isomorphism of the ambient triples, granted that the
principalization sequences correspond: if `BP TA' = (BP TA).pullback φ` for an isomorphism `φ` of
the ambients and `TA'.I = TA.I.comap φ`, then `BR_affine TA' emb = BR_affine TA (emb ≫ φ)`. The
first-centre index is the same (`firstCenterIndex_pullback_of_isIso`), and truncation commutes with
the pullback. The hypothesis is [Kol07, Theorem 35 (4)] for the smooth surjection `φ`, supplied in
`Hironaka.Resolution.Algebraic.Kol07.Thm36.Assembly`. -/
theorem BR_affine_eq_of_BP_eq_pullback (TA TA' : Triple k) (φ : TA'.X.left ⟶ TA.X.left) [IsIso φ]
    (hBP : Hironaka.Sequence.BP TA' = (Hironaka.Sequence.BP TA).pullback φ)
    (hI : TA'.I = TA.I.comap φ) {X : Scheme.{u}} (emb : X ⟶ TA'.X.left) :
    BR_affine TA' emb = BR_affine TA (emb ≫ φ) := by
  unfold BR_affine
  rw [hBP, hI, firstCenterIndex_pullback_of_isIso, ← take_pullback, pullback_comp]

end BRAffine

end Hironaka.Resolution
