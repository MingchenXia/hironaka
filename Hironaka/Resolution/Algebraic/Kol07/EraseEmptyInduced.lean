/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.EraseEmptyConcat
public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
import Hironaka.Resolution.Algebraic.Kol07.RefineIrreducible
import Hironaka.Scheme.BlowUpSequence.DisjointUnion
import Hironaka.Scheme.BlowUpSequence.Functoriality
import Hironaka.Scheme.BlowUpSequence.InducedData
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.BlowUpSequence.WeakTransformFlat
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The induced data of an erased sequence

The empty blow-up convention [Kol07, 32] deletes the empty blow-ups of a sequence, and the second
clause of functoriality for smooth morphisms [Kol07, 34.1] reindexes: this is `eraseEmpty`, and
the last stage of `S.eraseEmpty` is only isomorphic to the last stage of `S`, through
`eraseEmptyLastHom` (`Hironaka/Scheme/BlowUpSequence/EraseEmptyConcat.lean`). This module transports
the induced data of [Kol07, Definition 66] along that isomorphism:

* `eraseEmptyLastHom_comp_composite`: the composite map of the erased sequence factors through
  the isomorphism and the composite map of the sequence;
* `isIso_eraseEmptyLastHom`: the isomorphism, as an instance;
* `weakTransformSeq_eraseEmpty_last`: for a smooth blow-up sequence of order `m`, the weak
  transform along the erased sequence is the inverse image of the weak transform along the
  sequence (the weak transform along an empty blow-up is the inverse image along its blow-up map,
  `weakTransform_top_left`, and weak transforms commute with the flat pull-back along the inverse
  of that map, `weakTransformSeq_pullback_of_isOrderSeq`);
* `strictTransformSeq_eraseEmpty_last`: the same for the strict transform of a divisor, with no
  order hypothesis (`strictTransform_top_left`, `strictTransformSeq_pullback`);
* `markedTransformSeq_eraseEmpty_last` (with `markedTransformSeq_last_congr`,
  `markedTransformSeq_eq_idx`): the marked analogue for a sequence of order `≥ m`
  (`markedTransform_top_left` and `markedTransformSeq_comap_pullbackStageHom_mk`), and
  `Hironaka.BMO.smooth_eraseEmptyLastHom'`, the smoothness of the isomorphism as a theorem.

The total transform needs more than an inverse image: the erased sequence's boundary has fewer
members (the exceptional member of an empty blow-up is the unit ideal, `exceptionalDivisor_top`).
That is the subject of `Hironaka/Resolution/Algebraic/Kol07/EraseEmptyEmbedding.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry Scheme IdealSheafData BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-! ### Transport along equalities of sequences and of stage indices -/

/-- The composite map of two equal sequences, through the `eqToHom` of their last stages. -/
theorem stageMap_last_congr {S S' : BlowUpSequence X} (e : S = S') :
    S.stageMap (Fin.last _) =
      eqToHom (congrArg BlowUpSequence.last e) ≫ S'.stageMap (Fin.last _) := by
  subst e
  exact (Category.id_comp _).symm

/-- The weak transform at the last stage of two equal sequences. -/
theorem weakTransformSeq_last_congr {S S' : BlowUpSequence X} (e : S = S') (I : X.IdealSheafData) :
    S.weakTransformSeq I (Fin.last _) =
      (S'.weakTransformSeq I (Fin.last _)).comap (eqToHom (congrArg BlowUpSequence.last e)) := by
  subst e
  exact (Scheme.IdealSheafData.comap_id _).symm

/-- The strict transform at the last stage of two equal sequences. -/
theorem strictTransformSeq_last_congr {S S' : BlowUpSequence X} (e : S = S')
    (J : X.IdealSheafData) :
    S.strictTransformSeq J (Fin.last _) =
      (S'.strictTransformSeq J (Fin.last _)).comap (eqToHom (congrArg BlowUpSequence.last e)) := by
  subst e
  exact (Scheme.IdealSheafData.comap_id _).symm

/-- The total transform at the last stage of two equal sequences. -/
theorem totalTransformSeq_last_congr {S S' : BlowUpSequence X} (e : S = S') (E : DivisorFamily X) :
    S.totalTransformSeq E (Fin.last _) =
      (S'.totalTransformSeq E (Fin.last _)).comap (eqToHom (congrArg BlowUpSequence.last e)) := by
  subst e
  exact (DivisorFamily.comap_id _).symm

/-- The stage map at two equal indices, through the `eqToHom` of the stages. -/
theorem stageMap_eq_idx (S : BlowUpSequence X) {i j : Fin (S.length + 1)} (e : i = j) :
    S.stageMap j = eqToHom (congrArg S.stage e.symm) ≫ S.stageMap i := by
  cases e
  rw [eqToHom_refl, Category.id_comp]

/-- The weak transform at two equal indices, through the `eqToHom` of the stages. -/
theorem weakTransformSeq_eq_idx (S : BlowUpSequence X) (I : X.IdealSheafData)
    {i j : Fin (S.length + 1)} (e : i = j) :
    S.weakTransformSeq I j =
      (S.weakTransformSeq I i).comap (eqToHom (congrArg S.stage e.symm)) := by
  cases e
  rw [eqToHom_refl, Scheme.IdealSheafData.comap_id]

/-- The strict transform at two equal indices, through the `eqToHom` of the stages. -/
theorem strictTransformSeq_eq_idx (S : BlowUpSequence X) (J : X.IdealSheafData)
    {i j : Fin (S.length + 1)} (e : i = j) :
    S.strictTransformSeq J j =
      (S.strictTransformSeq J i).comap (eqToHom (congrArg S.stage e.symm)) := by
  cases e
  rw [eqToHom_refl, Scheme.IdealSheafData.comap_id]

/-- `strictTransformSeq_pullback` at the last stage, along the last-stage lift. -/
theorem strictTransformSeq_pullback_last (S : BlowUpSequence X) (h : Y ⟶ X) [Flat h]
    (J : X.IdealSheafData) :
    (S.pullback h).strictTransformSeq (J.comap h) (Fin.last _) =
      (S.strictTransformSeq J (Fin.last _)).comap (S.pullbackLastHom h) := by
  refine (strictTransformSeq_eq_idx (S.pullback h) (J.comap h) (pullbackStageIdx_last S h)).trans ?_
  refine Eq.trans (congrArg (fun D : (S.pullback h).stage _ |>.IdealSheafData =>
    D.comap (eqToHom (congrArg (S.pullback h).stage (pullbackStageIdx_last S h).symm)))
    (strictTransformSeq_pullback S h J (Fin.last _))) ?_
  exact (Scheme.IdealSheafData.comap_comp _ _ _).symm

/-- The total transform at two equal indices, through the `eqToHom` of the stages. -/
theorem totalTransformSeq_eq_idx (S : BlowUpSequence X) (E : DivisorFamily X)
    {i j : Fin (S.length + 1)} (e : i = j) :
    S.totalTransformSeq E j =
      (S.totalTransformSeq E i).comap (eqToHom (congrArg S.stage e.symm)) := by
  cases e
  rw [eqToHom_refl, DivisorFamily.comap_id]

/-- The last-stage lift of `h` over the composite maps: `h_r ≫ Π = Π' ≫ h`
(`pullbackStageHom_stageMap` at the last index). -/
theorem pullbackLastHom_comp_composite (S : BlowUpSequence X) (h : Y ⟶ X) :
    S.pullbackLastHom h ≫ S.composite = (S.pullback h).composite ≫ h := by
  change (eqToHom (congrArg (S.pullback h).stage (pullbackStageIdx_last S h).symm) ≫
    S.pullbackStageHom h (Fin.last _)) ≫ S.stageMap (Fin.last _) =
      (S.pullback h).stageMap (Fin.last _) ≫ h
  rw [Category.assoc, pullbackStageHom_stageMap, ← Category.assoc,
    ← stageMap_eq_idx (S.pullback h) (pullbackStageIdx_last S h)]

/-- The composite map of a `cons` (definitional). -/
theorem composite_cons (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp) :
    (cons X D rest).composite = rest.composite ≫ D.blowUpπ := rfl

/-- The composite map of the empty sequence (definitional). -/
theorem composite_nil : (nil X).composite = 𝟙 X := rfl

/-! ### The composite map and the isomorphism -/

/-- The composite map of the erased sequence is the composite map of the sequence through the
last-stage isomorphism. -/
theorem composite_congr {S S' : BlowUpSequence X} (e : S = S') :
    S.composite = eqToHom (congrArg BlowUpSequence.last e) ≫ S'.composite := by
  subst e
  rw [eqToHom_refl, Category.id_comp]

theorem eraseEmptyLastHom_comp_composite : ∀ {X : Scheme.{u}} (S : BlowUpSequence X),
    S.eraseEmptyLastHom ≫ S.composite = S.eraseEmpty.composite
  | _, nil X => by
    change 𝟙 X ≫ 𝟙 X = 𝟙 X
    rw [Category.id_comp]
  | _, cons X D rest => by
    classical
    by_cases h : D = ⊤
    · have := isIso_blowUpπ_of_eq_top h
      have e := eraseEmpty_cons_of_eq_top rest h
      have ih := eraseEmptyLastHom_comp_composite rest
      have hp := pullbackLastHom_comp_composite rest.eraseEmpty (inv D.blowUpπ)
      calc (cons X D rest).eraseEmptyLastHom ≫ (cons X D rest).composite
          = (eqToHom (congrArg BlowUpSequence.last e) ≫
              rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫
                  rest.eraseEmptyLastHom) ≫
              (rest.composite ≫ D.blowUpπ) := by
            rw [eraseEmptyLastHom_cons_of_eq_top D rest h]
            rfl
        _ = eqToHom (congrArg BlowUpSequence.last e) ≫
              (rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ) ≫
                (rest.eraseEmptyLastHom ≫ rest.composite)) ≫ D.blowUpπ := by
            simp only [Category.assoc]
        _ = eqToHom (congrArg BlowUpSequence.last e) ≫
              ((rest.eraseEmpty.pullback (inv D.blowUpπ)).composite ≫ inv
                  D.blowUpπ) ≫
                D.blowUpπ := by
            rw [ih, hp]
        _ = eqToHom (congrArg BlowUpSequence.last e) ≫
              (rest.eraseEmpty.pullback (inv D.blowUpπ)).composite := by
            rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        _ = (cons X D rest).eraseEmpty.composite := (composite_congr e).symm
    · have e := eraseEmpty_cons_of_ne_top rest h
      have e₁ : (cons X D rest).eraseEmpty.last = rest.eraseEmpty.last :=
        congrArg BlowUpSequence.last e
      have ih := eraseEmptyLastHom_comp_composite rest
      calc (cons X D rest).eraseEmptyLastHom ≫ (cons X D rest).composite
          = (eqToHom e₁ ≫ rest.eraseEmptyLastHom) ≫ (rest.composite ≫ D.blowUpπ) := by
            rw [eraseEmptyLastHom_cons_of_ne_top D rest h]
            rfl
        _ = eqToHom e₁ ≫ (rest.eraseEmptyLastHom ≫ rest.composite) ≫ D.blowUpπ := by
            simp only [Category.assoc]
        _ = eqToHom e₁ ≫ (rest.eraseEmpty.composite ≫ D.blowUpπ) := by rw [ih]
        _ = (cons X D rest).eraseEmpty.composite := by
            rw [composite_congr e]
            rfl

/-- The last stage of the erased sequence is isomorphic to the last stage of the sequence. -/
theorem isIso_eraseEmptyLastHom : ∀ {X : Scheme.{u}} (S : BlowUpSequence X),
    IsIso S.eraseEmptyLastHom
  | _, nil X => by
    change IsIso (𝟙 X)
    infer_instance
  | _, cons X D rest => by
    classical
    by_cases h : D = ⊤
    · have := isIso_blowUpπ_of_eq_top h
      rw [eraseEmptyLastHom_cons_of_eq_top D rest h]
      have h1 : IsIso rest.eraseEmptyLastHom := isIso_eraseEmptyLastHom rest
      have h2 : IsIso (rest.eraseEmpty.pullbackLastHom (inv D.blowUpπ)) := by
        have h3 := isIso_pullbackStageHom_of_isIso rest.eraseEmpty (inv D.blowUpπ)
            (Fin.last _)
        exact @IsIso.comp_isIso _ _ _ _ _
          (eqToHom (congrArg (rest.eraseEmpty.pullback (inv D.blowUpπ)).stage
            (pullbackStageIdx_last rest.eraseEmpty (inv D.blowUpπ)).symm)) _
          (Iso.isIso_hom (eqToIso (congrArg (rest.eraseEmpty.pullback (inv
              D.blowUpπ)).stage
            (pullbackStageIdx_last rest.eraseEmpty (inv D.blowUpπ)).symm))) h3
      exact @IsIso.comp_isIso _ _ _ _ _
        (eqToHom (congrArg BlowUpSequence.last (eraseEmpty_cons_of_eq_top rest h))) _
        (Iso.isIso_hom (eqToIso (congrArg BlowUpSequence.last (eraseEmpty_cons_of_eq_top rest h))))
        (@IsIso.comp_isIso _ _ _ _ _ _ _ h2 h1)
    · rw [eraseEmptyLastHom_cons_of_ne_top D rest h]
      exact @IsIso.comp_isIso _ _ _ _ _
        (eqToHom (congrArg BlowUpSequence.last (eraseEmpty_cons_of_ne_top rest h))) _
        (Iso.isIso_hom (eqToIso (congrArg BlowUpSequence.last (eraseEmpty_cons_of_ne_top rest h))))
        (isIso_eraseEmptyLastHom rest)

instance (S : BlowUpSequence X) : IsIso S.eraseEmptyLastHom := isIso_eraseEmptyLastHom S

instance (S : BlowUpSequence X) : IsOpenImmersion S.eraseEmptyLastHom :=
  IsOpenImmersion.of_isIso _

/-! ### Weak and strict transforms along the erased sequence -/

/-- The inverse image along `inv π` of the inverse image along `π` is the identity. -/
theorem comap_comap_inv {Z W : Scheme.{u}} (π : Z ⟶ W) [IsIso π] (I : W.IdealSheafData) :
    (I.comap π).comap (inv π) = I := by
  rw [← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]

/-- Four inverse images, as one along the composite (the shape of the last-stage isomorphism of a
`cons` on a trivial blow-up: `eqToHom ≫ pullbackLastHom ≫ eraseEmptyLastHom`). -/
theorem comap_comap_comap_comap {A B C W Z : Scheme.{u}} (I : Z.IdealSheafData) (e : A ⟶ B)
    (f : B ⟶ C) (g : C ⟶ W) (h : W ⟶ Z) :
    (((I.comap h).comap g).comap f).comap e = I.comap (e ≫ (f ≫ g) ≫ h) := by
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
    Scheme.IdealSheafData.comap_comp]

/-- The same for divisor families. -/
theorem _root_.AlgebraicGeometry.Scheme.DivisorFamily.comap_comap_inv {Z W : Scheme.{u}}
    (π : Z ⟶ W) [IsIso π]
    (E : DivisorFamily W) : (E.comap π).comap (inv π) = E := by
  rw [← DivisorFamily.comap_comp, IsIso.inv_hom_id, DivisorFamily.comap_id]

/-- For a smooth blow-up sequence of order `m`, the weak transform at the end of the erased
sequence is the inverse image, along the last-stage isomorphism, of the weak transform at the end
of the sequence [Kol07, 32 and Definition 66]. -/
theorem weakTransformSeq_eraseEmpty_last {k : Type u} [Field k] [CharZero k] :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (f : X ⟶ Spec (.of k)) (n : ℕ)
      [SmoothOfRelativeDimension n f] (I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ)
      (_hS : S.IsOrderSeq f I E m),
      S.eraseEmpty.weakTransformSeq I (Fin.last _) =
        (S.weakTransformSeq I (Fin.last _)).comap S.eraseEmptyLastHom
  | _, nil X, _, _, _, I, _, _, _ => by
    change I = I.comap (𝟙 X)
    rw [Scheme.IdealSheafData.comap_id]
  | _, cons X D rest, f, n, _, I, E, m, hS => by
    classical
    obtain ⟨⟨hD, -, -⟩, ht⟩ := (isOrderSeq_cons_iff f I E m D rest).1 hS
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have ih := weakTransformSeq_eraseEmpty_last rest (D.blowUpπ ≫ f) n
        (I.weakTransform D)
      (E.totalTransform D) m ht
    by_cases h : D = ⊤
    · subst h
      have hiso : IsIso (⊤ : X.IdealSheafData).blowUpπ := isIso_blowUpπ_of_eq_top rfl
      have e := eraseEmpty_cons_of_eq_top rest rfl
      have h1 : rest.eraseEmpty.IsOrderSeq ((⊤ : X.IdealSheafData).blowUpπ ≫ f) (I.weakTransform ⊤)
          (E.totalTransform ⊤) m := IsOrderSeq.eraseEmpty ((⊤ : X.IdealSheafData).blowUpπ ≫ f) n ht
      have h2 := IsOrderSeq.pullback ((⊤ : X.IdealSheafData).blowUpπ ≫ f) n (inv
          (⊤ : X.IdealSheafData).blowUpπ)
          (d := 0) h1
      rw [IsIso.inv_hom_id_assoc] at h2
      have key := weakTransformSeq_pullback_of_isOrderSeq ((⊤ : X.IdealSheafData).blowUpπ ≫ f) n f n
        (inv (⊤ : X.IdealSheafData).blowUpπ) h1 h2 (Fin.last _)
      have hI : (I.weakTransform ⊤).comap (inv (⊤ : X.IdealSheafData).blowUpπ) = I := by
        rw [weakTransform_top_left, comap_comap_inv]
      rw [hI] at key
      rw [eraseEmptyLastHom_cons_of_eq_top ⊤ rest rfl, weakTransformSeq_last_congr e,
        weakTransformSeq_eq_idx _ I (pullbackStageIdx_last rest.eraseEmpty (inv
            (⊤ : X.IdealSheafData).blowUpπ)),
        key, ih]
      exact (comap_comap_comap_comap _ _ _ _ _).trans rfl
    · have e := eraseEmpty_cons_of_ne_top rest h
      rw [eraseEmptyLastHom_cons_of_ne_top D rest h, weakTransformSeq_last_congr e]
      change (rest.eraseEmpty.weakTransformSeq (I.weakTransform D) (Fin.last _)).comap _ =
        (rest.weakTransformSeq (I.weakTransform D) (Fin.last _)).comap _
      rw [ih]
      exact (Scheme.IdealSheafData.comap_comp _ _ _).symm

/-- The strict transform of a divisor at the end of the erased sequence is the inverse image,
along the last-stage isomorphism, of the strict transform at the end of the sequence
[Kol07, 32]. -/
theorem strictTransformSeq_eraseEmpty_last : ∀ {X : Scheme.{u}} (S : BlowUpSequence X)
    (J : X.IdealSheafData),
    S.eraseEmpty.strictTransformSeq J (Fin.last _) =
      (S.strictTransformSeq J (Fin.last _)).comap S.eraseEmptyLastHom
  | _, nil X, J => by
    change J = J.comap (𝟙 X)
    rw [Scheme.IdealSheafData.comap_id]
  | _, cons X D rest, J => by
    classical
    have ih := strictTransformSeq_eraseEmpty_last rest (J.strictTransform D)
    by_cases h : D = ⊤
    · subst h
      have hiso : IsIso (⊤ : X.IdealSheafData).blowUpπ := isIso_blowUpπ_of_eq_top rfl
      have e := eraseEmpty_cons_of_eq_top rest rfl
      have key := strictTransformSeq_pullback rest.eraseEmpty (inv (⊤ : X.IdealSheafData).blowUpπ)
        (J.strictTransform ⊤) (Fin.last _)
      have hJ : (J.strictTransform ⊤).comap (inv (⊤ : X.IdealSheafData).blowUpπ) = J := by
        rw [strictTransform_top_left, comap_comap_inv]
      rw [hJ] at key
      rw [eraseEmptyLastHom_cons_of_eq_top ⊤ rest rfl, strictTransformSeq_last_congr e,
        strictTransformSeq_eq_idx _ J (pullbackStageIdx_last rest.eraseEmpty (inv
            (⊤ : X.IdealSheafData).blowUpπ)),
        key, ih]
      exact (comap_comap_comap_comap _ _ _ _ _).trans rfl
    · have e := eraseEmpty_cons_of_ne_top rest h
      rw [eraseEmptyLastHom_cons_of_ne_top D rest h, strictTransformSeq_last_congr e]
      change (rest.eraseEmpty.strictTransformSeq (J.strictTransform D) (Fin.last _)).comap _ =
        (rest.strictTransformSeq (J.strictTransform D) (Fin.last _)).comap _
      rw [ih]
      exact (Scheme.IdealSheafData.comap_comp _ _ _).symm

/-! ### The marked transform along the erased sequence -/

/-- The marked transform at the end of a sequence, transported along an equality of sequences
(the marked analogue of `weakTransformSeq_last_congr`). -/
theorem markedTransformSeq_last_congr {S S' : BlowUpSequence X} (e : S = S')
    (I : X.IdealSheafData) (m : ℕ) :
    S.markedTransformSeq I m (Fin.last _) =
      (S'.markedTransformSeq I m (Fin.last _)).comap
        (eqToHom (congrArg BlowUpSequence.last e)) := by
  subst e
  exact (Scheme.IdealSheafData.comap_id _).symm

/-- The marked transform at a stage, transported along an equality of stage indices (the marked
analogue of `weakTransformSeq_eq_idx`). -/
theorem markedTransformSeq_eq_idx (S : BlowUpSequence X) (I : X.IdealSheafData) (m : ℕ)
    {i j : Fin (S.length + 1)} (e : i = j) :
    S.markedTransformSeq I m j =
      (S.markedTransformSeq I m i).comap (eqToHom (congrArg S.stage e.symm)) := by
  subst e
  exact (Scheme.IdealSheafData.comap_id _).symm

/-- For a smooth blow-up sequence of order `≥ m`, the marked transform at the end of the erased
sequence is the inverse image, along the last-stage isomorphism, of the marked transform at the
end of the sequence [Kol07, 32 and Definition 66]; the marked analogue of
`weakTransformSeq_eraseEmpty_last`. The marked transform under an empty blow-up is the inverse
image (`markedTransform_top_left`), and a marked transform along the pull-back by an isomorphism
is the inverse image of the marked transform (`markedTransformSeq_comap_pullbackStageHom_mk`). -/
theorem markedTransformSeq_eraseEmpty_last {k : Type u} [Field k] [CharZero k] :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (f : X ⟶ Spec (.of k)) (n : ℕ)
      [SmoothOfRelativeDimension n f] (I : X.IdealSheafData) (m : ℕ) (E : DivisorFamily X)
      (_hS : S.IsOrderGeSeq f I m E),
      S.eraseEmpty.markedTransformSeq I m (Fin.last _) =
        (S.markedTransformSeq I m (Fin.last _)).comap S.eraseEmptyLastHom
  | _, nil X, _, _, _, I, _, _, _ => by
    change I = I.comap (𝟙 X)
    rw [Scheme.IdealSheafData.comap_id]
  | _, cons X D rest, f, n, _, I, m, E, hS => by
    classical
    obtain ⟨⟨hD, -, -⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 hS
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) :=
      smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    have ih := markedTransformSeq_eraseEmpty_last rest (D.blowUpπ ≫ f) n
      (I.markedTransform D m) m (E.totalTransform D) ht
    by_cases h : D = ⊤
    · subst h
      have hiso : IsIso (⊤ : X.IdealSheafData).blowUpπ := isIso_blowUpπ_of_eq_top rfl
      have hoi : IsOpenImmersion (inv (⊤ : X.IdealSheafData).blowUpπ) := IsOpenImmersion.of_isIso _
      have hsm : Smooth (inv (⊤ : X.IdealSheafData).blowUpπ) := inferInstance
      have e := eraseEmpty_cons_of_eq_top rest rfl
      have h1 : rest.eraseEmpty.IsOrderGeSeq ((⊤ : X.IdealSheafData).blowUpπ ≫ f) (I.markedTransform
          ⊤ m) m
          (E.totalTransform ⊤) := IsOrderGeSeq.eraseEmpty ((⊤ : X.IdealSheafData).blowUpπ ≫ f) n ht
      have key : (rest.eraseEmpty.pullback (inv (⊤ : X.IdealSheafData).blowUpπ)).markedTransformSeq
            ((I.markedTransform ⊤ m).comap (inv (⊤ : X.IdealSheafData).blowUpπ)) m
            (rest.eraseEmpty.pullbackStageIdx (inv (⊤ : X.IdealSheafData).blowUpπ) (Fin.last _)) =
          (rest.eraseEmpty.markedTransformSeq (I.markedTransform ⊤ m) m (Fin.last _)).comap
            (rest.eraseEmpty.pullbackStageHom (inv (⊤ : X.IdealSheafData).blowUpπ) (Fin.last _)) :=
        IsOrderGeSeq.markedTransformSeq_comap_pullbackStageHom_mk ((⊤ : X.IdealSheafData).blowUpπ ≫
            f) n
          (inv (⊤ : X.IdealSheafData).blowUpπ) h1 _ (Nat.lt_succ_self _)
      have hI : (I.markedTransform ⊤ m).comap (inv (⊤ : X.IdealSheafData).blowUpπ) = I := by
        rw [markedTransform_top_left, comap_comap_inv]
      rw [hI] at key
      rw [eraseEmptyLastHom_cons_of_eq_top ⊤ rest rfl, markedTransformSeq_last_congr e,
        markedTransformSeq_eq_idx _ I m (pullbackStageIdx_last rest.eraseEmpty (inv
            (⊤ : X.IdealSheafData).blowUpπ)),
        key, ih]
      exact (comap_comap_comap_comap _ _ _ _ _).trans rfl
    · have e := eraseEmpty_cons_of_ne_top rest h
      rw [eraseEmptyLastHom_cons_of_ne_top D rest h, markedTransformSeq_last_congr e]
      change (rest.eraseEmpty.markedTransformSeq (I.markedTransform D m) m (Fin.last _)).comap _ =
        (rest.markedTransformSeq (I.markedTransform D m) m (Fin.last _)).comap _
      rw [ih]
      exact (Scheme.IdealSheafData.comap_comp _ _ _).symm

end Hironaka.Sequence

namespace Hironaka.BMO

open Hironaka.Sequence

/-- The last-stage isomorphism of an erased sequence is smooth (an isomorphism, hence an open
immersion); the form used by the marked order reduction. -/
theorem smooth_eraseEmptyLastHom' {X : Scheme.{u}} (S : BlowUpSequence X) :
    Smooth S.eraseEmptyLastHom := by
  have hiso : IsIso S.eraseEmptyLastHom := isIso_eraseEmptyLastHom S
  have hoi : IsOpenImmersion S.eraseEmptyLastHom := IsOpenImmersion.of_isIso _
  infer_instance

end Hironaka.BMO
