/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingClass
public import Hironaka.Resolution.Algebraic.OrderReduction.Step24ClosedEmbedding
public import Hironaka.Resolution.Algebraic.OrderReduction.Step2Functorial
public import Hironaka.Resolution.Algebraic.Stage.Tower
import Hironaka.Resolution.Algebraic.Kol07.AppendLast
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Clause3
import Hironaka.Resolution.Algebraic.OrderReduction.ClosedEmbedding
import Hironaka.Resolution.Algebraic.Stage.Coherence
import Hironaka.Scheme.BlowUpSequence.EqNilMarked
import Hironaka.Scheme.BlowUpSequence.PullbackInduced
import Hironaka.Scheme.BlowUpSequence.PullbackSnc
import Hironaka.Scheme.BlowUpSequence.Pushforward
import Hironaka.Scheme.BlowUpSequence.Restrict
import Hironaka.Scheme.IdealSheaf.Order.Basic
import Hironaka.Scheme.Smooth.ExceptionalBundle
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Claim 71.2, the hypersurface case

Kollár's Claim 71.2 [Kol07, Claim 71.2] says that for a closed embedding `τ : Y ↪ X` of smooth
schemes with `τ_*(𝒪_Y/J) = 𝒪_X/I`, `BMO_1(X, I, 1, ∅) = τ_* BMO_1(Y, J, 1, ∅)`. Its proof
[Kol07, 108] reduces it to the case of a **hypersurface** `Y ⊂ X` and proves that case in two lines:
every local equation of `Y` lies in `I`, so `max-ord I = 1`; hence
`BMO_{dim X,1}(X, I, 1, ∅) = BO_{dim X,1}(X, I, ∅)` by (107.3), and (103.3) gives
`BO_{dim X,1}(X, I, ∅) = τ_* BMO_{dim Y,1}(Y, J, 1, ∅)`. This module is that case for the stage
functors of the tower: `tower_bmo_one_eq_pushforward_of_isSmoothDivisor_ker`, under the hypothesis
that the kernel `j.ker` of the closed immersion is a smooth divisor (`IsSmoothDivisor`, which also
admits the empty divisor: an empty `Y`).

*The two printed steps and their forms in the library.* (107.3) is `eq_BO_of_maxOrd` of
`Hironaka.MarkedOrderReduction` (`E = ∅`, `max-ord I = m`), applied at `m = 1` to the marked family
of the stage `n + 1`, which is the assembly of Theorem 107 at `BO_{n+1,·}` (`tower_succ_bmo`);
`BO_{n+1,1}` is the functor of Theorem 103 at the data of Lemma 102 (`boOfBMO_functor`), evaluated
on the local class by `functor_seq_localClass` — `Y` is a hypersurface of maximal contact for
`(I, 1)` because `I = τ_*J` contains the equation of `Y` (`isMaximalContact_one_of_eq_map`,
`bOClass_one_of_eq_map`, `maxOrd_le_one_of_eq_map_smoothDivisor`). (103.3) is
`maxContactCase_bdData_eq_pushforward`: with `E = ∅` Step 2.1 of [Kol07, 104] is empty and Step 2.2
is the push-forward of [Kol07, Lemma 102 (3)], along `Y_r ↪ X_r = X`, of the amalgam of the
stage-`n` marked family at the triple `(Y_r, J, 1, (F_r − Y_r)|_{Y_r} + ⊤)`
(`closedEmbeddingTriple`); the amalgam at the mark `1` is `BMO_{n,1}` (`amalgam_seq`). Below the
mark (`max-ord I = 0`, i.e. `I = 𝒪_X`, so `J = 𝒪_Y`) both sides are the empty sequence
(`eq_nil_of_isOrderGeSeq_of_maxOrd_lt`).

*Three transports, none of them mathematics.* (i) The identity is stated along an abstract closed
immersion `j : Y ⟶ X`, the maximal-contact case along `Y.subschemeι`; the bridge is Mathlib's
isomorphism `j.toImage : Y ≅ V(ker j)` of a closed immersion onto its image
(`IsClosedImmersion.isIso_of_ker_eq`), composed with the identification `Y_r = V(ker j)`
(`subscheme_nth_zero_step22Triple`). Along this isomorphism the value of `BMO_{n,1}` is transported
by the first bullet of [Kol07, 34.1] (the field `commutesWithSmooth`: an isomorphism is a smooth
surjection), and a push-forward along an isomorphism inverts the pull-back
(`pushforward_pullback_of_isIso`). (ii) The boundary `(F_r − Y_r)|_{Y_r} + ⊤` of the triple of Lemma
102 (3) has every member equal to `⊤` when `E = ∅` (the exceptional part `F_r` of the empty Step 2.1
sequence is empty), whereas `Y`'s triple carries the empty family `E|_Y`: the two values agree by
the field `indifferentToEmptyMembers` along the unique order embedding from the empty index type.
(iii) Step 2.1's sequence is the empty sequence only propositionally (`step21Seq_val_eq_nil`); the
push-forward Lemma 102 (3) produces lives on its last scheme, and the concatenation with the empty
prefix is transported by substituting the equation inside the core lemma.

The general case (a chain of hypersurfaces, the identity being "a local question on `X`") is
`Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingStep` and
`Hironaka.Resolution.Algebraic.Stage.ClosedEmbeddingGeneral`; nothing here depends on it.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme IdealSheafData BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence Hironaka.BO Hironaka.BD

namespace Hironaka.Stage

open AlgebraicGeometry

section Transport

variable {X Y : Scheme.{u}}

end Transport

section Hypersurface

variable {k : Type u} [Field k] [CharZero k] {n : ℕ}

/-- The core of the hypersurface case ([Kol07, 108]: "(103.3) gives that
`BO_{dim X,1}(X, I, ∅) = τ_* BMO_{dim Y,1}(Y, J, 1, ∅)`"): the push-forward of
[Kol07, Lemma 102 (3)] of the amalgam of the stage-`n` marked family at the triple
`(Y_r, J, 1, (F_r − Y_r)|_{Y_r} + ⊤)`, prefixed by the (empty) Step 2.1 sequence, is the
push-forward along `j` of `BMO_{n,1}` at `Y`'s marked triple. Stated over an arbitrary Step 2.1
sequence `S₁` with `e₀ : S₁ = nil` (the shape of `step22_closedEmbedding_aux`) so that the
identification of `Y_r` with `Y`, the isomorphism `Y ≅ Y_r` (`j.toImage`), the first bullet of
[Kol07, 34.1] along it (the field `commutesWithSmooth`) and the deletion of the `⊤` boundary members
(the field `indifferentToEmptyMembers`) are all stated on the empty prefix. -/
theorem bmo_one_eq_pushforward_of_eq_nil_aux (bmo : ∀ m : ℕ, BMOData.{u} n m) (T : Triple k)
    {S₁ : BlowUpSequence T.X.left} (e₀ : S₁ = nil T.X.left)
    (hS₁ : S₁.IsOrderSeq (T.X.left ↘ Spec (.of k)) T.I T.E 1) (hE : IsEmpty T.E.ι)
    (TY : MarkedTriple k) (j : TY.X.left ⟶ T.X.left) [IsClosedImmersion j]
    (hjc : Triple.ClosedEmbedding T TY.toTriple j) (hm : TY.m = 1)
    (hsnc : ((S₁.exceptionalFamily T.E).append (S₁.strictTransformSeq j.ker (Fin.last _))).IsSnc)
    (h₀ : 0 < Fintype.card (step22TripleOfSeq T S₁ hS₁ hsnc).E.ι)
    (e : ((step22TripleOfSeq T S₁ hS₁ hsnc).E.nth ⟨0, h₀⟩).subscheme = j.ker.subscheme)
    (J : j.ker.subscheme.IdealSheafData) (hJ : IsNonzeroEverywhere J)
    (hJI : J.comap j.toImage = TY.I)
    (hCET : (hypersurfaceTriple (step22TripleOfSeq T S₁ hS₁ hsnc) h₀ (J.comap (eqToHom e))
      (isNonzeroEverywhere_comap_eqToHom e J hJ)).AmalgamClass n)
    (hTY : TY.BMOClass n 1) :
    S₁.concat (BlowUpSequence.pushforward (X := (step22TripleOfSeq T S₁ hS₁ hsnc).X.left)
      (Y := ((step22TripleOfSeq T S₁ hS₁ hsnc).E.nth ⟨0, h₀⟩).subscheme)
      ((amalgam bmo k).seq
        (hypersurfaceTriple (step22TripleOfSeq T S₁ hS₁ hsnc) h₀ (J.comap (eqToHom e))
          (isNonzeroEverywhere_comap_eqToHom e J hJ)) hCET)
      ((step22TripleOfSeq T S₁ hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι) =
      (((bmo 1).functor k).seq TY hTY).pushforward j := by
  subst e₀
  -- the member at position `0` of the Step 2.2 boundary is `Y`
  have hFcard : Fintype.card ((nil T.X.left).exceptionalFamily T.E).ι = 0 :=
    @Fintype.card_eq_zero _ _ ⟨fun a => hE.elim a.1⟩
  have eY : (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩ = j.ker := by
    have h1 := nth_append_last ((nil T.X.left).exceptionalFamily T.E)
      ((nil T.X.left).strictTransformSeq j.ker (Fin.last _)) (card_lt_card_ι_append _ _)
    have hidx : (⟨0, h₀⟩ :
        Fin (Fintype.card (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.ι)) =
        ⟨Fintype.card ((nil T.X.left).exceptionalFamily T.E).ι, card_lt_card_ι_append _ _⟩ :=
      Fin.ext hFcard.symm
    rw [hidx]
    exact h1
  -- the closed immersion `Y_r ↪ X` (its last scheme is `X` once Step 2.1 is empty)
  -- the isomorphism `Y ≅ Y_r`: `j.toImage` onto `V(ker j)`, then the identification with `Y_r`
  have hiso : IsIso j.toImage :=
    IsClosedImmersion.isIso_of_ker_eq j j.imageι j.toImage j.toImage_imageι
      (Scheme.IdealSheafData.ker_subschemeι _).symm
  have hiso' : IsIso (j.toImage ≫ eqToHom e.symm) := inferInstance
  have hci : IsClosedImmersion (j.toImage ≫ eqToHom e.symm) := inferInstance
  have hsm : Smooth (j.toImage ≫ eqToHom e.symm) := inferInstance
  have hsub : eqToHom e.symm ≫
      ((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι =
      j.ker.subschemeι :=
    eqToHom_subschemeι eY.symm
  have hjfac : @Eq (TY.X.left ⟶ (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).X.left)
      ((j.toImage ≫ eqToHom e.symm) ≫
        ((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι) j := by
    rw [Category.assoc, hsub]
    exact j.toImage_imageι
  -- the ideal transports: `J` restricted along the isomorphism is `TY.I`
  have hI' : (J.comap (eqToHom e)).comap (j.toImage ≫ eqToHom e.symm) = TY.I := by
    rw [← comap_comp, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, hJI]
  -- the structure morphism of `Y_r` is the restriction of that of `X`
  have hover₁ : ((hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀
      (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)).X.left ↘ Spec (.of k)) =
      ((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι ≫
        (T.X.left ↘ Spec (.of k)) :=
    congrArg (fun g : T.X.left ⟶ Spec (.of k) =>
      ((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι ≫ g)
      (Category.id_comp (T.X.left ↘ Spec (.of k)))
  have hover : (j.toImage ≫ eqToHom e.symm) ≫
      ((hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀ (J.comap (eqToHom e))
        (isNonzeroEverywhere_comap_eqToHom e J hJ)).X.left ↘ Spec (.of k)) =
      TY.X.left ↘ Spec (.of k) :=
    calc (j.toImage ≫ eqToHom e.symm) ≫
          ((hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀
            (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)).X.left ↘ Spec (.of k))
        = (j.toImage ≫ eqToHom e.symm) ≫
            ((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι ≫
              (T.X.left ↘ Spec (.of k)) :=
          congrArg (fun g => (j.toImage ≫ eqToHom e.symm) ≫ g) hover₁
      _ = ((j.toImage ≫ eqToHom e.symm) ≫
            ((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι) ≫
              (T.X.left ↘ Spec (.of k)) :=
          (Category.assoc _ _ _).symm
      _ = j ≫ (T.X.left ↘ Spec (.of k)) := congrArg (fun g => g ≫ (T.X.left ↘ Spec (.of k))) hjfac
      _ = TY.X.left ↘ Spec (.of k) := hjc.1
  -- the pulled-back marked triple of `Y`, with the (all-`⊤`) boundary of Lemma 102 (3)'s triple
  have hPF : PerfectField k := PerfectField.ofCharZero
  have hsmT : Smooth (((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι ≫
      (T.X.left ↘ Spec (.of k))) :=
    Eq.mp (congrArg (fun g => Smooth g) hover₁)
      (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀ (J.comap (eqToHom e))
        (isNonzeroEverywhere_comap_eqToHom e J hJ)).smooth
  have hsnc' : ((hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀
      (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)).E.comap
        (j.toImage ≫ eqToHom e.symm)).IsSnc :=
    isSnc_comap_of_smooth
      (((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι ≫
        (T.X.left ↘ Spec (.of k)))
      (j.toImage ≫ eqToHom e.symm) (hypersurfaceTriple _ h₀ _ _).isSnc
  set TY₁ : MarkedTriple k :=
    { TY with
      E := (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀
        (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)).E.comap
          (j.toImage ≫ eqToHom e.symm)
      isSnc := hsnc' } with hTY₁def
  have hpb : MarkedTriple.IsPullbackOf TY₁
      (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀ (J.comap (eqToHom e))
        (isNonzeroEverywhere_comap_eqToHom e J hJ)) (j.toImage ≫ eqToHom e.symm) :=
    ⟨⟨hover, hI'.symm, rfl⟩, hm⟩
  have hTY₁ : MarkedTriple.BMOClass n 1 TY₁ := ⟨le_rfl, hTY.2.1, hm⟩
  have hCET₁ : MarkedTriple.BMOClass n 1 (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁
      hsnc) h₀ (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)) :=
    bmoClass_of_amalgamClass k hCET
  -- Kollár 34.1, first bullet, along the isomorphism
  have hsm'' : @Smooth TY₁.X.left
      (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀ (J.comap (eqToHom e))
        (isNonzeroEverywhere_comap_eqToHom e J hJ)).X.left (j.toImage ≫ eqToHom e.symm) := hsm
  have hiso'' : @IsIso Scheme.{u} _ TY₁.X.left
      (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀ (J.comap (eqToHom e))
        (isNonzeroEverywhere_comap_eqToHom e J hJ)).X.left (j.toImage ≫ eqToHom e.symm) := hiso'
  have hcw : ((bmo 1).functor k).seq TY₁ hTY₁ =
      (((bmo 1).functor k).seq (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀
        (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)) hCET₁).pullback
          (j.toImage ≫ eqToHom e.symm) :=
    seq_eq_pullback_of_isIso ((bmo 1).commutesWithSmooth k).1
      (T := hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀
        (J.comap (eqToHom e))
        (isNonzeroEverywhere_comap_eqToHom e J hJ)) (T' := TY₁) (j.toImage ≫ eqToHom e.symm) hpb
      hCET₁ hTY₁
  -- the `⊤` boundary members are deleted
  have hEY : IsEmpty TY.E.ι := by
    rw [hjc.2.2]
    exact hE
  have hsub2 : ∀ x y : (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.ι, x = y := by
    intro x y
    rcases x with x | ⟨⟩ <;> rcases y with y | ⟨⟩
    · exact hE.elim x.1
    · exact hE.elim x.1
    · exact hE.elim y.1
    · rfl
  have hcomp : ∀ b, (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀
      (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)).E.component b = ⊤ := by
    intro b
    rcases b with b | ⟨⟩
    · exact (b.2 (hsub2 _ _)).elim
    · rfl
  have hind : ((bmo 1).functor k).seq TY₁ hTY₁ = ((bmo 1).functor k).seq TY hTY :=
    (bmo 1).indifferentToEmptyMembers k TY₁ TY.E TY.isSnc OrderEmbedding.ofIsEmpty
      (fun i => hEY.elim i) (fun b _ => by
        change ((hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀
          (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)).E.component b).comap
            (j.toImage ≫ eqToHom e.symm) = ⊤
        rw [hcomp b, comap_top]) hTY₁ hTY
  -- assembly: the pushforward along `j = (Y ≅ Y_r) ≫ (Y_r ↪ X)`
  have hcij : @IsClosedImmersion TY.X.left (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).X.left j :=
    ‹IsClosedImmersion j›
  have hTYseq : ((bmo 1).functor k).seq TY hTY =
      (((bmo 1).functor k).seq (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀
        (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)) hCET₁).pullback
          (j.toImage ≫ eqToHom e.symm) :=
    hind.symm.trans hcw
  have hpush : BlowUpSequence.pushforward (X := (step22TripleOfSeq T (nil T.X.left) hS₁
      hsnc).X.left) (Y := ((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subscheme)
      (((bmo 1).functor k).seq (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc) h₀
        (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)) hCET₁)
      ((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι =
      BlowUpSequence.pushforward (X := (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).X.left)
        (Y := TY.X.left) (((bmo 1).functor k).seq TY hTY) j :=
    (congrArg (fun R => BlowUpSequence.pushforward
        (X := (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).X.left)
        (Y := ((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subscheme) R
        ((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι)
      (pushforward_pullback_of_isIso (j.toImage ≫ eqToHom e.symm)
        (((bmo 1).functor k).seq (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc)
          h₀ (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)) hCET₁)).symm).trans
    ((pushforward_comp
        ((((bmo 1).functor k).seq (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc)
          h₀ (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)) hCET₁).pullback
            (j.toImage ≫ eqToHom e.symm))
        (j.toImage ≫ eqToHom e.symm)
        ((step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).E.nth ⟨0, h₀⟩).subschemeι).trans
      ((pushforward_congr
        ((((bmo 1).functor k).seq (hypersurfaceTriple (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc)
          h₀ (J.comap (eqToHom e)) (isNonzeroEverywhere_comap_eqToHom e J hJ)) hCET₁).pullback
            (j.toImage ≫ eqToHom e.symm)) hjfac).trans
        (congrArg (fun R : BlowUpSequence TY.X.left => BlowUpSequence.pushforward
          (X := (step22TripleOfSeq T (nil T.X.left) hS₁ hsnc).X.left)
          (Y := TY.X.left) R j) hTYseq.symm)))
  exact hpush

/-- The hypersurface case of Claim 71.2 [Kol07, 108]: for a closed embedding `j : Y ↪ X` of smooth
`k`-schemes whose kernel is a smooth divisor (`Y` a hypersurface of `X`, or empty),
`τ_*(𝒪_Y/J) = 𝒪_X/I` (`MarkedTriple.ClosedEmbedding`), `E = ∅` and the mark `1`, the stage-`(n + 1)`
functor of the tower at `X` is the push-forward along `j` of its value at `Y`. Kollár's argument:
every local equation of `Y` lies in `I`, so `max-ord I = 1`, the marked and unmarked functors agree
by (107.3), and (103.3) gives the push-forward. The stage `n + 1` is the assembly of Theorem 107 at
`BO_{n+1,·}` (`tower_succ_bmo`); `Y`'s value is taken at the stage `n` (its dimension is `≤ n`) and
moved to the stage `n + 1` by the coherence of the tower (`tower_bmo_coherent`). When `I = 𝒪_X`
(`max-ord I = 0`) both sides are the empty sequence. -/
theorem tower_bmo_one_eq_pushforward_of_isSmoothDivisor_ker (base : OrderReductionStage.{u} 0)
    (TX TY : MarkedTriple k) (j : TY.X.left ⟶ TX.X.left) [IsClosedImmersion j]
    (hj : MarkedTriple.ClosedEmbedding TX TY j) (hE : IsEmpty TX.E.ι)
    (hTX : TX.BMOClass (n + 1) 1) (hY : IsSmoothDivisor j.ker) :
    (((tower base (n + 1)).bmo 1).functor k).seq TX hTX =
      ((((tower base (n + 1)).bmo 1).functor k).seq TY
        (bmoClass_of_closedEmbedding hj hTX)).pushforward j := by
  obtain ⟨T, m⟩ := TX
  obtain rfl : m = 1 := hTX.2.2
  have hjc : Triple.ClosedEmbedding T TY.toTriple j := hj.1
  have hm : TY.m = 1 := hj.2
  have hn : T.HasDimLE (n + 1) := hTX.2.1
  have hiso : IsIso j.toImage :=
    IsClosedImmersion.isIso_of_ker_eq j j.imageι j.toImage j.toImage_imageι
      (Scheme.IdealSheafData.ker_subschemeι _).symm
  -- `J` on the image `V(ker j)`: `TY.I` transported along the isomorphism
  have hJ : IsNonzeroEverywhere (TY.I.comap (inv j.toImage)) :=
    isNonzeroEverywhere_comap_of_flat _ TY.isNonzeroEverywhere
  have hJI : (TY.I.comap (inv j.toImage)).comap j.toImage = TY.I := by
    rw [← comap_comp, IsIso.hom_inv_id, comap_id]
  have hmapJ : TY.I.map j.toImage = TY.I.comap (inv j.toImage) := by
    conv_lhs => rw [← hJI]
    exact map_comap_of_ker_le j.toImage _ (by rw [Scheme.Hom.ker_eq_bot_of_isIso]; exact bot_le)
  have hIJ : T.I = (TY.I.comap (inv j.toImage)).map j.ker.subschemeι := by
    rw [hjc.2.1, ← hmapJ, ← map_comp, j.toImage_imageι]
  -- `(X, I, ∅)` is in the class of `BO_{n+1,1}` with `Y` of maximal contact
  have hT : Triple.BOClass (n + 1) 1 T := bOClass_one_of_eq_map T hn hY hIJ
  have hle := isMaximalContact_one_of_eq_map T _ hIJ
  have hmax₁ := maxOrd_le_one_of_eq_map_smoothDivisor T hY hIJ
  by_cases h1 : T.I.maxOrd = ((1 : ℕ) : ℕ∞)
  · -- Kollár's case `max-ord I = 1`
    have e := subscheme_nth_zero_step22Triple T hn hmax₁ (fun m j =>
      Hironaka.BD.bdData (n + 1) m j (amalgamDom n) (fun k _ _ => amalgam (tower base n).bmo k)
        (fun k _ _ T' hd hm => amalgamClass_of_tuningParam k m T' hd hm)
        (fun k _ _ T' hT' => amalgam_maxOrd_endTriple_lt (tower base n).bmo k T' hT')
        (fun k _ _ => amalgam_commutesWithSmooth (tower base n).bmo k)
        (fun k _ _ _ _ _ σ => amalgam_commutesWithBaseChange (tower base n).bmo k σ))
      le_rfl hY hle hE
    -- `Y` has dimension `≤ n`: it is isomorphic to `Y_r`, of dimension `≤ (n + 1) − 1`
    have hci : IsClosedImmersion (j.toImage ≫ eqToHom e.symm) := inferInstance
    have hdimTY : TY.toTriple.HasDimLE n :=
      @hasDimLE_of_closedEmbedding k _ _ (closedEmbeddingTriple T hn hmax₁ (fun m j =>
        Hironaka.BD.bdData (n + 1) m j (amalgamDom n) (fun k _ _ => amalgam (tower base n).bmo k)
          (fun k _ _ T' hd hm => amalgamClass_of_tuningParam k m T' hd hm)
          (fun k _ _ T' hT' => amalgam_maxOrd_endTriple_lt (tower base n).bmo k T' hT')
          (fun k _ _ => amalgam_commutesWithSmooth (tower base n).bmo k)
          (fun k _ _ _ _ _ σ => amalgam_commutesWithBaseChange (tower base n).bmo k σ))
        hY hle hE _ hJ).toTriple TY.toTriple (j.toImage ≫ eqToHom e.symm) hci _
        (hasDimLE_closedEmbeddingTriple T hn hmax₁ _ hY hle hE _ hJ)
    have hTYn : TY.BMOClass n 1 := ⟨le_rfl, hdimTY, hm⟩
    rw [tower_bmo_coherent base 1 (Nat.le_succ n) TY _ hTYn]
    refine (Hironaka.BMO.eq_BO_of_maxOrd (boOfBMO (tower base n).bmo) T hT hE h1).trans ?_
    rw [boOfBMO_functor, functor_seq_localClass _ _ _ T hT hY hle,
      maxContactCase_bdData_eq_pushforward T hY _ hJ hIJ hn hE (amalgamDom n)
        (fun k _ _ => amalgam (tower base n).bmo k)
        (fun m k _ _ T' hd hm => amalgamClass_of_tuningParam k m T' hd hm)
        (fun k _ _ T' hT' => amalgam_maxOrd_endTriple_lt (tower base n).bmo k T' hT')
        (fun k _ _ => amalgam_commutesWithSmooth (tower base n).bmo k)
        (fun k _ _ _ _ _ σ => amalgam_commutesWithBaseChange (tower base n).bmo k σ)]
    exact bmo_one_eq_pushforward_of_eq_nil_aux (tower base n).bmo T
      (step21Seq_val_eq_nil T hn hE hmax₁ _) (isOrderSeq_step21Seq T hn hmax₁ _ _) hE TY j hjc hm
      _ _ e _ hJ hJI _ hTYn
  · -- below the mark: `I = 𝒪_X`, `J = 𝒪_Y`, both sides empty
    have hlt : T.I.maxOrd < ((1 : ℕ) : ℕ∞) := lt_of_le_of_ne hmax₁ h1
    have hTtop : T.I = ⊤ := by
      refine eq_top_of_maxOrd_le_zero T.I ?_
      have h0 : T.I.maxOrd = 0 := Order.lt_one_iff.mp (by exact_mod_cast hlt)
      rw [h0]
      exact_mod_cast le_rfl
    have hTYtop : TY.I = ⊤ := by
      have h := comap_map_of_isClosedImmersion j TY.I
      rw [← hjc.2.1, hTtop, comap_top] at h
      exact h.symm
    have hL : (((tower base (n + 1)).bmo 1).functor k).seq ⟨T, 1⟩ hTX = nil T.X.left :=
      eq_nil_of_isOrderGeSeq_of_maxOrd_lt (T.X.left ↘ Spec (.of k))
        ((((tower base (n + 1)).bmo 1).functor k).isOrderGeSeq ⟨T, 1⟩ hTX)
        ((((tower base (n + 1)).bmo 1).functor k).noEmptyCenters ⟨T, 1⟩ hTX) hlt
    have hR : (((tower base (n + 1)).bmo 1).functor k).seq TY
        (bmoClass_of_closedEmbedding hj hTX) = nil TY.X.left := by
      refine eq_nil_of_isOrderGeSeq_of_maxOrd_lt (TY.X.left ↘ Spec (.of k))
        ((((tower base (n + 1)).bmo 1).functor k).isOrderGeSeq TY _)
        ((((tower base (n + 1)).bmo 1).functor k).noEmptyCenters TY _) ?_
      rw [hTYtop, hm]
      have h0 : (⊤ : TY.X.left.IdealSheafData).maxOrd ≤ 0 :=
        (maxOrd_le_iff _).mpr fun x => by simp
      exact lt_of_le_of_lt h0 (by norm_num)
    rw [hL, hR, pushforward_nil]

end Hypersurface

end Hironaka.Stage
