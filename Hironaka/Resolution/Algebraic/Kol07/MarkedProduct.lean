/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.Basic
import Hironaka.Scheme.BlowUp.Transform.StrictTransform
import Hironaka.Scheme.BlowUpSequence.InducedData
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Definition 60 iterated along a sequence: `Π^* I = I_r · ∏ Π^*_{r,j+1} F_j^m`

Along a blow-up sequence of order `≥ m` starting with the marked ideal `(I, m)`, each step
satisfies `F_{j+1}^m · (I_{j+1}, m) = π_j^* I_j` [Kol07, Definition 60, (60.1)], so the pull-back
of `I` to the end result is the last marked transform times the product of the exceptional
divisors of the steps, each pulled back along the later steps `Π_{r,j+1}` and raised to the mark:
`Π^* I = I_r · ∏_{j<r} Π_{r,j+1}^* F_j^m`. This module proves that identity for every sequence and
every mark `m` from the divisibilities `F_{j+1}^m ∣ π_j^* I_j` alone (a general fact of the
`markedTransformSeq` recursion). The principalization theorem applies it at `m = 1` to the marked
order reduction functor, where `I_r = 𝒪` (Theorem 69 (1), `max-ord I_r < 1`), which gives Kollár's
explicit monomial formula for `Π^* I` in the proof of Theorem 35 [Kol07, 72].

* `exceptionalAt_pow_mul_markedTransformSeq_succ`: (60.1) at stage `i` of a sequence.
* `stageMapBetween_zero_comp_eqToHom`: `Π_{i,0}` followed by the cast `X_0 = X` is `Π_i`.
* `dvd_of_comap_eqToHom_dvd`: divisibility of ideal sheaves is reflected by the cast along an
  equality of schemes.
* `comap_composite_eq_markedTransformSeq_last_mul_prod`: the iterated formula.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry Scheme.IdealSheafData Scheme BlowUpSequence

namespace Hironaka.Sequence

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-- Formula (60.1) of [Kol07, Definition 60] at stage `i` of a sequence (the recursion (2) of
[Kol07, Warning 63]): when `F_{i+1}^m` divides `π_i^* I_i`,
`F_{i+1}^m · (I_{i+1}, m) = π_i^* I_i`. -/
theorem exceptionalAt_pow_mul_markedTransformSeq_succ (S : BlowUpSequence X)
    (I : X.IdealSheafData) (m : ℕ) (i : Fin S.length)
    (h : S.exceptionalAt i ^ m ∣ (S.markedTransformSeq I m i.castSucc).comap (S.step i)) :
    S.exceptionalAt i ^ m * S.markedTransformSeq I m i.succ =
      (S.markedTransformSeq I m i.castSucc).comap (S.step i) := by
  rw [markedTransformSeq_succ]
  exact pow_mul_colon_of_dvd _ _ _ h

/-- `Π_{i,0}` followed by the cast `X_0 = X` (`stage_zero`) is the partial composite `Π_i`
("`Π_i := Π_{i0}`", [Kol07, Definition 29]), on either shape of the sequence. -/
theorem stageMapBetween_zero_comp_eqToHom :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (i : Fin (S.length + 1)),
      S.stageMapBetween i 0 (Fin.zero_le i) ≫ eqToHom (stage_zero S) = S.stageMap i
  | _, nil _, _ => Category.comp_id _
  | _, cons _ _ _, i => by
    rcases i with ⟨_ | j, hi⟩ <;> exact Category.comp_id _

/-- Divisibility of ideal sheaves is reflected by the inverse image along the cast `eqToHom e`
of an equality of schemes. -/
theorem dvd_of_comap_eqToHom_dvd {W V : Scheme.{u}} (e : W = V) {A B : V.IdealSheafData}
    (h : A.comap (eqToHom e) ∣ B.comap (eqToHom e)) : A ∣ B := by
  subst e
  rwa [eqToHom_refl, comap_id, comap_id] at h

/-- Definition 60 iterated along a sequence, the formula behind [Kol07, 72]: when each step
satisfies `F_{j+1}^m ∣ π_j^* I_j` (so that Definition 60 applies, `(I_{j+1}, m) = π_j^* I_j / F^m`),
the pull-back of `I` to the end result is the last marked transform times the product over the
steps of the exceptional divisors, pulled back along the later steps and raised to the mark:
`Π^* I = I_r · ∏_{j<r} (Π_{r,j+1}^* F_j)^m`. By induction on the sequence: the first step is
Definition 60 on `X`, the tail is the induction hypothesis on `(π_0)_*^{-1}(I, m)`, and the
`j = 0` factor of the product is `F_1^m` pulled back along `Π_{r,1}`, the composite of the tail. -/
theorem comap_composite_eq_markedTransformSeq_last_mul_prod :
    ∀ {X : Scheme.{u}} (S : BlowUpSequence X) (I : X.IdealSheafData) (m : ℕ),
      (∀ i : Fin S.length,
        S.exceptionalAt i ^ m ∣ (S.markedTransformSeq I m i.castSucc).comap (S.step i)) →
      I.comap S.composite = S.markedTransformSeq I m (Fin.last _) *
        ∏ j : Fin S.length,
          (S.exceptionalAt j ^ m).comap (S.stageMapBetween (Fin.last _) j.succ (Fin.le_last _))
  | _, nil X, I, m, _ => by
    change I.comap (𝟙 X) = _
    rw [comap_id, Finset.prod_eq_one (s := (Finset.univ : Finset (Fin (nil X).length)))
      (f := fun j => ((nil X).exceptionalAt j ^ m).comap
        ((nil X).stageMapBetween (Fin.last _) j.succ (Fin.le_last _)))
      (fun j _ => Fin.elim0 j), mul_one]
    rfl
  | _, cons X D rest, I, m, h => by
    -- Definition 60 at the first step, carried back across the cast `X_1 = D.blowUp`
    have h0 := h ⟨0, Nat.succ_pos _⟩
    change (D.comap (eqToHom (stage_zero rest) ≫ D.blowUpπ)) ^ m ∣
      I.comap (eqToHom (stage_zero rest) ≫ D.blowUpπ) at h0
    rw [comap_comp, comap_comp, ← comap_pow] at h0
    have hdvd : D.exceptionalDivisor ^ m ∣ I.comap D.blowUpπ :=
      dvd_of_comap_eqToHom_dvd (stage_zero rest) h0
    have hstep : I.comap D.blowUpπ = D.exceptionalDivisor ^ m * I.markedTransform D m :=
      (pow_mul_markedTransform D I m hdvd).symm
    -- the induction hypothesis on the tail, started at `(π_0)_*^{-1}(I, m)`
    have hrest : ∀ i : Fin rest.length, rest.exceptionalAt i ^ m ∣
        (rest.markedTransformSeq (I.markedTransform D m) m i.castSucc).comap (rest.step i) := by
      intro i
      obtain ⟨j, hj⟩ := i
      exact h ⟨j + 1, Nat.succ_lt_succ hj⟩
    have ih := comap_composite_eq_markedTransformSeq_last_mul_prod rest
      (I.markedTransform D m) m hrest
    -- the `j = 0` factor: `F_1^m` pulled back along the composite of the tail (in the tail's own
    -- vocabulary first, then transported to the `cons` shape by definitional unfolding)
    have hzero' : (D.exceptionalDivisor.comap (eqToHom (stage_zero rest)) ^ m).comap
        (rest.stageMapBetween (Fin.last _) 0 (Fin.zero_le _)) =
        (D.exceptionalDivisor ^ m).comap rest.composite := by
      rw [← comap_pow, ← comap_comp, stageMapBetween_zero_comp_eqToHom]
      rfl
    have hzero : ((cons X D rest).exceptionalAt (0 : Fin (rest.length + 1)) ^ m).comap
        ((cons X D rest).stageMapBetween (Fin.last _) (Fin.succ (0 : Fin (rest.length + 1)))
          (Fin.le_last _)) =
        (D.exceptionalDivisor ^ m).comap rest.composite := by
      have e1 : (cons X D rest).exceptionalAt (0 : Fin (rest.length + 1)) =
          D.exceptionalDivisor.comap (eqToHom (stage_zero rest)) :=
        exceptionalAt_cons_zero D rest
      rw [e1]
      exact hzero'
    -- assemble
    change I.comap (rest.composite ≫ D.blowUpπ) =
      (cons X D rest).markedTransformSeq I m (Fin.last _) *
        ∏ j : Fin (rest.length + 1), ((cons X D rest).exceptionalAt j ^ m).comap
          ((cons X D rest).stageMapBetween (Fin.last _) j.succ (Fin.le_last _))
    rw [Fin.prod_univ_succ, comap_comp, hstep, comap_mul, ih]
    refine (mul_left_comm _ _ _).trans ?_
    exact congrArg (fun J : ((cons X D rest).stage (Fin.last _)).IdealSheafData =>
      (cons X D rest).markedTransformSeq I m (Fin.last _) *
        (J * ∏ i : Fin rest.length, ((cons X D rest).exceptionalAt i.succ ^ m).comap
          ((cons X D rest).stageMapBetween (Fin.last _) i.succ.succ (Fin.le_last _)))) hzero.symm

end Hironaka.Sequence
