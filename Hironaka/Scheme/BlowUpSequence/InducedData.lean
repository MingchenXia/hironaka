/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUpSequence.FunctorVocabulary
public import Hironaka.Scheme.Snc.Basic
import Hironaka.Scheme.BlowUpSequence.SmoothCenter
import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# The ideals and divisors induced along a blow-up sequence

[Kol07, Definition 66] attaches to a smooth blow-up sequence `S` starting with a triple `(X, I, E)`
the induced data `(X_i, I_i, E_i)`: `X_i = S.stage i`, `I_i = S.weakTransformSeq I i` (the
unmarked birational transforms of condition (1)) or `S.markedTransformSeq I m i` (the marked ones
of condition (1′), [Kol07, Warning 63]), and `E_i = S.totalTransformSeq E i`. This module proves
their recursion equations, the description of the marked transform as a colon ideal, the recursion
of the order predicates, and the nonvanishing of the induced ideals on the components of the
stages.

**The recursion.** The three sequences are defined by the same structural recursion on the list
of centers: at `nil X` everything is the initial datum; on `cons X D rest` the index `0` returns
the initial datum and the index `j + 1` recurses into the tail with the datum transformed once
along the first blow-up (`weakTransform D`, `markedTransform D · m`,
`DivisorFamily.totalTransform · D`). So the equations on the constructor shapes are `rfl`.
Kollár's formula on a *variable* sequence, `I_{i+1} = (π_i)_*^{-1} I_i`, needs the stage-`i+1`
data expressed through `π_i = S.step i` and `F_{i+1} = S.exceptionalAt i`, whose types are the
stages; it is proved by induction on the sequence with the index in the form `⟨j, h⟩`, and at
index `0` on the `cons` shape by a case split on the tail's constructor, after which the cast
`eqToHom (stage_zero rest)` in `step_cons_zero` is `eqToHom rfl = 𝟙` and the two sides agree
definitionally (the total transform along a morphism `DivisorFamily.totalTransformAlong` being
the shape of the recursion step).

**The marked transform.** `markedTransform Z I m = (π^* I : F^m)` is Kollár's `𝒪(mF) · π^* I`
[Kol07, Definition 60]: when `F^m` divides `π^* I`, `F^m · (π^* I : F^m) = π^* I`, and this
determines the quotient because `F` is invertible (`blowUp.isInvertible_comap_π`).

**The order predicates.** `IsOrderSeq` and `IsOrderGeSeq` are `∀ i` over the recursions together
with `IsSmooth`; their recursion on the `cons` shape is read off index by index, exactly as
`isSmooth_cons_iff` is proved in `Hironaka/Scheme/BlowUpSequence/Basic.lean`.

**Nonvanishing on components.** `IsNonzeroEverywhere` (nonzero stalks) is Kollár's "nonzero on
every irreducible component" [Kol07, Notation 64 (2)]: a stalk vanishes at a point only if it
vanishes at the generic point of a component through it. Along a smooth blow-up sequence of order
`m` (or `≥ m`) the induced ideals stay nonzero on every component, and for `m ≥ 1` no center
contains a component of its stage.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme.IdealSheafData
  Scheme BlowUpSequence IdealSheafData

namespace AlgebraicGeometry

open Hironaka

variable {X : Scheme.{u}}

/-! ### `π_0` on the `cons` shape with a constructor-shaped tail: no cast -/

/-- `π_0 = D.blowUpπ` on `cons X D (nil _)` (the cast of `step_cons_zero` is `eqToHom rfl`). -/
theorem step_cons_nil_zero (D : X.IdealSheafData) :
    (cons X D (nil _)).step ⟨0, Nat.succ_pos _⟩ = D.blowUpπ := by
  change 𝟙 _ ≫ D.blowUpπ = D.blowUpπ
  exact Category.id_comp _

/-- `π_0 = D.blowUpπ` on `cons X D (cons _ D' rest')`. -/
theorem step_cons_cons_zero (D : X.IdealSheafData) (D' : D.blowUp.IdealSheafData)
    (rest' : BlowUpSequence D'.blowUp) :
    (cons X D (cons _ D' rest')).step ⟨0, Nat.succ_pos _⟩ = D.blowUpπ := by
  change 𝟙 _ ≫ D.blowUpπ = D.blowUpπ
  exact Category.id_comp _

/-- On the `cons` shape the first exceptional divisor is `D.exceptionalDivisor` carried along the
cast `X_1 = D.blowUp`; it is not `rfl` on a variable tail. -/
theorem exceptionalAt_cons_zero (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) :
    (cons X D rest).exceptionalAt ⟨0, Nat.succ_pos _⟩ =
      D.exceptionalDivisor.comap (eqToHom (stage_zero rest)) := by
  change D.comap (eqToHom (stage_zero rest) ≫ D.blowUpπ) = _
  rw [Scheme.IdealSheafData.comap_comp]
  rfl

/-! ### The recursion equations of the induced data -/

section Recursions

variable (I : X.IdealSheafData) (E : DivisorFamily X) (m : ℕ)

theorem weakTransformSeq_nil (i : Fin ((nil X).length + 1)) :
    (nil X).weakTransformSeq I i = I := rfl

theorem weakTransformSeq_cons_zero (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) :
    (cons X D rest).weakTransformSeq I 0 = I := rfl

theorem weakTransformSeq_cons_succ (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp)
    (j : ℕ) (h : j + 1 < (cons X D rest).length + 1) :
    (cons X D rest).weakTransformSeq I ⟨j + 1, h⟩ =
      rest.weakTransformSeq (I.weakTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩ := rfl

theorem markedTransformSeq_nil (i : Fin ((nil X).length + 1)) :
    (nil X).markedTransformSeq I m i = I := rfl

theorem markedTransformSeq_cons_zero (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) :
    (cons X D rest).markedTransformSeq I m 0 = I := rfl

theorem markedTransformSeq_cons_succ (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp)
    (j : ℕ) (h : j + 1 < (cons X D rest).length + 1) :
    (cons X D rest).markedTransformSeq I m ⟨j + 1, h⟩ =
      rest.markedTransformSeq (I.markedTransform D m) m ⟨j, Nat.lt_of_succ_lt_succ h⟩ := rfl

theorem totalTransformSeq_nil (i : Fin ((nil X).length + 1)) :
    (nil X).totalTransformSeq E i = E := rfl

theorem totalTransformSeq_cons_zero (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp) :
    (cons X D rest).totalTransformSeq E 0 = E := rfl

theorem totalTransformSeq_cons_succ (D : X.IdealSheafData)
    (rest : BlowUpSequence D.blowUp)
    (j : ℕ) (h : j + 1 < (cons X D rest).length + 1) :
    (cons X D rest).totalTransformSeq E ⟨j + 1, h⟩ =
      rest.totalTransformSeq (E.totalTransform D) ⟨j, Nat.lt_of_succ_lt_succ h⟩ := rfl

/-- `I_{j+1} = (π_j)_*^{-1} I_j` [Kol07, Definition 66 (1)], in the `⟨j, h⟩` form of the indices:
by induction on the sequence, the first step being a case split on the tail's constructor. -/
theorem weakTransformSeq_mk_succ (S : BlowUpSequence X) (j : ℕ) (hj : j < S.length) :
    S.weakTransformSeq I ⟨j + 1, Nat.succ_lt_succ hj⟩ =
      (S.weakTransformSeq I ⟨j, Nat.lt_succ_of_lt hj⟩).weakTransformAlong (S.step
          ⟨j, hj⟩) (S.exceptionalAt ⟨j, hj⟩) := by
  induction S generalizing j with
  | nil _ => exact absurd hj (Nat.not_lt_zero _)
  | cons Y D rest ih =>
    cases j with
    | zero =>
      cases rest <;> simp only [exceptionalAt, step_cons_nil_zero, step_cons_cons_zero] <;> rfl
    | succ j => exact ih (I.weakTransform D) j (Nat.lt_of_succ_lt_succ hj)

/-- `(I_{j+1}, m) = (π_j)_*^{-1}(I_j, m)` [Kol07, Warning 63 (2) and Definition 66 (1′)], in the
`⟨j, h⟩` form of the indices. -/
theorem markedTransformSeq_mk_succ (S : BlowUpSequence X) (j : ℕ) (hj : j < S.length) :
    S.markedTransformSeq I m ⟨j + 1, Nat.succ_lt_succ hj⟩ =
      (S.markedTransformSeq I m ⟨j, Nat.lt_succ_of_lt hj⟩).controlledTransformAlong (S.step
          ⟨j, hj⟩) (S.exceptionalAt ⟨j, hj⟩) m := by
  induction S generalizing j with
  | nil _ => exact absurd hj (Nat.not_lt_zero _)
  | cons Y D rest ih =>
    cases j with
    | zero =>
      cases rest <;> simp only [exceptionalAt, step_cons_nil_zero, step_cons_cons_zero] <;> rfl
    | succ j => exact ih (I.markedTransform D m) j (Nat.lt_of_succ_lt_succ hj)

/-- `E_{j+1} = (π_j)_tot^{-1} E_j` [Kol07, Definition 66 (1)], in the `⟨j, h⟩` form of the
indices. -/
theorem totalTransformSeq_mk_succ (S : BlowUpSequence X) (j : ℕ) (hj : j < S.length) :
    S.totalTransformSeq E ⟨j + 1, Nat.succ_lt_succ hj⟩ =
      (S.totalTransformSeq E ⟨j, Nat.lt_succ_of_lt hj⟩).totalTransformAlong (S.step ⟨j, hj⟩)
        (S.exceptionalAt ⟨j, hj⟩) := by
  induction S generalizing j with
  | nil _ => exact absurd hj (Nat.not_lt_zero _)
  | cons Y D rest ih =>
    cases j with
    | zero =>
      cases rest <;> simp only [exceptionalAt, step_cons_nil_zero, step_cons_cons_zero] <;> rfl
    | succ j => exact ih (E.totalTransform D) j (Nat.lt_of_succ_lt_succ hj)

/-- `I_{i+1} = (π_i)_*^{-1} I_i` [Kol07, Definition 66 (1)]. -/
theorem weakTransformSeq_succ (S : BlowUpSequence X) (i : Fin S.length) :
    S.weakTransformSeq I i.succ =
      (S.weakTransformSeq I i.castSucc).weakTransformAlong (S.step i) (S.exceptionalAt i) := by
  obtain ⟨j, hj⟩ := i
  exact weakTransformSeq_mk_succ I S j hj

/-- `(I_{i+1}, m) = (π_i)_*^{-1}(I_i, m)` [Kol07, Warning 63 (2) and Definition 66 (1′)]. -/
theorem markedTransformSeq_succ (S : BlowUpSequence X) (i : Fin S.length) :
    S.markedTransformSeq I m i.succ =
      (S.markedTransformSeq I m i.castSucc).controlledTransformAlong (S.step i) (S.exceptionalAt
          i) m := by
  obtain ⟨j, hj⟩ := i
  exact markedTransformSeq_mk_succ I m S j hj

/-- `E_{i+1} = (π_i)_tot^{-1} E_i` [Kol07, Definition 66 (1)]. -/
theorem totalTransformSeq_succ (S : BlowUpSequence X) (i : Fin S.length) :
    S.totalTransformSeq E i.succ =
      (S.totalTransformSeq E i.castSucc).totalTransformAlong (S.step i) (S.exceptionalAt i) := by
  obtain ⟨j, hj⟩ := i
  exact totalTransformSeq_mk_succ E S j hj

end Recursions

/-! ### The total transform along a morphism -/

section TotalTransform

variable {B : Scheme.{u}} (π : B ⟶ X) (F : B.IdealSheafData) (E : DivisorFamily X)

theorem totalTransform_eq_totalTransformAlong (Z : X.IdealSheafData) :
    E.totalTransform Z = E.totalTransformAlong Z.blowUpπ Z.exceptionalDivisor :=
        rfl

theorem totalTransformAlong_component_inl (j : E.ι) :
    (E.totalTransformAlong π F).component (toLex (Sum.inl j)) =
      (E.component j).strictTransformAlong π F := rfl

theorem totalTransformAlong_component_inr :
    (E.totalTransformAlong π F).component (toLex (Sum.inr PUnit.unit)) = F := rfl

/-- The exceptional divisor receives the largest index ("added as the last divisor",
[Kol07, Definition 65]). -/
theorem totalTransformAlong_le_inr (i : (E.totalTransformAlong π F).ι) :
    i ≤ toLex (Sum.inr PUnit.unit) := by
  rcases i with j | u
  · exact Sum.Lex.inl_le_inr j PUnit.unit
  · cases u
    exact le_rfl

end TotalTransform

/-! ### The marked transform as a colon ideal -/

section MarkedTransform

variable (Z I : X.IdealSheafData) (m : ℕ)

theorem markedTransform_eq_colon :
    I.markedTransform Z m = (I.comap Z.blowUpπ).colon (Z.exceptionalDivisor ^ m) :=
        rfl

/-- `F^m · π_*^{-1}(I, m) = π^* I` when `F^m ∣ π^* I` [Kol07, Definition 60]. -/
theorem pow_mul_markedTransform (h : Z.exceptionalDivisor ^ m ∣ I.comap Z.blowUpπ) :
    Z.exceptionalDivisor ^ m * I.markedTransform Z m = I.comap Z.blowUpπ :=
  Scheme.IdealSheafData.pow_mul_colon_of_dvd (I.comap Z.blowUpπ) _ _ h

/-- `𝒪(mF) · π^* I` is the unique `K` with `F^m · K = π^* I` [Kol07, Definition 60]. -/
theorem eq_markedTransform_of_pow_mul_eq (K : Z.blowUp.IdealSheafData)
    (h : Z.exceptionalDivisor ^ m * K = I.comap Z.blowUpπ) :
    K = I.markedTransform Z m :=
  (Scheme.IdealSheafData.colon_pow_eq_of_mul_eq (I.comap Z.blowUpπ)
    (blowUp.isInvertible_comap_π Z) m K h).symm

end MarkedTransform

/-- Transport of the marked transform along an equality of centers `e : I = J`: the `eqToHom` of
`eqToHom_comp_blowUpπ` (`Hironaka/Scheme/BlowUp/BlowUpMap.lean`) pulls `markedTransform J K m` back
to `markedTransform I K m`. -/
theorem comap_markedTransform_eqToHom {I J : X.IdealSheafData} (e : I = J) (K : X.IdealSheafData)
    (m : ℕ) :
    (K.markedTransform J m).comap (eqToHom (congrArg IdealSheafData.blowUp e)) =
      K.markedTransform I m := by
  subst e
  rw [eqToHom_refl, Scheme.IdealSheafData.comap_id]

/-! ### The order predicates -/

section OrderSeq

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (I : X.IdealSheafData)
  (E : DivisorFamily X) (m : ℕ)

theorem isOrderSeq_nil : (nil X).IsOrderSeq f I E m :=
  ⟨isSmooth_nil f, fun i => i.elim0⟩

theorem isOrderGeSeq_nil : (nil X).IsOrderGeSeq f I m E :=
  ⟨isSmooth_nil f, fun i => i.elim0⟩

/-- [Kol07, Definition 66] unrolled on the `cons` shape: the first blow-up is a smooth blow-up of
order `m` of `(X, I, E)` [Kol07, Definition 65], and the tail is a sequence of order `m` for the
transformed triple. -/
theorem isOrderSeq_cons_iff (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp) :
    (cons X D rest).IsOrderSeq f I E m ↔
      (Smooth (D.subschemeι ≫ f) ∧ E.HasSncWith D ∧ I.OrdAlongEq D.support (m : ℕ∞)) ∧
        rest.IsOrderSeq (D.blowUpπ ≫ f) (I.weakTransform D) (E.totalTransform D) m := by
  unfold IsOrderSeq
  rw [isSmooth_cons_iff]
  constructor
  · rintro ⟨⟨h0, hr⟩, h⟩
    refine ⟨⟨h0, (h ⟨0, Nat.succ_pos _⟩).1, (h ⟨0, Nat.succ_pos _⟩).2⟩, hr, fun j => ?_⟩
    obtain ⟨j, hj⟩ := j
    exact h ⟨j + 1, Nat.succ_lt_succ hj⟩
  · rintro ⟨⟨h0, hsnc, hord⟩, hr, h⟩
    refine ⟨⟨h0, hr⟩, fun i => ?_⟩
    rcases i with ⟨_ | j, hi⟩
    · exact ⟨hsnc, hord⟩
    · exact h ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- The marked form of [Kol07, Definition 66] unrolled on the `cons` shape. -/
theorem isOrderGeSeq_cons_iff (D : X.IdealSheafData) (rest : BlowUpSequence D.blowUp) :
    (cons X D rest).IsOrderGeSeq f I m E ↔
      (Smooth (D.subschemeι ≫ f) ∧ E.HasSncWith D ∧ I.LeOrdAlong D.support (m : ℕ∞)) ∧
        rest.IsOrderGeSeq (D.blowUpπ ≫ f) (I.markedTransform D m) m
            (E.totalTransform D) := by
  unfold IsOrderGeSeq
  rw [isSmooth_cons_iff]
  constructor
  · rintro ⟨⟨h0, hr⟩, h⟩
    refine ⟨⟨h0, (h ⟨0, Nat.succ_pos _⟩).1, (h ⟨0, Nat.succ_pos _⟩).2⟩, hr, fun j => ?_⟩
    obtain ⟨j, hj⟩ := j
    exact h ⟨j + 1, Nat.succ_lt_succ hj⟩
  · rintro ⟨⟨h0, hsnc, hord⟩, hr, h⟩
    refine ⟨⟨h0, hr⟩, fun i => ?_⟩
    rcases i with ⟨_ | j, hi⟩
    · exact ⟨hsnc, hord⟩
    · exact h ⟨j, Nat.lt_of_succ_lt_succ hi⟩

variable {f I E m} {S : BlowUpSequence X}

theorem IsOrderSeq.isSmooth (h : S.IsOrderSeq f I E m) : S.IsSmooth f := h.1

theorem IsOrderSeq.hasSncWith (h : S.IsOrderSeq f I E m) (i : Fin S.length) :
    (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i) := (h.2 i).1

theorem IsOrderSeq.ordAlongEq (h : S.IsOrderSeq f I E m) (i : Fin S.length) :
    (S.weakTransformSeq I i.castSucc).OrdAlongEq (S.center i).support (m : ℕ∞) := (h.2 i).2

theorem IsOrderGeSeq.isSmooth (h : S.IsOrderGeSeq f I m E) : S.IsSmooth f := h.1

theorem IsOrderGeSeq.hasSncWith (h : S.IsOrderGeSeq f I m E) (i : Fin S.length) :
    (S.totalTransformSeq E i.castSucc).HasSncWith (S.center i) := (h.2 i).1

theorem IsOrderGeSeq.leOrdAlong (h : S.IsOrderGeSeq f I m E) (i : Fin S.length) :
    (S.markedTransformSeq I m i.castSucc).LeOrdAlong (S.center i).support (m : ℕ∞) := (h.2 i).2

end OrderSeq

/-! ### Nonzero stalks and nonzero on every irreducible component -/

/-- `IsNonzeroEverywhere I` iff `I` is nonzero at the generic point of every irreducible
component: the condition "nonzero on every irreducible component" of [Kol07, Notation 64 (2)]. -/
theorem isNonzeroEverywhere_iff_irreducibleComponents (I : X.IdealSheafData) :
    IsNonzeroEverywhere I ↔
      ∀ W ∈ irreducibleComponents X, ∀ η, IsGenericPoint η W → I.stalkIdeal η ≠ ⊥ := by
  constructor
  · intro h W _ η _
    exact h η
  · intro h x
    exact Scheme.IdealSheafData.stalkIdeal_ne_bot_of_irreducibleComponents I h x

/-! ### One blow-up: nonvanishing on the components is preserved -/

section Nonvanishing

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [Smooth f]

/-- The unmarked birational transform of an ideal sheaf nonzero on every component is nonzero on
every component of `B_Z X` (`stalkIdeal_controlledTransform_ne_bot`, the weak transform being a
controlled transform); the condition of [Kol07, Notation 64 (2)] is preserved. -/
theorem isNonzeroEverywhere_weakTransform (Z : X.IdealSheafData)
    (hZ : Smooth (Z.subschemeι ≫ f)) (I : X.IdealSheafData) (hI : IsNonzeroEverywhere I) :
    IsNonzeroEverywhere (I.weakTransform Z) := by
  have := hZ
  intro q
  exact stalkIdeal_controlledTransform_ne_bot f Z I hI _ q

/-- The marked transform `π_*^{-1}(I, m)` of an ideal sheaf nonzero on every component is nonzero
on every component of `B_Z X` (compare the remark after [Kol07, Lemma 62]). The order hypothesis
`_hm` is present because `π_*^{-1}(I, m)` is the marked transform of [Kol07, Definition 60] only
under `m ≤ ord_Z I`, the clause that a sequence of order `≥ m` supplies at every stage; the proof
does not need it, because the colon `(π^* I : F^m)` has nonzero stalks for every `m`
(`stalkIdeal_controlledTransform_ne_bot`: over the center by injectivity of `π^♯`, off it because
`π` is an isomorphism there). -/
theorem isNonzeroEverywhere_markedTransform (Z : X.IdealSheafData)
    (hZ : Smooth (Z.subschemeι ≫ f)) (I : X.IdealSheafData) (hI : IsNonzeroEverywhere I) (m : ℕ)
    (_hm : I.LeOrdAlong Z.support (m : ℕ∞)) : IsNonzeroEverywhere (I.markedTransform Z m) := by
  have := hZ
  intro q
  exact stalkIdeal_controlledTransform_ne_bot f Z I hI m q

end Nonvanishing

/-! ### The stages of a smooth blow-up sequence are smooth (Kollár Notation 19 along the sequence)
-/

section StageSmooth

variable {k : Type u} [Field k] [PerfectField k]

/-- [Kol07, Notation 19] along a sequence, for centers of any shape: if `X` is smooth of relative
dimension `n` and every center is smooth over `k` (`IsSmooth`), every stage is smooth of relative
dimension `n`, by `smoothOfRelativeDimension_blowUpπ_comp_of_smooth` at every stage.
(`Hironaka/Scheme/BlowUpSequence/Basic.lean` states this for centers of pure codimension; condition
(2) of [Kol07, Definition 66] needs it for `IsSmooth`.) -/
theorem IsSmooth.smoothOfRelativeDimension_stageMap {S : BlowUpSequence X}
    {f : X ⟶ Spec (.of k)} {n : ℕ} [SmoothOfRelativeDimension n f] (h : S.IsSmooth f)
    (i : Fin (S.length + 1)) : SmoothOfRelativeDimension n (S.stageMap i ≫ f) := by
  induction S with
  | nil Y =>
    change SmoothOfRelativeDimension n (𝟙 Y ≫ f)
    rw [Category.id_comp]
    infer_instance
  | cons Y D rest ih =>
    obtain ⟨hD, ht⟩ := (isSmooth_cons_iff f D rest).1 h
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
      have := hD
      exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | j, hi⟩
    · change SmoothOfRelativeDimension n (𝟙 Y ≫ f)
      rw [Category.id_comp]
      infer_instance
    · change SmoothOfRelativeDimension n
        ((rest.stageMap ⟨j, Nat.lt_of_succ_lt_succ hi⟩ ≫ D.blowUpπ) ≫ f)
      rw [Category.assoc]
      exact ih ht ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- [Kol07, Notation 19] along a sequence: every stage is smooth over `k`. -/
theorem IsSmooth.smooth_stageMap {S : BlowUpSequence X} {f : X ⟶ Spec (.of k)} {n : ℕ}
    [SmoothOfRelativeDimension n f] (h : S.IsSmooth f) (i : Fin (S.length + 1)) :
    Smooth (S.stageMap i ≫ f) := by
  have := IsSmooth.smoothOfRelativeDimension_stageMap (n := n) h i
  exact SmoothOfRelativeDimension.smooth n _

end StageSmooth

/-! ### Nonvanishing along a sequence -/

section NonvanishingSeq

variable {k : Type u} [Field k] [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
  [SmoothOfRelativeDimension n f] {I : X.IdealSheafData} {E : DivisorFamily X} {m : ℕ}
  {S : BlowUpSequence X}

include n

/-- Along a smooth blow-up sequence of order `m` starting with `(X, I, E)`, every induced ideal is
nonzero on every irreducible component of its stage. -/
theorem IsOrderSeq.isNonzeroEverywhere_weakTransformSeq (h : S.IsOrderSeq f I E m)
    (hI : IsNonzeroEverywhere I) (i : Fin (S.length + 1)) :
    IsNonzeroEverywhere (S.weakTransformSeq I i) := by
  induction S with
  | nil Y => exact hI
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, -⟩, ht⟩ := (isOrderSeq_cons_iff f I E m D rest).1 h
    have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
      have := hD
      exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | j, hi⟩
    · exact hI
    · exact ih (D.blowUpπ ≫ f) ht (isNonzeroEverywhere_weakTransform f D hD I hI)
        ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- Along a smooth blow-up sequence of order `≥ m` starting with `(X, I, m, E)`, every induced
marked ideal is nonzero on every irreducible component of its stage. -/
theorem IsOrderGeSeq.isNonzeroEverywhere_markedTransformSeq (h : S.IsOrderGeSeq f I m E)
    (hI : IsNonzeroEverywhere I) (i : Fin (S.length + 1)) :
    IsNonzeroEverywhere (S.markedTransformSeq I m i) := by
  induction S with
  | nil Y => exact hI
  | cons Y D rest ih =>
    obtain ⟨⟨hD, -, hord⟩, ht⟩ := (isOrderGeSeq_cons_iff f I E m D rest).1 h
    have hs : Smooth f := SmoothOfRelativeDimension.smooth n f
    have hπ : SmoothOfRelativeDimension n (D.blowUpπ ≫ f) := by
      have := hD
      exact smoothOfRelativeDimension_blowUpπ_comp_of_smooth f n D
    rcases i with ⟨_ | j, hi⟩
    · exact hI
    · exact ih (D.blowUpπ ≫ f) ht (isNonzeroEverywhere_markedTransform f D hD I hI m
        hord)
        ⟨j, Nat.lt_of_succ_lt_succ hi⟩

/-- No center of a smooth blow-up sequence of order `≥ m ≥ 1` starting with `(X, I, m, E)`
contains an irreducible component of its stage (compare the remark after [Kol07, Lemma 62]): at a
generic point of a component the stalk of the induced ideal is a nonzero ideal of a field, so its
order there is `0 < m`. -/
theorem IsOrderGeSeq.not_component_subset_center (h : S.IsOrderGeSeq f I m E)
    (hI : IsNonzeroEverywhere I) (hm : 1 ≤ m) (i : Fin S.length)
    (W : Set (S.stage i.castSucc)) (hW : W ∈ irreducibleComponents (S.stage i.castSucc)) :
    ¬ W ⊆ ((S.center i).support : Set (S.stage i.castSucc)) := by
  have hs : Smooth (S.stageMap i.castSucc ≫ f) :=
    IsSmooth.smooth_stageMap (n := n) (IsOrderGeSeq.isSmooth h) i.castSucc
  exact not_subset_support_of_leOrdAlong (S.stageMap i.castSucc ≫ f) (S.center i)
    (S.markedTransformSeq I m i.castSucc)
    (IsOrderGeSeq.isNonzeroEverywhere_markedTransformSeq f n h hI i.castSucc) hm
    (IsOrderGeSeq.leOrdAlong h i) hW

/-- The unmarked form: no center of a smooth blow-up sequence of order `m ≥ 1` starting with
`(X, I, E)` contains an irreducible component of its stage. -/
theorem IsOrderSeq.not_component_subset_center (h : S.IsOrderSeq f I E m)
    (hI : IsNonzeroEverywhere I) (hm : 1 ≤ m) (i : Fin S.length)
    (W : Set (S.stage i.castSucc)) (hW : W ∈ irreducibleComponents (S.stage i.castSucc)) :
    ¬ W ⊆ ((S.center i).support : Set (S.stage i.castSucc)) := by
  have hs : Smooth (S.stageMap i.castSucc ≫ f) :=
    IsSmooth.smooth_stageMap (n := n) (IsOrderSeq.isSmooth h) i.castSucc
  exact not_subset_support_of_leOrdAlong (S.stageMap i.castSucc ≫ f) (S.center i)
    (S.weakTransformSeq I i.castSucc)
    (IsOrderSeq.isNonzeroEverywhere_weakTransformSeq f n h hI i.castSucc) hm
    (fun η hη => (IsOrderSeq.ordAlongEq h i η hη).ge) hW

end NonvanishingSeq

end AlgebraicGeometry
