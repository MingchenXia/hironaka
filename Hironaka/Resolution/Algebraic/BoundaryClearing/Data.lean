/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Data.Fintype.Sort
public import Hironaka.Resolution.Algebraic.Kol07.MaximalContactClasses
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded
/-!
# The boundary-clearing functor `BD_{n,m,j}`: its class, its data and the first center

Kollár's Lemma 102 ([Kol07, Lemma 102]): assuming order reduction for marked ideals
([Kol07, Theorem 69]) in dimensions `< n`, for every `m` and `j` there is a smooth blow-up sequence
functor `BD_{n,m,j}` of order `m`, defined on the triples `(X, I, E)` with `dim X = n`,
`max-ord I ≤ m` and `E = ∑_i E^i`, whose output `Π : X_r → ⋯ → X_0 = X` satisfies (1)
`cosupp(I_r, m) ∩ Π^{-1}_* E^j = ∅`, the final cosupport misses the birational transform of the
`j`-th boundary component, and (2) commutes with smooth morphisms and with change of fields
([Kol07, 34.1, 34.2]). Its proof opens with a trivial blow-up: `Z_{-1}` is the union of the
irreducible components of `E^j` contained in `cosupp(I, m)`, and `π_{-1} : X_0 → X` the blow-up of
`Z_{-1}`, an isomorphism along which the order of `I` along those components drops by `m`.

This module defines the objects of the statement and of that first step, in the vocabulary of
blow-up sequences, divisor families and triples:

* `DivisorFamily.nth E j`, the component `E^j`. Kollár's divisors carry an ordered index set
  ([Kol07, Definition 31]; [Kol07, Notation 64, (3)]; the ordering is kept by the birational
  transform of [Kol07, Definition 65]), and `BD_{n,m,j}` is one functor for each index `j`, defined
  on every triple whose family has a `j`-th member: `nth` is the `j`-th component in the linear
  order of `E.ι` (Mathlib's `monoEquivOfFin`), positions counted from `0`; it has the body of
  `DivisorFamily.nth` (`Hironaka/Resolution/Algebraic/Kol07/Componentwise.lean`), repeated here
  under the name the boundary-clearing modules use. Pull-back and base change keep the index set
  (`DivisorFamily.comap`), so the position is functorial.
* `Triple.HasDimLE T n`, "`dim X ≤ n`": the disjunction of `HasDim n'`
  (`Hironaka/Resolution/Algebraic/Kol07/MaximalContactClasses.lean`) over `n' ≤ n`. Kollár's `dim X
  = n` is read as `dim X ≤ n`, so that disjoint unions and the restriction to `E^j` stay in the
  classes.
* `Triple.BDClass n m j`, the domain of `BD_{n,m,j}`: the triples with `dim X ≤ n`, `max-ord I ≤ m`
  and a `j`-th component.
* `BDData n m j`, Lemma 102 (1)–(2) as a structure: a smooth blow-up sequence functor of order `m`
  on `BDClass n m j` for every field of characteristic zero at once, whose final cosupport misses
  the birational transform of `E^j`, and which commutes with smooth morphisms and with change of
  fields. Its existence under the inductive hypothesis is Lemma 102 itself (`Assembly.lean` and
  the modules following it); clause (3) of Lemma 102 is `ClauseThree.lean`.
* `BD.Zminus1 I m D`, the center `Z_{-1}` for the divisor `D = E^j`: the union of the irreducible
  components of `V(D)` whose generic point lies in `cosupp(I, m)`, with its reduced structure, i.e.
  the vanishing ideal sheaf of the union of the closures of those generic points
  (`Closeds.genericPoints`, `Hironaka/Scheme/IdealSheaf/Order/Along.lean`). A component is contained
  in `cosupp(I, m)` iff its generic point is, the order growing under specialization.
* `BD.piMinusOne I m D`, the one-step blow-up sequence `π_{-1}` with center `Z_{-1}`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme.DivisorFamily

open Hironaka

variable {X : Scheme.{u}}

/-- The component `E^j` of a divisor family with ordered index set ([Kol07, Definition 31];
[Kol07, Notation 64, (3)]; [Kol07, Lemma 102], "for every `m, j`"): the `j`-th member of the family
in the linear order of its index set, positions counted from `0`. -/
noncomputable def nth (E : DivisorFamily X) (j : Fin (Fintype.card E.ι)) : X.IdealSheafData :=
  E.component (monoEquivOfFin E.ι rfl j)

end AlgebraicGeometry.Scheme.DivisorFamily

namespace Hironaka

end Hironaka

namespace AlgebraicGeometry.Triple

open Hironaka

variable {k : Type u} [Field k]

/-- The triple has dimension at most `n`: its structure morphism is smooth of some relative
dimension `n' ≤ n` (`HasDim n'`). Kollár's "`dim X = n`" in [Kol07, Lemma 102] is read as
`dim X ≤ n`, so that disjoint unions and the restriction to `E^j` stay in the class. -/
def HasDimLE (T : Triple k) (n : ℕ) : Prop :=
  ∃ n' ≤ n, T.HasDim n'

/-- The domain of `BD_{n,m,j}` ([Kol07, Lemma 102]: triples `(X, I, E)` with `dim X = n`,
`max-ord I ≤ m` and `E = ∑_i E^i`): the triples with `dim X ≤ n`, `max-ord I ≤ m` and a `j`-th
component `E^j`. -/
def BDClass (n m j : ℕ) (T : Triple k) : Prop :=
  T.HasDimLE n ∧ T.I.maxOrd ≤ (m : ℕ∞) ∧ j < Fintype.card T.E.ι

end AlgebraicGeometry.Triple

namespace Hironaka

/-- **The data of the boundary-clearing functor `BD_{n,m,j}`** ([Kol07, Lemma 102], clauses (1) and
(2)): for every field `k` of characteristic zero a smooth blow-up sequence functor of order `m` on
the triples of `BDClass n m j` (`OrderSeqFunctor`: [Kol07, Definition 31] with the order condition
of [Kol07, Definition 66] and the no-empty-blow-ups convention of [Kol07, 32]), such that (1) for
every triple `(X, I, E)` of the class with `BD_{n,m,j}(X, I, E) = Π : X_r → ⋯ → X_0 = X`, the
cosupport `cosupp(I_r, m)` of the final induced ideal is disjoint from the birational transform
`Π^{-1}_* E^j` of `E^j` (`strictTransformSeq`, [Kol07, 30.2]), and (2) the functor commutes with
smooth morphisms (`CommutesWithSmooth`, [Kol07, 34.1]) and with change of fields
(`CommutesWithBaseChange` between the functors over `k` and over `L`, [Kol07, 34.2]). The
existence of such data under the inductive hypothesis (Theorem 69 in dimensions `< n`) is Lemma
102 itself (`Assembly.lean` and the modules following it); clause (3) of Lemma 102 is
`ClauseThree.lean`. -/
structure BDData (n m j : ℕ) where
  /-- The functor `BD_{n,m,j}` over each field `k` of characteristic zero. -/
  functor : ∀ (k : Type u) [Field k] [CharZero k], OrderSeqAssignment k m (Triple.BDClass n m j)
  /-- Clause (1) of [Kol07, Lemma 102]: `cosupp(I_r, m) ∩ Π^{-1}_* E^j = ∅`. -/
  disjoint_cosupp : ∀ (k : Type u) [Field k] [CharZero k] (T : Triple k)
    (hT : Triple.BDClass n m j T),
    Disjoint
      {x | (m : ℕ∞) ≤ (((functor k).seq T hT).weakTransformSeq T.I (Fin.last _)).ord x}
      ((((functor k).seq T hT).strictTransformSeq (T.E.nth ⟨j, hT.2.2⟩) (Fin.last _)).support :
        Set _)
  /-- Clause (2) of [Kol07, Lemma 102], first half: `BD_{n,m,j}` commutes with smooth morphisms
  ([Kol07, 34.1]). -/
  commutesWithSmooth : ∀ (k : Type u) [Field k] [CharZero k], (functor k).CommutesWithSmooth
  /-- Clause (2) of [Kol07, Lemma 102], second half: `BD_{n,m,j}` commutes with change of fields
  ([Kol07, 34.2]). -/
  commutesWithBaseChange : ∀ (k L : Type u) [Field k] [CharZero k] [Field L] [CharZero L]
    (σ : k →+* L), (functor k).CommutesWithBaseChange (functor L) σ

end Hironaka

namespace Hironaka.BD

open Scheme BlowUpSequence AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- Kollár's first center `Z_{-1}`, the union of the irreducible components `E^{jk}` of `E^j`
contained in `cosupp(I, m)` (the proof of [Kol07, Lemma 102]), for the divisor `D = E^j`: the union
of the irreducible components of `V(D)` whose generic point has `ord I ≥ m` (a component lies in
`cosupp(I, m)` iff its generic point does, the order growing under specialization), with its
reduced structure, the vanishing ideal sheaf of the union of the closures of those generic points
(`Closeds.genericPoints`). -/
noncomputable def Zminus1 (I : X.IdealSheafData) (m : ℕ) (D : X.IdealSheafData) :
    X.IdealSheafData :=
  vanishingIdeal
    (⨆ η : {η : X // η ∈ D.support.genericPoints ∧ (m : ℕ∞) ≤ I.ord η},
      Closeds.closure {(η : X)})

/-- Kollár's `π_{-1} : X_0 → X`, the blow-up of `Z_{-1}` (the proof of [Kol07, Lemma 102]), as the
one-step blow-up sequence with center `Z_{-1}`. Its stage `1` is `X_0 = B_{Z_{-1}} X`, its induced
data `I_0 = (π_{-1})^{-1}_* I` (`weakTransformSeq`) and `E_0 = (π_{-1})^{-1}_{tot} E`
(`totalTransformSeq`). -/
noncomputable def piMinusOne (I : X.IdealSheafData) (m : ℕ) (D : X.IdealSheafData) :
    BlowUpSequence X :=
  cons X (Zminus1 I m D) (nil _)

end Hironaka.BD
