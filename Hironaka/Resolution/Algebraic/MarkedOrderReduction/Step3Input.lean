/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Basic
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces
public import Hironaka.Resolution.Algebraic.BoundaryClearing.Basic
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.SplitTriple
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Exponent
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Input
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Nerve
import Hironaka.Resolution.Algebraic.Monomial.Geometric.OrderSeq
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Realize
import Hironaka.Resolution.Algebraic.Snc.DictionaryGenericPoints
import Hironaka.Scheme.BlowUpSequence.MarkedMono
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Step 3 of marked order reduction: the geometric monomial step on a marked triple

Step 3 of the proof of [Kol07, Theorem 107] ([Kol07, 111, Step 3]) treats the monomial case: a
smooth variety `X`, a simple normal crossing divisor `∪_{j ∈ J} E^j` with ordered index set `J`,
and the monomial ideal `I = 𝒪_X(−∑ a_j E^j)` for natural numbers `a_j`. After Step 2 the marked
triple `(X, I, m, E)` has `cosupp(I, m) ∩ cosupp N(I) = ∅`, and Kollár runs Step 3 for `M(I)` on
`X ∖ cosupp N(I)`, where `I = M(I)`. Here the geometric Step 3 of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/` is run on `X` itself for the marked ideal
`(M(I), m)`: its centres lie in `cosupp(M(I), m) ⊆ cosupp(I, m)`, hence off `cosupp N(I)`, and the
sequence is of order `≥ m` for `(I, m)` because `I ⊆ M(I)`
(`Hironaka/Scheme/BlowUpSequence/MarkedMono.lean`).

The geometric Step 3 (`PieceFamily.realize`,
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Pieces.lean`) takes a piece family realizing `E`:
the irreducible components of the members, enumerated, with the exponent at each generic point. This
module builds that input from a marked triple and reads the results of the run for `(I, m)`.

* `labelIso E`, `componentsEquiv E`: the enumerations (the finite linear order `E.ι` against `Fin`,
  and the finitely many generic points of the members on the Noetherian `X`).
* `step3Family T`: `ofDivisorFamily` on `T.E` with the exponents of the monomial part
  `M(I) = E.monomial (fun η => (ord_η I).toNat)` (Kollár's `a_j = ord_{E^j} I`, the orders of `I`
  at the generic points of the components, where `ord N(I) = 0`, so they are the orders of `M(I)`
  too); it realizes `T.E` (`step3Family_realizes`), and its marked monomial ideal is `M(I)`
  (`monomial_exponentAt_step3Family`).
* `step3Seq T hT`: the geometric Step 3 of `(X, M(I), m, E)` on `X` (`realize` on the state
  `toState`, valid by `valid_of_realizes` from the class `BMOClass n m`): a smooth blow-up
  sequence of order `≥ m` for `(X, I, m, E)` (`step3Seq_isOrderGeSeq`), without empty blow-ups
  (`step3Seq_noEmptyCenters`), at whose end the marked transform of `M(I)` has `max-ord < m`
  (`step3Seq_maxOrd_lt`).

The assembly of the three steps is
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Assembly.lean`; that the run reduces the order
of `(I, m)` itself, not only of `(M(I), m)`, is
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Clause1.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Hironaka BlowUpSequence
  Scheme.IdealSheafData Hironaka.Monomial Hironaka.Monomial.PieceFamily

namespace Hironaka.BMO

section Enumerations

variable {X : Scheme.{u}}

/-- The finitely many irreducible components of the members of `E` (their generic points) form a
finite type on a Noetherian scheme. -/
theorem finite_components [NoetherianSpace X] (E : DivisorFamily X) : Finite (Components E) := by
  have : ∀ j : E.ι, Finite ↥(E.component j).support.genericPoints := fun j =>
    (Snc.genericPoints_component_finite E j).to_subtype
  exact inferInstanceAs (Finite (Σ j : E.ι, ↥(E.component j).support.genericPoints))

/-- The label isomorphism of Step 3's input: the finite linear order `E.ι` of the members against
`Fin` (`monoEquivOfFin`), labels counted from `0` in the order of `E`. -/
noncomputable def labelIso (E : DivisorFamily X) : E.ι ≃o Fin (Fintype.card E.ι) :=
  (monoEquivOfFin E.ι rfl).symm

/-- An enumeration of the irreducible components of the members of `E` (their generic points), the
component data of Step 3's input piece family. -/
noncomputable def componentsEquiv [NoetherianSpace X] (E : DivisorFamily X) :
    Fin (Nat.card (Components E)) ≃ Components E :=
  haveI := finite_components E
  (Finite.equivFin (Components E)).symm

end Enumerations

section Input

variable {k : Type u} [Field k] [CharZero k] (T : MarkedTriple k)

/-- **Step 3's input piece family** of a marked triple ([Kol07, 111, Step 3]: the normal-crossings
divisor `∪ E^j` with ordered index set `J` and the exponents `a_j` of the monomial ideal
`𝒪_X(−∑ a_j E^j)`, here for `M(I)` after Step 2): `ofDivisorFamily` on `T.E`, the irreducible
components of the members with the exponents `a_j = ord_{E^j} I` of the monomial part `M(I)` at
their generic points (`monomialPart I E = E.monomial (fun η => (ord_η I).toNat)`). -/
noncomputable def step3Family : PieceFamily T.X.left :=
  ofDivisorFamily T.E (fun x => (T.I.ord x).toNat) (labelIso T.E)
    (@componentsEquiv _ (Hironaka.BD.noetherianSpace_triple T.toTriple) T.E)

omit [CharZero k] in
/-- Step 3's input family realizes the boundary `T.E` through the label isomorphism
(`ofDivisorFamily_realizes`). -/
theorem step3Family_realizes : (step3Family T).Realizes T.E (labelIso T.E) :=
  ofDivisorFamily_realizes T.E _ (labelIso T.E)
    (@componentsEquiv _ (Hironaka.BD.noetherianSpace_triple T.toTriple) T.E) T.isSnc

omit [CharZero k] in
/-- **The marked monomial ideal of Step 3's input family is the monomial part `M(I)`**:
`monomial_exponentAt_ofDivisorFamily` at the exponents `(ord_η I).toNat` (the exponent at a point
is that of the piece through it, read at the generic points), and
`monomialPart I E = E.monomial (fun η => (ord_η I).toNat)` by definition. -/
theorem monomial_exponentAt_step3Family :
    T.E.monomial (step3Family T).exponentAt = monomialPart T.I T.E := by
  have := T.smooth
  unfold step3Family
  rw [monomial_exponentAt_ofDivisorFamily (T.X.left ↘ Spec (.of k)) T.isSnc
    (fun x => (T.I.ord x).toNat) (labelIso T.E)
    (@componentsEquiv _ (Hironaka.BD.noetherianSpace_triple T.toTriple) T.E)]
  exact (monomialPart_eq_monomial T.I T.E).symm

variable {n m : ℕ}

/-- For a marked triple of `BMOClass n m` the input family's data are valid (`valid_of_realizes`):
`1 ≤ m` and `dim X ≤ n` are the class's, the normal crossings are the triple's; so the state
`toState` and its run are defined. -/
theorem step3Family_isValid (hT : T.BMOClass n m) : (step3Family T).IsValid n m := by
  have := T.smooth
  exact valid_of_realizes (step3Family T) (T.X.left ↘ Spec (.of k)) T.isSnc (step3Family_realizes T)
    hT.1 hT.2.1

/-- **The geometric Step 3 of a marked triple** ([Kol07, 111, Step 3], run for `M(I)` on `X`):
`PieceFamily.realize` of the combinatorial run on Step 3's input family. -/
noncomputable def step3Seq (hT : T.BMOClass n m) : BlowUpSequence T.X.left :=
  (step3Family T).realize n m (step3Family_isValid T hT)

/-- **Step 3 is a smooth blow-up sequence of order `≥ m` for `(X, I, m, E)`** (conditions
(2′)–(4′) of [Kol07, Definition 66] for `(I, m)`): it is one for `(X, M(I), m, E)`
(`realize_isOrderGeSeq` through `monomial_exponentAt_step3Family`), and `I ⊆ M(I)` by the split
`I = M(I) · N(I)`, so the order at every centre is at least as large (`isOrderGeSeq_of_le`). -/
theorem step3Seq_isOrderGeSeq (hT : T.BMOClass n m) :
    (step3Seq T hT).IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E := by
  have := T.smooth
  have h := realize_isOrderGeSeq (f := T.X.left ↘ Spec (.of k)) (Φ := step3Family T) T.isSnc
    (step3Family_realizes T) (step3Family_isValid T hT) hT.2.1
  rw [monomial_exponentAt_step3Family] at h
  have hle : T.I ≤ monomialPart T.I T.E :=
    calc T.I = monomialPart T.I T.E * nonmonomialPart T.I T.E :=
          (monomialPart_mul_nonmonomialPart T.toTriple).symm
      _ ≤ monomialPart T.I T.E := IdealSheafData.mul_le_self_left _ _
  rw [hT.2.2]
  exact isOrderGeSeq_of_le _ h hle

/-- Step 3 contains no empty blow-up ([Kol07, 32]; `realize_noEmptyCenters`). -/
theorem step3Seq_noEmptyCenters (hT : T.BMOClass n m) : (step3Seq T hT).NoEmptyCenters := by
  have := T.smooth
  exact realize_noEmptyCenters (f := T.X.left ↘ Spec (.of k)) (Φ := step3Family T) T.isSnc
    (step3Family_realizes T) (step3Family_isValid T hT) hT.2.1

/-- At the end of Step 3 the marked transform of the monomial part has `max-ord < m`
([Kol07, 111, Step 3]: "at the end of Step 3.n we are done"; `realize_maxOrd_lt`). -/
theorem step3Seq_maxOrd_lt (hT : T.BMOClass n m) :
    ((step3Seq T hT).markedTransformSeq (monomialPart T.I T.E) m
      (Fin.last (step3Seq T hT).length)).maxOrd < (m : ℕ∞) := by
  have := T.smooth
  have h := realize_maxOrd_lt (f := T.X.left ↘ Spec (.of k)) (Φ := step3Family T) T.isSnc
    (step3Family_realizes T) (step3Family_isValid T hT) hT.2.1
  rwa [monomial_exponentAt_step3Family] at h

end Input

end Hironaka.BMO
