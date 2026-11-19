/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MaximalContact.EtaleEquivSeq
public import Hironaka.Resolution.Algebraic.MaximalContact.Theorem97Setup
import Hironaka.Resolution.Algebraic.MaximalContact.AgreeOnBlowUpKernel
import Hironaka.Resolution.Algebraic.MaximalContact.Theorem97Induction
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Theorem 97: étale equivalent blow-up sequences are equal

[Kol07, Theorem 97]: two étale equivalent blow-up sequences of order `m` for an MC-invariant ideal
sheaf on a smooth variety over a field of characteristic zero are equal. The proof in this library
has two parts. The marked form (`eq_of_pullback_eq_of_agreeOn_of_step` in
`Hironaka/Resolution/Algebraic/MaximalContact/Theorem97Induction.lean`, a structural induction on
the common pull-back) and the reduction of Theorem 97 to it (`eq_of_etaleEquivSeq_of_step`) both
take the one inductive step the induction needs, the descent of agreement of two morphisms through
one blow-up, as an explicit hypothesis `hstep`; that step is `agreeOn_blowUpMap`
(`Hironaka/Resolution/Algebraic/MaximalContact/AgreeOnBlowUpKernel.lean`), in exactly the shape of
`hstep`. The two theorems below are the unconditional forms: `hstep := agreeOn_blowUpMap`.

**Conventions.** Theorem 97 needs no hypothesis on `I` beyond `m ≥ 1`: MC-invariance enters the
uniqueness of maximal contact only through Theorem 92, so Kollár's "MC-invariant" and
"`m = max-ord I`" are not hypotheses here (`Theorem97Induction.lean` explains why the marked form
uses no property of `I`). Kollár's "étale surjections" are read in the form of
[Kol07, Definition 96] where the images of `ψ, ψ'` contain the cosupport (`EtaleEquivSeq`,
`Hironaka/Resolution/Algebraic/MaximalContact/EtaleEquivSeq.lean`). The theorem is used for the
independence of the order-reduction functor from the hypersurface of maximal contact
(`Hironaka/Resolution/Algebraic/MaximalContact/FunctorIndependence.lean`).
-/

public section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open CategoryTheory Scheme BlowUpSequence

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- **The marked form of [Kol07, Theorem 97]**: for flat `ψ, ψ' : U ⟶ X` agreeing on `V(M)`,
blow-up sequences `B, B'` on `X` with the common pull-back `C` of order `≥ 1` for `(M, 1)`, and the
centres of `B`, `B'` in the images of the lifts, `B = B'`. This is
`eq_of_pullback_eq_of_agreeOn_of_step` with the one-step descent `agreeOn_blowUpMap`. -/
theorem eq_of_pullback_eq_of_agreeOn {U : Scheme.{u}} (ψ ψ' : U ⟶ X) [Flat ψ] [Flat ψ']
    (M : U.IdealSheafData) (h1 : AgreeOn ψ ψ' M) (B B' : BlowUpSequence X) (C : BlowUpSequence U)
    (hB : B.pullback ψ = C) (hB' : B'.pullback ψ' = C) (h2 : C.IsMarkedOneSeq M)
    (h3 : B.CentersInRange ψ) (h3' : B'.CentersInRange ψ') : B = B' :=
  eq_of_pullback_eq_of_agreeOn_of_step
    (fun f g C M hJ hM hfg => agreeOn_blowUpMap f g C M hJ hM hfg) ψ ψ' M h1 B B' C hB hB' h2 h3 h3'

/-- **[Kol07, Theorem 97]**: for `X` smooth of relative dimension `n` over `k` of characteristic
zero, `m ≥ 1`, smooth blow-up sequences `B` of order `m` for `(X, I, E)` and `B'` of order `m` for
`(X, I, E')` that are étale equivalent ([Kol07, Definition 96], with the images of `ψ, ψ'`
containing the cosupport), `B = B'`. -/
theorem eq_of_etaleEquivSeq [CharZero k] (f : X ⟶ Spec (.of k)) (n : ℕ)
    [SmoothOfRelativeDimension n f] {I : X.IdealSheafData} {m : ℕ} (hm : 1 ≤ m)
    {E E' : DivisorFamily X} {B B' : BlowUpSequence X} (hB : B.IsOrderSeq f I E m)
    (hB' : B'.IsOrderSeq f I E' m) (e : EtaleEquivSeq f I m B B') : B = B' :=
  eq_of_etaleEquivSeq_of_step (fun f g C M hJ hM hfg => agreeOn_blowUpMap f g C M hJ hM hfg)
    f n hm hB hB' e

end AlgebraicGeometry.Scheme.IdealSheafData
