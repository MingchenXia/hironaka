/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Assembly
public import Hironaka.Scheme.BlowUpSequence.ConcatPullback
public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.InducedClass
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.LoopFunctorial
import Hironaka.Resolution.Algebraic.MarkedOrderReduction.Step3Functorial
import Hironaka.Resolution.Algebraic.OrderReduction.Step21Functorial
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Clause (2) of marked order reduction: smooth surjections

Clause (2) of [Kol07, Theorem 107] with the first clause of [Kol07, 34.1] ("`B` commutes with every
smooth surjection `h`"; [Kol07, 111]: "the functoriality conditions are just as obvious as
before"): `BMO_{n,m}(Y, h^* I, m, h^{-1} E) = h^* BMO_{n,m}(X, I, m, E)` for a smooth surjection
`h`. The functor is the concatenation `Step 1 ++ Step 2 ++ Step 3` on the marked triples induced
after each step (`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Assembly.lean`); the pull-back
of a concatenation is the concatenation of the pull-backs, the later ones along the last-stage lifts
(`pullback_concat`), and each step commutes with the smooth surjective lift on the induced marked
triple, which carries the pull-back data of the triple induced on `X`
(`MarkedTriple.isPullbackOf_induced_last`): Step 1 by `step1_pullback_of_surjective`, Step 2 by
`step2_pullback_of_surjective`
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/LoopFunctorial.lean`) and Step 3 by
`step3Seq_pullback_of_surjective`
(`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Step3Functorial.lean`). The step values are
carried as subtype values (the sequence with its order and no-empty-centres proofs) through the
tails `tailAfterStep2` (after Step 2) and `tailAfterStep1` (after Step 1), so that the equality of a
step on `Y` with the pull-back of the step on `X` is substituted into the induced marked triple of
the next step without motive problems (`tailAfterStep2_pullback`, `tailAfterStep1_pullback`,
`concat_tailAfterStep1_pullback`). The second clause of [Kol07, 34.1], for an arbitrary smooth
morphism, is `Hironaka/Resolution/Algebraic/MarkedOrderReduction/Smooth.lean`.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Hironaka Scheme BlowUpSequence
  Scheme.IdealSheafData Hironaka.Sequence

namespace Hironaka.BMO

variable {k : Type u} [Field k] [CharZero k] {n : ℕ} (bo : ∀ d : ℕ, BOData.{u} n d) {m : ℕ}

/-- Step 3 of `BMO_{n,m}` after a Step-2 value `τ` (the sequence with its proofs) on the marked
triple `T` induced after Step 1, run on the marked triple induced at the end of `τ`: the tail of
the concatenation after Step 2. -/
noncomputable def tailAfterStep2 (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T)
    (τ : {R : BlowUpSequence T.X.left //
      R.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧ R.NoEmptyCenters}) :
    BlowUpSequence T.X.left :=
  τ.1.concat (step3Seq (T.induced τ.1 τ.2.1 (Fin.last _))
    (MarkedTriple.bmoClass_induced T hT τ.2.1 (Fin.last _)))

/-- Steps 2 and 3 of `BMO_{n,m}` after a Step-1 value `σ` (the sequence with its proofs), on the
marked triple induced at its end: the tail of the concatenation `bmoSeq`. -/
noncomputable def tailAfterStep1 (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T)
    (σ : {S : BlowUpSequence T.X.left //
      S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧ S.NoEmptyCenters}) :
    BlowUpSequence σ.1.last :=
  tailAfterStep2 (T.induced σ.1 σ.2.1 (Fin.last _))
    (MarkedTriple.bmoClass_induced T hT σ.2.1 (Fin.last _))
    (step2 bo (T.induced σ.1 σ.2.1 (Fin.last _))
      (MarkedTriple.bmoClass_induced T hT σ.2.1 (Fin.last _)))

/-- `bmoSeq` is Step 1 followed by its tail (definitional; the class proofs are irrelevant). -/
theorem bmoSeq_eq_concat_tailAfterStep1 (T : MarkedTriple k) (hT : MarkedTriple.BMOClass n m T) :
    bmoSeq bo T hT = (step1 bo T hT).1.concat (tailAfterStep1 bo T hT (step1 bo T hT)) :=
  rfl

/-- The tail after Step 2 under a smooth surjection: if the Step-2 value on the pull-back data is
the pull-back of the Step-2 value, the tail (Step 3) on the pull-back data is the pull-back of the
tail, by `step3Seq_pullback_of_surjective` on the marked triples induced after Step 2, along the
last-stage lift, which is smooth and surjective. -/
theorem tailAfterStep2_pullback (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T')
    (τ : {R : BlowUpSequence T.X.left //
      R.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧ R.NoEmptyCenters})
    (τ' : {R : BlowUpSequence T'.X.left //
      R.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E ∧ R.NoEmptyCenters})
    (e : τ'.1 = τ.1.pullback h) :
    tailAfterStep2 T' hT' τ' = (tailAfterStep2 T hT τ).pullback h := by
  obtain ⟨R', hR'⟩ := τ'
  dsimp only at e
  subst e
  have hsm₂ : @Smooth (T'.induced (τ.1.pullback h) hR'.1 (Fin.last _)).X.left
      (T.induced τ.1 τ.2.1 (Fin.last _)).X.left (τ.1.pullbackLastHom h) :=
    smooth_pullbackLastHom _ _
  dsimp only [tailAfterStep2]
  refine Eq.trans ?_ (pullback_concat _ _ _).symm
  exact congrArg (τ.1.pullback h).concat
    (step3Seq_pullback_of_surjective _ _ _ (surjective_pullbackLastHom _ _ hs)
      (MarkedTriple.isPullbackOf_induced_last h hp τ.2.1 hR'.1) _ _)

/-- The tail after Step 1 under a smooth surjection: the tail (Steps 2 and 3) on the pull-back of a
Step-1 value is the pull-back of the tail along the last-stage lift, by
`step2_pullback_of_surjective` on the induced marked triples (the lift is smooth and surjective,
and the induced triple carries the pull-back data), then `tailAfterStep2_pullback`. -/
theorem tailAfterStep1_pullback (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T') (S : BlowUpSequence T.X.left)
    (hS : S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧ S.NoEmptyCenters)
    (hS' : (S.pullback h).IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E ∧
      (S.pullback h).NoEmptyCenters) :
    tailAfterStep1 bo T' hT' ⟨S.pullback h, hS'⟩ =
      (tailAfterStep1 bo T hT ⟨S, hS⟩).pullback (S.pullbackLastHom h) := by
  have hpb₁ := MarkedTriple.isPullbackOf_induced_last h hp hS.1 hS'.1
  have hsm₁ : @Smooth (T'.induced (S.pullback h) hS'.1 (Fin.last _)).X.left
      (T.induced S hS.1 (Fin.last _)).X.left (S.pullbackLastHom h) := smooth_pullbackLastHom S h
  have hsurj₁ := surjective_pullbackLastHom S h hs
  have h2 := step2_pullback_of_surjective bo (T.induced S hS.1 (Fin.last _))
    (T'.induced (S.pullback h) hS'.1 (Fin.last _)) (S.pullbackLastHom h) hsurj₁ hpb₁
    (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _))
    (MarkedTriple.bmoClass_induced T' hT' hS'.1 (Fin.last _))
  dsimp only [tailAfterStep1]
  exact tailAfterStep2_pullback (T.induced S hS.1 (Fin.last _))
    (T'.induced (S.pullback h) hS'.1 (Fin.last _)) (S.pullbackLastHom h) hsurj₁ hpb₁
    (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _))
    (MarkedTriple.bmoClass_induced T' hT' hS'.1 (Fin.last _))
    (step2 bo (T.induced S hS.1 (Fin.last _))
      (MarkedTriple.bmoClass_induced T hT hS.1 (Fin.last _)))
    (step2 bo (T'.induced (S.pullback h) hS'.1 (Fin.last _))
      (MarkedTriple.bmoClass_induced T' hT' hS'.1 (Fin.last _))) h2

/-- The whole assembly under a smooth surjection: if the Step-1 value on the pull-back data is the
pull-back of the Step-1 value, the concatenation with the tail on the pull-back data is the
pull-back of the concatenation (`pullback_concat`, `tailAfterStep1_pullback`). -/
theorem concat_tailAfterStep1_pullback (T T' : MarkedTriple k) (h : T'.X.left ⟶ T.X.left) [Smooth h]
    (hs : Function.Surjective h) (hp : T'.IsPullbackOf T h) (hT : MarkedTriple.BMOClass n m T)
    (hT' : MarkedTriple.BMOClass n m T')
    (σ : {S : BlowUpSequence T.X.left //
      S.IsOrderGeSeq (T.X.left ↘ Spec (.of k)) T.I T.m T.E ∧ S.NoEmptyCenters})
    (σ' : {S : BlowUpSequence T'.X.left //
      S.IsOrderGeSeq (T'.X.left ↘ Spec (.of k)) T'.I T'.m T'.E ∧ S.NoEmptyCenters})
    (e : σ'.1 = σ.1.pullback h) :
    σ'.1.concat (tailAfterStep1 bo T' hT' σ') =
      (σ.1.concat (tailAfterStep1 bo T hT σ)).pullback h := by
  obtain ⟨S', hS'⟩ := σ'
  dsimp only at e
  subst e
  refine Eq.trans ?_ (pullback_concat _ _ _).symm
  exact congrArg (σ.1.pullback h).concat
    (tailAfterStep1_pullback bo T T' h hs hp hT hT' σ.1 σ.2 hS')

/-- **`BMO_{n,m}` commutes with smooth surjections** (clause (2) of [Kol07, Theorem 107] with the
first clause of [Kol07, 34.1]): the round parameters are preserved (`roundOrder_of_isPullbackOf`,
`sepOrder_of_isPullbackOf`), each round commutes by the field `commutesWithSmooth` of the
order-reduction data, and Step 3 by `realize_pullback_of_surjective` on the refining family
`refinesAlong_ofDivisorFamily` taken with Step 3's own enumeration of the components (the two
families coincide by `ofDivisorFamily_congr_of_forall`); no round is skipped and no blow-up is
deleted. -/
theorem commutesWithSmoothSurjections :
    (Hironaka.BMO.functor (k := k) bo m).CommutesWithSmoothSurjections := by
  intro T T' h _ hs hp hT hT'
  change bmoSeq bo T' hT' = (bmoSeq bo T hT).pullback h
  rw [bmoSeq_eq_concat_tailAfterStep1, bmoSeq_eq_concat_tailAfterStep1]
  exact concat_tailAfterStep1_pullback bo T T' h hs hp hT hT' (step1 bo T hT) (step1 bo T' hT')
    (step1_pullback_of_surjective bo T T' h hs hp hT hT')

end Hironaka.BMO
