/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.BoundaryClearing.Data
public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces
public import Hironaka.Resolution.Algebraic.Monomial.Restrict
import Hironaka.Resolution.Algebraic.Monomial.Geometric.PullbackRun
import Hironaka.Scheme.BlowUpSequence.BaseChange
import Hironaka.Scheme.BlowUpSequence.BaseChangeOrder
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The realised Step 3 under a change of fields

[Kol07, 34.2] for the geometric Step 3: for the base change `p : X_L → X` of a triple along a
field extension `σ : k ↪ L` (`Triple.IsBaseChangeOf` of
`Hironaka/Scheme/BlowUpSequence/FunctorVocabulary.lean`: a cartesian square over `Spec σ`, the
ideal and the boundary pulled back), the realised Step 3 on `X_L` is the base change of the
realised Step 3 on `X`, with no empty blow-up to delete, as Kollár's display of the base-changed
sequence with every centre `(Z_i)_{L,σ}` says. Not in the sources as a statement; Kollár treats the
change of fields as evident.

The three statements are the flat, surjective-on-points instances of the general forms of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Refinement.lean` and
`Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackRun.lean`: `p` is flat and surjective on
points (`IsBaseChangeOf.flat`, `IsBaseChangeOf.surjective`), the pulled-back boundary is snc because
it is the boundary of the base-changed triple, `X_L` is Noetherian (of finite type over `L`), and
the dimension bound over `L` is a hypothesis `hn'`.

* `exists_refinesAlong_baseChange`: the refining family exists (`exists_refinesAlong_of_flat`).
  Its witness is `ofDivisorFamily (E.comap p) (Φ.exponentAt ∘ p) e σ'` on the irreducible
  components of the pulled-back members, refining `Φ` through the parent map `parentOf`
  (`refinesAlong_ofDivisorFamily`): the image of the generic point of a component of `(D_c)_L`
  is the generic point of `D_c` (flat morphisms are generalising), so the child carries the
  parent's exponent.
* `refines_toState_of_isBaseChangeOf`: the state of `X_L` refines the full state of `X`
  (`refines_toState_of_surjective`, which uses no smoothness: every face of `X` has a point over
  `X_L` because `p` is surjective on points).
* `realize_pullback_of_isBaseChangeOf`: the fold. The run on `X_L` is the chain run of the run
  on `X` (`step3_chain` of `Hironaka/Resolution/Algebraic/Monomial/Geometric/ChainRun.lean`), and
  the chain run realises the pull-back (`realizeAux_pullback_of_surjective` with `X_L`'s own
  structure morphism over `L`; the label match is `component_comap_memberOf` for `E' = E.comap p`).

The third statement is what `Hironaka/Resolution/Algebraic/MarkedOrderReduction/BaseChangeLoop.lean`
uses for the Step 3 part of clause (2) of [Kol07, Theorem 107].
-/

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace Hironaka Scheme.IdealSheafData

namespace Hironaka.Monomial.PieceFamily

variable {k : Type u} [Field k] [CharZero k] {L : Type u} [Field L] {T : Triple k} {T' : Triple L}
  {σ : k →+* L} {p : T'.X.left ⟶ T.X.left} (Φ : PieceFamily T.X.left)
  {e : T.E.ι ≃o Fin Φ.nextLabel} {n m : ℕ}

omit [CharZero k] in
/-- The boundary of the base-changed triple is snc; read on `T.E.comap p` through the third
clause of the base-change data. -/
theorem isSnc_comap_of_isBaseChangeOf (hbc : T'.IsBaseChangeOf T σ p) : (T.E.comap p).IsSnc :=
  hbc.2.2 ▸ T'.isSnc

omit [CharZero k] in
/-- [Kol07, 34.2], the refining family: a piece family of `T'.X.left` refining `Φ` along the base
change `p` exists and realises `T.E.comap p` (`exists_refinesAlong_of_flat`, whose witness is
`ofDivisorFamily (T.E.comap p) (Φ.exponentAt ∘ p) e σ'` refining `Φ` through `parentOf`): the
components of `(D_c)_L` each dominate `D_c` with the parent's exponent. `p` is flat
(`IsBaseChangeOf.flat`), `T'.X.left` is Noetherian (of finite type over `L`), and `T.E.comap p` is
snc (`isSnc_comap_of_isBaseChangeOf`). -/
theorem exists_refinesAlong_baseChange (hbc : T'.IsBaseChangeOf T σ p) (hΦ : Φ.Realizes T.E e) :
    ∃ (Φ' : PieceFamily T'.X.left) (ρ : ℕ → ℕ) (hρ : Φ'.RefinesAlong p ρ Φ),
      Φ'.Realizes (T.E.comap p) (e.trans (Fin.castOrderIso hρ.nextLabel_eq.symm)) := by
  have := hbc.flat
  have hN : IsNoetherian T'.X.left := (T'.X.left ↘ Spec (CommRingCat.of L)).isNoetherian_of_field
  exact Φ.exists_refinesAlong_of_flat (T.X.left ↘ Spec (CommRingCat.of k)) p T.isSnc hΦ
    (isSnc_comap_of_isBaseChangeOf hbc)

omit [CharZero k] in
/-- [Kol07, 34.2], the states: the state of a refining family of `T'.X.left` refines the full state
of `T.X.left` (`refines_toState_of_surjective` with `IsBaseChangeOf.surjective`; no smoothness is
used). -/
theorem refines_toState_of_isBaseChangeOf (hbc : T'.IsBaseChangeOf T σ p) (hV : Φ.IsValid n m)
    {Φ' : PieceFamily T'.X.left} {ρ : ℕ → ℕ} (hρ : Φ'.RefinesAlong p ρ Φ) (hV' : Φ'.IsValid n m) :
    MonomialState.Refines ρ (Φ'.toState n m hV') (Φ.toState n m hV) :=
  refines_toState_of_surjective hρ hbc.surjective hV hV'

/-- [Kol07, 34.2], "the blow-up sequence `(π_i)_{L,σ}` with centres `(Z_i)_{L,σ}`": *the
geometric Step 3 on `T'.X.left` is the base change of the geometric Step 3 on `T.X.left`*. The run
on `T'.X.left` is the chain run of the run on `T.X.left` (`step3_chain` on
`refines_toState_of_isBaseChangeOf`) and the chain run realises the pull-back
(`realizeAux_pullback_of_surjective`, with `T'.X.left`'s own structure morphism over `L`, the
dimension bound `hn'`, the label match `component_comap_memberOf` from the refinement alone, the
snc of `T.E.comap p` from `T'`, and the perfect fields from characteristic zero, `L` having
characteristic zero through `σ`). No empty blow-up is deleted. -/
theorem realize_pullback_of_isBaseChangeOf (hbc : T'.IsBaseChangeOf T σ p) (hΦ : Φ.Realizes T.E e)
    (hV : Φ.IsValid n m) (hn : T.HasDimLE n) (hn' : T'.HasDimLE n) {Φ' : PieceFamily T'.X.left}
    {ρ : ℕ → ℕ} (hρ : Φ'.RefinesAlong p ρ Φ)
    (hΦ' : Φ'.Realizes (T.E.comap p) (e.trans (Fin.castOrderIso hρ.nextLabel_eq.symm)))
    (hV' : Φ'.IsValid n m) :
    Φ'.realize n m hV' = (Φ.realize n m hV).pullback p := by
  have := hbc.flat
  have hL : CharZero L := charZero_of_ringHom σ
  have hE' : (T.E.comap p).IsSnc := isSnc_comap_of_isBaseChangeOf hbc
  have hR := refines_toState_of_surjective hρ hbc.surjective hV hV'
  obtain ⟨-, hrun, -⟩ := MonomialState.step3_chain hR
  have hlab := component_comap_memberOf (e := e) hρ
  change realizeAux Φ' m (MonomialState.step3 (Φ'.toState n m hV')).2 =
    (realizeAux Φ m (MonomialState.step3 (Φ.toState n m hV)).2).pullback p
  rw [hrun]
  exact realizeAux_pullback_of_surjective _ (T.X.left ↘ Spec (CommRingCat.of k))
    (T'.X.left ↘ Spec (CommRingCat.of L)) p hbc.surjective Φ T.isSnc hΦ hV hn
    (MonomialState.step3_isRun _) Φ' hρ.toW hE' hΦ' hlab hV' hn' hR

end Hironaka.Monomial.PieceFamily
