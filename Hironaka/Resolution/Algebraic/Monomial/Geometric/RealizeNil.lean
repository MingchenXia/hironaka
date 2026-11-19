/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.MarkedOrderReduction.MonomialPart
public import Hironaka.Resolution.Algebraic.Monomial.Geometric.Pieces
public import Hironaka.Scheme.IdealSheaf.Order.Constructible
import Hironaka.Resolution.Algebraic.Monomial.Geometric.Exponent
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# The empty run of Step 3: below the mark, Step 3 does nothing

The last paragraph of [Kol07, 111] proves clause (3) of Theorem 107: when `E = ∅` and
`m = max-ord I`, after Step 1 the cosupport of the marked transform is empty and its monomial
part is `𝒪_{X¹}`, "Steps 2 and 3 do nothing". On the combinatorial side Step 3 is the sequence
of phases `1, …, n`, each blowing up Kollár's choice of faces while `(∗_r)` fails
(`Hironaka/Resolution/Algebraic/Monomial/Step3Phases.lean`); on a state that already satisfies
`(∗_s)` for every `s`, every face having sum `< m`, every choice is empty and the run is `[]`
(`step3_eq_of_star`). Geometrically the realised sequence of the empty run is the empty blow-up
sequence (`realize_eq_nil`), and the state of a piece family whose marked monomial ideal has
`max-ord < m` satisfies every `(∗_s)`: each face of the nerve lies in the face of some point,
whose sum is the order of the monomial ideal there (`ord_monomial_eq_total` of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/Exponent.lean`), hence `< m`
(`star_toState_of_maxOrd_lt`). These three lemmas are what
`Hironaka/Resolution/Algebraic/MarkedOrderReduction/Clause3.lean` uses for the Step 3 half of clause
(3). Not in the sources as statements. -/

public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace Scheme Scheme.IdealSheafData

namespace Hironaka.Monomial

namespace MonomialState

/-- The phases `r, …, r + k − 1` of Step 3 on a state satisfying every `(∗_s)`: no choice is
ever made, the state is unchanged and the run is empty. -/
theorem phases_eq_of_star : ∀ (k r : ℕ) (st : MonomialState) (hs : ∀ s < r, st.Star s),
    (∀ s, st.Star s) → phases k r st hs = (st, [])
  | 0, _, _, _, _ => rfl
  | k + 1, r, st, hs, h => by
    have hp : phase r st hs = (st, []) :=
      phase_of_not_nonempty st hs (by rw [choice_nonempty_iff]; exact not_not.2 (h r))
    rw [phases_succ]
    generalize phase_star_succ st hs = q
    revert q
    rw [hp]
    intro q
    dsimp only
    rw [phases_eq_of_star k (r + 1) st q h]
    rfl

/-- The combinatorial Step 3 on a state that already satisfies `(∗_s)` for every `s` (every
face has sum `< m`) is the empty run: Kollár's "eventually we reach the stage where the
property `(∗_r)` also holds" of [Kol07, 111, Step 3.r] is reached at once. -/
theorem step3_eq_of_star (st : MonomialState) (h : ∀ s, st.Star s) : step3 st = (st, []) :=
  phases_eq_of_star st.n 1 st (star_of_lt_one st) h

end MonomialState

namespace PieceFamily

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
  {E : DivisorFamily X} (Φ : PieceFamily X) {e : E.ι ≃o Fin Φ.nextLabel} {n m : ℕ}

/-- When the marked monomial ideal of a piece family has `max-ord < m`, its state satisfies
`(∗_s)` for every `s`: a face of the nerve is contained in the face of any point of its
stratum, whose sum is the order of the monomial ideal there (`ord_monomial_eq_total`), hence
`< m`. This is the Step 3 half of "Steps 2 and 3 do nothing" in the last paragraph of
[Kol07, 111]. -/
theorem star_toState_of_maxOrd_lt [CharZero k] [QuasiCompact f]
    (hE : E.IsSnc) (hΦ : Φ.Realizes E e) (hV : Φ.IsValid n m)
    (h : (E.monomial Φ.exponentAt).maxOrd < (m : ℕ∞)) (s : ℕ) : (Φ.toState n m hV).Star s := by
  intro T hT
  rw [MonomialState.mem_faces] at hT
  obtain ⟨hsub, -, hne⟩ := (mem_nerve (Φ := Φ)).1 hT.1
  obtain ⟨x, hx⟩ : ((Φ.faceSet T : Set X)).Nonempty :=
    Set.nonempty_iff_ne_empty.2 fun h0 =>
      hne (SetLike.coe_injective (h0.trans (Closeds.coe_bot (α := X)).symm))
  have hTsub : T ⊆ Φ.faceAt x := fun c hc =>
    (mem_faceAt (Φ := Φ)).2 ⟨Finset.mem_range.1 (hsub hc), (mem_faceSet (Φ := Φ)).1 hx c hc⟩
  have h1 : Φ.total T ≤ Φ.total (Φ.faceAt x) := Finset.sum_le_sum_of_subset hTsub
  have h2 : (Φ.total (Φ.faceAt x) : ℕ∞) < m := by
    rw [← ord_monomial_eq_total (f := f) (Φ := Φ) hE hΦ x]
    exact lt_of_le_of_lt (IdealSheafData.le_maxOrd (I := E.monomial Φ.exponentAt) x) h
  change Φ.total T < m
  exact lt_of_le_of_lt h1 (by exact_mod_cast h2)

end PieceFamily

namespace PieceFamily

/-- The geometric Step 3 of a family whose state satisfies `(∗_s)` for every `s` is the empty
sequence, the fold of the empty run (`step3_eq_of_star`). The structure morphism `f` is present
because every statement about `realize` is made over the structure morphism of `X`, the
realisation being a construction on triples over `k`; the proof does not need it, since the run is
empty and the fold of the empty run is `nil` on any scheme. -/
theorem realize_eq_nil {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k))
    {n m : ℕ} (Φ : PieceFamily X) (hV : Φ.IsValid n m)
    (h : ∀ s, (Φ.toState n m hV).Star s) : Φ.realize n m hV = BlowUpSequence.nil X := by
  have _ := f
  unfold realize
  rw [MonomialState.step3_eq_of_star _ h]
  rfl

end PieceFamily

end Hironaka.Monomial
