/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.Restrict.Extend
public import Hironaka.Resolution.Algebraic.Monomial.Restrict
public import Hironaka.Resolution.Algebraic.Monomial.Step3Phases
import Hironaka.Resolution.Algebraic.Monomial.Restrict.Refine
import Hironaka.Resolution.Algebraic.Monomial.Restrict.RefinePhase

/-!
# The run of a refining state as an explicit chain

`step3_refine` of `Hironaka/Resolution/Algebraic/Monomial/Restrict/RefinePhase.lean` describes the
run of Step 3 on a refining state `Y` as the `ρ'`-preimage run of the run on `L`, for some extension
`ρ'` of the parent map to the new components. The geometric fold of
`Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackRun.lean` needs the extension explicitly,
the new component of a face `Q` of `Y`'s centre being the child of the new component of `ρ(Q)`, so
this module re-runs the lockstep induction with the parent map carried as the explicit chain of
`extendComp`s (`Hironaka/Resolution/Algebraic/Monomial/Restrict/Extend.lean`):

* `chainRun ρ Y L Ns`: the run on `Y` induced by the run `Ns` on `L`. Each centre of `L` is
  replaced by the faces of the current nerve of `Y` mapping into it, and the parent map is
  extended by `extendComp` at each step;
* `chainMap`, `chainStateY`: the parent map and the state of `Y` after the chain;
* `phase_chain`, `phases_chain`, `step3_chain`: *the run of Step 3 on `Y` is the chain run of
  the run on `L`*, with `Refines` between the final states along the chain map.

The proofs are those of `phase_refine` and `phases_refine` with the stronger conclusion. Not in
the sources; bookkeeping for the first clause of [Kol07, 34.1].
-/

@[expose] public section

namespace Hironaka.Monomial.MonomialState

open Finset

/-! ### The chain run -/

/-- The run on `Y` induced by a run on `L` along the parent map `ρ`: each centre `S` of `L` is
replaced by the faces of the current nerve of `Y` mapping into `S`, and the parent map is
extended across the blow-up by `extendComp`. -/
def chainRun (ρ : ℕ → ℕ) : MonomialState → MonomialState → List (Finset (Finset ℕ)) →
    List (Finset (Finset ℕ))
  | _, _, [] => []
  | Y, L, S :: Ns =>
    (Y.nerve.filter fun Q => Q.image ρ ∈ S) ::
      chainRun (extendComp ρ Y L (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
        (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (L.blowUp S) Ns

/-- The parent map after the chain. -/
def chainMap (ρ : ℕ → ℕ) : MonomialState → MonomialState → List (Finset (Finset ℕ)) → (ℕ → ℕ)
  | _, _, [] => ρ
  | Y, L, S :: Ns =>
    chainMap (extendComp ρ Y L (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
      (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (L.blowUp S) Ns

/-- The state of `Y` after the chain. -/
def chainStateY (ρ : ℕ → ℕ) : MonomialState → MonomialState → List (Finset (Finset ℕ)) →
    MonomialState
  | Y, _, [] => Y
  | Y, L, S :: Ns =>
    chainStateY (extendComp ρ Y L (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
      (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (L.blowUp S) Ns

theorem chainRun_nil (ρ : ℕ → ℕ) (Y L : MonomialState) : chainRun ρ Y L [] = [] := rfl

theorem chainRun_cons (ρ : ℕ → ℕ) (Y L : MonomialState) (S : Finset (Finset ℕ))
    (Ns : List (Finset (Finset ℕ))) :
    chainRun ρ Y L (S :: Ns) = (Y.nerve.filter fun Q => Q.image ρ ∈ S) ::
      chainRun (extendComp ρ Y L (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
        (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (L.blowUp S) Ns := rfl

theorem chainMap_nil (ρ : ℕ → ℕ) (Y L : MonomialState) : chainMap ρ Y L [] = ρ := rfl

theorem chainMap_cons (ρ : ℕ → ℕ) (Y L : MonomialState) (S : Finset (Finset ℕ))
    (Ns : List (Finset (Finset ℕ))) :
    chainMap ρ Y L (S :: Ns) =
      chainMap (extendComp ρ Y L (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
        (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (L.blowUp S) Ns := rfl

theorem chainStateY_nil (ρ : ℕ → ℕ) (Y L : MonomialState) : chainStateY ρ Y L [] = Y := rfl

theorem chainStateY_cons (ρ : ℕ → ℕ) (Y L : MonomialState) (S : Finset (Finset ℕ))
    (Ns : List (Finset (Finset ℕ))) :
    chainStateY ρ Y L (S :: Ns) =
      chainStateY (extendComp ρ Y L (Y.nerve.filter fun Q => Q.image ρ ∈ S) S)
        (Y.blowUp (Y.nerve.filter fun Q => Q.image ρ ∈ S)) (L.blowUp S) Ns := rfl

/-- The state after the chain is the fold of the chain run. -/
theorem chainStateY_eq_foldl (ρ : ℕ → ℕ) : ∀ (Y L : MonomialState) (Ns : List (Finset (Finset ℕ))),
    chainStateY ρ Y L Ns = (chainRun ρ Y L Ns).foldl blowUp Y
  | _, _, [] => rfl
  | Y, L, S :: Ns => by
    rw [chainStateY_cons, chainRun_cons, List.foldl_cons]
    exact chainStateY_eq_foldl _ _ _ Ns

/-- The chain along a concatenation. -/
theorem chainRun_append (ρ : ℕ → ℕ) : ∀ (Y L : MonomialState) (N₁ N₂ : List (Finset (Finset ℕ))),
    chainRun ρ Y L (N₁ ++ N₂) =
      chainRun ρ Y L N₁ ++
        chainRun (chainMap ρ Y L N₁) (chainStateY ρ Y L N₁) (N₁.foldl blowUp L) N₂
  | _, _, [], _ => rfl
  | Y, L, S :: N₁, N₂ => by
    rw [List.cons_append, chainRun_cons, chainRun_cons, chainMap_cons, chainStateY_cons,
      List.foldl_cons, List.cons_append]
    exact congrArg _ (chainRun_append _ _ _ N₁ N₂)

theorem chainMap_append (ρ : ℕ → ℕ) : ∀ (Y L : MonomialState) (N₁ N₂ : List (Finset (Finset ℕ))),
    chainMap ρ Y L (N₁ ++ N₂) =
      chainMap (chainMap ρ Y L N₁) (chainStateY ρ Y L N₁) (N₁.foldl blowUp L) N₂
  | _, _, [], _ => rfl
  | Y, L, S :: N₁, N₂ => by
    rw [List.cons_append, chainMap_cons, chainMap_cons, chainStateY_cons, List.foldl_cons]
    exact chainMap_append _ _ _ N₁ N₂

theorem chainStateY_append (ρ : ℕ → ℕ) :
    ∀ (Y L : MonomialState) (N₁ N₂ : List (Finset (Finset ℕ))),
    chainStateY ρ Y L (N₁ ++ N₂) =
      chainStateY (chainMap ρ Y L N₁) (chainStateY ρ Y L N₁) (N₁.foldl blowUp L) N₂
  | _, _, [], _ => rfl
  | Y, L, S :: N₁, N₂ => by
    rw [List.cons_append, chainStateY_cons, chainStateY_cons, chainMap_cons, List.foldl_cons]
    exact chainStateY_append _ _ _ N₁ N₂

/-! ### The lockstep, with the chain -/

/-- `phase_refine` with the explicit chain: the phase-`r` run on `Y` is the chain run of the
phase-`r` run on `L`, and the final states refine along the chain map. -/
theorem phase_chain (r : ℕ) : ∀ (L : MonomialState) (hsL : ∀ s < r, L.Star s) (Y : MonomialState)
    (ρ : ℕ → ℕ), Refines ρ Y L → ∀ hsY : ∀ s < r, Y.Star s,
    Refines (chainMap ρ Y L (phase r L hsL).2) (phase r Y hsY).1 (phase r L hsL).1 ∧
      (phase r Y hsY).2 = chainRun ρ Y L (phase r L hsL).2 ∧
      (phase r Y hsY).1 = chainStateY ρ Y L (phase r L hsL).2 := by
  intro L hsL
  induction L, hsL using phase.induct r with
  | case1 L hsL hne ih =>
    intro Y ρ href hsY
    have hYne : (Y.choice r).Nonempty := (href.choice_nonempty_iff r).mpr hne
    rw [phase_of_nonempty L hsL hne, phase_of_nonempty Y hsY hYne]
    have hSY : Y.choice r ⊆ Y.nerve := (Y.isCenter_choice r).1
    have hSL : L.choice r = (Y.choice r).image (Finset.image ρ) := href.choice_image r
    have hpre : ∀ Q ∈ Y.nerve, Q.image ρ ∈ L.choice r → Q ∈ Y.choice r := fun Q hQ hQL => by
      rw [href.choice_eq]; exact Finset.mem_filter.mpr ⟨hQ, hQL⟩
    have hfil : (Y.nerve.filter fun Q => Q.image ρ ∈ L.choice r) = Y.choice r :=
      (href.choice_eq r).symm
    obtain ⟨href', hrun, hst⟩ := ih (Y.blowUp (Y.choice r)) _ (href.blowUp hSY hSL hpre)
      (fun _ hsr => Y.star_blowUp hsY hsr)
    simp only [chainRun_cons, chainMap_cons, chainStateY_cons, hfil]
    exact ⟨href', by rw [hrun], hst⟩
  | case2 L hsL hne =>
    intro Y ρ href hsY
    have hYe : ¬ (Y.choice r).Nonempty := fun hY => hne ((href.choice_nonempty_iff r).mp hY)
    rw [phase_of_not_nonempty L hsL hne, phase_of_not_nonempty Y hsY hYe]
    exact ⟨href, rfl, rfl⟩

/-- `phases_refine` with the explicit chain. -/
theorem phases_chain (k : ℕ) : ∀ (r : ℕ) (L : MonomialState) (hsL : ∀ s < r, L.Star s)
    (Y : MonomialState) (ρ : ℕ → ℕ), Refines ρ Y L → ∀ hsY : ∀ s < r, Y.Star s,
    Refines (chainMap ρ Y L (phases k r L hsL).2) (phases k r Y hsY).1 (phases k r L hsL).1 ∧
      (phases k r Y hsY).2 = chainRun ρ Y L (phases k r L hsL).2 ∧
      (phases k r Y hsY).1 = chainStateY ρ Y L (phases k r L hsL).2 := by
  induction k with
  | zero =>
    intro r L hsL Y ρ href hsY
    exact ⟨href, rfl, rfl⟩
  | succ k ih =>
    intro r L hsL Y ρ href hsY
    rw [phases_succ, phases_succ]
    obtain ⟨href₁, hrun₁, hst₁⟩ := phase_chain r L hsL Y ρ href hsY
    obtain ⟨href', hrun', hst'⟩ := ih (r + 1) _ (phase_star_succ L hsL) _ _ href₁
      (phase_star_succ Y hsY)
    have hfoldL : (phase r L hsL).1 = (phase r L hsL).2.foldl blowUp L := phase_fst_eq_foldl L hsL
    simp only
    rw [chainRun_append, chainMap_append, chainStateY_append, ← hst₁, ← hfoldL]
    exact ⟨href', by rw [hrun₁, hrun'], hst'⟩

/-- The run of Step 3 on a refining state `Y` is the chain run of the run of Step 3 on `L`, and
the final states refine along the chain map. -/
theorem step3_chain {ρ : ℕ → ℕ} {Y L : MonomialState} (h : Refines ρ Y L) :
    Refines (chainMap ρ Y L (step3 L).2) (step3 Y).1 (step3 L).1 ∧
      (step3 Y).2 = chainRun ρ Y L (step3 L).2 ∧ (step3 Y).1 = chainStateY ρ Y L (step3 L).2 := by
  have e : step3 Y = phases L.n 1 Y (star_of_lt_one Y) := by rw [step3, h.n_eq]
  rw [e, step3]
  exact phases_chain L.n 1 L (star_of_lt_one L) Y ρ h (star_of_lt_one Y)

end Hironaka.Monomial.MonomialState
