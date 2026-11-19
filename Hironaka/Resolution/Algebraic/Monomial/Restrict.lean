/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Resolution.Algebraic.Monomial.State

/-!
# Functoriality of the combinatorial Step 3: the definitions

The two relations between states along which Kollár's Step 3 on the monomial state (`step3` of
`Hironaka/Resolution/Algebraic/Monomial/Step3Phases.lean`) is functorial. They are the combinatorial
shadows of the two clauses of [Kol07, 34.1]: a blow-up sequence functor commutes with smooth
surjections, and for an arbitrary smooth morphism `h` its value on the pull-back is the pull-back of
its value with the blow-ups of empty centre deleted and the sequence reindexed. Kollár's "the
functoriality conditions are just as obvious as before" at the end of [Kol07, 111, Step 3]
is the entire text on this point; the definitions and proofs are not in the sources.

* `Sub L N`: restriction to a down-closed subnerve. `L` has the same dimension bound, mark,
  counters, labels and exponents as `N`, and `L.nerve ⊆ N.nerve`. This is the state of `h⁻¹E`
  for a smooth `h : Y → X` along which every component stays irreducible (an open immersion,
  say): the faces are those meeting the image.
* `restrictRun L Ns`: the pulled-back run, the centres `Ns` of the run on `N` applied to `L` in
  order, each replaced by its faces in the current nerve of `L` (the faces outside are empty
  blow-ups, allocating dead components), the centres with no such face deleted, the deletion of
  empty blow-ups of [Kol07, 32] and [Kol07, 34.1].
* `Refines ρ Y L`: refinement along a map `ρ` of components. `ρ` preserves labels and exponents,
  is injective on every face of `Y`, and maps faces of `Y` onto faces of `L`. This is the state
  of `h⁻¹E` for a smooth surjection `h` along which components may split, such as
  `X ⊔ X → X`.

The theorems are proved in the submodules: `Restrict/Invariant.lean` (the invariant of the
restriction argument), `Restrict/Rename.lean` and `Restrict/Extend.lean` (the renumbering of
components between the direct and the pulled-back run), `Restrict/Phase.lean`
(`step3_restrict`), `Restrict/Refine.lean` and `Restrict/RefinePhase.lean` (`step3_refine`).
They feed the functoriality of the geometric Step 3 in
`Hironaka/Resolution/Algebraic/Monomial/Geometric/ChainRun.lean` and
`Hironaka/Resolution/Algebraic/Monomial/Geometric/PullbackRun.lean`.
-/

@[expose] public section

namespace Hironaka.Monomial.MonomialState

/-- `L` is the restriction of `N` to a down-closed subnerve: the same dimension bound, mark,
counters, labels and exponents, and `L.nerve ⊆ N.nerve`. -/
structure Sub (L N : MonomialState) : Prop where
  n_eq : L.n = N.n
  m_eq : L.m = N.m
  nextComp_eq : L.nextComp = N.nextComp
  nextLabel_eq : L.nextLabel = N.nextLabel
  label_eq : L.label = N.label
  a_eq : L.a = N.a
  nerve_sub : L.nerve ⊆ N.nerve

/-- The pulled-back run: the centres `Ns` applied to the state in order, each centre replaced by
its faces in the current nerve (its other faces are empty blow-ups), the centres with no face in
the current nerve deleted, as the empty blow-ups are deleted in [Kol07, 32] and
[Kol07, 34.1]. -/
def restrictRun : MonomialState → List (Finset (Finset ℕ)) → List (Finset (Finset ℕ))
  | _, [] => []
  | st, S :: Ns =>
    (if S.filter (· ∈ st.nerve) = ∅ then [] else [S.filter (· ∈ st.nerve)]) ++
      restrictRun (st.blowUp S) Ns

/-- `Y` refines `L` along `ρ`: the same dimension bound, mark and label count; `ρ` maps the
components of `Y` to components of `L` preserving labels and exponents, is injective on every
face of `Y`, maps faces to faces, and every face of `L` is the image of a face of `Y`. -/
structure Refines (ρ : ℕ → ℕ) (Y L : MonomialState) : Prop where
  n_eq : Y.n = L.n
  m_eq : Y.m = L.m
  nextLabel_eq : Y.nextLabel = L.nextLabel
  lt : ∀ c, c < Y.nextComp → ρ c < L.nextComp
  label_eq : ∀ c, c < Y.nextComp → L.label (ρ c) = Y.label c
  a_eq : ∀ c, c < Y.nextComp → L.a (ρ c) = Y.a c
  injOn : ∀ T ∈ Y.nerve, Set.InjOn ρ T
  image_mem : ∀ T ∈ Y.nerve, T.image ρ ∈ L.nerve
  exists_lift : ∀ T' ∈ L.nerve, ∃ T ∈ Y.nerve, T.image ρ = T'

end Hironaka.Monomial.MonomialState
