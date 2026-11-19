/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.Topology.JacobsonSpace

/-!
# Covering a closed set by neighbourhoods of its closed points

In a Jacobson space every point `x` of a closed set `S` specializes to a closed point `p ∈ S`
(a closed point of the closed set `closure {x}`), and an open set containing `p` contains `x`.
Hence open sets around the closed points of `S` cover `S`.

* `exists_isClosed_singleton_mem_specializes`: the closed point `p` with `x ⤳ p`.
* `subset_iUnion_of_isOpen_of_closedPoints`: the covering statement.

Kollár's proof of the uniqueness of maximal contact up to étale equivalence
[Kol07, 95 (proof of Theorem 92)] constructs an étale neighbourhood `U(p)` at each point `p` and
concludes that "the images of finitely many of the `U(p)` cover `X`"; the neighbourhoods are built
at closed points, and this file supplies the topology that makes them cover. A scheme locally of
finite type over a field is a Jacobson space (`LocallyOfFiniteType.jacobsonSpace`). Not stated in
the source.
-/

public section


variable {X : Type*} [TopologicalSpace X]

/-- In a Jacobson space, every point `x` of a closed set `S` specializes to a closed point
`p ∈ S` — a closed point of the closed set `closure {x} ⊆ S`. -/
theorem exists_isClosed_singleton_mem_specializes [JacobsonSpace X] {S : Set X} (hS : IsClosed S)
    {x : X} (hx : x ∈ S) : ∃ p, IsClosed {p} ∧ p ∈ S ∧ x ⤳ p := by
  obtain ⟨p, hp, hpc⟩ := nonempty_inter_closedPoints (Z := closure {x})
    ⟨x, subset_closure rfl⟩ ⟨Set.univ, closure {x}, isOpen_univ, isClosed_closure,
      (Set.univ_inter _).symm⟩
  exact ⟨p, hpc, (hS.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx)) hp,
    specializes_iff_mem_closure.mpr hp⟩

/-- Open sets `O p` around the closed points `p` of a closed set `S` of a Jacobson space cover
`S`: the closed points are dense in `S`, and each point of `S` lies in the open set attached to a
closed point it specializes to. -/
theorem subset_iUnion_of_isOpen_of_closedPoints [JacobsonSpace X] {S : Set X} (hS : IsClosed S)
    (O : {p : X // IsClosed {p} ∧ p ∈ S} → Set X) (hO : ∀ p, IsOpen (O p))
    (hpO : ∀ p, p.1 ∈ O p) : S ⊆ ⋃ p, O p := by
  intro x hx
  obtain ⟨p, hpc, hpS, hxp⟩ := exists_isClosed_singleton_mem_specializes hS hx
  exact Set.mem_iUnion.mpr ⟨⟨p, hpc, hpS⟩, hxp.mem_open (hO _) (hpO _)⟩

