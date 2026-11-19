/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Hironaka.Geometry.StableModification.CurvesField.Trees
import Mathlib.Topology.Connected.Clopen

/-!
# Topological and combinatorial connectedness of a subcurve

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.4.2 (T:3131–3133): Corollary B.2 is applied to the fibre `Z = f⁻¹(x)`, which is connected
by Zariski's connectedness theorem (`Cohomology.ConnectedBirationalHeight`). The combinatorial
form of Corollary B.2 (`BlowDown.Criterion`, `CurvesField.Trees`) uses connectedness of the set of
components of `Z` in the sense of the incidence data (`IncidenceGraph.IsConnected`: every proper
nonempty part is joined to the rest by a double point). This file proves that the two notions agree
(blueprint `prop:sm-bd-graph-connected`, chapter `sm-cohomology-connected-birational-height.tex`).

## Setting

`G` is the incidence data of a reduced curve over an algebraically closed field (CRV1's
`IncidenceGraph`: components `V`, double points `E` with the components `ends e` of their branches).
A *realization* of `G` along a set `Y` of components (`IsRealization`) consists of subsets
`C v ⊆ T` (the components, in some ambient space `T` such as the underlying space of the curve) and
points `pt e ∈ T` (the double points) such that

* each double point with both branches on `Y` lies on the components of its two branches
  (`ends_mem`), and
* two distinct components of `Y` meet only if some double point has its branches on them
  (`exists_ends`).

For a curve all of whose points on `Y` are smooth or ordinary double points (for instance `Y` in
the semi-stable locus) this is the defining property of the incidence data
(`def:sm-incidence-graph`).

## Main results

* `isPreconnected_biUnion_of_isConnected`: if `G.IsConnected Y` and the `C v` are preconnected,
  `⋃_{v ∈ Y} C v` is preconnected.
* `isConnected_of_isPreconnected_biUnion`: conversely, if the `C v` are closed and nonempty and
  `⋃_{v ∈ Y} C v` is preconnected, then `G.IsConnected Y`.
* `isConnected_iff_isConnected_biUnion`, `isConnected_iff_of_genericPoints`: the equivalence,
  in particular for components given as closures `closure {η_v}` of generic points.
-/

namespace Hironaka.StableModification.BlowDown

open Finset CurvesField CurvesField.IncidenceGraph

universe u v w t

variable {T : Type t} [TopologicalSpace T]
variable {V : Type u} {E : Type v} {M : Type w} (G : IncidenceGraph V E M)
  [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype M] [DecidableEq M]

/-- A **realization** of the incidence data `G` along a set `Y` of components by subsets
`C v` (the components) and points `pt e` (the double points) of a space `T`: double points with
both branches on `Y` lie on both branch components, and two distinct components of `Y` meet only
when a double point joins them. -/
structure IsRealization (C : V → Set T) (pt : E → T) (Y : Finset V) : Prop where
  /-- A double point with branches on `a, b ∈ Y` lies on `C a` and on `C b`. -/
  ends_mem : ∀ e a b, G.ends e = s(a, b) → a ∈ Y → b ∈ Y → pt e ∈ C a ∧ pt e ∈ C b
  /-- Two distinct components of `Y` which meet are joined by a double point. -/
  exists_ends : ∀ a ∈ Y, ∀ b ∈ Y, a ≠ b → (C a ∩ C b).Nonempty → ∃ e, G.ends e = s(a, b)

variable {G}

/-- **Connected incidence data give a connected curve**: if `G.IsConnected Y` and the components
`C v`, `v ∈ Y`, are preconnected, then `⋃_{v ∈ Y} C v` is preconnected. -/
theorem isPreconnected_biUnion_of_isConnected {C : V → Set T} {pt : E → T} {Y : Finset V}
    (h : IsRealization G C pt Y) (hC : ∀ v ∈ Y, IsPreconnected (C v)) (hY : G.IsConnected Y) :
    IsPreconnected (⋃ v ∈ Y, C v) := by
  classical
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u w hu hw hcov hdisj
  have hsub : ∀ v ∈ Y, C v ⊆ ⋃ x ∈ Y, C x := fun v hv => Set.subset_biUnion_of_mem (u := C) hv
  -- every component lies in `u` or in `w`
  have huw : ∀ v ∈ Y, C v ⊆ u ∨ C v ⊆ w := by
    intro v hv
    refine (isPreconnected_iff_subset_of_disjoint_closed.mp (hC v hv)) u w hu hw
      ((hsub v hv).trans hcov) ?_
    refine Set.eq_empty_of_subset_empty ?_
    rw [← hdisj]
    exact Set.inter_subset_inter_left _ (hsub v hv)
  have hnot : ∀ t ∈ ⋃ x ∈ Y, C x, t ∈ u → t ∈ w → False := by
    intro t ht htu htw
    have : t ∈ (⋃ x ∈ Y, C x) ∩ (u ∩ w) := ⟨ht, htu, htw⟩
    rw [hdisj] at this
    exact this
  let X : Finset V := Y.filter fun v => C v ⊆ u
  have hXY : X ⊆ Y := filter_subset _ _
  by_cases hXeq : X = Y
  · left
    refine Set.iUnion₂_subset fun v hv => ?_
    have : v ∈ X := hXeq ▸ hv
    exact (mem_filter.mp this).2
  by_cases hXne : X.Nonempty
  · obtain ⟨e, he, heb⟩ := hY.2 X hXY hXne hXeq
    obtain ⟨a, b, hab⟩ := exists_ends (G := G) e
    obtain ⟨haY, hbY⟩ := (mem_inner_of_ends hab).mp he
    have hpt := h.ends_mem e a b hab haY hbY
    have hcomp : ∀ x ∈ Y, x ∉ X → C x ⊆ w := fun x hx hxX =>
      (huw x hx).resolve_left fun hxu => hxX (mem_filter.mpr ⟨hx, hxu⟩)
    exfalso
    rcases (mem_boundary_of_ends hab).mp heb with ⟨haX, hbX⟩ | ⟨haX, hbX⟩
    · exact hnot _ (hsub a haY hpt.1) ((mem_filter.mp haX).2 hpt.1) (hcomp b hbY hbX hpt.2)
    · exact hnot _ (hsub b hbY hpt.2) ((mem_filter.mp hbX).2 hpt.2) (hcomp a haY haX hpt.1)
  · right
    refine Set.iUnion₂_subset fun v hv => ?_
    refine (huw v hv).resolve_left fun hvu => hXne ⟨v, mem_filter.mpr ⟨hv, hvu⟩⟩

/-- **A connected curve has connected incidence data**: if the components `C v`, `v ∈ Y`, are
closed and nonempty, `Y` is nonempty and `⋃_{v ∈ Y} C v` is preconnected, then `G.IsConnected Y`.
-/
theorem isConnected_of_isPreconnected_biUnion {C : V → Set T} {pt : E → T} {Y : Finset V}
    (h : IsRealization G C pt Y) (hC : ∀ v ∈ Y, IsClosed (C v))
    (hne : ∀ v ∈ Y, (C v).Nonempty) (hY : Y.Nonempty)
    (hU : IsPreconnected (⋃ v ∈ Y, C v)) : G.IsConnected Y := by
  classical
  refine ⟨hY, fun X hXY hXne hXeq => ?_⟩
  by_contra hno
  push Not at hno
  let A : Set T := ⋃ v ∈ X, C v
  let A' : Set T := ⋃ v ∈ Y \ X, C v
  have hA : IsClosed A := (X.finite_toSet).isClosed_biUnion fun v hv => hC v (hXY hv)
  have hA' : IsClosed A' := ((Y \ X).finite_toSet).isClosed_biUnion fun v hv =>
    hC v (mem_sdiff.mp hv).1
  have hcov : (⋃ v ∈ Y, C v) ⊆ A ∪ A' := by
    refine Set.iUnion₂_subset fun v hv => ?_
    by_cases hvX : v ∈ X
    · exact (Set.subset_biUnion_of_mem (u := C) hvX).trans Set.subset_union_left
    · exact (Set.subset_biUnion_of_mem (u := C) (show v ∈ Y \ X from mem_sdiff.mpr ⟨hv, hvX⟩)).trans
        Set.subset_union_right
  -- `A` and `A'` do not meet
  have hAA' : ∀ t, t ∈ A → t ∈ A' → False := by
    intro t htA htA'
    obtain ⟨a, haX, hta⟩ := Set.mem_iUnion₂.mp htA
    obtain ⟨b, hbYX, htb⟩ := Set.mem_iUnion₂.mp htA'
    obtain ⟨hbY, hbX⟩ := mem_sdiff.mp hbYX
    have hab : a ≠ b := fun h => hbX (h ▸ haX)
    obtain ⟨e, he⟩ := h.exists_ends a (hXY haX) b hbY hab ⟨t, hta, htb⟩
    exact hno e ((mem_inner_of_ends he).mpr ⟨hXY haX, hbY⟩)
      ((mem_boundary_of_ends he).mpr (Or.inl ⟨haX, hbX⟩))
  have hdisj : (⋃ v ∈ Y, C v) ∩ (A ∩ A') = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ⟨_, htA, htA'⟩ => hAA' t htA htA'
  obtain ⟨b, hbY, hbX⟩ := exists_of_ssubset (ssubset_of_subset_of_ne hXY hXeq)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hU) A A' hA hA' hcov hdisj with hs | hs
  · obtain ⟨t, ht⟩ := hne b hbY
    have htU : t ∈ ⋃ v ∈ Y, C v := Set.mem_biUnion hbY ht
    exact hAA' t (hs htU) (Set.mem_biUnion (show b ∈ Y \ X from mem_sdiff.mpr ⟨hbY, hbX⟩) ht)
  · obtain ⟨a, haX⟩ := hXne
    obtain ⟨t, ht⟩ := hne a (hXY haX)
    have htU : t ∈ ⋃ v ∈ Y, C v := Set.mem_biUnion (hXY haX) ht
    exact hAA' t (Set.mem_biUnion haX ht) (hs htU)

/-- **Topological and combinatorial connectedness agree** (blueprint
`prop:sm-bd-graph-connected`): for a realization of `G` along `Y` by closed connected components
`C v`, the subcurve `⋃_{v ∈ Y} C v` is connected if and only if `G.IsConnected Y`. -/
theorem isConnected_iff_isConnected_biUnion {C : V → Set T} {pt : E → T} {Y : Finset V}
    (h : IsRealization G C pt Y) (hC : ∀ v ∈ Y, IsClosed (C v))
    (hCc : ∀ v ∈ Y, IsConnected (C v)) :
    G.IsConnected Y ↔ IsConnected (⋃ v ∈ Y, C v) := by
  constructor
  · intro hY
    obtain ⟨v, hv⟩ := hY.nonempty
    obtain ⟨t, ht⟩ := (hCc v hv).nonempty
    exact ⟨⟨t, Set.mem_biUnion hv ht⟩,
      isPreconnected_biUnion_of_isConnected h (fun v hv => (hCc v hv).isPreconnected) hY⟩
  · intro hU
    have hY : Y.Nonempty := by
      obtain ⟨t, ht⟩ := hU.nonempty
      obtain ⟨v, hv, -⟩ := Set.mem_iUnion₂.mp ht
      exact ⟨v, hv⟩
    exact isConnected_of_isPreconnected_biUnion h hC (fun v hv => (hCc v hv).nonempty) hY
      hU.isPreconnected

/-- **Connectedness of a curve given by generic points of its components** (blueprint
`prop:sm-bd-graph-connected`): if the subcurve `Z` is the union of the closures of the points
`η v`, `v ∈ Y` (the generic points of its irreducible components), and the double points `pt e`
realize `G` along `Y`, then `Z` is connected if and only if `G.IsConnected Y`. This is the form in
which the connectedness of `Z = f⁻¹(x)` (Zariski's theorem) enters Corollary B.2 in the proof of
Temkin's Lemma 4.4.2. -/
theorem isConnected_iff_of_genericPoints {η : V → T} {pt : E → T} {Y : Finset V}
    (h : IsRealization G (fun v => closure {η v}) pt Y) {Z : Set T}
    (hZ : Z = ⋃ v ∈ Y, closure {η v}) : G.IsConnected Y ↔ IsConnected Z := by
  rw [hZ]
  exact isConnected_iff_isConnected_biUnion h (fun _ _ => isClosed_closure)
    (fun v _ => isIrreducible_singleton.closure.isConnected)

end Hironaka.StableModification.BlowDown
