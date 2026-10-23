/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Inseparable

/-!
# Gluing connected fibres along specializations

This file contains the topological step of Zariski's connectedness theorem for a birational
morphism onto a normal curve over a valuation ring of height `≥ 2` (blueprint
`lem:sm-connbirh-glue`, chapter `sm-cohomology-connected-birational-height.tex`; M. Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, proof of Lemma 4.4.2, T:3133).

Let `f : X → Y` be a continuous closed map, `G ⊆ Y` a finite set of generizations of a point
`z ∈ G` which is closed in `G`. Two-chart Zariski connectedness
(`Cohomology.ConnectedBirational.isPreconnected_preimage_zeroLocus_of_twoCharts_birational`) gives
the connectedness of `f⁻¹(G)` only, because the first cohomology of the structure sheaf may be
supported on all of `G`. If moreover, for every `y ∈ G ∖ {z}`, the closure of `f⁻¹(y)` meets
`f⁻¹(z)` in a preconnected set, then `f⁻¹(z)` is preconnected
(`isPreconnected_preimage_singleton_of_closure`): a decomposition of `f⁻¹(z)` into two disjoint
closed pieces extends, piece by piece along the closures of the fibres `f⁻¹(y)`, to a
decomposition of `f⁻¹(G)`.

## Main results

* `exists_mem_closure_singleton_preimage`: for a closed map, a point over a generization of `z`
  has a specialization over `z`.
* `isPreconnected_preimage_singleton_of_closure`: the gluing statement.
-/

namespace DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeight

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **Specializations over a specialization** (closed maps lift specializations): if `f` is a
continuous closed map and `f x ⤳ z`, then some specialization `x'` of `x` lies over `z`. -/
theorem exists_mem_closure_singleton_preimage {f : X → Y} (hcl : IsClosedMap f) {x : X} {z : Y}
    (hxz : f x ⤳ z) : ∃ x' ∈ closure ({x} : Set X), f x' = z := by
  have hclosed : IsClosed (f '' closure ({x} : Set X)) := hcl _ isClosed_closure
  have hmem : f x ∈ f '' closure ({x} : Set X) := ⟨x, subset_closure rfl, rfl⟩
  have hz : z ∈ f '' closure ({x} : Set X) := hxz.mem_closed hclosed hmem
  obtain ⟨x', hx', rfl⟩ := hz
  exact ⟨x', hx', rfl⟩

/-- **Gluing connected fibres along specializations** (blueprint `lem:sm-connbirh-glue`). Let
`f : X → Y` be a continuous closed map, `G ⊆ Y` finite and `z ∈ G` such that every point of `G`
specializes to `z` and `z` has no proper specialization in `G`. Suppose that `f⁻¹(G)` is
preconnected and that for every `y ∈ G ∖ {z}` the set `closure (f⁻¹(y)) ∩ f⁻¹(z)` is
preconnected. Then `f⁻¹(z)` is preconnected. -/
theorem isPreconnected_preimage_singleton_of_closure {f : X → Y} (hf : Continuous f)
    (hcl : IsClosedMap f) {G : Set Y} (hG : G.Finite) {z : Y} (hzG : z ∈ G)
    (hz : ∀ w ∈ G, z ⤳ w → w = z) (hgen : ∀ w ∈ G, w ⤳ z)
    (hF : IsPreconnected (f ⁻¹' G))
    (hK : ∀ y ∈ G, y ≠ z → IsPreconnected (closure (f ⁻¹' {y}) ∩ f ⁻¹' {z})) :
    IsPreconnected (f ⁻¹' {z}) := by
  classical
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro u v hu hv hPuv hPdisj
  -- the pieces `K_y = closure (f⁻¹ y) ∩ f⁻¹ z` lie in `u` or in `v`
  have hKuv : ∀ y ∈ G, y ≠ z → closure (f ⁻¹' {y}) ∩ f ⁻¹' {z} ⊆ u ∨
      closure (f ⁻¹' {y}) ∩ f ⁻¹' {z} ⊆ v := by
    intro y hy hyz
    refine (isPreconnected_iff_subset_of_disjoint_closed.mp (hK y hy hyz)) u v hu hv
      (inter_subset_right.trans hPuv) ?_
    refine eq_empty_of_subset_empty ?_
    rw [← hPdisj]
    exact inter_subset_inter_left _ inter_subset_right
  -- the two sets of generizations
  let SA : Set Y := {y | y ∈ G ∧ y ≠ z ∧ closure (f ⁻¹' {y}) ∩ f ⁻¹' {z} ⊆ u}
  let SB : Set Y := {y | y ∈ G ∧ y ≠ z ∧ ¬ closure (f ⁻¹' {y}) ∩ f ⁻¹' {z} ⊆ u}
  have hSA : SA.Finite := hG.subset fun y hy => hy.1
  have hSB : SB.Finite := hG.subset fun y hy => hy.1
  have hSBv : ∀ y ∈ SB, closure (f ⁻¹' {y}) ∩ f ⁻¹' {z} ⊆ v := fun y hy =>
    (hKuv y hy.1 hy.2.1).resolve_left hy.2.2
  let Cz : Set X := f ⁻¹' closure {z}
  have hCz : IsClosed Cz := isClosed_closure.preimage hf
  let u' : Set X := (u ∩ Cz) ∪ ⋃ y ∈ SA, closure (f ⁻¹' {y})
  let v' : Set X := (v ∩ Cz) ∪ ⋃ y ∈ SB, closure (f ⁻¹' {y})
  have hu' : IsClosed u' :=
    (hu.inter hCz).union (hSA.isClosed_biUnion fun _ _ => isClosed_closure)
  have hv' : IsClosed v' :=
    (hv.inter hCz).union (hSB.isClosed_biUnion fun _ _ => isClosed_closure)
  -- points of `u'` (resp. `v'`) over `z` lie in `u` (resp. `v`)
  have hu'P : ∀ x ∈ u', f x = z → x ∈ u := by
    intro x hx hfx
    rcases hx with hx | hx
    · exact hx.1
    · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
      exact hy.2.2 ⟨hxy, hfx⟩
  have hv'P : ∀ x ∈ v', f x = z → x ∈ v := by
    intro x hx hfx
    rcases hx with hx | hx
    · exact hx.1
    · obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp hx
      exact hSBv y hy ⟨hxy, hfx⟩
  -- points of `Cz` over `G` lie over `z`
  have hCzG : ∀ x, f x ∈ G → x ∈ Cz → f x = z := by
    intro x hxG hxC
    exact hz (f x) hxG (specializes_iff_mem_closure.mpr hxC)
  have hPuv' : ∀ x, f x = z → x ∈ u → x ∈ v → False := by
    intro x hfx hxu hxv
    have : x ∈ f ⁻¹' {z} ∩ (u ∩ v) := ⟨hfx, hxu, hxv⟩
    rw [hPdisj] at this
    exact this
  -- `f⁻¹ G` is covered by `u'` and `v'`
  have hcov : f ⁻¹' G ⊆ u' ∪ v' := by
    intro x hx
    by_cases hfx : f x = z
    · have hxC : x ∈ Cz := by
        change f x ∈ closure {z}
        rw [hfx]
        exact subset_closure rfl
      rcases hPuv (show x ∈ f ⁻¹' {z} from hfx) with h | h
      · exact Or.inl (Or.inl ⟨h, hxC⟩)
      · exact Or.inr (Or.inl ⟨h, hxC⟩)
    · have hxy : x ∈ closure (f ⁻¹' {f x}) := subset_closure rfl
      by_cases hKu : closure (f ⁻¹' {f x}) ∩ f ⁻¹' {z} ⊆ u
      · exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨f x, ⟨hx, hfx, hKu⟩, hxy⟩))
      · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨f x, ⟨hx, hfx, hKu⟩, hxy⟩))
  -- and they do not meet on `f⁻¹ G`
  have hdisj : f ⁻¹' G ∩ (u' ∩ v') = ∅ := by
    refine eq_empty_of_forall_notMem fun x ⟨hxG, hxu, hxv⟩ => ?_
    by_cases hfx : f x = z
    · exact hPuv' x hfx (hu'P x hxu hfx) (hv'P x hxv hfx)
    · have hxC : x ∉ Cz := fun h => hfx (hCzG x hxG h)
      have hxu' : x ∈ ⋃ y ∈ SA, closure (f ⁻¹' {y}) := hxu.resolve_left fun h => hxC h.2
      have hxv' : x ∈ ⋃ y ∈ SB, closure (f ⁻¹' {y}) := hxv.resolve_left fun h => hxC h.2
      obtain ⟨y₁, hy₁, hxy₁⟩ := mem_iUnion₂.mp hxu'
      obtain ⟨y₂, hy₂, hxy₂⟩ := mem_iUnion₂.mp hxv'
      obtain ⟨x', hx'x, hfx'⟩ := exists_mem_closure_singleton_preimage hcl (hgen (f x) hxG)
      have h₁ : x' ∈ closure (f ⁻¹' {y₁}) :=
        closure_minimal (singleton_subset_iff.mpr hxy₁) isClosed_closure hx'x
      have h₂ : x' ∈ closure (f ⁻¹' {y₂}) :=
        closure_minimal (singleton_subset_iff.mpr hxy₂) isClosed_closure hx'x
      exact hPuv' x' hfx' (hy₁.2.2 ⟨h₁, hfx'⟩) (hSBv y₂ hy₂ ⟨h₂, hfx'⟩)
  have hP : f ⁻¹' {z} ⊆ f ⁻¹' G := preimage_mono (singleton_subset_iff.mpr hzG)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hF) u' v' hu' hv' hcov hdisj with h | h
  · exact Or.inl fun x hx => hu'P x (h (hP hx)) hx
  · exact Or.inr fun x hx => hv'P x (h (hP hx)) hx

end DeJongAlterations.StableModification.Cohomology.ConnectedBirationalHeight
