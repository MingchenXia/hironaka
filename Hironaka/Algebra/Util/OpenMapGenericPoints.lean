/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.IdealSheaf.Order.Along
import Hironaka.Scheme.IdealSheaf.Order.Specialization
import Hironaka.Scheme.Snc.Dictionary
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Generic points of a preimage under an open surjective map

Włodarczyk's embedded desingularization commutes with smooth morphisms
[Wlo05, Theorem 1.0.2 (d), and §4.1]. The resolution of a subvariety `Y = V(I)` is driven by the
irreducible components of `Y` (the closures of the generic points of its support), and along a
smooth surjection `h : X' → X` the components of `h⁻¹(Y)` are finer than the preimages of the
components of `Y` (an étale cover may split a component). Transporting the construction along `h`
therefore needs the topology of generic points under an open surjective continuous map `f`:

* `mem_genericPoints_of_mem_genericPoints_preimage`: the image of a generic point of `f⁻¹(Z)` is a
  generic point of `Z`. The component `closure {η'}` of `f⁻¹(Z)` maps onto a dense subset of the
  component `C` of `Z` through `f η'`: the finitely many other components of `f⁻¹(C)` (the source
  is Noetherian) leave an open neighbourhood `O` of `η'` on which `f⁻¹(C) ∩ O ⊆ closure {η'}`;
  `f(O)` is open and meets `C`, hence contains the generic point of `C`.
* `exists_mem_genericPoints_preimage_of_mem_genericPoints`: every generic point of `Z` is the image
  of a generic point of `f⁻¹(Z)` (surjectivity and a generization inside the preimage).

Pure topology, not stated in the sources; the schemes to which it is applied are sober and, being
of finite type over a field, Noetherian.
-/

public section

open TopologicalSpace Topology


variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The generic point of an irreducible closed set is the unique point of the set generizing all
of it: a point of the set that generizes the generic point is the generic point. -/
theorem eq_of_specializes_of_isGenericPoint [T0Space X] {S : Set X} {ξ x : X}
    (hξ : IsGenericPoint ξ S) (hx : x ∈ S) (h : x ⤳ ξ) : x = ξ :=
  (h.antisymm (hξ.specializes hx)).eq

/-- A generic point of a closed set lies in no other component: if `g ≠ η` are generic points of
`Z`, then `η ∉ closure {g}` (both are maximal irreducible closed subsets of `Z`). -/
theorem notMem_closure_singleton_of_mem_genericPoints [T0Space X] [QuasiSober X] (Z : Closeds X)
    {g η : X} (hg : g ∈ Z.genericPoints) (hη : η ∈ Z.genericPoints) (hne : g ≠ η) :
    η ∉ closure {g} := by
  intro hmem
  rw [Closeds.mem_genericPoints_iff] at hg hη
  have hle : closure {η} ⊆ closure {g} :=
    (isClosed_closure.closure_subset_iff).mpr (Set.singleton_subset_iff.mpr hmem)
  have heq : closure {η} = closure {g} := hη.eq_of_le hg.1 hle
  have hg' : g ∈ closure {η} := by rw [heq]; exact subset_closure rfl
  exact hne ((specializes_iff_mem_closure.mpr hmem).antisymm
    (specializes_iff_mem_closure.mpr hg')).eq

/-- The image of a generic point of the preimage of a closed set under an open surjective
continuous map is a generic point of the closed set. -/
theorem mem_genericPoints_of_mem_genericPoints_preimage [T0Space X] [QuasiSober X] [T0Space Y]
    [QuasiSober Y] [NoetherianSpace Y] {f : Y → X} (hf : Continuous f) (ho : IsOpenMap f)
    (Z : Closeds X) {η' : Y} (hη' : η' ∈ (Z.preimage hf).genericPoints) :
    f η' ∈ Z.genericPoints := by
  classical
  have hη'Z : f η' ∈ Z := hη'.1
  -- the component `C` of `Z` through `f η'` and its generic point `ξ`
  obtain ⟨ξ, hξZ, hξ⟩ := Closeds.exists_mem_genericPoints_specializes Z hη'Z
  suffices hcl : f η' = ξ by rw [hcl]; exact hξZ
  -- `C := closure {ξ}`, `W := f⁻¹(C)`, a closed set of `Y` containing `closure {η'}`
  let C : Closeds X := ⟨closure {ξ}, isClosed_closure⟩
  have hCZ : (C : Set X) ⊆ Z :=
    Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hξZ.1)
  have hξC : IsGenericPoint ξ (C : Set X) := isGenericPoint_closure
  let W : Closeds Y := C.preimage hf
  have hη'W : η' ∈ W := by
    change f η' ∈ closure {ξ}
    exact specializes_iff_mem_closure.mp hξ
  -- `η'` is a generic point of `W` (maximal irreducible in the bigger `f⁻¹(Z)`, and inside `W`)
  have hη'gW : η' ∈ W.genericPoints := by
    rw [Closeds.mem_genericPoints_iff] at hη' ⊢
    refine ⟨⟨W.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη'W),
      isIrreducible_singleton.closure⟩, fun T hT hle => ?_⟩
    exact hη'.2 ⟨hT.1.trans fun y hy => hCZ hy, hT.2⟩ hle
  -- the open neighbourhood `O` of `η'` avoiding the other components of `W`
  have hfin : W.genericPoints.Finite := Closeds.genericPoints_finite W
  let O : Set Y := (⋃ g ∈ hfin.toFinset.erase η', closure {g})ᶜ
  have hO : IsOpen O := by
    apply isOpen_compl_iff.mpr
    exact Set.Finite.isClosed_biUnion (Finset.finite_toSet _) fun g _ => isClosed_closure
  have hη'O : η' ∈ O := by
    intro hmem
    obtain ⟨g, hg, hη'g⟩ := Set.mem_iUnion₂.mp hmem
    obtain ⟨hne, hgW⟩ := Finset.mem_erase.mp hg
    exact notMem_closure_singleton_of_mem_genericPoints W (hfin.mem_toFinset.mp hgW) hη'gW hne
      hη'g
  have hOW : ∀ w ∈ W, w ∈ O → w ∈ closure {η'} := by
    intro w hw hwO
    obtain ⟨g, hgW, hgw⟩ := Closeds.exists_mem_genericPoints_specializes W hw
    by_cases hg : g = η'
    · exact specializes_iff_mem_closure.mp (hg ▸ hgw)
    · exfalso
      exact hwO (Set.mem_iUnion₂.mpr ⟨g, Finset.mem_erase.mpr ⟨hg, hfin.mem_toFinset.mpr hgW⟩,
        specializes_iff_mem_closure.mp hgw⟩)
  -- `f(O)` is open and meets `C` (at `f η'`), so it contains the generic point `ξ` of `C`
  have hξO : ξ ∈ f '' O := (hξC.mem_open_set_iff (ho O hO)).mpr
    ⟨f η', hξ.mem_closure, ⟨η', hη'O, rfl⟩⟩
  obtain ⟨o, hoO, hoξ⟩ := hξO
  have hoW : o ∈ W := by
    change f o ∈ closure {ξ}
    rw [hoξ]; exact subset_closure rfl
  have hη'o : η' ⤳ o := specializes_iff_mem_closure.mpr (hOW o hoW hoO)
  have h1 : f η' ⤳ ξ := hoξ ▸ hη'o.map hf
  exact eq_of_specializes_of_isGenericPoint hξC (specializes_iff_mem_closure.mp hξ) h1

/-- Every generic point of `Z` is the image of a generic point of `f⁻¹(Z)` when `f` is surjective
and continuous: lift the point and generize inside the preimage. -/
theorem exists_mem_genericPoints_preimage_of_mem_genericPoints [T0Space X] [QuasiSober X]
    [T0Space Y] [QuasiSober Y] {f : Y → X} (hf : Continuous f) (hs : Function.Surjective f)
    (Z : Closeds X) {η : X} (hη : η ∈ Z.genericPoints) :
    ∃ η' ∈ (Z.preimage hf).genericPoints, f η' = η := by
  obtain ⟨y, rfl⟩ := hs η
  have hyZ : y ∈ Z.preimage hf := hη.1
  obtain ⟨η', hη'W, hη'y⟩ := Closeds.exists_mem_genericPoints_specializes (Z.preimage hf) hyZ
  refine ⟨η', hη'W, ?_⟩
  have hη'Z : f η' ∈ Z := hη'W.1
  rw [Closeds.mem_genericPoints_iff] at hη
  have hgen : IsGenericPoint (f y) (closure {f y}) := isGenericPoint_closure
  have hmax : closure {f y} = closure {f η'} := by
    refine hη.eq_of_le ⟨Z.isClosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hη'Z),
      isIrreducible_singleton.closure⟩ ?_
    exact isClosed_closure.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp (hη'y.map hf)))
  have hmem : f η' ∈ closure {f y} := by rw [hmax]; exact subset_closure rfl
  exact ((hη'y.map hf).antisymm (specializes_iff_mem_closure.mpr hmem)).eq

