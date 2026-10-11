/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.RegularLocusComponent

set_option autoImplicit false

/-!
# Global irreducible components are locally finite

Blueprint `rem:global-components` (Demailly, *Complex analytic and differential geometry*, II.5.3),
the usual global irreducible-component decomposition.

Let `A` be an analytic subset of a complex manifold.  The *global components* of `A` are the
closures of the connected components of the set of regular points of `A` (of any dimension).

* `isComplexAnalyticallyIrreducible_of_mem_globalComponents`: each is an irreducible analytic subset
  (`RegularLocusComponent.isComplexAnalyticallyIrreducible_closure_component`), contained in `A`;
* `exists_isOpen_finite_globalComponents`, `locallyFinite_globalComponents`: every point has an
  open neighbourhood meeting only finitely many of them.  Take the local statement with connected
  regular parts `Gᵢ` at the point (`LocalStatementConnected.exists_connectedParts`); a component
  whose closure meets the common neighbourhood `Ω` contains a regular point `z ∈ Ω`, near which `A`
  lies in the component, and `z` lies in the closure of some `Gᵢ`; so the component meets the
  connected set `Gᵢ` of regular points, hence contains it.  At most one component contains each `Gᵢ`;
* `sUnion_globalComponents`: their union is `A` (the regular locus is dense, and a locally finite
  union of closed sets is closed).

Sorry-free.
-/

open Set Filter
open scoped Topology

namespace Hironaka.GlobalComponents

open RegularLocusComponent AnalyticLocalStatement LocalStatementConnected

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The global components of `A`: the closures of the connected components of the regular
locus of `A`. -/
def globalComponents (A : Set M) : Set (Set M) :=
  {B | ∃ c ∈ regularPoints (n := n) A, B = closure (component (n := n) A c)}

omit [IsComplexManifold n M] in
theorem closure_component_mem_globalComponents {A : Set M} {c : M} {k : ℕ}
    (hc : RegularAtDim (n := n) A c k) :
    closure (component (n := n) A c) ∈ globalComponents (n := n) A :=
  ⟨c, ⟨k, hc⟩, rfl⟩

/-- A global component is an irreducible analytic subset. -/
theorem isComplexAnalyticallyIrreducible_of_mem_globalComponents {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) {B : Set M} (hB : B ∈ globalComponents (n := n) A) :
    IsComplexAnalyticallyIrreducible (n := n) B := by
  obtain ⟨c, ⟨k, hk⟩, rfl⟩ := hB
  exact isComplexAnalyticallyIrreducible_closure_component hA hk

/-- A global component is contained in `A`. -/
theorem subset_of_mem_globalComponents {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A)
    {B : Set M} (hB : B ∈ globalComponents (n := n) A) : B ⊆ A := by
  obtain ⟨c, -, rfl⟩ := hB
  exact closure_minimal (component_subset (n := n) A c) hA.isClosed

omit [IsComplexManifold n M] in
/-- Points of a preconnected set of regular points lie in the same component. -/
theorem component_eq_of_isPreconnected {A G : Set M} (hG : IsPreconnected G)
    (hGR : G ⊆ regularPoints (n := n) A) {y z : M} (hy : y ∈ G) (hz : z ∈ G) :
    component (n := n) A y = component (n := n) A z := by
  have h : G ⊆ component (n := n) A y :=
    subset_component_of_isPreconnected hG hGR ⟨y, hy, mem_connectedComponentIn (hGR hy)⟩
  exact connectedComponentIn_eq (h hz)

/-- **Local finiteness of the global components**: every point has an open neighbourhood
meeting only finitely many global components. -/
theorem exists_isOpen_finite_globalComponents {A : Set M}
    (hA : IsComplexAnalyticSubset (n := n) A) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      {B | B ∈ globalComponents (n := n) A ∧ (B ∩ U).Nonempty}.Finite := by
  classical
  by_cases hp : p ∈ A
  swap
  · refine ⟨Aᶜ, hA.isClosed.isOpen_compl, hp, ?_⟩
    convert finite_empty
    refine eq_empty_iff_forall_notMem.mpr ?_
    rintro B ⟨hB, x, hxB, hxA⟩
    exact hxA (subset_of_mem_globalComponents hA hB hxB)
  obtain ⟨D, ⟨G⟩⟩ := exists_connectedParts hA hp
  set Ω : Set M := D.nbhd ∩ ⋂ i, G.core i with hΩ
  have hΩo : IsOpen Ω := D.isOpen_nbhd.inter (isOpen_iInter_of_finite G.isOpen_core)
  have hpΩ : p ∈ Ω := ⟨D.mem_nbhd, mem_iInter.mpr G.mem_core⟩
  have hgoodR : ∀ i, G.good i ⊆ regularPoints (n := n) A :=
    fun i y hy => ⟨D.dim i, G.regularAtDim_of_mem_good i y hy⟩
  have hpieceA : ∀ i, D.piece i ⊆ A := fun i y hy =>
    ((D.inter_nbhd_eq.symm ▸ mem_iUnion.mpr ⟨i, hy⟩ : y ∈ A ∩ D.nbhd)).1
  -- the components meeting `Ω` come from the connected parts
  let T : Fin D.count → Set (Set M) := fun i =>
    (fun y => closure (component (n := n) A y)) '' G.good i
  have hT : ∀ i, (T i).Subsingleton := by
    rintro i _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    exact congrArg closure
      (component_eq_of_isPreconnected (G.isPreconnected_good i) (hgoodR i) hy hz)
  refine ⟨Ω, hΩo, hpΩ, (finite_iUnion fun i => (hT i).finite).subset ?_⟩
  rintro B ⟨⟨c, -, rfl⟩, x, hxB, hxΩ⟩
  -- a point `z` of the component inside `Ω`
  obtain ⟨z, hzΩ, hzC⟩ := mem_closure_iff.mp hxB Ω hΩo hxΩ
  obtain ⟨j, hj⟩ := component_subset_regularPoints (n := n) A c hzC
  obtain ⟨W, hWo, hzW, hWC, -, -⟩ := exists_isOpen_inter_subset hzC hj
  have hzA : z ∈ A := component_subset (n := n) A c hzC
  have hzU : z ∈ ⋃ i, D.piece i := by rw [← D.inter_nbhd_eq]; exact ⟨hzA, hzΩ.1⟩
  obtain ⟨i, hzi⟩ := mem_iUnion.mp hzU
  have hzcore : z ∈ G.core i := mem_iInter.mp hzΩ.2 i
  have hzcl : z ∈ closure (G.good i) := G.subset_closure_good i ⟨hzi, hzcore⟩
  obtain ⟨y, hyW, hyG⟩ := mem_closure_iff.mp hzcl W hWo hzW
  have hyA : y ∈ A := hpieceA i (G.good_subset i hyG).1
  have hyC : y ∈ component (n := n) A c := hWC ⟨hyA, hyW⟩
  exact mem_iUnion.mpr ⟨i, y, hyG, (congrArg closure (connectedComponentIn_eq hyC)).symm⟩

/-- The global components form a locally finite family. -/
theorem locallyFinite_globalComponents {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) :
    LocallyFinite (fun B : globalComponents (n := n) A => (B : Set M)) := by
  intro p
  obtain ⟨U, hU, hpU, hfin⟩ := exists_isOpen_finite_globalComponents hA p
  refine ⟨U, hU.mem_nhds hpU, ?_⟩
  exact (hfin.preimage Subtype.val_injective.injOn).subset fun B hB => ⟨B.2, hB⟩

/-- **`A` is the union of its global components.** -/
theorem sUnion_globalComponents {A : Set M} (hA : IsComplexAnalyticSubset (n := n) A) :
    ⋃₀ globalComponents (n := n) A = A := by
  refine Subset.antisymm (sUnion_subset fun B hB => subset_of_mem_globalComponents hA hB) ?_
  intro x hx
  obtain ⟨U, hU, hxU, hfin⟩ := exists_isOpen_finite_globalComponents hA x
  set S := {B | B ∈ globalComponents (n := n) A ∧ (B ∩ U).Nonempty} with hS
  have hcl : IsClosed (⋃₀ S) := by
    rw [sUnion_eq_biUnion]
    refine hfin.isClosed_biUnion fun B hB => ?_
    obtain ⟨⟨c, -, rfl⟩, -⟩ := hB
    exact isClosed_closure
  have hxcl : x ∈ closure (⋃₀ S) := by
    refine mem_closure_iff.mpr fun o ho hxo => ?_
    obtain ⟨y, hyo, k, hyk⟩ :=
      RegularLocusDense.exists_regularAtDim_mem_nhds hA hx ((ho.inter hU).mem_nhds ⟨hxo, hxU⟩)
    have hyB : y ∈ closure (component (n := n) A y) := subset_closure (mem_component_self hyk)
    exact ⟨y, hyo.1, mem_sUnion.mpr ⟨_, ⟨closure_component_mem_globalComponents hyk,
      y, hyB, hyo.2⟩, hyB⟩⟩
  obtain ⟨B, hB, hxB⟩ := mem_sUnion.mp (hcl.closure_subset hxcl)
  exact mem_sUnion.mpr ⟨B, hB.1, hxB⟩

end Hironaka.GlobalComponents
