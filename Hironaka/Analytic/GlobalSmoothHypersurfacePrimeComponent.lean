/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.IrreducibleComponentFilling
import Hironaka.Analytic.AnalyticSubsetPreimage

set_option autoImplicit false

/-! # Genuine global prime components of whole smooth hypersurfaces -/

open Set Filter
open scoped Topology

namespace Hironaka.GlobalSmoothHypersurfacePrimeComponent

open RegularLocusComponent IrreducibleComponentFilling

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (m + 1)) Y] [IsComplexManifold (m + 1) Y]

/-- Whole closed smooth hypersurface geometry internally supplies the actual global prime component. -/
theorem exists_global_prime_component {A : Set Y} (hclosed : IsClosed A)
    (hreg : ∀ y ∈ A, RegularAtDim (n := m + 1) A y m) {c : Y} (hc : c ∈ A) :
    ∃ V : ClosedIrreducibleAnalyticSubvariety (m + 1) Y,
      V.dim = m ∧ V.carrier = connectedComponentIn A c ∧ c ∈ V.carrier ∧
      V.carrier ⊆ A ∧ IsConnected V.carrier ∧
      (∀ y ∈ V.carrier, RegularAtDim (n := m + 1) V.carrier y m) ∧
      ∀ y ∈ V.carrier, ∃ W : Set Y, IsOpen W ∧ y ∈ W ∧ A ∩ W = V.carrier ∩ W := by
  have hA := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
    ⟨hclosed, fun y hy => ⟨m, hreg y hy⟩⟩
  have hRA : regularPoints (n := m + 1) A = A :=
    Subset.antisymm (regularPoints_subset A) (fun y hy => ⟨m, hreg y hy⟩)
  have hcomp : component (n := m + 1) A c = connectedComponentIn A c := by
    unfold component
    rw [hRA]
  have hcl : closure (connectedComponentIn A c) = connectedComponentIn A c := by
    apply Subset.antisymm
    · exact isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
        (subset_closure (mem_connectedComponentIn hc))
        (closure_minimal (connectedComponentIn_subset A c) hclosed)
    · exact subset_closure
  let V := componentSubvariety hA (hreg c hc)
  have hVC : V.carrier = connectedComponentIn A c := by
    change closure (component (n := m + 1) A c) = connectedComponentIn A c
    rw [hcomp, hcl]
  refine ⟨V, rfl, hVC, ?_, componentSubvariety_subset hA (hreg c hc), ?_, ?_, ?_⟩
  · rw [hVC]
    exact mem_connectedComponentIn hc
  · rw [hVC]
    exact isConnected_connectedComponentIn_iff.mpr hc
  · intro y hy
    apply regularAtDim_closure_component (hreg c hc)
    rw [hcomp, ← hVC]
    exact hy
  · intro y hy
    have hyC : y ∈ component (n := m + 1) A c := by rwa [hcomp, ← hVC]
    obtain ⟨W, hW, hyW, hAW⟩ := exists_open_inter_subset_component (hreg c hc) hyC
    refine ⟨W, hW, hyW, Subset.antisymm ?_ ?_⟩
    · intro z hz
      refine ⟨?_, hz.2⟩
      rw [hVC, ← hcomp]
      exact hAW hz
    · exact fun z hz => ⟨componentSubvariety_subset hA (hreg c hc) hz.1, hz.2⟩

end Hironaka.GlobalSmoothHypersurfacePrimeComponent
