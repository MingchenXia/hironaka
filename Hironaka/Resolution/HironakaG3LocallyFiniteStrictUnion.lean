import Hironaka.Resolution.HironakaAdmissibleCalculus
set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3LocallyFiniteStrictUnion
noncomputable section
open Hironaka.BlowupSequences BlowupTowers

theorem strictTransform_iUnion_of_locallyFinite {n : ℕ} {X Z : CMfd.{0} n} {ι : Type*}
    (C : ι → Set X) (hLF : LocallyFinite C) (P : Z → X) (hP : Continuous P) :
    strictTransform n P (⋃ i, C i) = ⋃ i, strictTransform n P (C i) := by
  have h : LocallyFinite (fun i => P ⁻¹' C i \ exceptionalLocus n P) :=
    (hLF.preimage_continuous hP).subset (fun i => sdiff_subset)
  simp only [strictTransform, preimage_iUnion, iUnion_sdiff]
  exact h.closure_iUnion
end
end Hironaka.HironakaG3LocallyFiniteStrictUnion
