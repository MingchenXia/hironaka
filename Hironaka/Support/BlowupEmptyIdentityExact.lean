/- Exact complete original codimension-one and empty-centre identity blowup proofs. -/
import Hironaka.Blowup.BlowupExistenceCodimOne
import Hironaka.Blowup.SmoothHypersurfaceIdeal
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Set Filter
open scoped Topology Manifold ContDiff
namespace Hironaka.BlowupExistenceCodimOne
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences BlowupFlatCoordinates
noncomputable section
universe u
variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- **Existence of the blowup along a smooth hypersurface.**  The blowup of `X` along a centre
that is regular of codimension one at each of its points is `X` itself. -/
theorem isBlowupAlong_id_of_codimOne {C : Set X} (hC : IsClosedSubmanifold n C)
    (hCint : interior C = ∅)
    (hcodim : ∀ x ∈ C, ∃ k, RegularAtDim (n := n) C x k ∧ k + 1 = n) :
    IsBlowupAlong n C (id : X → X) := by
  refine ⟨hC, hCint, contMDiff_id, ?_, ?_⟩
  · intro y
    obtain ⟨U, hU, hyU, h, hhd, hhne, hmem⟩ :=
      isInvertible_vanishingIdeal_of_codimOne hC.1 hCint hcodim y
    exact ⟨U, hU, hyU, h, hhd, hhne, fun z hz g =>
      (pullback_id_vanishingIdeal_mem_iff (C := C)).trans (hmem z hz g)⟩
  · intro m Z _ _ _ g hg _
    refine ⟨g, ⟨hg, rfl⟩, ?_⟩
    rintro h ⟨-, hgh⟩
    exact (Function.id_comp h).symm.trans hgh

/-- The blowup along the empty centre. -/
theorem isBlowupAlong_id_empty : IsBlowupAlong n (∅ : Set X) (id : X → X) :=
  isBlowupAlong_id_of_codimOne ⟨isClosed_empty, by simp⟩ (by simp) (by simp)

end
end Hironaka.BlowupExistenceCodimOne
