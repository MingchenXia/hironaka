import Hironaka.Resolution.StrictTransformSubvariety
import Hironaka.Analytic.SingularLocus

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Strict transforms along a sequence of blowups

The one-blowup strict-transform construction is iterated along an
`IsBlowupSequence`.  If the original subvariety is not contained in the image
of the exceptional locus of the complete sequence, the same is true at every
stage: exceptional images of earlier stages lie in that final image, and the
strict transform is not contained in the exceptional image of the next stage.

The resulting strict transform is a closed irreducible analytic subvariety.
Its carrier is connected without an additional resolution-theoretic input: an
irreducible analytic set is the closure of the regular component through any
of its regular points, and closures of connected sets are connected.
-/

open Set
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.StrictTransformSubvarietySequence

open Hironaka.BlowupSequences RegularLocusComponent

noncomputable section

variable {n : ℕ}
  {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
  {Xt : Type u} [TopologicalSpace Xt] [ChartedSpace (ComplexModel n) Xt]
    [IsComplexManifold n Xt]

/-- The strict transform along a compact blowup sequence is an irreducible analytic
subvariety, provided the original subvariety is not exceptional for the complete sequence. -/
theorem exists_strictTransform_subvariety_of_isBlowupSequence [CompactSpace X]
    {μ : Xt → X} (hμ : IsBlowupSequence n X Xt μ)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hV : ¬ V.carrier ⊆ μ '' exceptionalLocus n μ) :
    ∃ Vt : ClosedIrreducibleAnalyticSubvariety n Xt,
      Vt.carrier = strictTransform n μ V.carrier ∧ Vt.dim = V.dim := by
  induction hμ with
  | refl =>
      refine ⟨V, ?_, rfl⟩
      simp [strictTransform, exceptionalLocus_id, V.isClosed_carrier.closure_eq]
  | step f C g hfs hg ih =>
      obtain ⟨hcompact, hsurjf⟩ :=
        StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hfs
      have := hcompact
      have hsurjg := StrictTransformComposition.surjective_of_isBlowupAlong hg
      have hVf : ¬ V.carrier ⊆ f '' exceptionalLocus n f := fun h =>
        hV (h.trans (StrictTransformComposition.image_exceptionalLocus_subset_comp
          (hfs.contMDiff.mdifferentiable (by simp)) (hg.contMDiff.mdifferentiable (by simp))
          hsurjg))
      obtain ⟨W, hWc, hWd⟩ := ih hVf
      have hW : ¬ W.carrier ⊆ g '' exceptionalLocus n g := by
        rw [hWc]
        exact StrictTransformComposition.not_strictTransform_subset_image_exceptionalLocus
          hfs.contMDiff hg.contMDiff hsurjf hsurjg hV
      obtain ⟨Vt, hVc, hVd⟩ :=
        StrictTransformSubvariety.exists_strictTransform_subvariety_of_isBlowupAlong hg W hW
      refine ⟨Vt, ?_, hVd.trans hWd⟩
      rw [hVc, hWc, StrictTransformComposition.strictTransform_comp hfs.contMDiff
        hg.contMDiff]

/-- Exceptional-image control by the singular locus ensures that an irreducible subvariety
has a point outside the exceptional image. -/
theorem not_subset_image_exceptionalLocus_of_image_exceptionalLocus_subset_singular
    (V : ClosedIrreducibleAnalyticSubvariety n X) {μ : Xt → X}
    (hExcS : μ '' exceptionalLocus n μ ⊆ singularLocus V) :
    ¬ V.carrier ⊆ μ '' exceptionalLocus n μ := by
  obtain ⟨x, hx⟩ := V.regularLocus_nonempty
  intro hV
  exact (hExcS (hV (regularLocus_subset _ _ hx))).2 hx

/-- The strict transform is connected when the exceptional image is contained in the
singular locus. -/
theorem isConnected_strictTransform_of_isBlowupSequence [CompactSpace X]
    {μ : Xt → X} (hμ : IsBlowupSequence n X Xt μ)
    (V : ClosedIrreducibleAnalyticSubvariety n X)
    (hExcS : μ '' exceptionalLocus n μ ⊆ singularLocus V) :
    IsConnected (strictTransform n μ V.carrier) := by
  obtain ⟨Vt, hVt, -⟩ := exists_strictTransform_subvariety_of_isBlowupSequence hμ V
    (not_subset_image_exceptionalLocus_of_image_exceptionalLocus_subset_singular V hExcS)
  obtain ⟨c, -, hc⟩ := Vt.exists_regular_point
  have hcomponent : IsConnected (component (n := n) Vt.carrier c) := by
    change IsConnected (connectedComponentIn (regularPoints (n := n) Vt.carrier) c)
    exact isConnected_connectedComponentIn_iff.mpr ⟨Vt.dim, hc⟩
  rw [← hVt, StrictTransformSubvariety.eq_closure_component Vt.irreducible_carrier hc]
  exact hcomponent.closure

end

end Hironaka.StrictTransformSubvarietySequence
