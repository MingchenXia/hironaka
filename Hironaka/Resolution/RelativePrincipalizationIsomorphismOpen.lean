import Hironaka.Blowup.BlowupSequenceIsomorphismOff
import Hironaka.Resolution.StrictTransformComposition

set_option autoImplicit false

/-!
# The canonical non-exceptional open set for relative principalization

For a finite blowup sequence, the complement of the image of the exceptional
locus is open and is an isomorphism locus.  If the strict transform of `W` is
nonempty, this open set meets `W`: a non-exceptional point in the defining dense
set of the strict transform cannot map into the exceptional image, because its
fibre is a singleton.  This reconstructs the local-isomorphism clause in
relative principalization without treating it as additional Hironaka data.
-/

open Set
open scoped Manifold ContDiff

universe u

namespace Hironaka.RelativePrincipalizationIsomorphismOpen

open Hironaka.BlowupSequences

noncomputable section

variable {n : ℕ}
  {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
    [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
    [IsComplexManifold n Y]

/-- A nonempty strict transform meets the canonical isomorphism open set. -/
theorem exists_open_meets_isIsomorphismOver_of_strictTransform_nonempty [CompactSpace X]
    {f : Y → X} (hf : IsBlowupSequence n X Y f) {W : Set X}
    (hW : (strictTransform n f W).Nonempty) :
    ∃ U : Set X, IsOpen U ∧ (U ∩ W).Nonempty ∧ IsIsomorphismOver n f U := by
  let E : Set X := f '' exceptionalLocus n f
  refine ⟨Eᶜ, ?_, ?_, ?_⟩
  · have hclosed : IsClosed (exceptionalLocus n f) :=
      isOpen_compl_iff.mp
        (StrictTransformComposition.isOpen_compl_exceptionalLocus hf.contMDiff)
    obtain ⟨hcompact, -⟩ :=
      StrictTransformComposition.IsBlowupSequence.compactSpace_surjective hf
    exact (hclosed.isCompact.image hf.contMDiff.continuous).isClosed.isOpen_compl
  · have hraw : (f ⁻¹' W \ exceptionalLocus n f).Nonempty := by
      by_contra hraw
      have hraw' : f ⁻¹' W \ exceptionalLocus n f = ∅ :=
        not_nonempty_iff_eq_empty.mp hraw
      rcases hW with ⟨y, hy⟩
      rw [strictTransform, hraw', closure_empty] at hy
      simp only [Set.mem_empty_iff_false] at hy
    obtain ⟨y, hyW, hyExc⟩ := hraw
    refine ⟨f y, ?_, hyW⟩
    intro hyE
    change f y ∈ f '' exceptionalLocus n f at hyE
    obtain ⟨z, hzExc, hfz⟩ := hyE
    have hzy : z = y :=
      BlowupSequenceIsomorphismOff.eq_of_apply_eq_of_not_mem_exceptionalLocus hf hyExc hfz
    exact hyExc (hzy ▸ hzExc)
  · exact BlowupSequenceIsomorphismOff.isIsomorphismOver_compl_of_image_exceptionalLocus_subset
      hf Subset.rfl

end

end Hironaka.RelativePrincipalizationIsomorphismOpen
