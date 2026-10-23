import DeJongAlterations.Geometry.RationalCoordinateMapGenericFiberDimension

/-!
# Actual dimension preservation under nonempty open immersions

An affine neighbourhood inside the actual open image has the target's
function-field degree. The genuine open-immersion lift embeds it into the
source, so the source has at least that dimension. No comparison of caller
function fields or birational certificate is needed.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace DeJongAlterations.Geometry.FunctionFieldDimension

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k] {X Y : Scheme.{u}} [IsIntegral Y]

/-- Every nonempty actual open immersion into a finite-type integral scheme preserves dimension. -/
theorem topologicalKrullDim_eq_of_openImmersion (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (j : X ⟶ Y) [IsOpenImmersion j] [Nonempty X] :
    topologicalKrullDim X = topologicalKrullDim Y := by
  apply le_antisymm
  · exact j.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  · obtain ⟨d, hd, htr⟩ := exists_dimension_and_trdeg p
    let x : X := Classical.choice inferInstance
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUj⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (show j x ∈ j.opensRange from ⟨x, rfl⟩)
        j.opensRange.isOpen
    let : Nonempty U := ⟨⟨j x, hxU⟩⟩
    have hdim := affineSections_dimension_eq p ⟨U, hU⟩ d htr
    have hrange : Set.range hU.fromSpec ⊆ Set.range j := by
      rw [hU.range_fromSpec]
      exact hUj
    let l := IsOpenImmersion.lift j hU.fromSpec hrange
    have : IsOpenImmersion (l ≫ j) := by
      rw [show l ≫ j = hU.fromSpec from IsOpenImmersion.lift_fac j hU.fromSpec hrange]
      infer_instance
    have : IsOpenImmersion l := IsOpenImmersion.of_comp l j
    have hle := l.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
    change topologicalKrullDim (PrimeSpectrum Γ(Y, U)) ≤ topologicalKrullDim X at hle
    rw [hd, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim] at *
    exact hle

/-- The dimension-one bound transfers from an actual dense open to the integral target. -/
theorem topologicalKrullDim_le_one_of_dense_open (p : Y ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (j : X ⟶ Y) [IsOpenImmersion j] [IsDominant j]
    (hdim : topologicalKrullDim X ≤ 1) : topologicalKrullDim Y ≤ 1 := by
  let : Nonempty X := j.denseRange.nonempty
  rw [← topologicalKrullDim_eq_of_openImmersion p j]
  exact hdim

end DeJongAlterations.Geometry.FunctionFieldDimension
