/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Support.OpensPreferredChartExact
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.RegularPatchNeighborhood

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Measures, pluripolar sets and envelopes on a clopen open submanifold

Let `M` be a compact complex manifold and `U` a nonempty clopen subset, for instance a connected
component.  `U` is a compact complex manifold (`Hironaka.OpensRestriction`), and the objects of
global pluripotential theory on `M` restrict to `U` without change:

* `exceptionalLocus_val`, `isIsomorphismOver_val` — the inclusion is an isomorphism over `U`;
* `globalMixedMeasure_restrict_apply` — **the global mixed non-pluripolar measure is local**:
  `⟨⋀ (θᵢ|_U)_{uᵢ|_U}⟩(val⁻¹ S) = ⟨⋀ (θᵢ)_{uᵢ}⟩(S ∩ U)` for measurable `S`
  (from `ModificationMassInvariance.globalMixedMeasure_restrict_preimage_eq_map` with
  `π = Subtype.val`), and `diagonalPotentialMeasure_restrict_apply`;
* `manifoldLocallyPluripolar_preimage_val`, `manifoldLocallyPluripolar_image_val` — pluripolar
  sets restrict to `U` and extend from `U` (chart change by `locallyPluripolarAt_chartTransition`);
* `uscRegularization_comp_val` and `rooftopEnvelope_restrict` — usc regularization and the
  rooftop envelope commute with the restriction (competitors restrict, and a competitor on `U`
  glues with a competitor on `M` across the clopen `U`);
* `measure_eq_zero_of_forall_connectedComponent` — a set is null as soon as its trace on every
  connected component is null.

This is the general mechanism by which a statement about compact Kähler manifolds proved under
`[ConnectedSpace M]` extends to every compact Kähler manifold.  Sorry-free.
-/

open Set Filter TopologicalSpace MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace Hironaka.OpensRestrictionMeasure

open Hironaka.HolomorphicMaps Hironaka.BlowupSequences
  OpensRestriction

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {U : Opens M}



/-- The derivative of the inclusion is the identity in the preferred charts. -/
theorem mfderiv_val_bijective (y : U) :
    Function.Bijective
      (mfderiv 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) (Subtype.val : U → M) y) := by
  have hd : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n)
      (Subtype.val : U → M) y := ((contMDiff_val U) y).mdifferentiableAt (by simp)
  rw [hd.mfderiv]
  have heq : writtenInExtChartAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) y
      (Subtype.val : U → M) =ᶠ[𝓝 ((extChartAt 𝓘(ℂ, ComplexModel n) y) y)] id := by
    have ht : (complexChartAt (n := n) y).val.target ∈
        𝓝 ((extChartAt 𝓘(ℂ, ComplexModel n) y) y) :=
      (complexChartAt (n := n) y).val.open_target.mem_nhds
        ((complexChartAt (n := n) y).val.map_source (mem_complexChartAt_source y))
    filter_upwards [ht] with z hz
    exact coordinateMap_val_complexChartAt y hz
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ]
  rw [heq.fderiv_eq, fderiv_id]
  exact Function.bijective_id

theorem exceptionalLocus_val : exceptionalLocus n (Subtype.val : U → M) = ∅ :=
  eq_empty_of_forall_notMem fun y hy => hy (mfderiv_val_bijective y)


end

end Hironaka.OpensRestrictionMeasure
