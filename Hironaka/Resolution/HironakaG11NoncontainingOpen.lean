import Hironaka.Resolution.HironakaG11TangentNoncontainmentOpen
import Hironaka.Resolution.HironakaG11TransverseTrace

set_option autoImplicit false

/-!
# Local noncontainment for a normal-crossings centre

A single noncontaining centre germ supplies a scalar derivative witness.
Tangent noncontainment is open along the smooth centre; a locally containing
germ would force the opposite tangent inclusion. Thus noncontainment persists
on a neighborhood of the centre point.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11NoncontainingOpen

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupSpaceTangent BlowupStrictSubmanifold NormalCrossings
  HironakaG11TransverseTrace HironakaG11TangentNoncontainmentOpen

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- At a normal-crossings centre, noncontainment of the germ in an incident
member persists at all nearby centre points. -/
theorem eventually_noncontaining_germ_of_normalCrossings {C : Set X}
    (hC : IsClosedSubmanifold n C) {E : List (Set X)} (hcross : HasNormalCrossings n C E)
    {x : X} (hxC : x ∈ C) (i : Fin E.length) (hxH : x ∈ E.get i)
    (hnot : ¬ ∀ᶠ y in 𝓝 x, y ∈ C → y ∈ E.get i) :
    ∀ᶠ y in 𝓝 x, y ∈ C → ¬ ∀ᶠ z in 𝓝 y, z ∈ C → z ∈ E.get i := by
  obtain ⟨f, hf, hEq, ξ, hξC, hξf⟩ :=
    local_equation_of_normalCrossings_not_containing hcross hxC i hxH hnot
  have hfH : (vanishingIdeal (n := n) (E.get i)).mem x f := by
    refine ⟨hf, ?_⟩
    filter_upwards [hEq] with y hy hyH
    exact hy.mp hyH
  have hnt : ¬ tangentSpace n C x ≤ tangentSpace n (E.get i) x := by
    intro hle
    exact hξf (germDiff_eq_zero_of_mem_tangentSpace (hle hξC) hfH)
  filter_upwards [eventually_tangent_noncontainment hC hxC hnt] with y hy hyC hcontained
  apply hy hyC
  intro η hη
  apply mem_tangentSpace.mpr
  intro g hg
  apply germDiff_eq_zero_of_mem_tangentSpace hη
  refine ⟨hg.1, ?_⟩
  filter_upwards [hg.2, hcontained] with z hz hsub hzC
  exact hz (hsub hzC)

end

end Hironaka.HironakaG11NoncontainingOpen
