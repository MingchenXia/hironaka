import Hironaka.Resolution.HironakaG8GeneralCentreFibreCriterion

set_option autoImplicit false

/-!
# Strict-transform fibre containment and tangent-space containment

These statements are for smooth `P,H` that both contain the actual centre.
They compare the actual native strict transforms over a fixed base point,
or over the whole centre, by constructing native exceptional points.

The centre-containment hypothesis for `H` is essential. For a boundary
transverse to the centre, a fixed fibre and the germ of the total exceptional
trace have different containment behavior; neither a transverse-boundary
statement nor residual case (r1) is asserted here.
-/

open Set
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG8GeneralCentreFibreInclusion

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupConstruction BlowupSpaceTangent BlowupStrictSubmanifold
  HironakaG8GeneralCentreFibreCriterion

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {C : Set X} [Fact (IsClosedSubmanifold n C)]

/-- Fixed native exceptional-fibre containment of smooth strict transforms
is exactly tangent-space containment when both original sets contain C. -/
theorem strict_fibre_subset_iff_tangentSpace_le {P H : Set X}
    (hP : IsClosedSubmanifold n P) (hH : IsClosedSubmanifold n H)
    (hCP : C ⊆ P) (hCH : C ⊆ H) {x : X} (hxC : x ∈ C) :
    (∀ p : BlowupSpace n C, p.base = x →
      p ∈ geoStrictTransform (blowupProj n C) C P →
      p ∈ geoStrictTransform (blowupProj n C) C H) ↔
      tangentSpace n P x ≤ tangentSpace n H x := by
  constructor
  · intro hFibre ξ hξP
    have hTCH : tangentSpace n C x ≤ tangentSpace n H x := by
      intro η hη
      apply mem_tangentSpace.mpr
      intro f hfH
      apply germDiff_eq_zero_of_mem_tangentSpace hη
      refine ⟨hfH.1, ?_⟩
      filter_upwards [hfH.2] with y hy hyC
      exact hy (hCH hyC)
    by_cases hξC : ξ ∈ tangentSpace n C x
    · exact hTCH hξC
    · have hTCP : tangentSpace n C x ≤ tangentSpace n P x := by
        intro η hη
        apply mem_tangentSpace.mpr
        intro f hfP
        apply germDiff_eq_zero_of_mem_tangentSpace hη
        refine ⟨hfP.1, ?_⟩
        filter_upwards [hfP.2] with y hy hyC
        exact hy (hCP hyC)
      let p : BlowupSpace n C := excPoint x hxC ξ hξC
      have hpC : p.base ∈ C := hxC
      have hpdirP : p.dir ≤ tangentSpace n P p.base := by
        change tangentSpace n C x ⊔ ℂ ∙ ξ ≤ tangentSpace n P x
        exact sup_le hTCP ((Submodule.span_singleton_le_iff_mem _ _).mpr hξP)
      have hpP := mem_geoStrictTransform_of_dir_le_tangentSpace hP hCP hpC hpdirP
      have hpH := hFibre p rfl hpP
      have hdirH := dir_le_tangentSpace_of_mem_geoStrictTransform hCH hpH hpC
      apply hdirH
      change ξ ∈ tangentSpace n C x ⊔ ℂ ∙ ξ
      apply (show ℂ ∙ ξ ≤ tangentSpace n C x ⊔ ℂ ∙ ξ from le_sup_right)
      exact Submodule.mem_span_singleton_self _
  · intro hTangent p hbase hpP
    have hpC : p.base ∈ C := by rw [hbase]; exact hxC
    apply mem_geoStrictTransform_of_dir_le_tangentSpace hH hCH hpC
    refine (dir_le_tangentSpace_of_mem_geoStrictTransform hCP hpP hpC).trans ?_
    simpa only [hbase] using hTangent

/-- Containment of the whole native exceptional strict-transform trace
is equivalent to tangent containment at every original centre point. -/
theorem exceptional_strict_subset_iff_tangentSpace_le {P H : Set X}
    (hP : IsClosedSubmanifold n P) (hH : IsClosedSubmanifold n H)
    (hCP : C ⊆ P) (hCH : C ⊆ H) :
    ((blowupProj n C) ⁻¹' C ∩ geoStrictTransform (blowupProj n C) C P) ⊆
      geoStrictTransform (blowupProj n C) C H ↔
      ∀ x ∈ C, tangentSpace n P x ≤ tangentSpace n H x := by
  constructor
  · intro hAll x hxC
    apply (strict_fibre_subset_iff_tangentSpace_le hP hH hCP hCH hxC).mp
    intro p hbase hpP
    apply hAll
    refine ⟨?_, hpP⟩
    change p.base ∈ C
    rw [hbase]
    exact hxC
  · intro hTangent p hp
    have hpC : p.base ∈ C := hp.1
    exact (strict_fibre_subset_iff_tangentSpace_le hP hH hCP hCH hpC).mpr
      (hTangent p.base hpC) p rfl hp.2

end

end Hironaka.HironakaG8GeneralCentreFibreInclusion
