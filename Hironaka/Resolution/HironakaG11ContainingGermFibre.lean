import Hironaka.Resolution.HironakaG11ContainingFibreVariation

set_option autoImplicit false

/-!
# Fixed-fibre escape when the centre germ is contained in the old set

The old set is enlarged outside an actual source neighborhood by the part of
the centre outside that neighborhood. The enlarged set contains the entire
centre and has the same germ at the selected base. Its native strict transform
has the same germ near the selected exceptional point. The global
centre-containment fibre-variation theorem therefore applies without assuming
global containment of the original old set.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11ContainingGermFibre

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupConstruction BlowupSpaceTangent BlowupStrictSubmanifold
  HironakaG11ContainingFibreVariation

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {C : Set X} [Fact (IsClosedSubmanifold n C)]

/-- If the centre is contained in the old set only as a germ, tangent
noncontainment still gives local escape in the actual fixed fibre. -/
theorem frequently_strict_not_boundary_of_containing_germ
    {P H : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {p : BlowupSpace n C} (hp : p ∈ geoStrictTransform (blowupProj n C) C P)
    (hpC : p.base ∈ C) (hCH : ∀ᶠ x in 𝓝 p.base, x ∈ C → x ∈ H)
    (hnt : ¬ tangentSpace n P p.base ≤ tangentSpace n H p.base) :
    ∃ᶠ q in 𝓝 p, q.base = p.base ∧
      q ∈ geoStrictTransform (blowupProj n C) C P ∧
      q ∉ geoStrictTransform (blowupProj n C) C H := by
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.mp hCH
  let H' : Set X := H ∪ (C \ W)
  have hCH' : C ⊆ H' := by
    intro x hxC
    by_cases hxW : x ∈ W
    · exact Or.inl (hWsub hxW hxC)
    · exact Or.inr ⟨hxC, hxW⟩
  have hT : tangentSpace n H' p.base ≤ tangentSpace n H p.base := by
    intro ξ hξ
    apply mem_tangentSpace.mpr
    intro f hf
    apply germDiff_eq_zero_of_mem_tangentSpace hξ
    refine ⟨hf.1, ?_⟩
    filter_upwards [hf.2, hWopen.mem_nhds hpW] with x hx hxW hxH'
    rcases hxH' with hxH | ⟨-, hxNotW⟩
    · exact hx hxH
    · exact (hxNotW hxW).elim
  have hnt' : ¬ tangentSpace n P p.base ≤ tangentSpace n H' p.base :=
    fun h => hnt (h.trans hT)
  have hproj : ∀ᶠ q in 𝓝 p, q.base ∈ W :=
    (continuous_blowupProj (n := n) (C := C)).continuousAt.tendsto (hWopen.mem_nhds hpW)
  have hpred : ∀ᶠ q in 𝓝 p,
      q ∈ (blowupProj n C) ⁻¹' (H' \ C) ↔ q ∈ (blowupProj n C) ⁻¹' (H \ C) := by
    filter_upwards [hproj] with q hqW
    change (q.base ∈ H' ∧ q.base ∉ C) ↔ (q.base ∈ H ∧ q.base ∉ C)
    constructor
    · rintro ⟨hH', hC⟩
      rcases hH' with hH | ⟨-, hNotW⟩
      · exact ⟨hH, hC⟩
      · exact (hNotW hqW).elim
    · rintro ⟨hH, hC⟩
      exact ⟨Or.inl hH, hC⟩
  have hstrict : ∀ᶠ q in 𝓝 p,
      q ∈ geoStrictTransform (blowupProj n C) C H' ↔
        q ∈ geoStrictTransform (blowupProj n C) C H := by
    filter_upwards [hpred.eventually_nhds] with q hq
    change q ∈ closure ((blowupProj n C) ⁻¹' (H' \ C)) ↔
      q ∈ closure ((blowupProj n C) ⁻¹' (H \ C))
    rw [mem_closure_iff_frequently, mem_closure_iff_frequently]
    exact Filter.frequently_congr hq
  have hf := frequently_strict_not_boundary_of_tangent_noncontainment_native hP hCP hCH' hp hpC hnt'
  exact (hf.and_eventually hstrict).mono fun q ⟨⟨hqbase, hqP, hqH'⟩, hqeq⟩ =>
    ⟨hqbase, hqP, fun hqH => hqH' (hqeq.mpr hqH)⟩

end

end Hironaka.HironakaG11ContainingGermFibre
