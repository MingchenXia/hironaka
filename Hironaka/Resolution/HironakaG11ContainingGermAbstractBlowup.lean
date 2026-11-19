import Hironaka.Resolution.HironakaG11ContainingGermFibre
import Hironaka.Blowup.BlowupSpaceUniversal
import Hironaka.Blowup.BlowupUniqueness

set_option autoImplicit false

/-!
# Containing-germ fibre escape for an arbitrary blowup

The universal property identifies an arbitrary blowup with the native one
by a homeomorphism over the base. Geometric strict transforms commute with
that homeomorphism, so the native fixed-fibre escape transfers to the given
blowup. The empty-interior hypothesis is explicit for the native construction.
-/

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11ContainingGermAbstractBlowup

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupConstruction BlowupSpaceTangent BlowupStrictSubmanifold BlowupUniqueness
  HironakaG11ContainingGermFibre

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} [Fact (IsClosedSubmanifold n C)]

/-- For an arbitrary blowup with a centre of empty interior, local centre
germ containment and tangent noncontainment force fixed-fibre escape. -/
theorem frequently_strict_not_boundary_of_containing_germ
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCint : interior C = ∅)
    {P H : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {p : Y} (hp : p ∈ geoStrictTransform π C P) (hpC : π p ∈ C)
    (hCH : ∀ᶠ x in 𝓝 (π p), x ∈ C → x ∈ H)
    (hnt : ¬ tangentSpace n P (π p) ≤ tangentSpace n H (π p)) :
    ∃ᶠ q in 𝓝 p, π q = π p ∧ q ∈ geoStrictTransform π C P ∧
      q ∉ geoStrictTransform π C H := by
  obtain ⟨e, f, he, hf, hπe, -, hfe, hef⟩ :=
    exists_biholomorphism_over hπ (isBlowupAlong_blowupProj (n := n) (C := C) hCint)
  let φ : Y ≃ₜ BlowupSpace n C :=
    { toFun := e, invFun := f, left_inv := congrFun hfe, right_inv := congrFun hef,
      continuous_toFun := he.continuous, continuous_invFun := hf.continuous }
  have heProj : ∀ y : Y, (blowupProj n C) (e y) = π y := fun y => congrFun hπe y
  have heStrict (A : Set X) : geoStrictTransform π C A =
      e ⁻¹' geoStrictTransform (blowupProj n C) C A := by
    symm
    change (φ : Y → BlowupSpace n C) ⁻¹' closure ((blowupProj n C) ⁻¹' (A \ C)) =
      closure (π ⁻¹' (A \ C))
    rw [φ.isOpenMap.preimage_closure_eq_closure_preimage φ.continuous_toFun]
    congr 1
    ext y
    change (blowupProj n C) (e y) ∈ A \ C ↔ π y ∈ A \ C
    rw [heProj y]
  have hpP : e p ∈ geoStrictTransform (blowupProj n C) C P := by
    have hp' : p ∈ e ⁻¹' geoStrictTransform (blowupProj n C) C P := (heStrict P) ▸ hp
    exact hp'
  have hpbase : (e p).base = π p := heProj p
  have hpC' : (e p).base ∈ C := hpbase ▸ hpC
  have hCH' : ∀ᶠ x in 𝓝 (e p).base, x ∈ C → x ∈ H := hpbase ▸ hCH
  have hnt' : ¬ tangentSpace n P (e p).base ≤ tangentSpace n H (e p).base := hpbase ▸ hnt
  have hn := HironakaG11ContainingGermFibre.frequently_strict_not_boundary_of_containing_germ
    hP hCP hpP hpC' hCH' hnt'
  have hpull : ∃ᶠ q in 𝓝 p, (e q).base = (e p).base ∧
      e q ∈ geoStrictTransform (blowupProj n C) C P ∧
      e q ∉ geoStrictTransform (blowupProj n C) C H := by
    have hn' : ∃ᶠ q in Filter.map (φ : Y → BlowupSpace n C) (𝓝 p),
        q.base = (e p).base ∧ q ∈ geoStrictTransform (blowupProj n C) C P ∧
          q ∉ geoStrictTransform (blowupProj n C) C H := by
      rw [φ.map_nhds_eq]
      exact hn
    exact Filter.frequently_map.mp hn'
  exact hpull.mono fun q ⟨hqbase, hqP, hqH⟩ => by
    refine ⟨?_, ?_, ?_⟩
    · change (blowupProj n C) (e q) = (blowupProj n C) (e p) at hqbase
      rwa [heProj q, heProj p] at hqbase
    · change q ∈ e ⁻¹' geoStrictTransform (blowupProj n C) C P at hqP
      rwa [← heStrict P] at hqP
    · intro hq
      have hq' : q ∈ e ⁻¹' geoStrictTransform (blowupProj n C) C H := (heStrict H) ▸ hq
      exact hqH hq'

end

end Hironaka.HironakaG11ContainingGermAbstractBlowup
