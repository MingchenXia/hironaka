import Hironaka.Resolution.HironakaG11TransverseTrace
import Hironaka.Blowup.BlowupSpaceUniversal
import Hironaka.Blowup.BlowupUniqueness

set_option autoImplicit false

/-!
# Noncontaining-germ total-trace escape for an arbitrary blowup

A biholomorphism over the base identifies any blowup with the native one
when the centre has empty interior, and it transports geometric strict
transforms and frequent total-trace escape.
-/

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG11NoncontainingAbstractBlowup

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupConstruction BlowupSpaceTangent BlowupStrictSubmanifold BlowupUniqueness NormalCrossings
  HironakaG11TransverseTrace

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} [Fact (IsClosedSubmanifold n C)]

/-- At an arbitrary blowup, a normal-crossings centre germ not contained
in an old member forces local escape in the total exceptional trace. -/
theorem frequently_strict_not_boundary_of_noncontaining_germ
    {π : Y → X} (hπ : IsBlowupAlong n C π) (hCint : interior C = ∅)
    {P : Set X} (hP : IsClosedSubmanifold n P) (hCP : C ⊆ P)
    {E : List (Set X)} (hE : IsSNCDivisor n E) (hcross : HasNormalCrossings n C E)
    (i : Fin E.length) {p : Y} (hp : p ∈ geoStrictTransform π C P) (hpC : π p ∈ C)
    (hpH : π p ∈ E.get i) (hnot : ¬ ∀ᶠ x in 𝓝 (π p), x ∈ C → x ∈ E.get i) :
    ∃ᶠ q in 𝓝 p, π q ∈ C ∧ q ∈ geoStrictTransform π C P ∧
      q ∉ geoStrictTransform π C (E.get i) := by
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
  have hpH' : (e p).base ∈ E.get i := hpbase ▸ hpH
  have hnot' : ¬ ∀ᶠ x in 𝓝 (e p).base, x ∈ C → x ∈ E.get i := hpbase ▸ hnot
  have hn := frequently_exceptional_strict_not_boundary_of_normalCrossings hP hCP hE hcross i hpP hpC' hpH' hnot'
  have hpull : ∃ᶠ q in 𝓝 p, (e q).base ∈ C ∧
      e q ∈ geoStrictTransform (blowupProj n C) C P ∧
      e q ∉ geoStrictTransform (blowupProj n C) C (E.get i) := by
    have hn' : ∃ᶠ q in Filter.map (φ : Y → BlowupSpace n C) (𝓝 p),
        q.base ∈ C ∧ q ∈ geoStrictTransform (blowupProj n C) C P ∧
          q ∉ geoStrictTransform (blowupProj n C) C (E.get i) := by
      rw [φ.map_nhds_eq]
      exact hn
    exact Filter.frequently_map.mp hn'
  exact hpull.mono fun q ⟨hqbase, hqP, hqH⟩ => by
    refine ⟨?_, ?_, ?_⟩
    · change (blowupProj n C) (e q) ∈ C at hqbase
      rwa [heProj q] at hqbase
    · change q ∈ e ⁻¹' geoStrictTransform (blowupProj n C) C P at hqP
      rwa [← heStrict P] at hqP
    · intro hq
      have hq' : q ∈ e ⁻¹' geoStrictTransform (blowupProj n C) C (E.get i) := (heStrict (E.get i)) ▸ hq
      exact hqH hq'

end

end Hironaka.HironakaG11NoncontainingAbstractBlowup
