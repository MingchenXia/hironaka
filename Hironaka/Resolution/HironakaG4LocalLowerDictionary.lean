import Hironaka.Resolution.HironakaG4GammaOptionalDictionary

/-! A locally presented lower carrier has a coordinate mask. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4LocalLowerDictionary
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupFlatCoordinates NormalCrossings
  HironakaG4OptionalBoundaryTransform HironakaG34CoordinateScaling ExceptionalPushforwardAlong

variable {n : ℕ} {X : CMfd.{u} n}

/-- A lower carrier which is locally the intersection of the larger carrier
and an incident optional singleton boundary member is itself coordinate. -/
theorem lower_carrier_dictionary_of_local_mask
    {x₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (O : Opens (ComplexModel n)) (N W : Set X) (D : List (Set X)) (j : Fin D.length)
    (R₀ : Finset (Fin n)) (m : Fin D.length → Option (Fin n))
    (hW : ∀ y ∈ flatDomain Φ, y ∈ W ↔ y ∈ N ∩ D.get j) (hx : x₀ ∈ D.get j)
    (hN : ∀ y ∈ flatDomain Φ, y ∈ N ↔ flatMap Φ y ∈ coordSubspace R₀)
    (hD : ∀ i y, y ∈ flatDomain Φ → (y ∈ D.get i ↔
      flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k})))) :
    ∃ R : Finset (Fin n), R₀ ⊆ R ∧ ∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O →
      (y ∈ W ↔ flatMap Φ y ∈ coordSubspace R) := by
  have hm : ∃ k, m j = some k := by
    cases hj : m j with
    | none =>
      have hh := (hD j x₀ (mem_flatDomain_self Φ)).mp hx
      simp [hj, optionalCoordLocus] at hh
    | some k => exact ⟨k, rfl⟩
  obtain ⟨k, hk⟩ := hm
  refine ⟨R₀ ∪ {k}, Finset.subset_union_left, ?_⟩
  intro y hy _
  rw [hW y hy, coordSubspace_union]
  simp only [mem_inter_iff]
  exact and_congr (hN y hy) (by simpa [hk, optionalCoordLocus] using hD j y hy)

end
end Hironaka.HironakaG4LocalLowerDictionary
