import Hironaka.Resolution.HironakaG4OptionalGammaProtectedCentre
import Hironaka.Blowup.ExceptionalPushforwardAlong

/-! Read the equivariance dictionary from optional singleton equations. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4GammaOptionalDictionary
noncomputable section
open Hironaka.BlowupSequences BlowupTowers BlowupFlatCoordinates NormalCrossings
  HironakaG34CoordinateScaling HironakaG4OptionalBoundaryTransform
  ExceptionalPushforwardAlong

variable {n : ℕ} {X : CMfd.{u} n}

/-- Every tracked optional singleton is either an actual coordinate
hyperplane or absent. Adding one binomial member gives exactly the boundary
dictionary needed by equivariance, including members absent from the chart. -/
theorem optional_gamma_dictionary_of_masks_with_window
    {x₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (O : Opens (ComplexModel n)) (D E : List (Set X)) (H : Set X)
    (m : Fin D.length → Option (Fin n)) (s t : Fin n) (c : Fin n → ℕ)
    (hD : ∀ j y, y ∈ flatDomain Φ → (y ∈ D.get j ↔
      flatMap Φ y ∈ optionalCoordLocus ((m j).map (fun k => {k}))))
    (hH : ∀ y ∈ flatDomain Φ, y ∈ H ↔ binomial s t c (flatMap Φ y) = 0)
    (U : Set X) (hU : flatDomain Φ ⊆ U)
    (hE : ∀ K ∈ E, K = H ∨ (K ∈ D ∨ U ⊆ K)) :
    ∀ K ∈ E, (∃ R : Finset (Fin n), ∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O →
      (y ∈ K ↔ flatMap Φ y ∈ coordSubspace R)) ∨
      (∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O → (y ∈ K ↔ flatMap Φ y ∈ {w | binomial s t c w = 0})) ∨
      (∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O → y ∉ K) := by
  intro K hK
  rcases hE K hK with rfl | hKD | hWhole
  · right; left
    intro y hy _
    exact hH y hy
  · obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hKD
    cases hj : m j with
    | none =>
      right; right
      intro y hy _ hyD
      have hh := (hD j y hy).mp hyD
      simp [hj, optionalCoordLocus] at hh
    | some k =>
      left
      refine ⟨{k}, ?_⟩
      intro y hy _
      simpa [hj, optionalCoordLocus] using hD j y hy
  · left
    refine ⟨∅, ?_⟩
    intro y hy _
    exact iff_of_true (hWhole (hU hy)) (by simp [coordSubspace])

/-- The equivariance dictionary also admits source sets containing the whole chart. -/
theorem optional_gamma_dictionary_of_masks
    {x₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (O : Opens (ComplexModel n)) (D E : List (Set X)) (H : Set X)
    (m : Fin D.length → Option (Fin n)) (s t : Fin n) (c : Fin n → ℕ)
    (hD : ∀ j y, y ∈ flatDomain Φ → (y ∈ D.get j ↔
      flatMap Φ y ∈ optionalCoordLocus ((m j).map (fun k => {k}))))
    (hH : ∀ y ∈ flatDomain Φ, y ∈ H ↔ binomial s t c (flatMap Φ y) = 0)
    (hE : ∀ K ∈ E, K = H ∨ K ∈ D) :
    ∀ K ∈ E, (∃ R : Finset (Fin n), ∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O →
      (y ∈ K ↔ flatMap Φ y ∈ coordSubspace R)) ∨
      (∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O → (y ∈ K ↔ flatMap Φ y ∈ {w | binomial s t c w = 0})) ∨
      (∀ y ∈ flatDomain Φ, flatMap Φ y ∈ O → y ∉ K) :=
  optional_gamma_dictionary_of_masks_with_window Φ O D E H m s t c hD hH Set.univ (subset_univ _) fun K hK =>
    (hE K hK).imp id Or.inl

/-- If the lower carrier is the larger carrier intersected with one tracked
member passing through the chart centre, its chart equation is a coordinate
subspace whose mask contains the larger-carrier mask. -/
theorem lower_carrier_dictionary_of_mask
    {x₀ : X} (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x₀ x₀))
    (O : Opens (ComplexModel n)) (N W : Set X) (D : List (Set X)) (j : Fin D.length)
    (R₀ : Finset (Fin n)) (m : Fin D.length → Option (Fin n))
    (hW : W = N ∩ D.get j) (hx : x₀ ∈ D.get j)
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
  rw [hW, coordSubspace_union]
  simp only [mem_inter_iff]
  exact and_congr (hN y hy) (by simpa [hk, optionalCoordLocus] using hD j y hy)

end
end Hironaka.HironakaG4GammaOptionalDictionary
