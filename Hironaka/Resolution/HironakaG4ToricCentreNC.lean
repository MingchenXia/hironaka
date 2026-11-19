import Hironaka.Resolution.HironakaG4ToricDivisorRecognition
import Hironaka.Resolution.HironakaG4ToricCentreSuccessor

/-! A toric-invariant smooth centre meets the tracked divisors normally. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ToricCentreNC
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates NormalCrossings
  HironakaG34CoordinateScaling HironakaG4OptionalBoundaryTransform
  HironakaG4LocalToricDivisors HironakaG4ToricCentreSuccessor HironakaSharpNormalCrossingsOpenLocus

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {A : Type*} {F : Filter A}

/-- At an invariant smooth centre point, a strong state supplies simultaneous
coordinate equations for the centre and all incident tracked members. -/
theorem normalCrossingsAt_of_invariant_toric_state {N C : Set X} {E : List (Set X)}
    {x : X} {act : A → X → X} (hCN : C ⊆ N)
    (hCan : IsComplexAnalyticSubset (n := n) C) {k : ℕ} (hreg : RegularAtDim (n := n) C x k)
    (hstate : LocalToricDivisorState (n := n) F N (fun i : Fin E.length => E.get i) x act)
    (hpreserve : ∀ᶠ p in F ×ˢ 𝓝 x, p.2 ∈ C → act p.1 p.2 ∈ C) :
    normalCrossingsAt (n := n) C E x := by
  classical
  obtain ⟨S, μ, sec, Φ, m, hΦsrc, hN, hD, hm, hμ, hdiag, hsec, hrealize⟩ := hstate
  have hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) x).source →
      chartAt (ComplexModel n) x y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) x y) ∈ coordSubspace S) :=
    fun hy hyΦ => hN _ ⟨hy, hyΦ⟩
  obtain ⟨B, σ, Ψ, hΨΦ, hΨsrc, hcoords, hC, hN', hdiag', hsec', hrealize'⟩ :=
    exists_centre_flattening_with_partial_realization (π := id) (z := x)
      hΦsrc S hflatN hCN hCan hreg hμ hdiag hpreserve sec hsec hrealize
  let S₀ : Finset (Fin n) := Finset.univ.filter fun j => n - B.card ≤ j.val
  let R : Fin E.length → Finset (Fin n) := fun i => ((m i).map σ).elim ∅ (fun j => {j})
  have hsome : ∀ i, x ∈ E.get i → ∃ j, m i = some j := by
    intro i hi
    cases hmi : m i with
    | none =>
      have hh := (hD i x (mem_flatDomain_self Φ)).mp hi
      simp [hmi, optionalCoordLocus] at hh
    | some j => exact ⟨j, rfl⟩
  refine ⟨S₀, R, ?_, ?_⟩
  · apply coordinateFamilyAt_of_flattening Ψ
    · intro o ho y hy hyΨ
      cases o with
      | none =>
        change y ∈ C ↔ flatMap Ψ y ∈ coordSubspace S₀
        rw [coordSubspace_eq_complexCoordinatePlane]
        exact hC y ⟨hy, hyΨ⟩
      | some i =>
        obtain ⟨j, hj⟩ := hsome i ho
        have hDy := hD i y ⟨hy, hΨΦ hyΨ⟩
        have heq : flatMap Ψ y (σ j) = flatMap Φ y j := hcoords _ j
        change y ∈ E.get i ↔ flatMap Ψ y ∈ coordSubspace (R i)
        simp only [R, hj, Option.map_some, Option.elim_some, coordSubspace,
          Finset.mem_singleton, forall_eq]
        simp only [hj, Option.map_some, optionalCoordLocus, coordSubspace,
          Finset.mem_singleton, forall_eq] at hDy
        change y ∈ E.get i ↔ flatMap Ψ y (σ j) = 0
        rw [heq]
        exact hDy
    · exact mem_complexChartAt_source x
    · exact Ψ.center_mem_source
    · intro i hi
      exact hi
  · intro i hi
    obtain ⟨j, hj⟩ := hsome i hi
    simp [R, hj]

end
end Hironaka.HironakaG4ToricCentreNC
