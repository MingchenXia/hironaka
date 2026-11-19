import Hironaka.Resolution.HironakaG4ToricSuccessorChart
import Hironaka.Resolution.HironakaG4OptionalBoundaryTransform

/-!
# Centre-point successor with an optional boundary dictionary

The actual chart retains the action, carrier and free section while tracking
both present coordinate members and members already absent from the chart.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OptionalCentreSuccessor
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold NormalCrossings HironakaG34CoordinateScaling HironakaG34ToricCharts
  HironakaG4ToricCharacterSections HironakaG4ToricSuccessorChart HironakaG4OptionalBoundaryTransform

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C N : Set X} {π : Y → X} {z : Y}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z))}

/-- A centre-point toric successor chart retains the action, strict carrier,
free section, optional strict family and exceptional divisor simultaneously. -/
theorem exists_centre_optional_successor_chart
    (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target)
    (S₀ : Finset (Fin n))
    (hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace S₀))
    (hCN : C ⊆ N) (hCan : IsComplexAnalyticSubset (n := n) C)
    {k : ℕ} (hreg : RegularAtDim (n := n) C (π z) k)
    (hzN : z ∈ geoStrictTransform π C N)
    {A : Type*} {F : Filter A} {act : A → X → X} {act' : A → Y → Y}
    {μ : A → Fin n → ℂ} (hμ : Tendsto μ F (𝓝 1))
    (hdiag : ActsDiagonallyNear F act μ Φ (π z))
    (hpreserve : ∀ᶠ p in F ×ˢ 𝓝 (π z), p.2 ∈ C → act p.1 p.2 ∈ C)
    (hcomm : ∀ᶠ p in F ×ˢ 𝓝 z, π (act' p.1 p.2) = act p.1 (π p.2))
    (hcont : ∀ᶠ p in F ×ˢ 𝓝 z, ContinuousAt (act' p.1) p.2)
    (sec : (Fin n → ℂ) → A) (hsec : Tendsto sec (𝓝 1) F)
    (hrealize : ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S₀, μ (sec b) i = b i)
    {ι : Type*} (D : ι → Set X) (M : ι → Option (Finset (Fin n))) (hclosed : ∀ i, IsClosed (D i))
    (hflatD : ∀ i {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ D i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ optionalCoordLocus (M i))) :
    ∃ (B : Finset (Fin n)) (σ : Fin n ≃ Fin n) (j : Fin n),
      n - B.card ≤ j.val ∧ j ∉ S₀.image σ ∧
      ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z),
        Ψ.source ⊆ (chartAt (ComplexModel n) z).target ∧
        ActsDiagonallyNear F act' (fun a => chartVec (fun i => μ a (σ.symm i)) (n - B.card) j) Ψ z ∧
        (∀ u ∈ flatDomain Ψ, u ∈ geoStrictTransform π C N ↔
          flatMap Ψ u ∈ coordSubspace (S₀.image σ)) ∧
        (∀ u ∈ flatDomain Ψ,
          (∀ i, u ∈ geoStrictTransform π C (D i) ↔
            flatMap Ψ u ∈ optionalCoordLocus (successorMask σ j (M i))) ∧
          (π u ∈ C ↔ flatMap Ψ u j = 0)) ∧
        Tendsto (fun b => sec (fun i => inverseChartVec b (n - B.card) j (σ i))) (𝓝 1) F ∧
        ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S₀.image σ,
          chartVec (fun a => μ (sec (fun q => inverseChartVec b (n - B.card) j (σ q))) (σ.symm a))
            (n - B.card) j i = b i := by
  obtain ⟨B, σ, j, hj, hjfree, Θ, hΘΦ, hΘsrc, hperm, hflatC, Ψ, hΨsrc,
    hcoords, hdiag', hN', hsec', hrealize'⟩ :=
    exists_toric_successor_chart hπ hΦsrc S₀ hflatN hCN hCan hreg hzN
      hμ hdiag hpreserve hcomm hcont sec hsec hrealize
  have hD := optional_strict_family_after_permuted_chart hπ.contMDiff.continuous hΘΦ σ hperm hflatC
    D M hclosed hflatD hj Ψ hΨsrc hcoords
  refine ⟨B, σ, j, hj, hjfree, Ψ, hΨsrc, hdiag', hN', ?_, hsec', hrealize'⟩
  intro u hu
  obtain ⟨hdom, hmon⟩ := hcoords u hu
  refine ⟨hD u hu, ?_⟩
  rw [hflatC _ hdom]
  rw [← hmon, monomial_mem_plane_iff hj]

end
end Hironaka.HironakaG4OptionalCentreSuccessor
