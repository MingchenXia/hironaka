import Hironaka.Resolution.HironakaG4PartialToricRealization
import Hironaka.Resolution.HironakaG4ToricCentreFlattening
import Hironaka.Resolution.HironakaG4ToricFreePivot
import Hironaka.Resolution.HironakaG4ToricHistoryDictionary

/-!
# Successor toric chart above an invariant centre

At a point above the next centre, a partially realizable diagonal action
forces the actual centre to be a coordinate locus. Flatten it by a coordinate
permutation, retain the same action and carrier mask, and transfer both the
chart and the section across the blowup.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ToricCentreSuccessor
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold NormalCrossings HironakaG34CoordinateScaling HironakaG34ToricCharts
  HironakaG4ToricCharacterSections HironakaG4PartialToricRealization
  HironakaG4ToricCentreFlattening HironakaG4ToricFreePivot HironakaG4ToricHistoryDictionary

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {C N : Set X} {π : Y → X} {z : Y}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z))}

/-- The actual invariant centre can be flattened without losing the
carrier mask, the diagonal action, or the free character section. -/
theorem exists_centre_flattening_with_partial_realization
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target)
    (S : Finset (Fin n))
    (hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace S))
    (hCN : C ⊆ N) (hCan : IsComplexAnalyticSubset (n := n) C)
    {k : ℕ} (hreg : RegularAtDim (n := n) C (π z) k)
    {A : Type*} {F : Filter A} {act : A → X → X} {μ : A → Fin n → ℂ}
    (hμ : Tendsto μ F (𝓝 1)) (hdiag : ActsDiagonallyNear F act μ Φ (π z))
    (hpreserve : ∀ᶠ p in F ×ˢ 𝓝 (π z), p.2 ∈ C → act p.1 p.2 ∈ C)
    (sec : (Fin n → ℂ) → A) (hsec : Tendsto sec (𝓝 1) F)
    (hrealize : ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S, μ (sec b) i = b i) :
    ∃ (B : Finset (Fin n)) (σ : Fin n ≃ Fin n)
      (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z))),
      Ψ.source ⊆ Φ.source ∧ Ψ.source ⊆ (chartAt (ComplexModel n) (π z)).target ∧
      (∀ w i, Ψ.toFun w (σ i) = Φ.toFun w i) ∧
      (∀ y ∈ flatDomain Ψ, y ∈ C ↔ flatMap Ψ y ∈ complexCoordinatePlane n (n - B.card)) ∧
      (∀ y ∈ flatDomain Ψ, y ∈ N ↔ flatMap Ψ y ∈ coordSubspace (S.image σ)) ∧
      ActsDiagonallyNear F act (fun a i => μ a (σ.symm i)) Ψ (π z) ∧
      Tendsto (fun b : Fin n → ℂ => sec (fun i => b (σ i))) (𝓝 1) F ∧
      ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S.image σ,
        μ (sec (fun j => b (σ j))) (σ.symm i) = b i := by
  have hzero : ∀ᶠ y in 𝓝 (π z), y ∈ C → ∀ i ∈ S, flatMap Φ y i = 0 := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds (mem_flatDomain_self Φ)] with y hy hyC i hi
    exact (hflatN hy.1 hy.2).mp (hCN hyC) i hi
  have hinv := scaling_invariant_of_partial_realization S hdiag hpreserve hzero sec hsec hrealize
  obtain ⟨B, σ, Ψ, hzeroB, hσ, hΨΦ, hΨsrc, hflatC, hcoords, hdiag'⟩ :=
    exists_flattening_of_scaling_invariant hΦsrc hCan hreg hinv hμ hdiag
  obtain ⟨hsec', hrealize'⟩ := partial_realization_after_permutation S σ sec hsec hrealize
  refine ⟨B, σ, Ψ, hΨΦ, hΨsrc, hcoords, hflatC, ?_, hdiag', hsec', hrealize'⟩
  intro y hy
  have hΦy : y ∈ flatDomain Φ := ⟨hy.1, hΨΦ hy.2⟩
  rw [hflatN hΦy.1 hΦy.2]
  constructor
  · intro hN i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    change Ψ.toFun (chartAt (ComplexModel n) (π z) y) (σ j) = 0
    rw [hcoords]
    exact hN j hj
  · intro hN i hi
    have hi' : σ i ∈ S.image σ := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    have := hN (σ i) hi'
    change Ψ.toFun (chartAt (ComplexModel n) (π z) y) (σ i) = 0 at this
    rw [hcoords] at this
    exact this

end
end Hironaka.HironakaG4ToricCentreSuccessor
