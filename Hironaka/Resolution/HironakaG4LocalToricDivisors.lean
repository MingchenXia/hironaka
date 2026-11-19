import Hironaka.Resolution.HironakaG4LocalToricState
import Hironaka.Resolution.HironakaG4OptionalDivisorMasks

/-! A local toric state with distinct transverse coordinate divisors. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4LocalToricDivisors
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold NormalCrossings HironakaG34CoordinateScaling HironakaG34ToricCharts
  HironakaG4ToricCharacterSections HironakaG4OptionalBoundaryTransform
  HironakaG4OptionalCentreSuccessor HironakaG4OptionalOffCentre HironakaG4OptionalDivisorMasks

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {A : Type*} (F : Filter A)

def LocalToricDivisorState {ι : Type*} (N : Set X) (D : ι → Set X) (x : X)
    (act : A → X → X) : Prop :=
  ∃ (S : Finset (Fin n)) (μ : A → Fin n → ℂ) (sec : (Fin n → ℂ) → A)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (m : ι → Option (Fin n)),
    Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
    (∀ y ∈ flatDomain Φ, y ∈ N ↔ flatMap Φ y ∈ coordSubspace S) ∧
    (∀ i y, y ∈ flatDomain Φ → (y ∈ D i ↔
      flatMap Φ y ∈ optionalCoordLocus ((m i).map (fun k => {k})))) ∧
    DivisorMasksValid S m ∧ Tendsto μ F (𝓝 1) ∧ ActsDiagonallyNear F act μ Φ x ∧
    Tendsto sec (𝓝 1) F ∧
    ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S, μ (sec b) i = b i

/-- A permissible blowup preserves transverse distinct coordinate divisors. -/
theorem localToricDivisorState_step {ι : Type*} {N C : Set X} {D : ι → Set X} {π : Y → X} {z : Y}
    (hπ : IsBlowupAlong n C π) (hNclosed : IsClosed N) (hDclosed : ∀ i, IsClosed (D i))
    (hCN : C ⊆ N) (hzN : z ∈ geoStrictTransform π C N)
    {act : A → X → X} {act' : A → Y → Y}
    (hstate : LocalToricDivisorState (n := n) F N D (π z) act)
    (hpreserve : ∀ᶠ p in F ×ˢ 𝓝 (π z), p.2 ∈ C → act p.1 p.2 ∈ C)
    (hcomm : ∀ᶠ p in F ×ˢ 𝓝 z, π (act' p.1 p.2) = act p.1 (π p.2))
    (hcont : ∀ᶠ p in F ×ˢ 𝓝 z, ContinuousAt (act' p.1) p.2) :
    LocalToricDivisorState (n := n) F (geoStrictTransform π C N)
      (Sum.elim (fun i => geoStrictTransform π C (D i)) (fun _ : Unit => π ⁻¹' C)) z act' := by
  classical
  obtain ⟨S₀, μ, sec, Φ, m, hΦsrc, hN, hD, hm, hμ, hdiag, hsec, hrealize⟩ := hstate
  let M : ι → Option (Finset (Fin n)) := fun i => (m i).map (fun k => {k})
  have hflatD : ∀ i : ι, ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ D i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ optionalCoordLocus (M i)) := by
    intro i y hy hyΦ
    exact hD i y ⟨hy, hyΦ⟩
  have hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace S₀) :=
    fun hy hyΦ => hN _ ⟨hy,hyΦ⟩
  by_cases hzC : π z ∈ C
  · obtain ⟨k, hreg⟩ := hπ.1.2 _ hzC
    have hCan : IsComplexAnalyticSubset (n := n) C :=
      AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
    obtain ⟨B, σ, j, hj, hjfree, Ψ, hΨsrc, hdiag', hN', hD', hsec', hrealize'⟩ :=
      exists_centre_optional_successor_chart hπ hΦsrc S₀ hflatN hCN hCan hreg hzN
        hμ hdiag hpreserve hcomm hcont sec hsec hrealize D M hDclosed hflatD
    let μ' : A → Fin n → ℂ := fun a => chartVec (fun i => μ a (σ.symm i)) (n - B.card) j
    let sec' : (Fin n → ℂ) → A := fun b => sec (fun i => inverseChartVec b (n - B.card) j (σ i))
    have hμp : Tendsto (fun a i => μ a (σ.symm i)) F (𝓝 1) := by
      have hp : Continuous (fun b : Fin n → ℂ => fun i => b (σ.symm i)) :=
        continuous_pi fun i => continuous_apply (σ.symm i)
      exact (hp.tendsto 1).comp hμ
    have hμ' : Tendsto μ' F (𝓝 1) := tendsto_chartVec hμp _ _
    refine ⟨S₀.image σ, μ', sec', Ψ, nextDivisorMask σ j m, hΨsrc, hN', ?_,
      nextDivisorMask_valid S₀ m hm σ j hjfree, hμ', hdiag', hsec', hrealize'⟩
    intro i y hy
    cases i with
    | inl i =>
      change y ∈ geoStrictTransform π C (D i) ↔
        flatMap Ψ y ∈ optionalCoordLocus (((m i).bind fun k =>
          if σ k = j then none else some (σ k)).map (fun k => {k}))
      rw [← successorMask_singleton]
      exact (hD' y hy).1 i
    | inr i =>
      cases i
      simpa [nextDivisorMask, optionalCoordLocus, coordSubspace] using (hD' y hy).2
  · obtain ⟨Ψ, hΨsrc, hcoords, hdiag', hD'⟩ :=
      exists_off_centre_optional_chart hπ hzC hμ hdiag hcomm D M hDclosed hflatD
    have hN' : ∀ y ∈ flatDomain Ψ, y ∈ geoStrictTransform π C N ↔
        flatMap Ψ y ∈ coordSubspace S₀ := by
      intro y hy
      obtain ⟨hyC, hyΦ, heq⟩ := hcoords y hy
      rw [mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hNclosed hyC,
        hflatN hyΦ.1 hyΦ.2, heq]
      rfl
    refine ⟨S₀, μ, sec, Ψ, Sum.elim m (fun _ : Unit => none), hΨsrc, hN', ?_,
      offCentreDivisorMask_valid S₀ m hm, hμ, hdiag', hsec, hrealize⟩
    intro i y hy
    cases i with
    | inl i => exact hD' y hy i
    | inr i =>
      cases i
      have hyC := (hcoords y hy).1
      simp [optionalCoordLocus, hyC]

end
end Hironaka.HironakaG4LocalToricDivisors
