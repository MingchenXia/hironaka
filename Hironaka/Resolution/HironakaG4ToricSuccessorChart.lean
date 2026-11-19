import Hironaka.Resolution.HironakaG4ToricCentreSuccessor

/-!
# Successor toric chart above an invariant centre

At a point of the actual strict carrier above the next centre, flatten the
centre in the retained diagonal coordinates and transport the actual action,
carrier mask and partial character section through the same blowup chart.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ToricSuccessorChart
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold NormalCrossings HironakaG34CoordinateScaling HironakaG34ToricCharts
  HironakaG4ToricCharacterSections HironakaG4ToricFreePivot HironakaG4ToricHistoryDictionary
  HironakaG4ToricCentreSuccessor

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C N : Set X} {π : Y → X} {z : Y}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z))}

/-- A centre point of the next actual blowup has a toric successor chart,
retaining the exact strict-carrier mask and the transformed free section. -/
theorem exists_toric_successor_chart
    (hπ : IsBlowupAlong n C π)
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target)
    (S : Finset (Fin n))
    (hflatN : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ N ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace S))
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
    (hrealize : ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S, μ (sec b) i = b i) :
    ∃ (B : Finset (Fin n)) (σ : Fin n ≃ Fin n) (j : Fin n),
      n - B.card ≤ j.val ∧ j ∉ S.image σ ∧
      ∃ Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z)),
        Θ.source ⊆ Φ.source ∧ Θ.source ⊆ (chartAt (ComplexModel n) (π z)).target ∧
        (∀ w i, Θ.toFun w (σ i) = Φ.toFun w i) ∧
        (∀ y ∈ flatDomain Θ, y ∈ C ↔ flatMap Θ y ∈ complexCoordinatePlane n (n - B.card)) ∧
      ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z),
        Ψ.source ⊆ (chartAt (ComplexModel n) z).target ∧
        (∀ u ∈ flatDomain Ψ, π u ∈ flatDomain Θ ∧
          monomial (n - B.card) j (flatMap Ψ u) = flatMap Θ (π u)) ∧
        ActsDiagonallyNear F act' (fun a => chartVec (fun i => μ a (σ.symm i)) (n - B.card) j) Ψ z ∧
        (∀ u ∈ flatDomain Ψ, u ∈ geoStrictTransform π C N ↔
          flatMap Ψ u ∈ coordSubspace (S.image σ)) ∧
        Tendsto (fun b => sec (fun i => inverseChartVec b (n - B.card) j (σ i))) (𝓝 1) F ∧
        ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S.image σ,
          chartVec (fun a => μ (sec (fun q => inverseChartVec b (n - B.card) j (σ q))) (σ.symm a))
            (n - B.card) j i = b i := by
  obtain ⟨B, σ, Ψ, hΨΦ, hΨsrc, hperm, hflatC, hflatN', hdiag', hsec', hrealize'⟩ :=
    exists_centre_flattening_with_partial_realization hΦsrc S hflatN hCN hCan hreg
      hμ hdiag hpreserve sec hsec hrealize
  have hμ' : Tendsto (fun a i => μ a (σ.symm i)) F (𝓝 1) := by
    have hperm : Continuous (fun b : Fin n → ℂ => fun i => b (σ.symm i)) :=
      continuous_pi fun i => continuous_apply (σ.symm i)
    exact (hperm.tendsto 1).comp hμ
  have hflatC' : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Ψ.source →
        (y ∈ C ↔ Ψ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n (n - B.card)) :=
    fun hy hyΨ => hflatC _ ⟨hy,hyΨ⟩
  have hflatN'' : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Ψ.source →
        (y ∈ N ↔ Ψ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace (S.image σ)) :=
    fun hy hyΨ => hflatN' _ ⟨hy,hyΨ⟩
  obtain ⟨j, hj, hjfree, Ψ', hΨ'src, hcoords, hdiag'', hstrict, hsec'', hrealize''⟩ :=
    exists_toric_chart_with_partial_realization hπ hΨsrc hflatC' (S.image σ) hflatN''
      (mem_flatDomain_self Ψ) hzN hμ' hdiag' hcomm hcont
      (fun b : Fin n → ℂ => sec (fun i => b (σ i))) hsec' hrealize'
  refine ⟨B, σ, j, hj, hjfree, Ψ, hΨΦ, hΨsrc, hperm, hflatC, Ψ', hΨ'src, hcoords, hdiag'', ?_, hsec'', hrealize''⟩
  intro u hu
  rw [mem_geoStrictTransform_iff_flatMap hflatC' (S.image σ) hflatN'' hj Ψ' hΨ'src hcoords hu]
  simp [hjfree]

end
end Hironaka.HironakaG4ToricSuccessorChart
