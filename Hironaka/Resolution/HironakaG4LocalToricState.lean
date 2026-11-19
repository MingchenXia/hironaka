import Hironaka.Resolution.HironakaG4OptionalCentreSuccessor
import Hironaka.Resolution.HironakaG4OptionalOffCentre

/-!
# Local toric state and its one-blowup propagation

A local state records the actual diagonal action, exact carrier coordinates,
free-character section, and optional equations for each tracked boundary.
At a strict-carrier point, the state propagates across an actual blowup,
including its new exceptional member, in both centre and off-centre cases.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4LocalToricState
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold NormalCrossings HironakaG34CoordinateScaling HironakaG34ToricCharts
  HironakaG4ToricCharacterSections HironakaG4OptionalBoundaryTransform
  HironakaG4OptionalCentreSuccessor HironakaG4OptionalOffCentre

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {A : Type*} (F : Filter A)

/-- The actual local chart and action, with an optional coordinate equation
for every tracked boundary member. -/
def LocalToricState (N : Set X) (E : List (Set X)) (x : X) (act : A → X → X) : Prop :=
  ∃ (S : Finset (Fin n)) (μ : A → Fin n → ℂ) (sec : (Fin n → ℂ) → A)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)),
    Φ.source ⊆ (chartAt (ComplexModel n) x).target ∧
    (∀ y ∈ flatDomain Φ, y ∈ N ↔ flatMap Φ y ∈ coordSubspace S) ∧
    (∀ H ∈ E, ∃ M : Option (Finset (Fin n)),
      ∀ y ∈ flatDomain Φ, y ∈ H ↔ flatMap Φ y ∈ optionalCoordLocus M) ∧
    Tendsto μ F (𝓝 1) ∧ ActsDiagonallyNear F act μ Φ x ∧
    Tendsto sec (𝓝 1) F ∧
    ∀ᶠ b in 𝓝 (1 : Fin n → ℂ), ∀ i ∉ S, μ (sec b) i = b i

/-- Propagate one actual local toric state through a blowup, retaining all
tracked members and adding the exceptional divisor. -/
theorem localToricState_step {N C : Set X} {E : List (Set X)} {π : Y → X} {z : Y}
    (hπ : IsBlowupAlong n C π) (hNclosed : IsClosed N) (hEclosed : ∀ H ∈ E, IsClosed H)
    (hCN : C ⊆ N) (hzN : z ∈ geoStrictTransform π C N)
    {act : A → X → X} {act' : A → Y → Y}
    (hstate : LocalToricState (n := n) F N E (π z) act)
    (hpreserve : ∀ᶠ p in F ×ˢ 𝓝 (π z), p.2 ∈ C → act p.1 p.2 ∈ C)
    (hcomm : ∀ᶠ p in F ×ˢ 𝓝 z, π (act' p.1 p.2) = act p.1 (π p.2))
    (hcont : ∀ᶠ p in F ×ˢ 𝓝 z, ContinuousAt (act' p.1) p.2) :
    LocalToricState (n := n) F (geoStrictTransform π C N)
      (E.map (geoStrictTransform π C) ++ [π ⁻¹' C]) z act' := by
  classical
  obtain ⟨S₀, μ, sec, Φ, hΦsrc, hN, hE, hμ, hdiag, hsec, hrealize⟩ := hstate
  let I := {H : Set X // H ∈ E}
  let D : I → Set X := Subtype.val
  let M : I → Option (Finset (Fin n)) := fun i => Classical.choose (hE i.1 i.2)
  have hclosed : ∀ i : I, IsClosed (D i) := fun i => hEclosed i.1 i.2
  have hflatD : ∀ i : I, ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ D i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ optionalCoordLocus (M i)) := by
    intro i y hy hyΦ
    exact Classical.choose_spec (hE i.1 i.2) y ⟨hy,hyΦ⟩
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
        hμ hdiag hpreserve hcomm hcont sec hsec hrealize D M hclosed hflatD
    let μ' : A → Fin n → ℂ := fun a => chartVec (fun i => μ a (σ.symm i)) (n - B.card) j
    let sec' : (Fin n → ℂ) → A := fun b => sec (fun i => inverseChartVec b (n - B.card) j (σ i))
    have hμp : Tendsto (fun a i => μ a (σ.symm i)) F (𝓝 1) := by
      have hp : Continuous (fun b : Fin n → ℂ => fun i => b (σ.symm i)) :=
        continuous_pi fun i => continuous_apply (σ.symm i)
      exact (hp.tendsto 1).comp hμ
    have hμ' : Tendsto μ' F (𝓝 1) := tendsto_chartVec hμp _ _
    refine ⟨S₀.image σ, μ', sec', Ψ, hΨsrc, hN', ?_, hμ', hdiag', hsec', hrealize'⟩
    intro H hH
    rcases List.mem_append.mp hH with hH | hH
    · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      refine ⟨successorMask σ j (M ⟨H₀,hH₀⟩), ?_⟩
      intro y hy
      exact (hD' y hy).1 ⟨H₀,hH₀⟩
    · have hEq : H = π ⁻¹' C := by simpa only [List.mem_singleton] using hH
      subst H
      refine ⟨some {j}, ?_⟩
      intro y hy
      simpa [optionalCoordLocus, coordSubspace] using (hD' y hy).2
  · obtain ⟨Ψ, hΨsrc, hcoords, hdiag', hD'⟩ :=
      exists_off_centre_optional_chart hπ hzC hμ hdiag hcomm D M hclosed hflatD
    have hN' : ∀ y ∈ flatDomain Ψ, y ∈ geoStrictTransform π C N ↔
        flatMap Ψ y ∈ coordSubspace S₀ := by
      intro y hy
      obtain ⟨hyC, hyΦ, heq⟩ := hcoords y hy
      rw [mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous hNclosed hyC,
        hflatN hyΦ.1 hyΦ.2, heq]
      rfl
    refine ⟨S₀, μ, sec, Ψ, hΨsrc, hN', ?_, hμ, hdiag', hsec, hrealize⟩
    intro H hH
    rcases List.mem_append.mp hH with hH | hH
    · obtain ⟨H₀, hH₀, rfl⟩ := List.mem_map.mp hH
      exact ⟨M ⟨H₀,hH₀⟩, fun y hy => hD' y hy ⟨H₀,hH₀⟩⟩
    · have hEq : H = π ⁻¹' C := by simpa only [List.mem_singleton] using hH
      subst H
      refine ⟨none, ?_⟩
      intro y hy
      have hyC := (hcoords y hy).1
      simp [optionalCoordLocus, hyC]

end
end Hironaka.HironakaG4LocalToricState
