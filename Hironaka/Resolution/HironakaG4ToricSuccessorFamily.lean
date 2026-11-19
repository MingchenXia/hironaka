import Hironaka.Resolution.HironakaG4ToricHistoryDictionary

/-!
# Boundary and exceptional dictionaries in a permuted toric successor chart

The retained coordinate permutation and monomial projection equation give
exact equations for all strict transforms and the exceptional divisor in the
same actual successor chart.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ToricSuccessorFamily
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold NormalCrossings HironakaG34CoordinateScaling HironakaG4ToricHistoryDictionary

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C : Set X} {π : Y → X} {z : Y}
  {Φ Θ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z))}

/-- Exact strict-family and exceptional equations after the actual
coordinate permutation and monomial blowup chart. -/
theorem permuted_strict_family_and_exceptional
    (hΘΦ : Θ.source ⊆ Φ.source) (σ : Fin n ≃ Fin n)
    (hperm : ∀ w i, Θ.toFun w (σ i) = Φ.toFun w i)
    {k : ℕ} (hflatC : ∀ y ∈ flatDomain Θ,
      y ∈ C ↔ flatMap Θ y ∈ complexCoordinatePlane n k)
    {ι : Type*} (D : ι → Set X) (S : ι → Finset (Fin n))
    (hflatD : ∀ i {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ D i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace (S i)))
    {j : Fin n} (hj : k ≤ j.val)
    (Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z))
    (hΨsrc : Ψ.source ⊆ (chartAt (ComplexModel n) z).target)
    (hcoords : ∀ u ∈ flatDomain Ψ, π u ∈ flatDomain Θ ∧
      monomial k j (flatMap Ψ u) = flatMap Θ (π u)) :
    ∀ u ∈ flatDomain Ψ,
      (∀ i, u ∈ geoStrictTransform π C (D i) ↔
        j ∉ (S i).image σ ∧ flatMap Ψ u ∈ coordSubspace ((S i).image σ)) ∧
      (π u ∈ C ↔ flatMap Ψ u j = 0) := by
  have hflatC' : ∀ {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Θ.source →
        (y ∈ C ↔ Θ.toFun (chartAt (ComplexModel n) (π z) y) ∈ complexCoordinatePlane n k) :=
    fun hy hyΘ => hflatC _ ⟨hy,hyΘ⟩
  have hflatD' : ∀ i {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Θ.source →
        (y ∈ D i ↔ Θ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace ((S i).image σ)) := by
    intro i y hy hyΘ
    rw [hflatD i hy (hΘΦ hyΘ)]
    constructor
    · intro hD q hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
      rw [hperm]
      exact hD p hp
    · intro hD p hp
      have hq : σ p ∈ (S i).image σ := Finset.mem_image.mpr ⟨p,hp,rfl⟩
      have h := hD (σ p) hq
      rw [hperm] at h
      exact h
  exact strict_family_and_exceptional_coordinates hflatC' D (fun i => (S i).image σ)
    hflatD' hj Ψ hΨsrc hcoords

end
end Hironaka.HironakaG4ToricSuccessorFamily
