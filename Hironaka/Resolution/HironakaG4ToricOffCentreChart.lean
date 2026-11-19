import Hironaka.Invariant.MonomialResolution
import Hironaka.Resolution.HironakaG34CoordinateScaling

/-!
# Retaining uncentred coordinates off the next blowup centre

The blowup is a local biholomorphism off its centre. Translating a chart only
for the local inverse construction and translating back retains the literal
old coordinate values, so carrier and boundary masks pull back unchanged.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4ToricOffCentreChart
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupStrictSubmanifold
  NormalCrossings HironakaG34CoordinateScaling MonomialResolution

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X} {z : Y}

/-- The actual off-centre chart reads the literal original uncentred
coordinates through the blowup map. -/
theorem exists_uncentred_off_centre_chart (hπ : IsBlowupAlong n C π) (hz : π z ∉ C)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z))) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z),
      Ψ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      ∀ u ∈ flatDomain Ψ, π u ∉ C ∧ π u ∈ flatDomain Φ ∧ flatMap Ψ u = flatMap Φ (π u) := by
  let w := flatMap Φ (π z)
  let Φ₀ := RegularPatchPullback.subConst Φ w
  have hΦ₀ : Φ₀.toFun (chartAt (ComplexModel n) (π z) (π z)) = 0 := by
    change Φ.toFun (chartAt (ComplexModel n) (π z) (π z)) - w = 0
    simp [w, flatMap]
  obtain ⟨Θ, hΘsrc, hΘzero, hΘ⟩ := exists_chart_comp hπ hz Φ₀ hΦ₀
  let Ψ := RegularPatchPullback.subConst Θ (-w)
  refine ⟨Ψ, hΘsrc, ?_⟩
  intro u hu
  obtain ⟨huC, huΦ, heq⟩ := hΘ hu.1 hu.2
  refine ⟨huC, huΦ, ?_⟩
  change Θ.toFun (chartAt (ComplexModel n) z u) - -w = flatMap Φ (π u)
  rw [heq]
  change (flatMap Φ (π u) - w) - -w = flatMap Φ (π u)
  simp

/-- Each closed coordinate-described subset has exactly the same strict
coordinate locus in the retained off-centre chart. -/
theorem off_centre_strict_coordinate_family (hπ : IsBlowupAlong n C π) (hz : π z ∉ C)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z)))
    {ι : Type*} (D : ι → Set X) (S : ι → Finset (Fin n)) (hclosed : ∀ i, IsClosed (D i))
    (hflat : ∀ i {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ D i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ coordSubspace (S i))) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z),
      Ψ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      (∀ u ∈ flatDomain Ψ, π u ∉ C ∧ π u ∈ flatDomain Φ ∧ flatMap Ψ u = flatMap Φ (π u)) ∧
      ∀ u ∈ flatDomain Ψ, ∀ i, u ∈ geoStrictTransform π C (D i) ↔
        flatMap Ψ u ∈ coordSubspace (S i) := by
  obtain ⟨Ψ, hΨsrc, hcoords⟩ := exists_uncentred_off_centre_chart hπ hz Φ
  refine ⟨Ψ, hΨsrc, hcoords, ?_⟩
  intro u hu i
  obtain ⟨huC, huΦ, heq⟩ := hcoords u hu
  rw [mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous (hclosed i) huC,
    hflat i huΦ.1 huΦ.2, heq]
  rfl

end
end Hironaka.HironakaG4ToricOffCentreChart
