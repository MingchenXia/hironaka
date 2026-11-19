import Hironaka.Resolution.HironakaG4ToricOffCentreAction
import Hironaka.Resolution.HironakaG4OptionalBoundaryTransform

/-!
# Optional boundary dictionaries off a blowup centre

The same off-centre successor chart retains the actual diagonal action and
all optional boundary masks, including already absent members.
-/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4OptionalOffCentre
noncomputable section
open Hironaka.BlowupSequences BlowupFlatCoordinates BlowupStrictSubmanifold
  NormalCrossings HironakaG34CoordinateScaling HironakaG34ToricCharts
  HironakaG4ToricOffCentreAction HironakaG4OptionalBoundaryTransform

variable {n : ℕ} {X Y : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X} {z : Y}
  {Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (π z) (π z))}

/-- Off the centre, the actual successor chart retains the diagonal action
and every optional strict-boundary mask unchanged. -/
theorem exists_off_centre_optional_chart (hπ : IsBlowupAlong n C π) (hz : π z ∉ C)
    {A : Type*} {F : Filter A} {act : A → X → X} {act' : A → Y → Y}
    {μ : A → Fin n → ℂ} (hμ : Tendsto μ F (𝓝 1))
    (hdiag : ActsDiagonallyNear F act μ Φ (π z))
    (hcomm : ∀ᶠ p in F ×ˢ 𝓝 z, π (act' p.1 p.2) = act p.1 (π p.2))
    {ι : Type*} (D : ι → Set X) (M : ι → Option (Finset (Fin n))) (hclosed : ∀ i, IsClosed (D i))
    (hflat : ∀ i {y : X}, y ∈ (chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) y ∈ Φ.source →
        (y ∈ D i ↔ Φ.toFun (chartAt (ComplexModel n) (π z) y) ∈ optionalCoordLocus (M i))) :
    ∃ Ψ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) z z),
      Ψ.source ⊆ (chartAt (ComplexModel n) z).target ∧
      (∀ u ∈ flatDomain Ψ, π u ∉ C ∧ π u ∈ flatDomain Φ ∧ flatMap Ψ u = flatMap Φ (π u)) ∧
      ActsDiagonallyNear F act' μ Ψ z ∧
      ∀ u ∈ flatDomain Ψ, ∀ i, u ∈ geoStrictTransform π C (D i) ↔
        flatMap Ψ u ∈ optionalCoordLocus (M i) := by
  obtain ⟨Ψ, hΨsrc, hcoords, hdiag'⟩ := exists_diagonal_off_centre_chart hπ hz hμ hdiag hcomm
  refine ⟨Ψ, hΨsrc, hcoords, hdiag', ?_⟩
  intro u hu i
  obtain ⟨huC, huΦ, heq⟩ := hcoords u hu
  rw [mem_geoStrictTransform_iff_of_notMem hπ.contMDiff.continuous (hclosed i) huC,
    hflat i huΦ.1 huΦ.2, heq]
  rfl

end
end Hironaka.HironakaG4OptionalOffCentre
