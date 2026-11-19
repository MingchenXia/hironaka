import Hironaka.Resolution.HironakaG4RelativeGeneratorUnit
import Hironaka.Resolution.HironakaG4ProtectedResidualEndpoint

/-! A unit monomial part makes the actual residual generator a unit trace. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG4UnitResidualTrace
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan RestrictedIdealExtension DivisorExponentAlong
  MonomialPartAlong NonmonomialTransformAlong HironakaG4RelativeGeneratorUnit

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

/-- If the recorded monomial part is a unit, the normalized whole ideal and
its nonmonomial residual have the same germ. -/
theorem normalized_residual_germ_eq_of_monomial_unit {N : Set X} {I : GermIdeal n X}
    {B : List (Set X)} (hc : (restrictOn n N I).IsCoherent) {x : X}
    (hunit : (monomialPartAlong n N (restrictOn n N I) B).mem x 1) (g : X → ℂ) :
    (restrictOn n N I).mem x g ↔ (nonmonomialPartAlong n N (restrictOn n N I) B).mem x g := by
  exact HironakaG4ProtectedResidualEndpoint.normalized_residual_mem_iff_at_unit hc hunit g

/-- At a monomial-unit point, relative generators of the actual normalized
old trace and its actual residual differ by a holomorphic unit on N. -/
theorem exists_unit_trace_of_monomial_unit {N : Set X} {I : GermIdeal n X}
    {B : List (Set X)} {x : X} {f r : X → ℂ}
    (hc : (restrictOn n N I).IsCoherent) (hnz : IsNonzeroAlongAt N (restrictOn n N I) x)
    (hunit : (monomialPartAlong n N (restrictOn n N I) B).mem x 1)
    (hf : HolomorphicAt n f x) (hr : HolomorphicAt n r x)
    (hF : ∀ g, (restrictOn n N I).mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = f) x g)
    (hR : ∀ g, (nonmonomialPartAlong n N (restrictOn n N I) B).mem x g ↔
      HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) N (· = r) x g) :
    ∃ a : X → ℂ, HolomorphicAt n a x ∧ a x ≠ 0 ∧ ∀ᶠ y in 𝓝 x, y ∈ N → f y = a y * r y := by
  apply exists_unit_of_same_nonzero_relative_generator hf hr hnz hF
  intro g
  exact (normalized_residual_germ_eq_of_monomial_unit hc hunit g).trans (hR g)

end
end Hironaka.HironakaG4UnitResidualTrace
