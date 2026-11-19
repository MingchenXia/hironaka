import Hironaka.Geometry.ProjectiveSecantGeneralChartDimension
import Hironaka.Geometry.ProjectiveSecantEquation

/-!
# Whole original homogeneous secant equations for nonreduced and reducible sources
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection
open Algebra.ProjectiveProjectionFinite Algebra.ProjectiveSecant

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ) {X : Scheme.{u}}
  (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

/-- The entire original homogeneous ideal contains an internally produced nonzero remaining-coordinate equation. -/
theorem exists_homogeneous_secant_equation_general (hdim : topologicalKrullDim X < n) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k),
      0 < d ∧ F.IsHomogeneous d ∧ F ≠ 0 ∧
        MvPolynomial.rename Fin.succ F ∈ representativeIdeal k n i :=
  exists_homogeneous_remaining_equation k n (representativeIdeal k n i) (0 : Fin (n + 1))
    (exists_original_chart_relation_general k n i (0 : Fin (n + 1)) hdim)

/-- Actual equation data selected from the original dimension inequality, retaining original nilpotents. -/
def generalSecantEquation (hdim : topologicalKrullDim X < n) :
    {e : ℕ × MvPolynomial (Fin (n + 1)) k //
      0 < e.1 ∧ e.2.IsHomogeneous e.1 ∧ e.2 ≠ 0 ∧
        MvPolynomial.rename Fin.succ e.2 ∈ representativeIdeal k n i} := by
  let h := exists_homogeneous_secant_equation_general k n i hdim
  exact ⟨⟨h.choose, h.choose_spec.choose⟩, h.choose_spec.choose_spec⟩

end Hironaka.Geometry.ProjectiveSecant
