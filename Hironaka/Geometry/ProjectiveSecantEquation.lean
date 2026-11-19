import Hironaka.Geometry.ProjectiveSecantChartDimension
import Hironaka.Algebra.ProjectiveSecantHomogeneous

/-!
# The original low-dimensional projective source produces a genuine secant equation

Only the original closed immersion, original integrality and original
Krull-dimension inequality are inputs. The remaining-coordinate relation,
its homogeneous lift, its actual nonzero degree, and whole-kernel membership
are produced internally.
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
  (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i] [IsIntegral X]

/-- The actual original projective dimension internally produces a genuine positive homogeneous secant equation. -/
theorem exists_homogeneous_secant_equation (hdim : topologicalKrullDim X < n) :
    ∃ (d : ℕ) (F : MvPolynomial (Fin (n + 1)) k),
      0 < d ∧ F.IsHomogeneous d ∧ F ≠ 0 ∧
        MvPolynomial.rename Fin.succ F ∈ representativeIdeal k n i :=
  exists_homogeneous_remaining_equation k n (representativeIdeal k n i) (0 : Fin (n + 1))
    (exists_original_chart_relation k n i (0 : Fin (n + 1)) hdim)

/-- Actual secant-equation data are internally selected from the original geometric dimension argument. -/
def secantEquation (hdim : topologicalKrullDim X < n) :
    {e : ℕ × MvPolynomial (Fin (n + 1)) k //
      0 < e.1 ∧ e.2.IsHomogeneous e.1 ∧ e.2 ≠ 0 ∧
        MvPolynomial.rename Fin.succ e.2 ∈ representativeIdeal k n i} := by
  let h := exists_homogeneous_secant_equation k n i hdim
  exact ⟨⟨h.choose, h.choose_spec.choose⟩, h.choose_spec.choose_spec⟩

omit [IsIntegral X] in
/-- The represented whole original kernel has exactly the original closed image. -/
theorem zeroLocus_representativeIdeal_eq_range :
    ProjectiveSpectrum.zeroLocus (ProjectiveGrading k (n + 1))
      ((representativeIdeal k n i).toIdeal : Set _) = Set.range i := by
  rw [← GradedQuotient.quotientIdealSheaf_support_eq_zeroLocus]
  change ((originalInclusion k n (representativeIdeal k n i)).ker.support :
    Set (projectiveSpace k (n + 1))) = Set.range i
  rw [representativeInclusion_ker, Scheme.Hom.support_ker,
    i.isClosedEmbedding.isClosed_range.closure_eq]

end Hironaka.Geometry.ProjectiveSecant
