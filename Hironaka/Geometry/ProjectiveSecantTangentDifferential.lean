import Hironaka.Geometry.ProjectiveSecantTangentHomogeneous
import Hironaka.Algebra.ProjectiveSecantTangentDifferential
import Hironaka.Algebra.ProjectiveSecantTangentEuler

/-!
# Exact original homogeneous gradient and centre-direction nonvanishing from the computed original open
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection ProjectiveRationalPointCoordinates
open Algebra.ProjectiveSecant

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hdim : topologicalKrullDim X ≤ n)
  (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)

/-- The exact original chosen affine equation vanishes at the exact original point by the whole actual source-coordinate triangle. -/
theorem tangentChartEquation_eval_zero :
    chartAlgebraPoint k n (s ≫ i) hs (tangentChartEquation k n i s hs hdim hx).val = 0 := by
  let F := tangentChartEquation k n i s hs hdim hx
  have hF : F.val ∈ RingHom.ker (tangentChartPolynomialMap k n i (chosenChart k n (s ≫ i))) :=
    (tangentChartPolynomialMap_ker k n i _).symm.le F.property.1
  change tangentChartPolynomialMap k n i (chosenChart k n (s ≫ i)) F.val = 0 at hF
  calc
    chartAlgebraPoint k n (s ≫ i) hs F.val =
        tangentSourcePointRingHom k n i s
          (tangentChartPolynomialMap k n i (chosenChart k n (s ≫ i)) F.val) :=
      (RingHom.congr_fun (tangentSourcePointRingHom_comp k n i s hs) F.val).symm
    _ = 0 := by rw [hF, map_zero]

/-- The positive homogeneous equation is chosen internally in the whole original homogeneous ideal, with exactly the original chosen affine tangent equation. -/
def originalHomogeneousTangentEquation :
    {e : ℕ × MvPolynomial (Fin (n + 2)) k //
      0 < e.1 ∧ e.2.IsHomogeneous e.1 ∧ e.2 ≠ 0 ∧ e.2 ∈ representativeIdeal k n i ∧
      coordinateDehom (chosenChart k n (s ≫ i)) e.2 = (tangentChartEquation k n i s hs hdim hx).val} :=
  Classical.choice (by
    obtain ⟨d, H, hd, hH, hHn, hHJ, hHF, _⟩ :=
      exists_original_homogeneous_tangent_relation k n i s hs hdim hx
    exact ⟨⟨(d, H), hd, hH, hHn, hHJ, hHF⟩⟩)

/-- The internally produced whole original homogeneous equation vanishes at the same original normalized point. -/
theorem originalHomogeneousTangentEquation_eval_zero :
    MvPolynomial.eval (pointVector k n (s ≫ i) hs)
      (originalHomogeneousTangentEquation k n i s hs hdim hx).val.2 = 0 := by
  rw [← chartAlgebraPoint_dehom,
    (originalHomogeneousTangentEquation k n i s hs hdim hx).property.2.2.2.2]
  exact tangentChartEquation_eval_zero k n i s hs hdim hx

/-- Each whole original homogeneous gradient coefficient is exactly the corresponding original affine derivative coefficient at the exact original point. -/
theorem originalHomogeneousTangentEquation_partial
    (l : ChartIndex (chosenChart k n (s ≫ i))) :
    MvPolynomial.eval (pointVector k n (s ≫ i) hs)
        (MvPolynomial.pderiv l.val (originalHomogeneousTangentEquation k n i s hs hdim hx).val.2) =
      chartAlgebraPoint k n (s ≫ i) hs
        (MvPolynomial.pderiv l (tangentChartEquation k n i s hs hdim hx).val) := by
  rw [← chartAlgebraPoint_dehom, ← original_pderiv_coordinateDehom,
    (originalHomogeneousTangentEquation k n i s hs hdim hx).property.2.2.2.2]

/-- The whole internally produced original homogeneous gradient linear form is literally the already constructed original tangent linear form. -/
theorem originalHomogeneousTangentEquation_gradient :
    (∑ l : Fin (n + 2),
      C (MvPolynomial.eval (pointVector k n (s ≫ i) hs)
        (MvPolynomial.pderiv l (originalHomogeneousTangentEquation k n i s hs hdim hx).val.2)) * MvPolynomial.X l) =
      originalTangentLinearForm k n i s hs hdim hx := by
  rw [original_homogeneous_gradient_eq_tangentLinearForm
    (chosenChart k n (s ≫ i))
    (originalHomogeneousTangentEquation k n i s hs hdim hx).property.2.1
    (pointVector k n (s ≫ i) hs) (pointVector_chosenChart k n (s ≫ i) hs)
    (originalHomogeneousTangentEquation_eval_zero k n i s hs hdim hx)]
  simp only [originalHomogeneousTangentEquation_partial, originalTangentLinearForm]

/-- Membership of the actual original centre in the actual internally computed tangent open produces a genuinely nonzero derivative of the same whole original homogeneous equation in that original centre direction. -/
theorem originalHomogeneousTangentEquation_direction_ne_zero
    (p : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hp : p ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hc : pointImage k n p ∈ originalTangentOpen k n i s hs hdim hx) :
    (∑ l : Fin (n + 2),
      MvPolynomial.eval (pointVector k n (s ≫ i) hs)
        (MvPolynomial.pderiv l (originalHomogeneousTangentEquation k n i s hs hdim hx).val.2) *
          pointVector k n p hp l) ≠ 0 := by
  have he : MvPolynomial.eval (pointVector k n p hp)
      (originalTangentLinearForm k n i s hs hdim hx) ≠ 0 := by
    intro hz
    exact hc ((pointImage_mem_homogeneous k n p hp
      (originalTangentLinearForm_isHomogeneous k n i s hs hdim hx)).mpr hz)
  rw [← originalHomogeneousTangentEquation_gradient k n i s hs hdim hx] at he
  simpa only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X] using he

end Hironaka.Geometry.ProjectiveSecant
