import Hironaka.Geometry.ProjectiveSecantTangentCoordinates
import Hironaka.Geometry.ProjectiveSecantTangentOpen
import Hironaka.Algebra.ProjectiveSecantTangentHomogeneous

/-!
# The original smooth rational point produces a whole original homogeneous tangent relation
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveProjection ProjectiveRationalPointCoordinates

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]
  (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)

/-- The actual original closed source and original smooth rational source point internally produce a nonzero positive-degree relation in the WHOLE original homogeneous ideal, retaining a genuine original nonzero chart partial derivative. -/
theorem exists_original_homogeneous_tangent_relation (hdim : topologicalKrullDim X ≤ n)
    (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus) :
    ∃ (d : ℕ) (H : MvPolynomial (Fin (n + 2)) k),
      0 < d ∧ H.IsHomogeneous d ∧ H ≠ 0 ∧ H ∈ representativeIdeal k n i ∧
      coordinateDehom (chosenChart k n (s ≫ i)) H = (tangentChartEquation k n i s hs hdim hx).val ∧
      ∃ l : {j : Fin (n + 2) // j ≠ chosenChart k n (s ≫ i)},
        chartAlgebraPoint k n (s ≫ i) hs
          (MvPolynomial.pderiv l (coordinateDehom (chosenChart k n (s ≫ i)) H)) ≠ 0 := by
  let F := tangentChartEquation k n i s hs hdim hx
  obtain ⟨l, hl⟩ := F.property.2
  have hFn : F.val ≠ 0 := by
    intro hz
    apply hl
    rw [hz, map_zero, map_zero]
  have hF : F.val ∈ (representativeIdeal k n i).toIdeal.map
      (coordinateDehom (chosenChart k n (s ≫ i))).toRingHom :=
    (tangent_coordinateIdeal_eq k n i _).le F.property.1
  obtain ⟨d, H, hd, hH, hHn, hHJ, hHF⟩ :=
    Algebra.ProjectiveSecant.exists_homogeneous_mem_exact_dehom k n
      (representativeIdeal k n i) (chosenChart k n (s ≫ i)) hF hFn
  exact ⟨d, H, hd, hH, hHn, hHJ, hHF, l, by simpa only [hHF] using hl⟩

end Hironaka.Geometry.ProjectiveSecant
