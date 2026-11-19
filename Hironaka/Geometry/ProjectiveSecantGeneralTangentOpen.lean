import Hironaka.Geometry.ProjectiveSecantGeneralPointOpen
import Hironaka.Geometry.ProjectiveSecantTangentOpen

/-!
# A whole-source tangent and secant centre open without integrality
-/

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Hironaka.Geometry.ProjectiveSecant

open ProjectiveIdeal ProjectiveRationalPointCoordinates ProjectiveProjectionCenter

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (k : Type u) [Field k] (n : ℕ)
  {X : Scheme.{u}} (i : X ⟶ projectiveSpace k (n + 1)) [IsClosedImmersion i]

/-- The actual ambient generic point lies in the whole-source fixed-point centre open, without source integrality. -/
theorem generalFixedPointCenterOpen_mem_generic
    (q : Spec (CommRingCat.of k) ⟶ projectiveSpace k (n + 1))
    (hq : q ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
    (hdim : topologicalKrullDim X < n) :
    ambientGenericPoint k n ∈ generalFixedPointCenterOpen k n q hq i hdim := by
  change (coordinateAutomorphism k n (pointVector k n q hq) (pointVector_ne_zero k n q hq)).hom
    (ambientGenericPoint k n) ∈ generalSecantCenterOpen k n (fixedPointInclusion k n q hq i) hdim
  rw [coordinateAutomorphism_apply_generic]
  change MvPolynomial.rename Fin.succ (generalSecantEquation k n (fixedPointInclusion k n q hq i) hdim).val.2 ≠ 0
  exact (MvPolynomial.rename_eq_zero_iff_of_injective _ (Fin.succ_injective (n + 1))).not.mpr
    (generalSecantEquation k n (fixedPointInclusion k n q hq i) hdim).property.2.2.1

variable (s : Spec (CommRingCat.of k) ⟶ X)
  (hs : (s ≫ i) ≫ projectiveSpaceStructure k (n + 1) = 𝟙 _)
  (hx : s (⊥ : PrimeSpectrum k) ∈ (i ≫ projectiveSpaceStructure k (n + 1)).smoothLocus)
  (hdim : topologicalKrullDim X < n)

/-- The actual tangent and whole-source secant conditions are computed from the original embedding and smooth point. -/
def generalTangentSecantCenterOpen : (projectiveSpace k (n + 1)).Opens :=
  originalTangentOpen k n i s hs hdim.le hx ⊓ generalFixedPointCenterOpen k n (s ≫ i) hs i hdim

/-- Both original computed opens contain the same actual ambient generic point. -/
theorem generalTangentSecantCenterOpen_nonempty :
    (generalTangentSecantCenterOpen k n i s hs hx hdim : Set (projectiveSpace k (n + 1))).Nonempty :=
  ⟨ambientGenericPoint k n, originalTangentOpen_mem_generic k n i s hs hdim.le hx,
    generalFixedPointCenterOpen_mem_generic k n i (s ≫ i) hs hdim⟩

end Hironaka.Geometry.ProjectiveSecant
