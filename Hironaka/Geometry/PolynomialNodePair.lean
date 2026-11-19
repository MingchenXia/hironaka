import Hironaka.Geometry.PolynomialNodeBoundary
import Hironaka.Geometry.SNCLocality

/-!
# The actual resolved polynomial-node pair

The genuine Boolean node-chart cover assembles the released exact chart
boundaries into a strict normal crossings divisor on the whole native blowup.
This is the concrete affine crossing-node case of de Jong Proposition 3.6.
-/

open AlgebraicGeometry CategoryTheory MvPolynomial

noncomputable section

namespace Hironaka.Geometry.PolynomialNodePair

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open PolynomialNodeBoundary PolynomialNodeResolution

variable (K : Type u) [Field K]

/-- The exact boundary is SNC globally on the actual native crossing-node blowup. -/
theorem resolvedBoundary_isStrictNormalCrossings :
    IsStrictNormalCrossings (resolvedBoundary K) := by
  let : Fact ((X (0 : Fin 2) : Base K) ≠ 0) := ⟨X_ne_zero 0⟩
  let : Fact ((X (1 : Fin 2) : Base K) ≠ 0) := ⟨X_ne_zero 1⟩
  apply SNCLocality.isStrictNormalCrossings_of_openCover (resolvedBoundary K)
    (NodeBlowupCover.nodeBlowupOpenCover (X 0 : Base K) (X 1))
  intro b
  cases b
  · exact resolvedBoundary_uChart_isStrictNormalCrossings K
  · exact resolvedBoundary_tChart_isStrictNormalCrossings K

/-- The actual original crossing-node boundary pulled back from the polynomial base. -/
def originalNodeBoundary : (polynomialNode K (0 : Fin 2) 1).IdealSheafData :=
  (baseBoundary K).comap (originalNodeToBase K)

/-- Equality of actual ideal sheaves, with no radical or enlargement of the boundary. -/
theorem resolvedBoundary_eq_comap :
    resolvedBoundary K =
      (originalNodeBoundary K).comap (resolutionMorphism K (0 : Fin 2) 1) :=
  Scheme.IdealSheafData.comap_comp (baseBoundary K)
    (resolutionMorphism K (0 : Fin 2) 1) (originalNodeToBase K)

/-- Its support is exactly the inverse image of the original-node coefficient boundary. -/
theorem resolvedBoundary_support :
    (resolvedBoundary K).support = (originalNodeBoundary K).support.preimage
      (resolutionMorphism K (0 : Fin 2) 1).continuous := by
  rw [resolvedBoundary_eq_comap, Scheme.IdealSheafData.support_comap]

/-- The actual crossing-node morphism is a regular projective alteration with SNC boundary. -/
theorem crossing_regular_projective_alteration_snc :
    IsRegularScheme (resolvedNode K (0 : Fin 2) 1) ∧
      IsProjectiveOver (resolutionMorphism K (0 : Fin 2) 1) ∧
      IsAlteration (resolutionMorphism K (0 : Fin 2) 1) ∧
      IsStrictNormalCrossings (resolvedBoundary K) := by
  obtain ⟨hreg, hproj, halt⟩ := crossing_regular_projective_alteration K
  exact ⟨hreg, hproj, halt, resolvedBoundary_isStrictNormalCrossings K⟩

/-- The same native resolved pair, including its exact original inverse-image support. -/
theorem crossing_resolved_pair :
    IsRegularScheme (resolvedNode K (0 : Fin 2) 1) ∧
      IsProjectiveOver (resolutionMorphism K (0 : Fin 2) 1) ∧
      IsAlteration (resolutionMorphism K (0 : Fin 2) 1) ∧
      IsStrictNormalCrossings (resolvedBoundary K) ∧
      (resolvedBoundary K).support = (originalNodeBoundary K).support.preimage
        (resolutionMorphism K (0 : Fin 2) 1).continuous := by
  obtain ⟨hreg, hproj, halt, hsnc⟩ := crossing_regular_projective_alteration_snc K
  exact ⟨hreg, hproj, halt, hsnc, resolvedBoundary_support K⟩

end Hironaka.Geometry.PolynomialNodePair
