import DeJongAlterations.Geometry.SNCSubdivisorCartier

/-!
# Deleting actual strict normal crossings components

The reduced selected union has a genuine Cartier equation, actual
reduced structure, the actual selected irreducible components, and the
original scheme-theoretic regular intersections and codimensions.
-/

noncomputable section

open AlgebraicGeometry TopologicalSpace

namespace DeJongAlterations.Geometry.SNCSubdivisor

open SNCSubdivisorTopology

universe u

variable {X : Scheme.{u}}

/-- The actual reduced union of any finite subfamily of native SNC components is SNC. -/
theorem isStrictNormalCrossings_selected [IsLocallyNoetherian X]
    (D : X.IdealSheafData) (hD : IsStrictNormalCrossings D)
    (F : Finset (DivisorComponent D)) :
    IsStrictNormalCrossings (selectedDivisor D F) := by
  refine ⟨SNCSubdivisorCartier.selectedDivisor_isEffectiveCartierDivisor D hD F,
    selectedDivisor_isReduced D F, ?_, ?_, ?_⟩
  · intro x hx
    exact hD.regularAlong x (selectedSupport_le D F hx)
  · intro J hJ
    rw [componentIntersection_eq]
    exact hD.intersectionsRegular (J.map (componentEmbedding D F))
      (by simpa only [Finset.map_nonempty] using hJ)
  · intro J hJ
    rw [componentIntersection_eq, ← Finset.card_map (componentEmbedding D F)]
    exact hD.intersectionsCodimension (J.map (componentEmbedding D F))
      (by simpa only [Finset.map_nonempty] using hJ)

end DeJongAlterations.Geometry.SNCSubdivisor
