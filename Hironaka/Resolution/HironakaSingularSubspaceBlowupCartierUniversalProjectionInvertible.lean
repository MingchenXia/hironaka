import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartier
import Hironaka.Resolution.HironakaSingularIdealRegularPrincipal

/-!
# The SAME actual singular projection has standard invertible pulled ideal stalks

The canonical actual projection/inclusion image ideal is retained. Its
standard native Module.Invertible structure is derived from the already
constructed actual local Cartier section, using the disjoint standard
regular-principal ideal module equivalence. No ideal certificate is input.

Blueprint: `hironaka-singular-subspace-blowup-cartier-universal-projection-invertible.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartierUniversalProjectionInvertible

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaSingularSubspaceBlowupLift HironakaSingularSubspaceBlowupCartier
  HironakaSingularIdealRegularPrincipal

noncomputable section

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

/-- The canonical actual projection ideal is a standard invertible module
at every literal singular strict-transform stalk, derived from density. -/
theorem projection_pulled_ideal_moduleInvertible
    (hπ : IsBlowupAlong n C π) (hW : IsClosed W) (hdense : W ⊆ closure (W \ C))
    (x : strictTransform n π W) :
    Module.Invertible ((actualSubspaceSheaf (n := n) (strictTransform n π W)).presheaf.stalk x).carrier
      (Ideal.map ((strictTransformProjection hπ hW).stalkMap x).hom
        (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap
          ((strictTransformProjection hπ hW).base x)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C)
            ((strictTransformProjection hπ hW).base x).val))) := by
  obtain ⟨U, hxU, a, ha⟩ := exists_local_projection_cartier_generator hπ hW hdense x
  exact moduleInvertible_of_span_eq _ (ha x hxU).1 (ha x hxU).2

end

end Hironaka.HironakaSingularSubspaceBlowupCartierUniversalProjectionInvertible
