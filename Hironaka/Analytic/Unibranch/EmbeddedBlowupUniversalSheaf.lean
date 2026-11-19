import Hironaka.Analytic.Unibranch.EmbeddedBlowupUniversal
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalSheafGlobal

/-!
# Same canonical rank-one ideal sheaf and ORIGINAL-source universal lifting

This is the direct API connection to the original Hausdorff/paracompact source
category. The native whole-ideal stalk theorem applies to its raw original LRS;
no global source second countability or compactness is added.
Blueprint: `embedded-blowup-universal-sheaf.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedBlowupUniversalSheaf

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
  HironakaSingularSubspaceBlowupCartierUniversalSheafGlobal
  SourceReducedComplexSpace EmbeddedBlowup EmbeddedBlowupUniversal

noncomputable section

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

/-- Standard locally-free singleton generator data on the SAME canonical
ideal sheaf give a unique full lift for arbitrary ORIGINAL A, with no global SC. -/
theorem exists_unique_source_factorization_of_locallyFreeData
    (hπ : IsBlowupAlong n C π) (hWa : IsComplexAnalyticSubset (n := n) W)
    (A : SourceReducedComplexSpace) (F : A ⟶ ofClosedAnalytic W hWa)
    (q : (actualPulledCentreIdealModule
      (F.hom.left ≫ actualSubspaceInclusion (n := n) W) C).LocalGeneratorsData)
    [q.IsLocallyFreeData] [∀ i, Unique (q.generators i).I] :
    ∃! L : A ⟶ ofClosedAnalytic (strictTransform n π W)
        (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
          hπ hWa),
      L ≫ strictTransformMorphism hπ hWa = F :=
  exists_unique_source_factorization_of_module_invertible hπ hWa A F
    (moduleInvertible_original_nested_ideal_of_locallyFreeData F.hom.left q)

end

end Hironaka.Analytic.Unibranch.EmbeddedBlowupUniversalSheaf
