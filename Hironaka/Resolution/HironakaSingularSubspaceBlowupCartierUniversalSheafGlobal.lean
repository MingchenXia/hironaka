import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalIdealStalk
import Hironaka.Resolution.HironakaSingularLocallyFreeStalk
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalGlobal
import Mathlib.CategoryTheory.Sites.LeftExact

/-!
# Original singular-source blowup factorization from standard rank-one sheaf data

The input is native LocalGeneratorsData for the SAME actual canonical ideal
sheaf, its native IsLocallyFreeData, and singleton ORIGINAL generator indices.
The SAME original entire nested ideal is proved invertible internally; the
established ORIGINAL-source global actual factorization then applies.

Blueprint: `hironaka-singular-subspace-blowup-cartier-universal-sheaf-global.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaSingularSubspaceBlowupCartierUniversalSheafGlobal

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaReducedComplexAnalyticSpaces HironakaSingularSubspaceBlowupLift
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
  HironakaSingularSubspaceBlowupCartierUniversalIdealStalk
  HironakaSingularLocallyFreeStalk HironakaSingularSubspaceBlowupCartierUniversalGlobal

noncomputable section

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

private instance originalOverHasWeakSheafify (X : LocallyRingedSpace.{0}) (U : Opens X.toTopCat) :
    HasWeakSheafify ((Opens.grothendieckTopology X.toTopCat).over U) AddCommGrpCat.{0} :=
  CategoryTheory.sheafToPresheaf_isRightAdjoint
    ((Opens.grothendieckTopology X.toTopCat).over U) AddCommGrpCat.{0}

/-- Standard native local-free rank-one data on the SAME canonical actual
ideal sheaf imply standard invertibility of the ENTIRE original nested ideal. -/
theorem moduleInvertible_original_nested_ideal_of_locallyFreeData
    {X : LocallyRingedSpace} (F : X ⟶ actualSubspaceLocallyRingedSpace (n := n) W)
    (q : (actualPulledCentreIdealModule (F ≫ actualSubspaceInclusion (n := n) W) C).LocalGeneratorsData)
    [q.IsLocallyFreeData] [∀ i, Unique (q.generators i).I] (x : X) :
    Module.Invertible (X.presheaf.stalk x).carrier
      (Ideal.map (F.stalkMap x).hom
        (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F.base x)).hom
          (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) (F.base x).val))) := by
  have hM := stalkInvertible_of_locallyFreeData X.toSheafedSpace.sheaf q x
  have hH := moduleInvertible_actual_pulled_ideal_of_module_stalk
    (F ≫ actualSubspaceInclusion (n := n) W) C x hM
  have heq := (actualPulledCentreStalkInclusion_range
    (F ≫ actualSubspaceInclusion (n := n) W) C x).symm.trans
      (actualPulledCentreStalkInclusion_range_subspace F C x)
  rw [heq] at hH
  exact hH

/-- The ORIGINAL arbitrary reduced source admits a unique WHOLE actual
factorization from native locally-free rank-one data on its SAME canonical
pulled-centre ideal sheaf. No desired stalk dictionary or local lifts are input. -/
theorem exists_unique_intrinsic_factorization_of_locallyFreeData
    (hπ : IsBlowupAlong n C π) (hW : IsClosed W)
    (A : ReducedComplexAnalyticSpace)
    (F : A.obj.left ⟶ actualSubspaceLocallyRingedSpace (n := n) W)
    (hF : F ≫ subspacePointMap (n := n) W = A.obj.hom)
    (q : (actualPulledCentreIdealModule (F ≫ actualSubspaceInclusion (n := n) W) C).LocalGeneratorsData)
    [q.IsLocallyFreeData] [∀ i, Unique (q.generators i).I] :
    ∃! L : A.obj ⟶ Over.mk (subspacePointMap (n := n) (strictTransform n π W)),
      L.left ≫ strictTransformProjection hπ hW = F :=
  exists_unique_intrinsic_factorization_of_module_invertible hπ hW A F hF
    (moduleInvertible_original_nested_ideal_of_locallyFreeData F q)

end

end Hironaka.HironakaSingularSubspaceBlowupCartierUniversalSheafGlobal
