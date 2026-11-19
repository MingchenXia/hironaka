import Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup
import Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowupLanding
import Hironaka.Analytic.Unibranch.OriginalClosedSubspaceFactorization
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalSheafGlobal

/-!
# Full ORIGINAL-source lifting to the SAME geometric blowup, without target density

The old full lift is internally constructed, then its continuous ambient map
lands in the literal geometric carrier by derived source-good-locus density.
Actual reduced closed-subspace factorization upgrades this landing to a full
original morphism. The original target and ENTIRE pulled ideal are unchanged.
Blueprint FIRST: `embedded-geometric-blowup-universal.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowupUniversal

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaSingularSubspaceBlowupLift HironakaResolutionSpaceComplex
  HironakaSingularSubspaceBlowupCartierUniversalIdealSheaf
  HironakaSingularSubspaceBlowupCartierUniversalSheafGlobal
  BlowupStrictSubmanifold SourceReducedComplexSpace EmbeddedBlowup EmbeddedGeometricBlowup

noncomputable section

variable {n : ℕ} {M Y : Type} [TopologicalSpace M] [TopologicalSpace Y]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]
  {C W : Set M} {π : Y → M}

private theorem geometricAnalytic (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    IsComplexAnalyticSubset (n := n) (geoStrictTransform π C W) := by
  have hC := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hπ.1
  simpa only [geoStrictTransform, preimage_sdiff] using
    ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hW)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hπ.contMDiff hC)

private def geometricToStrict (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    geometricSource hπ hW ⟶ ofClosedAnalytic (strictTransform n π W)
      (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hW) :=
  OriginalClosedSubspaceFactorization.inclusion (geometricAnalytic hπ hW)
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hW)
    (BlowupStrictIdeal.geoStrictTransform_subset_strictTransform hπ W)

private instance geometricToStrict_left_mono (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) : Mono (geometricToStrict hπ hW).hom.left := by
  change Mono (OriginalClosedSubspaceFactorization.inclusion (geometricAnalytic hπ hW)
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hW)
    (BlowupStrictIdeal.geoStrictTransform_subset_strictTransform hπ W)).hom.left
  infer_instance

private theorem geometricToStrict_projection (hπ : IsBlowupAlong n C π)
    (hW : IsComplexAnalyticSubset (n := n) W) :
    geometricToStrict hπ hW ≫ strictTransformMorphism hπ hW = geometricProjectionMorphism hπ hW := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change actualSubspaceMap (f := (id : Y → Y)) contMDiff_id
      (fun _ hy => BlowupStrictIdeal.geoStrictTransform_subset_strictTransform hπ W hy) ≫
    strictTransformProjection hπ hW.isClosed = geometricProjection hπ hW.isClosed
  unfold strictTransformProjection geometricProjection
  rw [← actualSubspaceMap_comp]

/-- Standard invertibility of the SAME ENTIRE original pulled centre ideal
internally constructs the UNIQUE FULL original lift to the literal GEO source.
No target density, source SC, incoming lift or landing certificate is assumed. -/
theorem exists_unique_source_factorization_of_module_invertible
    (hπ : IsBlowupAlong n C π) (hW : IsComplexAnalyticSubset (n := n) W)
    (A : SourceReducedComplexSpace) (F : A ⟶ ofClosedAnalytic W hW)
    (hInv : ∀ x : A.obj.left,
      Module.Invertible (A.obj.left.presheaf.stalk x).carrier
        (Ideal.map (F.hom.left.stalkMap x).hom
          (Ideal.map ((actualSubspaceInclusion (n := n) W).stalkMap (F.hom.left.base x)).hom
            (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C)
              (F.hom.left.base x).val)))) :
    ∃! L : A ⟶ geometricSource hπ hW, L ≫ geometricProjectionMorphism hπ hW = F := by
  obtain ⟨L₀, hL₀, huniq⟩ :=
    EmbeddedBlowupUniversal.exists_unique_source_factorization_of_module_invertible hπ hW A F hInv
  have hL₀raw : L₀.hom.left ≫ strictTransformProjection hπ hW.isClosed = F.hom.left :=
    congrArg (fun H : A ⟶ ofClosedAnalytic W hW => H.hom.left) hL₀
  let k : A.obj.left → Y := fun a => (L₀.hom.left.base a).val
  have hk : Continuous k := continuous_subtype_val.comp L₀.hom.left.base.hom.continuous
  have hcomm (a : A.obj.left) : π (k a) = (F.hom.left.base a).val :=
    congrArg (fun H => (H.base a).val) hL₀raw
  have hland (a : A.obj.left) : (L₀.hom.left.base a).val ∈ geoStrictTransform π C W :=
    EmbeddedGeometricBlowupLanding.continuous_lift_lands_geometricTransform hπ hW A F hInv k hk hcomm a
  obtain ⟨L, hL, _⟩ := OriginalClosedSubspaceFactorization.exists_unique_factorization
    (geometricAnalytic hπ hW)
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hπ hW)
    (BlowupStrictIdeal.geoStrictTransform_subset_strictTransform hπ W) A L₀ hland
  have hLi : L ≫ geometricToStrict hπ hW = L₀ := hL
  refine ⟨L, ?_, ?_⟩
  · calc
      L ≫ geometricProjectionMorphism hπ hW =
          L ≫ (geometricToStrict hπ hW ≫ strictTransformMorphism hπ hW) :=
        congrArg (fun H => L ≫ H) (geometricToStrict_projection hπ hW).symm
      _ = (L ≫ geometricToStrict hπ hW) ≫ strictTransformMorphism hπ hW :=
        (Category.assoc _ _ _).symm
      _ = F := by rw [hLi, hL₀]
  · intro L' hL'
    have hL'i : L' ≫ geometricToStrict hπ hW = L₀ := huniq _ (by
      change (L' ≫ geometricToStrict hπ hW) ≫ strictTransformMorphism hπ hW = F
      rw [Category.assoc, geometricToStrict_projection, hL'])
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono (geometricToStrict hπ hW).hom.left).mp
    exact congrArg (fun H => H.hom.left) (hL'i.trans hLi.symm)

/-- Native singleton locally-free data on the SAME canonical pulled ideal
derive the preceding ENTIRE ideal-stalk input, retaining the SAME original p. -/
theorem exists_unique_source_factorization_of_locallyFreeData
    (hπ : IsBlowupAlong n C π) (hW : IsComplexAnalyticSubset (n := n) W)
    (A : SourceReducedComplexSpace) (F : A ⟶ ofClosedAnalytic W hW)
    (q : (actualPulledCentreIdealModule
      (F.hom.left ≫ actualSubspaceInclusion (n := n) W) C).LocalGeneratorsData)
    [q.IsLocallyFreeData] [∀ i, Unique (q.generators i).I] :
    ∃! L : A ⟶ geometricSource hπ hW, L ≫ geometricProjectionMorphism hπ hW = F :=
  exists_unique_source_factorization_of_module_invertible hπ hW A F
    (moduleInvertible_original_nested_ideal_of_locallyFreeData F.hom.left q)

end

end Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowupUniversal
