import Hironaka.Resolution.HironakaG8NativeHomogeneousRank
import Hironaka.Resolution.HironakaG8CofinalWeakRankEndpoint

/-! The intrinsic original TEST endpoint for homogeneous native windows. -/
set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8NativeHomogeneousEndpoint
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaG3RTowerClass
  G3UniversePhysicalClassComparisons HironakaG8CofinalOccupiedAncestry
  HironakaG8PhysicalChartOccupiedLifts HironakaG8SpatialCofinalPrecedence
  HironakaG8LabelledNativeHistory HironakaG8NativeHomogeneousRank
  HironakaG8CofinalWeakRankEndpoint HironakaEmbeddedBoundary
  HironakaLocallyFiniteResolutionSequence ResolutionInvariantSeq
  HironakaActualLocallyFiniteHistoryLimit HironakaActualLocallyFiniteHistoryOverlap
  HironakaActualLocallyFiniteLimitStrictTransforms HironakaActualLimitCarrierGeometry
  HironakaG4CompactComponentLimit HironakaAdmissibleSequence
  HomogenizedGlueingTower NormalCrossings SimultaneousNormalCrossings

attribute [local instance] limitChartedSpace
local instance {n : ℕ} {X : CMfd.{0} n} (s : GrowingSeq X)
    (hLF : LocallyFinite (centreImage s)) :
    IsComplexManifold n (actualHistoryGluedSpace s hLF) := limitSpace_isComplexManifold s hLF

variable {n : ℕ} {X Z : CMfd.{0} n} {K : LocalTowerClass X} {P : Z→X}
  {c : ℕ→TowerChart K Z P} {ι : Type*} {W : Set X}

theorem intrinsic_endpoint_of_homogeneous_native_windows (hn : 0<n)
    (hW : IsComplexAnalyticSubset (n := n) W)
    (E : CofinalEvents c ι) (cmp : HasPhysicalComparisons K)
    (hMono : Monotone fun i => (c i).U)
    (hLift : ∀ {i j} (h : i≤j) p,
      E.lift h p=chartOccupiedLift cmp (c i) (c j) (hMono h) p)
    (hCover : ∀ x : X, ∃ i, x∈(c i).U)
    (hOccurs : ∀ a, ∃ (i : ℕ) (p : {k // Occupied (c i).T k}), E.event i p=a)
    (hNative : ∀ i, ∃ L : List (ℕ→ℕ),
      LabelledNativeTower n ((Subtype.val : (c i).U→X) ⁻¹' W) [] univ (c i).T L)
    (hTransitive : ∀ i (p q : (c i).U),
      p∈singularSet (n := n) ((Subtype.val : (c i).U→X) ⁻¹' W) →
      q∈singularSet (n := n) ((Subtype.val : (c i).U→X) ⁻¹' W) →
      ∃ φ : (c i).U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (c i).U,
        φ ⁻¹' ((Subtype.val : (c i).U→X) ⁻¹' W)=((Subtype.val : (c i).U→X) ⁻¹' W) ∧
        φ p=q) :
    let M : MarkedIdeal n X := ⟨univ,[],vanishingIdeal (n := n) W,1⟩
    ∃ s : GrowingSeq X, ∃ hLF : LocallyFinite (centreImage s),
      (∀ k, IsGeoTestTower M (s.stage k).2) ∧
      (∀ k, StageCentres (fun T C => C ⊆ singularSet (n := n)
        (strictTransform n T.proj W)) (s.stage k).2) ∧
      IsClosedSubmanifold n (strictTransform n (gluedProjection s hLF) W) ∧
      limitStrictTransform s hLF W=strictTransform n (gluedProjection s hLF) W ∧
      IsProperMap (gluedProjection s hLF) ∧
      IsIsomorphismOver n (gluedProjection s hLF) (singularSet (n := n) W)ᶜ := by
  classical
  dsimp only
  obtain ⟨_hFinite,_i₀,_rank,_hInj,_hBound,_hBefore,hHeight⟩ :=
    finite_serial_rank_of_homogeneous_native_windows hn E cmp hMono hLift hCover
      hOccurs hNative hTransitive
  let M : MarkedIdeal n X := ⟨univ,[],vanishingIdeal (n := n) W,1⟩
  have hM : M.IsWellFormed :=
    ⟨isClosedSubmanifold_univ,CartanIrreducible.cartanCoherence W hW,
      isSNCDivisor_nil,isTransverse_univ_of_isSNCDivisor isSNCDivisor_nil⟩
  choose labels hLabels using hNative
  have hTest (i : ℕ) :
      IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U→X) M) (c i).T := by
    change IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : (c i).U→X)
      (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X)) (c i).T
    rw [pullback_val_mk_vanishingIdeal]
    exact (hLabels i).test_and_singular.1
  have hSing (i : ℕ) : StageCentres (fun T C => C ⊆ singularSet (n := n)
      (strictTransform n T.proj ((Subtype.val : (c i).U→X) ⁻¹' W))) (c i).T :=
    (hLabels i).test_and_singular.2
  have hSmooth (i : ℕ) : IsClosedSubmanifold n
      (strictTransform n (c i).T.proj ((Subtype.val : (c i).U→X) ⁻¹' W)) :=
    (hLabels i).target_smooth
  exact intrinsic_endpoint_of_cofinal_bounded_spatial_height hCover E cmp hMono hLift
    hOccurs hHeight M hM rfl hTest W hW hSing hSmooth

end
end Hironaka.HironakaG8NativeHomogeneousEndpoint
