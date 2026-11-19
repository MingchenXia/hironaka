import Hironaka.Resolution.HironakaG3FixedContactHeadClass
import Hironaka.Resolution.HironakaG3StoppedContainedBoundary
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3FixedContactHeadGeometry
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaActualNativeSectionFiniteHistory HironakaDisjointNativeReferenceWindow HironakaDisjointNativeOpenLift
  HironakaDisjointFiniteControlledHistory HironakaG3RStoppedOverlap HironakaG3RBoundaryEmbedded
  HironakaG3BoundaryContainedAnalyticTrace HironakaG3BoundaryContainedOriginalInputs
  HironakaG3FixedContactHeadClass HironakaG3StoppedContainedBoundary
open ResolutionInvariantSpec (IsInvDomain)

/-- Every actual fixed-contact head has full original-boundary testhood and
endpoint geometry on its very same ambient tower. -/
theorem fixedContactHead_full_boundary_geometry {d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (E : List (Set X)) (hE : IsSNCDivisor (d+t) E) (hBsub : B.Sublist E)
    (hOmitted : ∀ H ∈ E, H ∉ B → N ⊆ H)
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N)
    {r : ℕ} (hr : r < d) (hpure : W ⊆ closure (regularLocus (n := d+t) W r))
    (hAvoid : W ⊆ closure (W \ ⋃ H ∈ B, H))
    (U : Opens X) (Y : CMfd.{0} (d+t)) (A : BlowupTower (CMfd.of (n := d+t) U) Y)
    (hHead : fixedContactHead N hNc hN B W r U Y A) :
    let Jx := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) (vanishingIdeal (n := d+t) W)
    let Ex := E.map ((Subtype.val : U → X) ⁻¹' ·)
    let Wx := (Subtype.val : U → X) ⁻¹' W
    IsGeoTestTower (fullMarked Ex Jx) A ∧
      IsSNCDivisor (d+t) (geoTransformAlong (fullMarked Ex Jx) A).E ∧
      IsClosedSubmanifold (d+t) (strictTransform (d+t) A.proj Wx) ∧
      (∀ y ∈ strictTransform (d+t) A.proj Wx,
        RegularAtDim (n := d+t) (strictTransform (d+t) A.proj Wx) y r) ∧
      HasNormalCrossings (d+t) (strictTransform (d+t) A.proj Wx)
        (geoTransformAlong (fullMarked Ex Jx) A).E := by
  let := chartedSpace (Nat.le_add_right d t) hN
  let := isComplexManifold_chartedSpace (Nat.le_add_right d t) hN
  let V : Set (nativeManifold (Nat.le_add_right d t) N hN) := (Subtype.val : N → X) ⁻¹' W
  have hImage : (Subtype.val : N → X) '' V = W := by
    ext y
    constructor
    · rintro ⟨p,hp,rfl⟩; exact hp
    · intro hy; exact ⟨⟨y,hWN hy⟩,hy,rfl⟩
  have hVa := native_analytic_of_ambient_image N hN V (by rwa [hImage])
  have hVp := native_pure_of_ambient_image N hNc hN V r (by rwa [hImage])
  have hVA := native_dense_avoid_of_ambient_image N hNc hN V B (by rwa [hImage])
  have hInputs := original_contained_input_data hd N hNc hN B hB hTrans V hVa (by rwa [hImage]) hr hVp hVA
  dsimp only at hInputs
  obtain ⟨hJ,hNorm,hTrace,hDom,hEO,hPure,hDense⟩ := hInputs
  rw [hImage] at hJ hTrace
  obtain ⟨R,T,η,hM,hT,hTest,hC,hStop⟩ := hHead
  have hg := actual_stopped_full_boundary_geometry hd ht N hNc hN B hB hTrans E hE hBsub hOmitted
    (vanishingIdeal (n := d+t) W) hJ V hVa hTrace hr hVp hVA U T A η hC hStop hTest
  simpa only [hImage] using hg
end
end Hironaka.HironakaG3FixedContactHeadGeometry
