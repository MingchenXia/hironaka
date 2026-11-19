import Hironaka.Resolution.HironakaG3FixedContactHeadClass
import Hironaka.Resolution.HironakaG3StoppedCoupledNonerasure
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3FixedHeadNonerasure
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaActualNativeSectionFiniteHistory HironakaDisjointNativeReferenceWindow HironakaDisjointNativeOpenLift
  HironakaDisjointFiniteControlledHistory HironakaG3RStoppedOverlap HironakaG3RBoundaryEmbedded
  HironakaG3BoundaryContainedAnalyticTrace HironakaG3FixedContactHeadClass HironakaG3StoppedCoupledNonerasure

/-- Every actual fixed-contact head preserves its entire original target
under the projection of its conventional strict transform. -/
theorem fixed_head_nonerasure {d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    {X : CMfd.{0} (d+t)}
    (N : Set X) (hNc : IsClosed N) (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N)
    {r : ℕ} (hr : r < d) (hpure : W ⊆ closure (regularLocus (n := d+t) W r))
    (hAvoid : W ⊆ closure (W \ ⋃ H ∈ B, H))
    (U : Opens X) (Y : CMfd.{0} (d+t)) (A : BlowupTower (CMfd.of (n := d+t) U) Y)
    (hHead : fixedContactHead N hNc hN B W r U Y A) :
    A.proj '' strictTransform (d+t) A.proj ((Subtype.val : U → X) ⁻¹' W) =
      (Subtype.val : U → X) ⁻¹' W := by
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
  obtain ⟨R,T,η,hM,hT,hTest,hC,hStop⟩ := hHead
  have hn := actual_stopped_coupled_nonerasure hd ht N hNc hN B hB hTrans
    (vanishingIdeal (n := d+t) W) V hVa hr hVp hVA U T A η hC hStop
  simpa only [hImage] using hn
end
end Hironaka.HironakaG3FixedHeadNonerasure
