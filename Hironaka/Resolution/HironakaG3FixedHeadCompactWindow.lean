import Hironaka.Resolution.HironakaG3FixedContactHeadClass
import Hironaka.Resolution.HironakaG3RelativelyCompactStoppedContact
import Hironaka.Resolution.HironakaG3RChartOfMember
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3FixedHeadCompactWindow
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaActualNativeSectionFiniteHistory HironakaDisjointNativeReferenceWindow HironakaDisjointNativeOpenLift
  HironakaDisjointFiniteControlledHistory HironakaG3RStoppedOverlap HironakaG3RBoundaryEmbedded
  HironakaG3BoundaryContainedAnalyticTrace HironakaG3BoundaryContainedOriginalInputs
  HironakaG3BoundaryContainedAmbientGlobalLift HironakaG3StoppedBoundaryAmbientBridge HironakaG3RTowerClass
  HironakaG3FixedContactHeadClass HironakaG3RelativelyCompactStoppedContact
  HironakaG3LocalStoppedCoupledProducer HironakaG3RChartOfMember

/-- Every relatively compact ambient window admits one actual fixed-contact head. -/
theorem fixed_head_over_relatively_compact_window {d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    {X : CMfd.{0} (d+t)} (N : Set X) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N)
    {r : ℕ} (hr : r < d) (hpure : W ⊆ closure (regularLocus (n := d+t) W r))
    (hAvoid : W ⊆ closure (W \ ⋃ H ∈ B, H))
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ (Y : CMfd.{0} (d+t)) (A : BlowupTower (CMfd.of (n := d+t) U) Y),
      fixedContactHead N hNc hN B W r U Y A := by
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
  obtain ⟨hJ,hNorm,hTrace,hDom,hEO,hPure,hDense⟩ :=
    original_contained_input_data hd N hNc hN B hB hTrans V hVa (by rwa [hImage]) hr hVp hVA
  rw [hImage] at hJ hNorm hTrace
  let O := bdryOpen V r (B.map ((Subtype.val : N → X) ⁻¹' ·))
  obtain ⟨Q,S,hStop⟩ := stopped_native_history_over_relatively_compact_window N hNc hN _ hDom O U K hK hUK
  obtain ⟨R,T,Y,A,η,hdomT,hT,hA,hC,hStopped⟩ :=
    local_coupled_of_stopped ht N hNc hN B hB hTrans _ hJ hNorm V hTrace hDom O U S hStop
  exact ⟨Y,A,R,T,η,hdomT,hT,hA,hC,hStopped⟩

/-- Every relatively compact ambient window is a chart of any map glued
from the actual fixed-contact head class. -/
theorem fixed_head_chart_over_relatively_compact_window {d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    {X : CMfd.{0} (d+t)} (N : Set X) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (B : List (Set X)) (hB : IsSNCDivisor (d+t) B) (hTrans : IsTransverse (d+t) N B)
    (W : Set X) (hWa : IsComplexAnalyticSubset (n := d+t) W) (hWN : W ⊆ N)
    {r : ℕ} (hr : r < d) (hpure : W ⊆ closure (regularLocus (n := d+t) W r))
    (hAvoid : W ⊆ closure (W \ ⋃ H ∈ B, H)) {Z : CMfd.{0} (d+t)} {P : Z → X}
    (hG : IsGluedFrom (fixedContactHead N hNc hN B W r) Z P)
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ c : TowerChart (fixedContactHead N hNc hN B W r) Z P, c.U = U := by
  obtain ⟨Y,A,hA⟩ := fixed_head_over_relatively_compact_window hd ht N hNc hN B hB hTrans
    W hWa hWN hr hpure hAvoid U K hK hUK
  have hcmp := fixedContactHead_comparisons hd N hNc hN B hB hTrans W hWa hWN hr hpure hAvoid
  exact ⟨chartOfMember hcmp A hA hG.2.2.2 hG.1.continuous,rfl⟩
end
end Hironaka.HironakaG3FixedHeadCompactWindow
