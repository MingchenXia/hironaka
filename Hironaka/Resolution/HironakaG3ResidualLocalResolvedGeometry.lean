import Hironaka.Resolution.HironakaG3IndexedResidualHeadNonerasure
import Hironaka.Resolution.HironakaG3IndexedResidualFullHeadGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3ResidualLocalResolvedGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact
  HironakaG3OrderedFiniteWindows HironakaG3IndexedResidualFixedHeadClass HironakaG3FixedHeadNonerasure
  HironakaG3IndexedResidualFullHeadGeometry

theorem indexed_residual_member_resolved_geometry {d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    {X Y : CMfd.{0} (d+t)} {κ : Type*} [LinearOrder κ] (C : Set X) (D : κ → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := d+t) C) (hD : IsLocallyFiniteSNCDivisor (d+t) D)
    {r : ℕ} (hr : r < d) (hpure : C ⊆ closure (regularLocus (n := d+t) C r))
    (hNc : IsClosed (canonicalContact C D hC.nonempty hD.1))
    (hN : ∀ x ∈ canonicalContact C D hC.nonempty hD.1,
      RegularAtDim (n := d+t) (canonicalContact C D hC.nonempty hD.1) x d)
    (U : Opens X) (T : BlowupTower (CMfd.of (n := d+t) U) Y)
    (hT : residualFixedHead (canonicalContact C D hC.nonempty hD.1) hNc hN C r D
      (containingLabels C D hC.nonempty hD.1) U Y T) :
    T.proj '' strictTransform (d+t) T.proj ((Subtype.val : U → X) ⁻¹' C) = (Subtype.val : U → X) ⁻¹' C ∧
    ∀ y ∈ strictTransform (d+t) T.proj ((Subtype.val : U → X) ⁻¹' C),
      RegularAtDim (n := d+t) (strictTransform (d+t) T.proj ((Subtype.val : U → X) ⁻¹' C)) y r := by
  obtain ⟨R,hDis,_hVis,hHead⟩ := hT
  let S := containingLabels C D hC.nonempty hD.1
  let N := canonicalContact C D hC.nonempty hD.1
  let B := (R.sort (· ≤ ·)).map D
  have hCN : C ⊆ N := (canonicalContact_geometry C D hC hD).1
  have hB : IsSNCDivisor (d+t) B := sorted_boundary_snc D hD R
  have hTrans : IsTransverse (d+t) N B := isTransverse_residual_window C D hC hD R hDis
  have hAvoid : C ⊆ closure (C \ ⋃ H ∈ B, H) := by
    apply (dense_off_residual_family C D hC hD).trans
    apply closure_mono
    rintro x ⟨hxC,hxOut⟩
    refine ⟨hxC,?_⟩
    intro hxB
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxB
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hH
    have hjR : j ∈ R := by simpa [B] using hj
    have hjS : j ∉ S := fun hjS => (Finset.disjoint_left.mp hDis) hjS hjR
    exact hxOut (mem_iUnion.mpr ⟨⟨j,hjS⟩,hxH⟩)
  have hProj := fixed_head_nonerasure hd ht N hNc hN B hB hTrans C hC.analytic hCN hr hpure hAvoid U Y T hHead
  have hg := indexed_residual_full_head_geometry hd ht C D hC hD hr hpure hNc hN R hDis U Y T hHead
  exact ⟨hProj,hg.2.2.2.1⟩
end
end Hironaka.HironakaG3ResidualLocalResolvedGeometry
