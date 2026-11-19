import Hironaka.Resolution.HironakaG3IndexedResidualFullWindow
import Hironaka.Resolution.HironakaG3FixedContactHeadGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedResidualFullHeadGeometry
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact
  HironakaG3OrderedFiniteWindows HironakaG3FixedContactHeadClass HironakaG3FixedContactHeadGeometry
  HironakaDisjointFiniteControlledHistory
  HironakaG3IndexedResidualFullWindow

/-- The actual head has full SNC and normal-crossing geometry for its finite
residual window followed by every globally containing label. -/
theorem indexed_residual_full_head_geometry {d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    {X : CMfd.{0} (d+t)} {ι : Type*} [LinearOrder ι] (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := d+t) C) (hD : IsLocallyFiniteSNCDivisor (d+t) D)
    {r : ℕ} (hr : r < d) (hpure : C ⊆ closure (regularLocus (n := d+t) C r))
    (hNc : IsClosed (canonicalContact C D hC.nonempty hD.1))
    (hN : ∀ x ∈ canonicalContact C D hC.nonempty hD.1,
      RegularAtDim (n := d+t) (canonicalContact C D hC.nonempty hD.1) x d)
    (R : Finset ι) (hDis : Disjoint (containingLabels C D hC.nonempty hD.1) R)
    (U : Opens X) (Y : CMfd.{0} (d+t)) (A : BlowupTower (CMfd.of (n := d+t) U) Y)
    (hHead : fixedContactHead (canonicalContact C D hC.nonempty hD.1) hNc hN ((R.sort (· ≤ ·)).map D) C r U Y A) :
    let S := containingLabels C D hC.nonempty hD.1
    let B := (R.sort (· ≤ ·)).map D
    let E := B ++ (S.sort (· ≤ ·)).map D
    let Jx := GermIdeal.pullback (m := d+t) (Subtype.val : U → X) (vanishingIdeal (n := d+t) C)
    let Ex := E.map ((Subtype.val : U → X) ⁻¹' ·)
    let Cx := (Subtype.val : U → X) ⁻¹' C
    IsGeoTestTower (fullMarked Ex Jx) A ∧
      IsSNCDivisor (d+t) (geoTransformAlong (fullMarked Ex Jx) A).E ∧
      IsClosedSubmanifold (d+t) (strictTransform (d+t) A.proj Cx) ∧
      (∀ y ∈ strictTransform (d+t) A.proj Cx,
        RegularAtDim (n := d+t) (strictTransform (d+t) A.proj Cx) y r) ∧
      HasNormalCrossings (d+t) (strictTransform (d+t) A.proj Cx)
        (geoTransformAlong (fullMarked Ex Jx) A).E := by
  let S := containingLabels C D hC.nonempty hD.1
  let N := canonicalContact C D hC.nonempty hD.1
  let B := (R.sort (· ≤ ·)).map D
  let E := B ++ (S.sort (· ≤ ·)).map D
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
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    have hiR : i ∈ R := by simpa [B] using hi
    have hiS : i ∉ S := fun hiS => (Finset.disjoint_left.mp hDis) hiS hiR
    exact hxOut (mem_iUnion.mpr ⟨⟨i,hiS⟩,hxH⟩)
  have hFull := residual_then_containing_full_window C D hC.nonempty hD R hDis
  exact fixedContactHead_full_boundary_geometry hd ht N hNc hN B hB hTrans E hFull.1 hFull.2.1 hFull.2.2
    C hC.analytic hCN hr hpure hAvoid U Y A hHead
end
end Hironaka.HironakaG3IndexedResidualFullHeadGeometry
