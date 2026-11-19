import Hironaka.Resolution.HironakaG3IndexedResidualFixedHeadClass
import Hironaka.Resolution.HironakaG3FixedHeadGlobalGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Function TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG3IndexedResidualHeadNonerasure
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.BlowupSequences BlowupTowers NormalCrossings SubmanifoldChartedSpace
  HironakaActualLocallyFiniteBoundary HironakaG3RTowerClass HironakaG3RPureEmbedded HironakaG3GluedClassFootprint
  HironakaG3FixedContactHeadClass HironakaG3FixedHeadTargetFootprint HironakaG3FixedHeadNonerasure
  HironakaG3IndexedContainingBoundary HironakaG3IndexedCanonicalContact HironakaG3OrderedFiniteWindows
  HironakaG3IndexedResidualFixedHeadClass

/-- A map glued from indexed residual heads is an isomorphism outside the target. -/
theorem glued_indexed_residual_head_isomorphism_off_target {d t : ℕ} {X Z : CMfd.{0} (d+t)}
    {ι : Type*} [LinearOrder ι] (N : Set X) (hNc : IsClosed N)
    (hN : ∀ x ∈ N, RegularAtDim (n := d+t) N x d)
    (C : Set X) (hCa : IsComplexAnalyticSubset (n := d+t) C) (r : ℕ) (D : ι → Set X) (S : Finset ι)
    {P : Z → X} (h : IsGluedFrom (residualFixedHead N hNc hN C r D S) Z P) :
    IsIsomorphismOver (d+t) P Cᶜ := by
  apply glued_isomorphism_over_compl C hCa.isClosed ?_ h
  intro U Y A hHead
  obtain ⟨R,_hDis,_hVis,hR⟩ := hHead
  exact fixed_head_centres_over_target N hNc hN ((R.sort (· ≤ ·)).map D) C hCa r U Y A hR

/-- The conventional strict transform under the same glued map projects onto
all of the original irreducible target. -/
theorem glued_indexed_residual_head_nonerasure {d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    {X Z : CMfd.{0} (d+t)} {ι : Type*} [LinearOrder ι]
    (C : Set X) (D : ι → Set X)
    (hC : IsComplexAnalyticallyIrreducible (n := d+t) C) (hD : IsLocallyFiniteSNCDivisor (d+t) D)
    {r : ℕ} (hr : r < d) (hpure : C ⊆ closure (regularLocus (n := d+t) C r))
    (hNc : IsClosed (canonicalContact C D hC.nonempty hD.1))
    (hN : ∀ x ∈ canonicalContact C D hC.nonempty hD.1,
      RegularAtDim (n := d+t) (canonicalContact C D hC.nonempty hD.1) x d)
    {P : Z → X} (h : IsGluedFrom (residualFixedHead (canonicalContact C D hC.nonempty hD.1) hNc hN C r D
      (containingLabels C D hC.nonempty hD.1)) Z P) :
    P '' strictTransform (d+t) P C = C := by
  let S := containingLabels C D hC.nonempty hD.1
  let N := canonicalContact C D hC.nonempty hD.1
  have hCN : C ⊆ N := (canonicalContact_geometry C D hC hD).1
  have hAvoidR (R : Finset ι) (hDis : Disjoint S R) :
      C ⊆ closure (C \ ⋃ H ∈ (R.sort (· ≤ ·)).map D, H) := by
    apply (dense_off_residual_family C D hC hD).trans
    apply closure_mono
    rintro x ⟨hxC,hxOut⟩
    refine ⟨hxC,?_⟩
    intro hxB
    obtain ⟨H,hH,hxH⟩ := mem_iUnion₂.mp hxB
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hH
    have hiR : i ∈ R := by simpa using hi
    have hiS : i ∉ S := fun hiS => (Finset.disjoint_left.mp hDis) hiS hiR
    exact hxOut (mem_iUnion.mpr ⟨⟨i,hiS⟩,hxH⟩)
  apply Set.Subset.antisymm
  · rintro x ⟨z,hz,rfl⟩
    exact HironakaAdmissibleCalculus.strictTransform_subset_preimage h.1.continuous hC.analytic.isClosed hz
  · intro x hx
    obtain ⟨c,hxU⟩ := h.2.2.2 x
    let xU : c.U := ⟨x,hxU⟩
    have hp : xU ∈ (Subtype.val : c.U → X) ⁻¹' C := hx
    obtain ⟨R,hDis,_hVis,hHead⟩ := c.mem
    let B := (R.sort (· ≤ ·)).map D
    have hB : IsSNCDivisor (d+t) B := sorted_boundary_snc D hD R
    have hTrans : IsTransverse (d+t) N B := isTransverse_residual_window C D hC hD R hDis
    have hProjection := fixed_head_nonerasure hd ht N hNc hN B hB hTrans C hC.analytic hCN
      hr hpure (hAvoidR R hDis) c.U c.Y c.T hHead
    have hm : xU ∈ c.T.proj '' strictTransform (d+t) c.T.proj ((Subtype.val : c.U → X) ⁻¹' C) := by
      rw [hProjection]
      exact hp
    obtain ⟨y,hy,hyProj⟩ := hm
    refine ⟨chartIncl c y,?_,?_⟩
    · rw [strictTransform_chart c h.1 C] at hy
      exact hy
    · have hh := proj_chartIncl c y
      rw [hyProj] at hh
      exact hh
end
end Hironaka.HironakaG3IndexedResidualHeadNonerasure
