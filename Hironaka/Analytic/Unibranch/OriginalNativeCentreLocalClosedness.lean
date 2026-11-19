import Hironaka.Analytic.Unibranch.HironakaG11CompatibleAnalyticCover
import Hironaka.Analytic.Unibranch.OriginalNativePrecompactNeighbourhood

/-! Derive closedness near a compact shadow from ACTUAL compatible native
local smooth centres, without a compact cover of the WHOLE support.
Blueprint FIRST: original-native-centre-local-closedness.tex.
Supporting geometry for the ordinary derived invariant-centre construction. -/
set_option autoImplicit false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeCentreLocalClosedness
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11CompatibleAnalyticCover

variable {X : SourceReducedComplexSpace} {ι : Type*} (F : LocalSmoothCentres X ι)

def coveredOpen : Opens X.obj.left :=
  ⟨⋃ i, range (F.windowMap i).hom.left.base,
    isOpen_iUnion (fun i => (F.windowMap_isOpenImmersion i).base_open.isOpen_range)⟩

def neighbourhood (D : Set X.obj.left) (hD : IsClosed D) : Opens X.obj.left :=
  ⟨(coveredOpen F : Set X.obj.left) ∪ Dᶜ, (coveredOpen F).isOpen.union hD.isOpen_compl⟩

theorem compact_subset_neighbourhood (D : Set X.obj.left) (hD : IsClosed D)
    {K : Set X.obj.left} (hcov : K ∩ D ⊆ coveredOpen F) : K ⊆ neighbourhood F D hD := by
  intro x hx
  by_cases hxD : x ∈ D
  · exact Or.inl (hcov ⟨hx, hxD⟩)
  · exact Or.inr hxD

/-- WHOLE local trace compatibility derives relative closedness, including all window boundaries. -/
theorem support_trace_closed (D : Set X.obj.left) (hD : IsClosed D)
    (hc : F.Compatible) (hFD : F.support ⊆ D) :
    IsClosed ((Subtype.val : neighbourhood F D hD → X.obj.left) ⁻¹' F.support) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  by_cases hzU : z.val ∈ coveredOpen F
  · obtain ⟨i, c, hcz⟩ := mem_iUnion.mp hzU
    have hcn : c ∉ F.trace i := by
      intro hct
      exact hz (F.mem_support.mpr ⟨i, c, hct, hcz⟩)
    let A : Set X.obj.left := (F.windowMap i).hom.left.base '' (F.trace i)ᶜ
    have hA : IsOpen A :=
      (F.windowMap_isOpenImmersion i).base_open.isOpenMap _ (F.trace_isClosed i).isOpen_compl
    have hzA : z.val ∈ A := ⟨c, hcn, hcz⟩
    have hAS : A ⊆ F.supportᶜ := by
      rintro q ⟨d, hd, rfl⟩ hq
      exact hd ((Set.ext_iff.mp (F.preimage_support hc i) d).mp hq)
    exact mem_of_superset ((hA.preimage continuous_subtype_val).mem_nhds hzA)
      (fun q hq => hAS hq)
  · have hzD : z.val ∉ D := z.property.resolve_left hzU
    refine mem_of_superset ((hD.isOpen_compl.preimage continuous_subtype_val).mem_nhds hzD) ?_
    intro q hq hqs
    exact hq (hFD hqs)

/-- Actual native maps factor continuously through the derived original OPEN. -/
theorem native_preimage_closed (D : Set X.obj.left) (hD : IsClosed D)
    (hc : F.Compatible) (hFD : F.support ⊆ D) {Y : SourceReducedComplexSpace} (j : Y ⟶ X)
    (hr : range j.hom.left.base ⊆ (neighbourhood F D hD : Set X.obj.left)) :
    IsClosed (j.hom.left.base ⁻¹' F.support) := by
  let f : Y.obj.left → neighbourhood F D hD := fun y => ⟨j.hom.left.base y, hr ⟨y, rfl⟩⟩
  have hf : Continuous f := j.hom.left.base.hom.continuous.subtype_mk (fun y => hr ⟨y, rfl⟩)
  exact (support_trace_closed F D hD hc hFD).preimage hf

/-- A genuine precompact original native target, chosen from the actual derived open. -/
def target (D : Set X.obj.left) (hD : IsClosed D) (K : Set X.obj.left) (hK : IsCompact K)
    (hcov : K ∩ D ⊆ coveredOpen F) :
    OriginalNativePrecompactNeighbourhood.Neighbourhood X K (neighbourhood F D hD) :=
  OriginalNativePrecompactNeighbourhood.neighbourhood X K hK (neighbourhood F D hD)
    (compact_subset_neighbourhood F D hD hcov)

theorem target_centre_closed (D : Set X.obj.left) (hD : IsClosed D)
    (hc : F.Compatible) (hFD : F.support ⊆ D)
    (K : Set X.obj.left) (hK : IsCompact K) (hcov : K ∩ D ⊆ coveredOpen F) :
    IsClosed ((target F D hD K hK hcov).inclusion.hom.left.base ⁻¹' F.support) := by
  apply native_preimage_closed F D hD hc hFD
  rintro x ⟨y, rfl⟩
  apply (target F D hD K hK hcov).closure_subset
  apply subset_closure
  change y.val ∈ (target F D hD K hK hcov).openSet
  exact y.property

theorem target_centre_singular (D : Set X.obj.left) (hD : IsClosed D)
    (K : Set X.obj.left) (hK : IsCompact K) (hcov : K ∩ D ⊆ coveredOpen F)
    (hSing : F.support ⊆ intrinsicSingularLocus X.obj) :
    (target F D hD K hK hcov).inclusion.hom.left.base ⁻¹' F.support ⊆
      intrinsicSingularLocus (target F D hD K hK hcov).source.obj := by
  intro y hy
  exact (Set.ext_iff.mp (target F D hD K hK hcov).preimage_singular y).mp (hSing hy)

end
end Hironaka.Analytic.Unibranch.OriginalNativeCentreLocalClosedness
