import Hironaka.Analytic.Unibranch.OriginalNativeEmbeddingOpenPullback
import Hironaka.Analytic.Unibranch.HironakaG11CompatibleAnalyticCover

/-! # The SAME labelled local smooth centres on an actual native target open

All ambient traces, centre restrictions and full native maps are derived
from the ordinary family and native open immersion. Blueprint FIRST.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalNativeCentreOpenPullback
noncomputable section
open Hironaka Hironaka.BlowupSequences
  Hironaka
  HironakaReducedComplexAnalyticSpaces SourceReducedComplexSpace
  HironakaG11CompatibleAnalyticCover OriginalAnalyticClosedSubspaceSmoothCentres
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  OriginalNativeSmoothOpenLocality

variable {X Y : SourceReducedComplexSpace} {ι : Type*}
  (F : LocalSmoothCentres X ι) (j : Y ⟶ X)
  (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)

private abbrev restrictedEmbedding (i : ι) : LocalEmbedding Y :=
  OriginalNativeEmbeddingOpenPullback.embedding (F.emb i) j hj

/-- The actual old ambient window restricted to the derived coordinate open. -/
def ambientWindow (i : ι) :
    Opens (OriginalNativeEmbeddingOpenPullback.coordinateOpen (F.emb i) j hj) :=
  ⟨(Opens.inclusion (OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset
      (F.emb i) j hj)) ⁻¹' (F.window i : Set (F.emb i).ambient),
    (F.window i).isOpen.preimage
      (contMDiff_inclusion (I := 𝓘(ℂ, ComplexModel (F.emb i).dim)) (n := ∞)
        (OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset
        (F.emb i) j hj)).continuous⟩

/-- The entire old ambient window lying in the derived actual open trace. -/
def oldWindowTrace (i : ι) : Opens (F.window i) :=
  ⟨(Subtype.val : F.window i → (F.emb i).ambient) ⁻¹'
      (OriginalNativeEmbeddingOpenPullback.ambientTrace (F.emb i) j hj).openSet,
    (OriginalNativeEmbeddingOpenPullback.ambientTrace (F.emb i) j hj).openSet.isOpen.preimage
      continuous_subtype_val⟩

private theorem coordinate_mem_trace (i : ι)
    (x : OriginalNativeEmbeddingOpenPullback.coordinateOpen (F.emb i) j hj) :
    Opens.inclusion (OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset (F.emb i) j hj) x ∈
      (OriginalNativeEmbeddingOpenPullback.ambientTrace (F.emb i) j hj).openSet := by
  obtain ⟨u, hu, heq⟩ := x.property
  have h : u = Opens.inclusion
      (OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset (F.emb i) j hj) x :=
    Subtype.ext heq
  exact h ▸ hu

/-- Literal coordinate-preserving biholomorphism of the two actual window restrictions. -/
def windowEquiv (i : ι) :
    ambientWindow F j hj i ≃ₘ⟮𝓘(ℂ, ComplexModel (F.emb i).dim), 𝓘(ℂ, ComplexModel (F.emb i).dim)⟯ oldWindowTrace F j hj i where
  toEquiv :=
    { toFun := fun x => ⟨⟨Opens.inclusion
        (OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset (F.emb i) j hj) x.val,
        x.property⟩, coordinate_mem_trace F j hj i x.val⟩
      invFun := fun y => ⟨⟨y.val.val.val, ⟨y.val.val, y.property, rfl⟩⟩, y.val.property⟩
      left_inv := fun x => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext (Subtype.ext (Subtype.ext rfl)) }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (oldWindowTrace F j hj i) _).mp
    apply (ContMDiff.subtypeVal_comp_iff (F.window i) _).mp
    exact (contMDiff_inclusion (I := 𝓘(ℂ, ComplexModel (F.emb i).dim)) (n := ∞)
      (OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset (F.emb i) j hj)).comp
      contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (ambientWindow F j hj i) _).mp
    apply (ContMDiff.subtypeVal_comp_iff
      (OriginalNativeEmbeddingOpenPullback.coordinateOpen (F.emb i) j hj) _).mp
    change ContMDiff 𝓘(ℂ, ComplexModel (F.emb i).dim)
      𝓘(ℂ, ComplexModel (F.emb i).dim) ∞
      (fun y : oldWindowTrace F j hj i => y.val.val.val)
    exact (contMDiff_subtype_val (U := (F.emb i).ambient)).comp
      ((contMDiff_subtype_val (U := F.window i)).comp
        (contMDiff_subtype_val (U := oldWindowTrace F j hj i)))

/-- Actual holomorphic ambient inclusion retaining the original coordinates. -/
def windowInclusion (i : ι) : ambientWindow F j hj i → F.window i :=
  fun x => (windowEquiv F j hj i x).val

theorem windowInclusion_contMDiff (i : ι) :
    ContMDiff 𝓘(ℂ, ComplexModel (F.emb i).dim) 𝓘(ℂ, ComplexModel (F.emb i).dim) ∞
      (windowInclusion F j hj i) :=
  contMDiff_subtype_val.comp (windowEquiv F j hj i).contMDiff

/-- The exact ambient inverse image of the old centre. -/
def centre (i : ι) : Set (ambientWindow F j hj i) :=
  windowInclusion F j hj i ⁻¹' F.centre i

private theorem centre_isClosedSubmanifold (i : ι) :
    IsClosedSubmanifold (F.emb i).dim (centre F j hj i) :=
  MarkedIdealBiholomorphism.isClosedSubmanifold_preimage
    (windowEquiv F j hj i).contMDiff (windowEquiv F j hj i).symm.contMDiff
    (windowEquiv F j hj i).apply_symm_apply (windowEquiv F j hj i).symm_apply_apply
    (BlowupRestrictOpen.isClosedSubmanifold_preimage_val (F.isClosedSubmanifold i)
      (oldWindowTrace F j hj i))

/-- The SAME-labelled ordinary local smooth-centre family on the actual native target open. -/
def family : LocalSmoothCentres Y ι where
  emb := restrictedEmbedding F j hj
  window := ambientWindow F j hj
  centre := centre F j hj
  isClosedSubmanifold := centre_isClosedSubmanifold F j hj
  centre_subset i _x hx := F.centre_subset i hx

private def carrierMap (i : ι) (x : ((family F j hj).windowSpace i).obj.left) :
    (F.windowSpace i).obj.left :=
  ⟨windowInclusion F j hj i x.val, x.property⟩

private theorem point_square (i : ι) (x : ((family F j hj).windowSpace i).obj.left) :
    j.hom.left.base (((family F j hj).windowMap i).hom.left.base x) =
      (F.windowMap i).hom.left.base (carrierMap F j hj i x) := by
  change j.hom.left.base ((restrictedEmbedding F j hj i).toPoint
      ⟨x.val.val, x.property⟩) = (F.emb i).toPoint
        ⟨(windowInclusion F j hj i x.val).val, x.property⟩
  exact (OriginalNativeEmbeddingOpenPullback.point_square (F.emb i) j hj
    ⟨x.val.val, x.property⟩).trans
    ((F.emb i).restrict_toPoint _ _ ⟨x.val.val, x.property⟩)

private theorem window_range_subset (i : ι) :
    range (((family F j hj).windowMap i ≫ j).hom.left.base) ⊆
      range (F.windowMap i).hom.left.base := by
  rintro _ ⟨x, rfl⟩
  exact ⟨carrierMap F j hj i x, (point_square F j hj i x).symm⟩

/-- Full native comparison of the actual window spaces. -/
def windowMap (i : ι) : (family F j hj).windowSpace i ⟶ F.windowSpace i :=
  (exists_native_open_lift (F.windowMap i) ((family F j hj).windowMap i ≫ j)
    (F.windowMap_isOpenImmersion i)
    (by
      change LocallyRingedSpace.IsOpenImmersion
        (((family F j hj).windowMap i).hom.left ≫ j.hom.left)
      let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
      infer_instance)
    (window_range_subset F j hj i)).choose

theorem windowMap_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (windowMap F j hj i).hom.left :=
  (exists_native_open_lift (F.windowMap i) ((family F j hj).windowMap i ≫ j)
    (F.windowMap_isOpenImmersion i)
    (by
      change LocallyRingedSpace.IsOpenImmersion
        (((family F j hj).windowMap i).hom.left ≫ j.hom.left)
      let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
      infer_instance)
    (window_range_subset F j hj i)).choose_spec.1

/-- Entire original native window square, before point-map faithfulness is used. -/
theorem windowMap_square (i : ι) :
    windowMap F j hj i ≫ F.windowMap i = (family F j hj).windowMap i ≫ j :=
  (exists_native_open_lift (F.windowMap i) ((family F j hj).windowMap i ≫ j)
    (F.windowMap_isOpenImmersion i)
    (by
      change LocallyRingedSpace.IsOpenImmersion
        (((family F j hj).windowMap i).hom.left ≫ j.hom.left)
      let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
      infer_instance)
    (window_range_subset F j hj i)).choose_spec.2

theorem windowMap_scalar (i : ι) :
    (windowMap F j hj i).hom.left ≫ (F.windowSpace i).obj.hom =
      ((family F j hj).windowSpace i).obj.hom :=
  Over.w (windowMap F j hj i).hom

/-- Exact point formula of the already constructed full window comparison. -/
theorem windowMap_base (i : ι) (x : ((family F j hj).windowSpace i).obj.left) :
    (windowMap F j hj i).hom.left.base x =
      ⟨windowInclusion F j hj i x.val, x.property⟩ := by
  apply (F.windowMap_isOpenImmersion i).base_open.injective
  exact (congrArg (fun a => a.hom.left.base x) (windowMap_square F j hj i)).trans
    (point_square F j hj i x)

/-- Actual full native reduced-centre comparison induced by the derived ambient inclusion. -/
def centreMap (i : ι) :
    ofClosedAnalytic ((family F j hj).centre i)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
        ((family F j hj).isClosedSubmanifold i)) ⟶
    ofClosedAnalytic (F.centre i)
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
        (F.isClosedSubmanifold i)) :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (n := (F.emb i).dim) (m := (F.emb i).dim)
      (C := (family F j hj).centre i) (D := F.centre i) (f := windowInclusion F j hj i)
      (windowInclusion_contMDiff F j hj i) (fun _ hx => hx))
    (actualSubspaceMap_point (n := (F.emb i).dim) (m := (F.emb i).dim)
      (C := (family F j hj).centre i) (D := F.centre i) (f := windowInclusion F j hj i)
      (windowInclusion_contMDiff F j hj i) (fun _ hx => hx)))

theorem centreMap_scalar (i : ι) :
    (centreMap F j hj i).hom.left ≫
        (ofClosedAnalytic (F.centre i)
          (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
            (F.isClosedSubmanifold i))).obj.hom =
      (ofClosedAnalytic ((family F j hj).centre i)
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
          ((family F j hj).isClosedSubmanifold i))).obj.hom :=
  Over.w (centreMap F j hj i).hom

/-- Full original inclusion square of the actual reduced centre spaces. -/
theorem centreMap_inclusion (i : ι) :
    OriginalClosedSubspaceFactorization.inclusion
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
          ((family F j hj).isClosedSubmanifold i))
        (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
          ((family F j hj).emb i).analytic ((family F j hj).window i))
        ((family F j hj).centre_subset i) ≫ windowMap F j hj i =
      centreMap F j hj i ≫ OriginalClosedSubspaceFactorization.inclusion
        (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
          (F.isClosedSubmanifold i))
        (AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val
          (F.emb i).analytic (F.window i)) (F.centre_subset i) := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro x
  exact windowMap_base F j hj i ⟨x.val, (family F j hj).centre_subset i x.property⟩

/-- The entire old native window over the actual open immersion is retained. -/
theorem window_range (i : ι) :
    j.hom.left.base ⁻¹' range (F.windowMap i).hom.left.base =
      range (((family F j hj).windowMap i).hom.left.base) := by
  ext y
  constructor
  · rintro ⟨c, hc⟩
    have hcA : c.val.val ∈
        (OriginalNativeEmbeddingOpenPullback.ambientTrace (F.emb i) j hj).openSet :=
      (Set.ext_iff.mp
        (OriginalNativeEmbeddingOpenPullback.ambientTrace (F.emb i) j hj).trace
        ⟨c.val.val, c.property⟩).mpr ⟨y, hc.symm⟩
    let x : ((family F j hj).windowSpace i).obj.left :=
      ⟨⟨⟨c.val.val.val, ⟨c.val.val, hcA, rfl⟩⟩, c.val.property⟩, c.property⟩
    have hxc : carrierMap F j hj i x = c := Subtype.ext (Subtype.ext (Subtype.ext rfl))
    refine ⟨x, hj.base_open.injective ?_⟩
    exact (point_square F j hj i x).trans
      ((congrArg (F.windowMap i).hom.left.base hxc).trans hc)
  · rintro ⟨x, rfl⟩
    exact ⟨carrierMap F j hj i x, (point_square F j hj i x).symm⟩

/-- Exact whole centre-trace inverse image under the actual full native window map. -/
theorem trace_preimage (i : ι) :
    (windowMap F j hj i).hom.left.base ⁻¹' F.trace i = (family F j hj).trace i := by
  ext x
  change ((windowMap F j hj i).hom.left.base x).val ∈ F.centre i ↔
    x.val ∈ centre F j hj i
  rw [windowMap_base]
  rfl

/-- Exact support inverse image, without a compatibility or cover assumption. -/
theorem support_eq_preimage :
    (family F j hj).support = j.hom.left.base ⁻¹' F.support := by
  ext y
  constructor
  · intro hy
    obtain ⟨i, x, hx, hxy⟩ := (family F j hj).mem_support.mp hy
    refine F.mem_support.mpr ⟨i, (windowMap F j hj i).hom.left.base x, ?_, ?_⟩
    · exact (Set.ext_iff.mp (trace_preimage F j hj i) x).mpr hx
    · exact (congrArg (fun a => a.hom.left.base x) (windowMap_square F j hj i)).trans
        (congrArg j.hom.left.base hxy)
  · intro hy
    obtain ⟨i, c, hc, hcy⟩ := F.mem_support.mp hy
    obtain ⟨x, hxy⟩ := (Set.ext_iff.mp (window_range F j hj i) y).mp ⟨c, hcy⟩
    have hxc : (windowMap F j hj i).hom.left.base x = c := by
      apply (F.windowMap_isOpenImmersion i).base_open.injective
      exact (congrArg (fun a => a.hom.left.base x) (windowMap_square F j hj i)).trans
        ((congrArg j.hom.left.base hxy).trans hcy.symm)
    refine (family F j hj).mem_support.mpr ⟨i, x, ?_, hxy⟩
    apply (Set.ext_iff.mp (trace_preimage F j hj i) x).mp
    change (windowMap F j hj i).hom.left.base x ∈ F.trace i
    rw [hxc]
    exact hc

/-- Genuine original overlap compatibility restricts to the same-labelled actual family. -/
theorem compatible (hF : F.Compatible) : (family F j hj).Compatible := by
  intro i k x z hxz hx
  apply (Set.ext_iff.mp (trace_preimage F j hj k) z).mp
  apply hF i k ((windowMap F j hj i).hom.left.base x)
    ((windowMap F j hj k).hom.left.base z)
  · exact (congrArg (fun a => a.hom.left.base x) (windowMap_square F j hj i)).trans
      ((congrArg j.hom.left.base hxz).trans
        (congrArg (fun a => a.hom.left.base z) (windowMap_square F j hj k)).symm)
  · exact (Set.ext_iff.mp (trace_preimage F j hj i) x).mpr hx

/-- Closed original support remains closed on the actual target open. -/
theorem isClosed_support (hF : IsClosed F.support) : IsClosed (family F j hj).support := by
  rw [support_eq_preimage]
  exact hF.preimage j.hom.left.base.hom.continuous

/-- Current singular containment pulls back to the actual current target-open source. -/
theorem support_subset_intrinsicSingularLocus
    (hF : F.support ⊆ HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus X.obj) :
    (family F j hj).support ⊆
      HironakaIntrinsicComplexAnalyticRegularLocus.intrinsicSingularLocus Y.obj := by
  rw [support_eq_preimage]
  have h := preimage_intrinsicSingularLocus_of_isOpenImmersion j hj
  rw [← h]
  exact preimage_mono hF

end
end Hironaka.Analytic.Unibranch.OriginalNativeCentreOpenPullback
