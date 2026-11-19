import Hironaka.Analytic.Unibranch.OriginalNativeHSZero
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothBarrierThreshold
import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterHistory

/-! Actual PAST physical histories and full original square DERIVE current
smooth rank/profile. No globally smooth CURRENT source or rank/density packet.
Full Blueprint FIRST: original-native-current-smooth-product-rank.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeCurrentSmoothProductRank
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG1NativeFiniteProductState
  HironakaG1NativeFiniteProductHSValues OriginalLocalEmbeddingStalkHS HironakaG11HSPhaseInduction
  OriginalNativeProductWindow OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition
  OriginalNativeSmoothSingularLocus OriginalNativeSmoothBarrierThreshold OriginalNativeHSZero
  OriginalNativeSmoothGivenTargetWindow OriginalNativeHSOuterHistory
open scoped ProductComplexManifold

private theorem product_smooth {Y : SourceReducedComplexSpace} (e : LocalEmbedding Y)
    (r : ℕ) (O : Opens (productAmbient e r)) : IsSmoothMorphism (windowFirst e r O) := by
  let hWP : MapsTo (Prod.fst : productAmbient e r→e.ambient) O (⊤ : Opens e.ambient) :=
    fun _ _=>mem_univ _
  have hp := isSmoothMorphism_comp (nativeProjection e r ⊤ O hWP) (targetInclusion e ⊤)
    (nativeProjection_isSmooth e r ⊤ O hWP)
    (isSmoothMorphism_of_isOpenImmersion _ (targetInclusion_isOpenImmersion e ⊤))
  exact (nativeProjection_square e r ⊤ O hWP) ▸ hp

variable {Y B C S T : SourceReducedComplexSpace} (e0 : LocalEmbedding Y) (r : ℕ)
  (O : Opens (productAmbient e0 r))
  (iS : B⟶windowSpace e0 r O) (hiS : LocallyRingedSpace.IsOpenImmersion iS.hom.left)
  (iT : C⟶Y) (hiT : LocallyRingedSpace.IsOpenImmersion iT.hom.left)
  (hS : PhysicalHistory B S) (hT : PhysicalHistory C T) (g : S⟶T)
  (hSquare : g≫hT.projection≫iT=hS.projection≫iS≫windowFirst e0 r O)

include hiS hiT hSquare in
/-- A genuine actual current product window has DERIVED original rank r,
using only PAST physical histories and the FULL original native square. -/
theorem current_window_rank_eq {x : S.obj.left} {d : LocalEmbedding T} {V : Opens S.obj.left}
    (w : GivenTargetWindow g x d V) : w.rank=r := by
  let D := w.sourceMap.hom.left.base ⁻¹'
    (hS.projection.hom.left.base ⁻¹' intrinsicRegularLocus B.obj)
  have hD : Dense D := hS.singularModification.dense_preimage_intrinsicRegularLocus.preimage
    w.source_open.base_open.isOpenMap
  have hNonempty : D.Nonempty := hD.nonempty_iff.mpr ⟨w.sourcePoint⟩
  obtain ⟨z,hz⟩ := hNonempty
  let s := w.sourceMap.hom.left.base z
  let u := hS.projection.hom.left.base s
  let t := g.hom.left.base s
  let v := hT.projection.hom.left.base t
  let a := iS.hom.left.base u
  let b := iT.hom.left.base v
  have hpoint : b=(windowFirst e0 r O).hom.left.base a :=
    congrArg (fun k : S⟶Y=>k.hom.left.base s) hSquare
  have hSourceReg : a∈intrinsicRegularLocus (windowSpace e0 r O).obj :=
    (smoothAt_regular_iff iS u (isSmoothMorphism_of_isOpenImmersion iS hiS u)).mp hz
  have hOriginalTargetReg : b∈intrinsicRegularLocus Y.obj := by
    rw [hpoint]
    exact (smoothAt_regular_iff (windowFirst e0 r O) a (product_smooth e0 r O a)).mp hSourceReg
  have hTargetReg : v∈intrinsicRegularLocus C.obj :=
    (smoothAt_regular_iff iT v (isSmoothMorphism_of_isOpenImmersion iT hiT v)).mpr hOriginalTargetReg
  have hSourceHS : originalStalkHS S s=originalStalkHS (windowSpace e0 r O) a :=
    (originalStalkHS_isIsoOver hS.singularModification.isIsoOver_intrinsicRegularLocus hz).trans
      (originalStalkHS_openImmersion iS hiS u).symm
  have hTargetHS : originalStalkHS T t=originalStalkHS Y b :=
    (originalStalkHS_isIsoOver hT.singularModification.isIsoOver_intrinsicRegularLocus hTargetReg).trans
      (originalStalkHS_openImmersion iT hiT v).symm
  have hOriginal : originalStalkHS S s=finiteProductHS r (originalStalkHS T t) := by
    calc
      _=originalStalkHS (windowSpace e0 r O) a := hSourceHS
      _=finiteProductHS r (originalStalkHS Y ((windowFirst e0 r O).hom.left.base a)) :=
        window_point_profile e0 r O a
      _=finiteProductHS r (originalStalkHS Y b) :=
        congrArg (fun y=>finiteProductHS r (originalStalkHS Y y)) hpoint.symm
      _=_ := congrArg (finiteProductHS r) hTargetHS.symm
  have hCurrent : originalStalkHS S s=finiteProductHS w.rank (originalStalkHS T t) :=
    given_target_window_profile w z
  have hOne := congrFun (hCurrent.symm.trans hOriginal) 1
  rw [finiteProductHS_one,finiteProductHS_one,originalStalkHS_zero T t,mul_one,mul_one] at hOne
  exact Nat.add_left_cancel hOne

include hiS hiT hSquare in
/-- Ordinary smooth g INTERNALLY chooses the true current product chart;
PAST history density derives its rank and the whole profile at EVERY point. -/
theorem current_point_profile (hg : IsSmoothMorphism g) (x : S.obj.left) :
    originalStalkHS S x=finiteProductHS r (originalStalkHS T (g.hom.left.base x)) := by
  let d := LocalEmbedding.ofPoint T (g.hom.left.base x)
  obtain ⟨w⟩ := exists_given_target_window g x (hg x) d
    (LocalEmbedding.mem_range_ofPoint T (g.hom.left.base x)) ⊤ trivial
  have hw := current_window_rank_eq e0 r O iS hiS iT hiT hS hT g hSquare w
  have hProfile := given_target_window_profile w w.sourcePoint
  simpa only [w.point,hw] using hProfile

end
end Hironaka.Analytic.Unibranch.OriginalNativeCurrentSmoothProductRank
