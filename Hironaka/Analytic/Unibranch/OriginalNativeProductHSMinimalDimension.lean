import Hironaka.Analytic.Unibranch.OriginalNativeSmoothGivenTargetWindow
import Hironaka.Analytic.Unibranch.HironakaG11PresPresentation
import Hironaka.Resolution.HironakaG1NativeFiniteProductHSValues

/-! Genuine HS and minimal dimension at the SAME native given-target source point.
Blueprint FIRST: original-native-product-hs-minimal-dimension.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeProductHSMinimalDimension
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaReducedComplexAnalyticSpaces SourceReducedComplexSpace
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal HironakaHolomorphicJetChartInvariance
  HironakaG11PresLineState HironakaG1NativeFiniteProductState HironakaG1NativeFiniteProductHSValues
  OriginalLocalEmbeddingStalkHS OriginalNativeProductWindow OriginalNativeSmoothGivenTargetWindow
  HironakaG11HSPhaseInduction HironakaG11PresPresentation
open scoped ProductComplexManifold

variable {X Y : SourceReducedComplexSpace}

/-- Original native stalks on the ACTUAL ambient-open product restriction. -/
theorem window_point_profile (e : LocalEmbedding Y) (r : ℕ)
    (O : Opens (productAmbient e r))
    (Q : MarkedIdeal e.dim (CMfd.of (n := e.dim) e.ambient)) {H : ℕ→ℕ}
    (hState : NativeHSState Q e.carrier H) (hE : Q.E=[])
    (b : (windowSpace e r O).obj.left) (hb : b.val.val.1∈Q.cosupp) :
    originalStalkHS (windowSpace e r O) b=finiteProductHS r H := by
  let p := (windowInclusion e r O).hom.left.base b
  have hOpen:=originalStalkHS_openImmersion (windowInclusion e r O)
    (windowInclusion_isOpenImmersion e r O) b
  have hProfile:=native_product_point_profile r hState hE p.val hb
  funext l
  exact (congrFun hOpen l).symm.trans
    ((originalStalkHS_ofClosedAnalytic (productCarrier_analytic e r) p l).trans
      (congrFun hProfile l))

/-- The FULL given-target square derives the actual base cosupport. -/
theorem given_target_source_profile {f : X ⟶ Y} {x : X.obj.left}
    {e : LocalEmbedding Y} {V : Opens X.obj.left} (w : GivenTargetWindow f x e V)
    (Q : MarkedIdeal w.target.dim (CMfd.of (n := w.target.dim) w.target.ambient)) {H : ℕ→ℕ}
    (hState : NativeHSState Q w.target.carrier H) (hE : Q.E=[])
    (hBase : originalStalkHS Y (f.hom.left.base x)=H) :
    originalStalkHS X x=finiteProductHS w.rank H := by
  let c : w.target.carrier := ⟨w.sourcePoint.val.val.1,w.sourcePoint.property⟩
  have hPoint : w.target.toPoint c=f.hom.left.base x := by
    have h:=congrArg (fun a=>a.hom.left.base w.sourcePoint) w.square
    change f.hom.left.base (w.sourceMap.hom.left.base w.sourcePoint)=w.target.toPoint c at h
    rw [w.point] at h
    exact h.symm
  have hc : c.val∈Q.cosupp := by
    apply (Set.ext_iff.mp hState.cosupp_eq c.val).mpr
    intro l
    have h:=originalStalkHS_localEmbedding_eq Y w.target c l
    rw [hPoint] at h
    exact h.symm.trans (congrFun hBase l)
  have hWindow:=window_point_profile w.target w.rank w.window Q hState hE w.sourcePoint hc
  have hOpen:=originalStalkHS_openImmersion w.sourceMap w.source_open w.sourcePoint
  rw [w.point] at hOpen
  exact hOpen.trans hWindow

/-- The SAME actual source point has the matching minimal ambient dimension. -/
theorem given_target_source_minimal_dimension {f : X ⟶ Y} {x : X.obj.left}
    {e : LocalEmbedding Y} {V : Opens X.obj.left} (w : GivenTargetWindow f x e V)
    (Q : MarkedIdeal w.target.dim (CMfd.of (n := w.target.dim) w.target.ambient)) {H : ℕ→ℕ}
    (hState : NativeHSState Q w.target.carrier H) (hE : Q.E=[])
    (hBase : originalStalkHS Y (f.hom.left.base x)=H) (he : e.dim=H 1-1) :
    e.dim+w.rank=originalStalkHS X x 1-1 := by
  rw [given_target_source_profile w Q hState hE hBase]
  exact finiteProductHS_minimal_dimension w.rank hState.1 he

end
end Hironaka.Analytic.Unibranch.OriginalNativeProductHSMinimalDimension
