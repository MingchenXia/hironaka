import Hironaka.Analytic.Unibranch.OriginalNativeSmoothGivenTargetWindow
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothSingularLocus
import Hironaka.Analytic.Unibranch.OriginalNativeSmoothComposition
import Hironaka.Analytic.Unibranch.OriginalNativeHSThresholdIsomorphism
import Hironaka.Analytic.Unibranch.OriginalNativeHSOuterInitialBound
import Hironaka.Resolution.HironakaG1NativeFiniteProductWholeProfile
import Hironaka.Resolution.HironakaG1NativeFiniteProductHSLex

/-! Actual all-point native product profiles and exact singular-threshold
pullback under the genuine SINGULAR-guarded Lex barrier. Blueprint FIRST.
No pointwise convolution reflection, equidimensionality or global rank. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothBarrierThreshold
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  SourceReducedComplexSpace HironakaReducedComplexAnalyticSpaces
  HironakaHolomorphicJetChartInvariance HironakaActualAnalyticSubspace
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11HSPhaseInduction HironakaG11PresPresentation
  HironakaG1NativeFiniteProductState HironakaG1NativeFiniteProductWholeProfile HironakaG1NativeFiniteProductHSLex
  OriginalLocalEmbeddingStalkHS OriginalNativeProductWindow OriginalNativeSmoothGivenTargetWindow
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothComposition OriginalNativeSmoothSingularLocus
  OriginalIntrinsicHSSuperlevels OriginalNativeHSThresholdIsomorphism OriginalNativeHSOuterInitialBound
open scoped ProductComplexManifold

variable {X Y : SourceReducedComplexSpace}

/-- No cosupport, singularity, native record or equality-stratum premise. -/
theorem product_point_profile (e : LocalEmbedding Y) (r : ℕ) (p : (productSpace e r).obj.left) :
    originalStalkHS (productSpace e r) p=
      finiteProductHS r (originalStalkHS Y ((first e r).hom.left.base p)) := by
  have hs : originalStalkHS (productSpace e r) p=
      hilbertSamuelAt (vanishingIdeal (n := e.dim+r) (productCarrier e r)) p.val := by
    funext l
    exact originalStalkHS_ofClosedAnalytic (productCarrier_analytic e r) p l
  have ht : originalStalkHS Y ((first e r).hom.left.base p)=
      hilbertSamuelAt (vanishingIdeal (n := e.dim) e.carrier) p.val.1 := by
    funext l
    exact originalStalkHS_localEmbedding_eq Y e (pointEquiv e r p).1 l
  exact hs.trans ((finite_product_vanishing_profile
    (X := BlowupTowers.CMfd.of (n := e.dim) e.ambient) e.carrier e.analytic r p.val).trans
    (congrArg (finiteProductHS r) ht.symm))

/-- EVERY actual point of the SAME ambient-open product window. -/
theorem window_point_profile (e : LocalEmbedding Y) (r : ℕ) (O : Opens (productAmbient e r))
    (p : (windowSpace e r O).obj.left) :
    originalStalkHS (windowSpace e r O) p=
      finiteProductHS r (originalStalkHS Y ((windowFirst e r O).hom.left.base p)) := by
  let q:=(windowInclusion e r O).hom.left.base p
  have ho:=originalStalkHS_openImmersion (windowInclusion e r O)
    (windowInclusion_isOpenImmersion e r O) p
  calc
    _=originalStalkHS (productSpace e r) q := ho.symm
    _=finiteProductHS r (originalStalkHS Y ((first e r).hom.left.base q)) := product_point_profile e r q
    _=_ := congrArg (fun y=>finiteProductHS r (originalStalkHS Y y))
      (congrArg (fun k=>k.hom.left.base p) (window_first_square e r O))

/-- Fixed rank belongs ONLY to this actual local product representation. -/
theorem given_target_window_profile {f : X⟶Y} {x : X.obj.left} {e : LocalEmbedding Y}
    {V : Opens X.obj.left} (w : GivenTargetWindow f x e V)
    (p : (windowSpace w.target w.rank w.window).obj.left) :
    originalStalkHS X (w.sourceMap.hom.left.base p)=
      finiteProductHS w.rank (originalStalkHS Y (f.hom.left.base (w.sourceMap.hom.left.base p))) := by
  calc
    _=originalStalkHS (windowSpace w.target w.rank w.window) p :=
      originalStalkHS_openImmersion w.sourceMap w.source_open p
    _=finiteProductHS w.rank (originalStalkHS Y ((windowFirst w.target w.rank w.window).hom.left.base p)) :=
      window_point_profile w.target w.rank w.window p
    _=_ := congrArg (fun y=>finiteProductHS w.rank (originalStalkHS Y y))
      (congrArg (fun k=>k.hom.left.base p) w.square).symm

private theorem window_first_smooth (e : LocalEmbedding Y) (r : ℕ) (O : Opens (productAmbient e r)) :
    IsSmoothMorphism (windowFirst e r O) := by
  let hWP : MapsTo (Prod.fst : productAmbient e r→e.ambient) O (⊤ : Opens e.ambient) :=
    fun _ _=>mem_univ _
  have hp:=isSmoothMorphism_comp (nativeProjection e r ⊤ O hWP) (targetInclusion e ⊤)
    (nativeProjection_isSmooth e r ⊤ O hWP)
    (isSmoothMorphism_of_isOpenImmersion _ (targetInclusion_isOpenImmersion e ⊤))
  exact (nativeProjection_square e r ⊤ O hWP) ▸ hp

/-- The true barrier is needed ONLY on actual target singular points. -/
theorem window_threshold_preimage (e : LocalEmbedding Y) (r : ℕ) (O : Opens (productAmbient e r))
    (H : ℕ→ℕ)
    (hBound : ∀ y∈intrinsicSingularLocus Y.obj,toLex (originalStalkHS Y y)≤toLex H) :
    (windowFirst e r O).hom.left.base ⁻¹' originalSingularHSThreshold Y H=
      originalSingularHSThreshold (windowSpace e r O) (finiteProductHS r H) := by
  ext p
  have hSing:=smoothAt_singular_iff (windowFirst e r O) p (window_first_smooth e r O p)
  have hProfile:=window_point_profile e r O p
  constructor
  · rintro ⟨hs,hlo⟩
    have heq : originalStalkHS Y ((windowFirst e r O).hom.left.base p)=H :=
      congrArg ofLex (le_antisymm (hBound _ hs) (Pi.toLex_monotone hlo))
    refine ⟨hSing.mpr hs,?_⟩
    intro l
    rw [hProfile,heq]
  · rintro ⟨hs,hlo⟩
    have hTargetSing:=hSing.mp hs
    have hProd : toLex (finiteProductHS r H)≤
        toLex (finiteProductHS r (originalStalkHS Y ((windowFirst e r O).hom.left.base p))) := by
      rw [←hProfile]
      exact Pi.toLex_monotone hlo
    have hRaw:=(finiteProductHS_lex_le_iff r H _).mp hProd
    have heq : originalStalkHS Y ((windowFirst e r O).hom.left.base p)=H :=
      congrArg ofLex (le_antisymm (hBound _ hTargetSing) hRaw)
    exact ⟨hTargetSing,fun l=>(congrFun heq l).ge⟩

theorem window_threshold_compl_preimage (e : LocalEmbedding Y) (r : ℕ) (O : Opens (productAmbient e r))
    (H : ℕ→ℕ)
    (hBound : ∀ y∈intrinsicSingularLocus Y.obj,toLex (originalStalkHS Y y)≤toLex H) :
    (windowFirst e r O).hom.left.base ⁻¹' (originalSingularHSThreshold Y H)ᶜ=
      (originalSingularHSThreshold (windowSpace e r O) (finiteProductHS r H))ᶜ := by
  rw [preimage_compl,window_threshold_preimage e r O H hBound]

/-- Exact correspondence on the ORIGINAL source image; no global relative rank. -/
theorem given_target_window_threshold {f : X⟶Y} {x : X.obj.left} {e : LocalEmbedding Y}
    {V : Opens X.obj.left} (w : GivenTargetWindow f x e V) (H : ℕ→ℕ)
    (hBound : ∀ y∈intrinsicSingularLocus Y.obj,toLex (originalStalkHS Y y)≤toLex H) :
    w.sourceMap.hom.left.base ⁻¹' (f.hom.left.base ⁻¹' originalSingularHSThreshold Y H)=
      w.sourceMap.hom.left.base ⁻¹' originalSingularHSThreshold X (finiteProductHS w.rank H) := by
  ext p
  have hp:=congrArg (fun k=>k.hom.left.base p) w.square
  have hw:=Set.ext_iff.mp (window_threshold_preimage w.target w.rank w.window H hBound) p
  have hi:=Set.ext_iff.mp (threshold_preimage_openImmersion (finiteProductHS w.rank H)
    w.sourceMap w.source_open) p
  exact (iff_of_eq (congrArg (fun y=>y∈originalSingularHSThreshold Y H) hp)).trans (hw.trans hi.symm)

/-- D40 supplies the ACTUAL singular-guarded bound, with no extra packet. -/
theorem factory_window_threshold (Y : SourceReducedComplexSpace) (L : Set Y.obj.left)
    (hL : IsCompact L) (hne : (L∩intrinsicSingularLocus Y.obj).Nonempty)
    (e : LocalEmbedding (OriginalNativeHSShadowPhaseFactory.base Y L hL hne))
    (r : ℕ) (O : Opens (productAmbient e r)) :
    (windowFirst e r O).hom.left.base ⁻¹'
        originalSingularHSThreshold (OriginalNativeHSShadowPhaseFactory.base Y L hL hne)
          (factoryProfile Y L hL hne)=
      originalSingularHSThreshold (windowSpace e r O) (finiteProductHS r (factoryProfile Y L hL hne)) :=
  window_threshold_preimage e r O (factoryProfile Y L hL hne) (factory_base_bound Y L hL hne)

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothBarrierThreshold
