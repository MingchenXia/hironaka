import Hironaka.Analytic.Unibranch.OriginalNativeSmoothReducedIdealPullback
import Hironaka.Analytic.Unibranch.HironakaG11PresPresentation
import Hironaka.Resolution.HironakaG11IntrinsicRegularOpenImmersion

/-! Exact original intrinsic singular/regular inverse images under genuine
native analytic smooth maps, and their whole intrinsic singular ideals.
Blueprint first: `original-native-smooth-singular-locus.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothSingularLocus
noncomputable section
open Hironaka Hironaka
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaG11IntrinsicRegularOpenImmersion
  HironakaIntrinsicReducedCentreIdealSheaf HironakaNativePulledIdealSheaf
  HironakaIntrinsicReducedCentreOpenPullback
  SourceReducedComplexSpace OriginalNativeProductWindow OriginalNativeSmoothLocalProduct
  OriginalNativeSmoothReducedIdealPullback
open scoped ProductComplexManifold

variable {X Y : SourceReducedComplexSpace}

/-- True singularity reflection/preservation on the SAME actual quotient windows. -/
theorem nativeProjection_singular_iff (e : LocalEmbedding Y) (r : ℕ) (P : Opens e.ambient)
    (W : Opens (productAmbient e r)) (hWP : MapsTo (Prod.fst : productAmbient e r → e.ambient) W P)
    (s : (windowSpace e r W).obj.left) :
    s ∈ intrinsicSingularLocus (windowSpace e r W).obj ↔
      (nativeProjection e r P W hWP).hom.left.base s ∈ intrinsicSingularLocus (targetSpace e P).obj := by
  have hsrc := HironakaG11PresPresentation.mem_intrinsicSingularLocus_ofClosedAnalytic_iff
    (windowCarrier_analytic e r W) s
  have htgt := HironakaG11PresPresentation.mem_intrinsicSingularLocus_ofClosedAnalytic_iff
    (targetCarrier_analytic e P) ((nativeProjection e r P W hWP).hom.left.base s)
  have hpull := HironakaOriginalCanonicalDimensionList.singularSet_preimage_eq
    (X := BlowupTowers.CMfd.of (n := e.dim) P)
    (Y := BlowupTowers.CMfd.of (n := e.dim+r) W)
    (ambientProjection_isSubmersion e r P W hWP) (targetCarrier e P)
  have hpoint := Set.ext_iff.mp hpull s.val
  exact hsrc.trans (hpoint.trans htgt.symm)

/-- Ordinary native smoothness detects the ORIGINAL singular points in both directions. -/
theorem smoothAt_singular_iff (f : X ⟶ Y) (x : X.obj.left) (hsm : IsSmoothAt f x) :
    x ∈ intrinsicSingularLocus X.obj ↔ f.hom.left.base x ∈ intrinsicSingularLocus Y.obj := by
  obtain ⟨e,r,P,W,hWP,iS,s,hiS,hs,_,_,hsq,_,_⟩ :=
    exists_ambient_representation f x hsm ⊤ ⊤ (Set.mem_univ x) (Set.mem_univ _)
  have hsource := not_congr (mem_intrinsicRegularLocus_map_iff iS.hom.left hiS (Over.w iS.hom) s)
  have htarget := not_congr (mem_intrinsicRegularLocus_map_iff (targetInclusion e P).hom.left
    (targetInclusion_isOpenImmersion e P) (Over.w (targetInclusion e P).hom)
    ((nativeProjection e r P W hWP).hom.left.base s))
  have hp : f.hom.left.base (iS.hom.left.base s) =
      (targetInclusion e P).hom.left.base ((nativeProjection e r P W hWP).hom.left.base s) :=
    congrArg (fun a => a.hom.left.base s) hsq
  have hlocal : iS.hom.left.base s ∈ intrinsicSingularLocus X.obj ↔
      f.hom.left.base (iS.hom.left.base s) ∈ intrinsicSingularLocus Y.obj := by
    exact hsource.trans ((nativeProjection_singular_iff e r P W hWP s).trans
      (htarget.symm.trans (iff_of_eq (congrArg (fun y => y ∈ intrinsicSingularLocus Y.obj) hp.symm))))
  exact hs ▸ hlocal

/-- The SAME ordinary smooth map reflects and preserves all original regular points. -/
theorem smoothAt_regular_iff (f : X ⟶ Y) (x : X.obj.left) (hsm : IsSmoothAt f x) :
    x ∈ intrinsicRegularLocus X.obj ↔ f.hom.left.base x ∈ intrinsicRegularLocus Y.obj := by
  have h := not_congr (smoothAt_singular_iff f x hsm)
  simpa only [intrinsicSingularLocus,Set.mem_compl_iff,not_not] using h

/-- Entire original singular loci, with no surjectivity or purity premise. -/
theorem preimage_intrinsicSingularLocus (f : X ⟶ Y) (hsm : IsSmoothMorphism f) :
    f.hom.left.base ⁻¹' intrinsicSingularLocus Y.obj = intrinsicSingularLocus X.obj :=
  Set.ext fun x => (smoothAt_singular_iff f x (hsm x)).symm

/-- Entire original regular loci, including empty sources and relative dimension zero. -/
theorem preimage_intrinsicRegularLocus (f : X ⟶ Y) (hsm : IsSmoothMorphism f) :
    f.hom.left.base ⁻¹' intrinsicRegularLocus Y.obj = intrinsicRegularLocus X.obj :=
  Set.ext fun x => (smoothAt_regular_iff f x (hsm x)).symm

/-- The whole native unit submodule is the original source singular ideal. -/
theorem smooth_singular_submodule_eq (f : X ⟶ Y) (hsm : IsSmoothMorphism f) :
    nativePulledIdealSubmodule f.hom.left
      (intrinsicReducedCentreIdealModule Y.obj.left (intrinsicSingularLocus Y.obj))
      (intrinsicReducedCentreIdealInclusion Y.obj.left (intrinsicSingularLocus Y.obj)) =
      intrinsicReducedCentreSubmodule X.obj.left (intrinsicSingularLocus X.obj) :=
  (smooth_pulled_submodule_eq f hsm
    (OriginalIntrinsicSingularLocus.isAnalyticSubset_intrinsicSingularLocus Y)).trans
      (congrArg (intrinsicReducedCentreSubmodule X.obj.left) (preimage_intrinsicSingularLocus f hsm))

/-- Full native original singular-ideal iso with the SAME actual scalar map. -/
def smooth_singular_idealIso (f : X ⟶ Y) (hsm : IsSmoothMorphism f) :
    nativePulledIdealModule f.hom.left
      (intrinsicReducedCentreIdealModule Y.obj.left (intrinsicSingularLocus Y.obj))
      (intrinsicReducedCentreIdealInclusion Y.obj.left (intrinsicSingularLocus Y.obj)) ≅
      intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj) where
  hom := ⟨PresheafOfModules.Submodule.homOfLE (smooth_singular_submodule_eq f hsm).le⟩
  inv := ⟨PresheafOfModules.Submodule.homOfLE (smooth_singular_submodule_eq f hsm).ge⟩
  hom_inv_id := by ext U s; rfl
  inv_hom_id := by ext U s; rfl

theorem smooth_singular_idealIso_hom_comp_inclusion (f : X ⟶ Y) (hsm : IsSmoothMorphism f) :
    (smooth_singular_idealIso f hsm).hom ≫
      intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj) =
      nativePulledIdealInclusion f.hom.left
        (intrinsicReducedCentreIdealModule Y.obj.left (intrinsicSingularLocus Y.obj))
        (intrinsicReducedCentreIdealInclusion Y.obj.left (intrinsicSingularLocus Y.obj)) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (smooth_singular_submodule_eq f hsm).le

theorem smooth_singular_idealIso_inv_comp_inclusion (f : X ⟶ Y) (hsm : IsSmoothMorphism f) :
    (smooth_singular_idealIso f hsm).inv ≫
      nativePulledIdealInclusion f.hom.left
        (intrinsicReducedCentreIdealModule Y.obj.left (intrinsicSingularLocus Y.obj))
        (intrinsicReducedCentreIdealInclusion Y.obj.left (intrinsicSingularLocus Y.obj)) =
      intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (smooth_singular_submodule_eq f hsm).ge

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothSingularLocus
