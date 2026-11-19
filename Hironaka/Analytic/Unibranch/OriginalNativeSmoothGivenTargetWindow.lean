import Hironaka.Analytic.Unibranch.OriginalNativeEmbeddingOpenPullback

/-!
# Actual smooth product windows over a GIVEN original target embedding

The target is a literal open restriction of the supplied embedding, with
unchanged ambient dimension. Only actual native product/open-immersion
universality is used; no closed-embedding invariant comparison is assumed.
Blueprint FIRST: `original-native-smooth-given-target-window.tex`.
-/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothGivenTargetWindow
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka HironakaReducedComplexAnalyticSpaces
  SourceReducedComplexSpace OriginalNativeProductWindow OriginalNativeProductTransport
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothOpenLocality
open scoped ProductComplexManifold

variable {X Y : SourceReducedComplexSpace}

/-- Actual output data: the target is a literal restriction of the GIVEN
embedding, and the source is its genuine reduced product trace. -/
structure GivenTargetWindow (f : X ⟶ Y) (x : X.obj.left)
    (e : LocalEmbedding Y) (V : Opens X.obj.left) where
  targetOpen : Opens (ComplexModel e.dim)
  targetOpen_subset : targetOpen ≤ e.ambient
  rank : ℕ
  window : Opens (productAmbient (e.restrict targetOpen targetOpen_subset) rank)
  sourceMap : windowSpace (e.restrict targetOpen targetOpen_subset) rank window ⟶ X
  source_open : LocallyRingedSpace.IsOpenImmersion sourceMap.hom.left
  sourcePoint : (windowSpace (e.restrict targetOpen targetOpen_subset) rank window).obj.left
  point : sourceMap.hom.left.base sourcePoint = x
  source_range : range sourceMap.hom.left.base ⊆ (V : Set X.obj.left)
  square : sourceMap ≫ f = windowFirst (e.restrict targetOpen targetOpen_subset) rank window

namespace GivenTargetWindow

variable {f : X ⟶ Y} {x : X.obj.left} {e : LocalEmbedding Y} {V : Opens X.obj.left}

def target (w : GivenTargetWindow f x e V) : LocalEmbedding Y :=
  e.restrict w.targetOpen w.targetOpen_subset

theorem target_dim (w : GivenTargetWindow f x e V) : w.target.dim = e.dim := rfl

theorem target_range (w : GivenTargetWindow f x e V) :
    range w.target.toPoint ⊆ range e.toPoint := by
  rintro _ ⟨c, rfl⟩
  exact ⟨⟨Opens.inclusion w.targetOpen_subset c.val, c.property⟩,
    (e.restrict_toPoint w.targetOpen w.targetOpen_subset c).symm⟩

/-- The actual projection certificate, retaining its exact dependent
chart instances from the genuine product-window theorem. -/
theorem ambientProjection_submersion (w : GivenTargetWindow f x e V) :
    type_of% (window_projection_isSubmersion
      (e.restrict w.targetOpen w.targetOpen_subset) w.rank w.window) :=
  window_projection_isSubmersion (e.restrict w.targetOpen w.targetOpen_subset) w.rank w.window

/-- The entire ideal equality with the SAME dependent native chart
instances as the actual product window; no support-level replacement. -/
theorem whole_source_ideal (w : GivenTargetWindow f x e V) :
    type_of% (window_whole_ideal
      (e.restrict w.targetOpen w.targetOpen_subset) w.rank w.window) :=
  window_whole_ideal (e.restrict w.targetOpen w.targetOpen_subset) w.rank w.window

theorem source_scalar (w : GivenTargetWindow f x e V) :
    w.sourceMap.hom.left ≫ X.obj.hom =
      (windowSpace w.target w.rank w.window).obj.hom :=
  Over.w w.sourceMap.hom

theorem target_scalar (w : GivenTargetWindow f x e V) :
    (chartInclusion w.target).hom.left ≫ Y.obj.hom = (chartSpace w.target).obj.hom :=
  Over.w (chartInclusion w.target).hom

end GivenTargetWindow

/-- Ordinary smoothness and ordinary image membership internally give an
actual product window over a restriction of the GIVEN target embedding. -/
theorem exists_given_target_window (f : X ⟶ Y) (x : X.obj.left)
    (hsm : IsSmoothAt f x) (e : LocalEmbedding Y)
    (he : f.hom.left.base x ∈ range e.toPoint)
    (V : Opens X.obj.left) (hxV : x ∈ V) :
    Nonempty (GivenTargetWindow f x e V) := by
  obtain ⟨d,r,P,W₀,hWP,i₀,s₀,hi₀,hs₀,hrV,_hrT,hsq₀,_hsub,_hideal⟩ :=
    exists_ambient_representation f x hsm V ⊤ hxV (Set.mem_univ _)
  have hi₀sq : i₀ ≫ f = windowFirst d r W₀ :=
    hsq₀.trans (nativeProjection_square d r P W₀ hWP)
  let j := chartInclusion d
  have hj : LocallyRingedSpace.IsOpenImmersion j.hom.left := d.isOpenImmersion
  let dpoint : d.carrier := ⟨s₀.val.val.1,s₀.property⟩
  have hdpoint : j.hom.left.base dpoint = f.hom.left.base x := by
    have hp := congrArg (fun a => a.hom.left.base s₀) hi₀sq
    exact hp.symm.trans (congrArg f.hom.left.base hs₀)
  let eR := OriginalNativeEmbeddingOpenPullback.restricted e j hj
  let F := OriginalNativeEmbeddingOpenPullback.nativeLift e j hj
  have hF : LocallyRingedSpace.IsOpenImmersion F.hom.left :=
    OriginalNativeEmbeddingOpenPullback.nativeLift_isOpenImmersion e j hj
  have hFj : F ≫ j = chartInclusion eR :=
    OriginalNativeEmbeddingOpenPullback.nativeLift_square e j hj
  have hdimage : dpoint ∈ j.hom.left.base ⁻¹' range e.toPoint := by
    change j.hom.left.base dpoint ∈ range e.toPoint
    rw [hdpoint]
    exact he
  have hdF : dpoint ∈ range
      (OriginalNativeEmbeddingOpenPullback.embedding e j hj).toPoint :=
    (Set.ext_iff.mp (OriginalNativeEmbeddingOpenPullback.range_dictionary e j hj) dpoint).mp hdimage
  obtain ⟨cR,hcR⟩ := hdF
  have hcF : F.hom.left.base cR = dpoint := hcR
  let PM := productMap eR d r F
  have hPM : LocallyRingedSpace.IsOpenImmersion PM.hom.left :=
    productMap_isOpenImmersion eR d r F hF
  let j₀ := windowInclusion d r W₀
  have hj₀ : LocallyRingedSpace.IsOpenImmersion j₀.hom.left :=
    windowInclusion_isOpenImmersion d r W₀
  let p₀ : (productSpace eR r).obj.left := ⟨(cR.val,s₀.val.val.2),cR.property⟩
  have hp₀ : PM.hom.left.base p₀ = j₀.hom.left.base s₀ := by
    apply Subtype.ext
    exact (productMap_point eR d r F p₀).trans
      (Prod.ext (congrArg Subtype.val hcF) rfl)
  let O : Opens (productSpace eR r).obj.left :=
    ⟨PM.hom.left.base ⁻¹' range j₀.hom.left.base,
      hj₀.base_open.isOpen_range.preimage PM.hom.left.base.hom.continuous⟩
  have hpO : p₀ ∈ O := ⟨s₀,hp₀.symm⟩
  obtain ⟨W,hW,hWpoint⟩ := exists_window_of_native_open eR r O
  let s : (windowSpace eR r W).obj.left := ⟨⟨p₀.val,hWpoint p₀ hpO⟩,p₀.property⟩
  let M := windowInclusion eR r W ≫ PM
  have hM : LocallyRingedSpace.IsOpenImmersion M.hom.left :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (windowInclusion eR r W).hom.left
      (windowInclusion_isOpenImmersion eR r W) PM.hom.left hPM
  have hrM : range M.hom.left.base ⊆ range j₀.hom.left.base := by
    rintro _ ⟨z,rfl⟩
    have hz : (windowInclusion eR r W).hom.left.base z ∈ O :=
      (Set.ext_iff.mp hW _).mp ⟨z,rfl⟩
    exact hz
  obtain ⟨L,hL,hLj⟩ := exists_native_open_lift j₀ M hj₀ hM hrM
  have hLs : L.hom.left.base s = s₀ :=
    hj₀.base_open.injective ((congrArg (fun a => a.hom.left.base s) hLj).trans hp₀)
  let iS := L ≫ i₀
  have hiS : LocallyRingedSpace.IsOpenImmersion iS.hom.left :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ L.hom.left hL i₀.hom.left hi₀
  have hs : iS.hom.left.base s = x := (congrArg i₀.hom.left.base hLs).trans hs₀
  have hiSV : range iS.hom.left.base ⊆ (V : Set X.obj.left) := by
    rintro _ ⟨z,rfl⟩
    exact hrV ⟨L.hom.left.base z,rfl⟩
  have hPMfirst : PM ≫ first d r = first eR r := by
    calc
      _ = (PM ≫ firstToChart d r) ≫ chartInclusion d := (Category.assoc _ _ _).symm
      _ = (firstToChart eR r ≫ F) ≫ chartInclusion d :=
        congrArg (fun a => a ≫ chartInclusion d) (productMap_first eR d r F)
      _ = _ := (Category.assoc _ _ _).trans
        (congrArg (fun a => firstToChart eR r ≫ a) hFj)
  have hfull : iS ≫ f = windowFirst eR r W := by
    calc
      _ = L ≫ (i₀ ≫ f) := Category.assoc _ _ _
      _ = L ≫ windowFirst d r W₀ := congrArg (fun a => L ≫ a) hi₀sq
      _ = L ≫ (j₀ ≫ first d r) :=
        congrArg (fun a => L ≫ a) (window_first_square d r W₀).symm
      _ = (L ≫ j₀) ≫ first d r := (Category.assoc _ _ _).symm
      _ = M ≫ first d r := congrArg (fun a => a ≫ first d r) hLj
      _ = windowInclusion eR r W ≫ (PM ≫ first d r) := Category.assoc _ _ _
      _ = windowInclusion eR r W ≫ first eR r :=
        congrArg (fun a => windowInclusion eR r W ≫ a) hPMfirst
      _ = _ := window_first_square eR r W
  exact ⟨⟨OriginalNativeEmbeddingOpenPullback.coordinateOpen e j hj,
    OriginalNativeEmbeddingOpenPullback.coordinateOpen_subset e j hj,
    r,W,iS,hiS,s,hs,hiSV,hfull⟩⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothGivenTargetWindow
