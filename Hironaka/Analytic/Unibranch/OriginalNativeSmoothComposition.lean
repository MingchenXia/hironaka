import Hironaka.Analytic.Unibranch.OriginalNativeProductAssociativity

/-! Ordinary native analytic smoothness is closed under actual composition.
Blueprint first: `original-native-smooth-composition.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothComposition
noncomputable section
open Hironaka Hironaka
  HironakaReducedComplexAnalyticSpaces SourceReducedComplexSpace
  OriginalNativeProductWindow OriginalNativeProductTransport OriginalNativeProductAssociativity
  OriginalNativeSmoothLocalProduct OriginalNativeSmoothAmbientConverse
open scoped ProductComplexManifold

variable {X Y Z A : SourceReducedComplexSpace}

private theorem lift_isOpenImmersion {B C D : LocallyRingedSpace}
    (i : B ⟶ D) (a : C ⟶ D) [LocallyRingedSpace.IsOpenImmersion i]
    [LocallyRingedSpace.IsOpenImmersion a] (hr : range a.base ⊆ range i.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift i a hr) := by
  let : IsIso (CategoryTheory.Limits.pullback.snd i a) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset i a hr
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

/-- A genuine common local source with complete product square gives standard smoothness. -/
theorem isSmoothAt_of_product_immersion (f : X ⟶ Y) (e : LocalEmbedding Y) (r : ℕ)
    (P : LocallyRingedSpace) (i : P ⟶ X.obj.left) (j : P ⟶ (productSpace e r).obj.left)
    (hi : LocallyRingedSpace.IsOpenImmersion i) (hj : LocallyRingedSpace.IsOpenImmersion j)
    (hsq : i ≫ f.hom.left = j ≫ (first e r).hom.left)
    (x : X.obj.left) (hx : x ∈ range i.base) : IsSmoothAt f x := by
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  let O : Opens (productSpace e r).obj.left := ⟨range j.base,hj.base_open.isOpen_range⟩
  let ι := productOpenInclusion e r O
  have hι : LocallyRingedSpace.IsOpenImmersion ι :=
    PresheafedSpace.IsOpenImmersion.ofRestrict (productSpace e r).obj.left.toPresheafedSpace O.isOpenEmbedding
  let : LocallyRingedSpace.IsOpenImmersion ι := hι
  have hr : range ι.base ⊆ range j.base := by
    rintro _ ⟨u,rfl⟩
    exact u.property
  let k := LocallyRingedSpace.IsOpenImmersion.lift j ι hr
  have hk : LocallyRingedSpace.IsOpenImmersion k := lift_isOpenImmersion j ι hr
  have hfac : k ≫ j = ι := LocallyRingedSpace.IsOpenImmersion.lift_fac j ι hr
  have hsource : LocallyRingedSpace.IsOpenImmersion (k ≫ i) :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ k hk i hi
  have hlocal : (k ≫ i) ≫ f.hom.left = ι ≫ (first e r).hom.left :=
    (Category.assoc _ _ _).trans ((congrArg (fun a => k ≫ a) hsq).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ (first e r).hom.left) hfac)))
  obtain ⟨s,hs⟩ := hx
  let u : productOpen e r O := ⟨j.base s,⟨s,rfl⟩⟩
  have hku : k.base u = s := hj.base_open.injective (congrArg (fun a => a.base u) hfac)
  refine ⟨e,r,O,k ≫ i,hsource,hlocal,u,?_⟩
  exact (congrArg i.base hku).trans hs

theorem isSmoothAt_of_precomp_openImmersion (i : A ⟶ X) (f : X ⟶ Y)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) (a : A.obj.left)
    (hsm : IsSmoothAt (i ≫ f) a) : IsSmoothAt f (i.hom.left.base a) := by
  obtain ⟨e,r,O,j,hj,hsq,u,hu⟩ := hsm
  refine ⟨e,r,O,j ≫ i.hom.left,
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ j hj i.hom.left hi,?_,u,?_⟩
  · exact (Category.assoc _ _ _).trans hsq
  · exact congrArg i.hom.left.base hu

theorem isSmoothAt_postcomp_openImmersion (f : X ⟶ Y) (i : Y ⟶ Z)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) (x : X.obj.left)
    (hsm : IsSmoothAt f x) : IsSmoothAt (f ≫ i) x := by
  obtain ⟨e,r,O,j,hj,hsq,hx⟩ := hsm
  let d : LocalEmbedding Z :=
    ⟨e.dim,e.ambient,e.carrier,e.analytic,e.map ≫ i.hom.left,
      @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ e.map e.isOpenImmersion i.hom.left hi,
      (Category.assoc _ _ _).trans ((congrArg (fun a => e.map ≫ a) (Over.w i.hom)).trans e.overPoint)⟩
  have hfirst : (first d r).hom.left = (first e r).hom.left ≫ i.hom.left :=
    (Category.assoc _ _ _).symm
  refine ⟨d,r,O,j,hj,?_,hx⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ i.hom.left) hsq).trans
      ((Category.assoc _ _ _).trans (congrArg (fun a => productOpenInclusion e r O ≫ a) hfirst.symm)))

theorem isSmoothMorphism_postcomp_openImmersion (f : X ⟶ Y) (i : Y ⟶ Z)
    (hf : IsSmoothMorphism f) (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left) :
    IsSmoothMorphism (f ≫ i) := fun x => isSmoothAt_postcomp_openImmersion f i hi x (hf x)

/-- Ordinary smoothness composes with the SAME true cylinder projection. -/
theorem isSmoothAt_comp_first (e : LocalEmbedding Y) (s : ℕ) (f : X ⟶ productSpace e s)
    (x : X.obj.left) (hsm : IsSmoothAt f x) : IsSmoothAt (f ≫ first e s) x := by
  obtain ⟨d,r,O,j,hj,hsq,hx⟩ := hsm
  let B := chartInclusion d ≫ (flatChartIso e s).inv
  have hInv : LocallyRingedSpace.IsOpenImmersion (flatChartIso e s).inv.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft (flatChartIso e s).symm).hom
    infer_instance
  have hB : LocallyRingedSpace.IsOpenImmersion B.hom.left :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ d.map d.isOpenImmersion
      (flatChartIso e s).inv.hom.left hInv
  let M := productMap d (flatChart e s) r B
  have hM : LocallyRingedSpace.IsOpenImmersion M.hom.left := productMap_isOpenImmersion d (flatChart e s) r B hB
  let H := M ≫ (associator e s r).hom
  have hAssoc : LocallyRingedSpace.IsOpenImmersion (associator e s r).hom.hom.left := by
    change LocallyRingedSpace.IsOpenImmersion (isoLeft (associator e s r)).hom
    infer_instance
  have hH : LocallyRingedSpace.IsOpenImmersion H.hom.left :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ M.hom.left hM (associator e s r).hom.hom.left hAssoc
  have hBfirst : B ≫ chartInclusion (flatChart e s) = chartInclusion d := by
    change (chartInclusion d ≫ (flatChartIso e s).inv) ≫ (flatChartIso e s).hom = chartInclusion d
    exact (Category.assoc _ _ _).trans ((congrArg (fun a => chartInclusion d ≫ a)
      (flatChartIso e s).inv_hom_id).trans (Category.comp_id _))
  have hproj : H ≫ first e (s+r) = first d r ≫ first e s := by
    calc
      _ = M ≫ (firstToChart (flatChart e s) r ≫ chartInclusion (flatChart e s) ≫ first e s) :=
        (Category.assoc _ _ _).trans (congrArg (fun a => M ≫ a) (associator_first e s r))
      _ = ((M ≫ firstToChart (flatChart e s) r) ≫ chartInclusion (flatChart e s)) ≫ first e s := by
        simp only [Category.assoc]
      _ = ((firstToChart d r ≫ B) ≫ chartInclusion (flatChart e s)) ≫ first e s :=
        congrArg (fun a => (a ≫ chartInclusion (flatChart e s)) ≫ first e s)
          (productMap_first d (flatChart e s) r B)
      _ = (firstToChart d r ≫ chartInclusion d) ≫ first e s :=
        congrArg (fun a => a ≫ first e s) ((Category.assoc _ _ _).trans
          (congrArg (fun a => firstToChart d r ≫ a) hBfirst))
      _ = _ := rfl
  let ι := productOpenInclusion d r O
  have hι : LocallyRingedSpace.IsOpenImmersion ι :=
    PresheafedSpace.IsOpenImmersion.ofRestrict (productSpace d r).obj.left.toPresheafedSpace O.isOpenEmbedding
  have htarget : LocallyRingedSpace.IsOpenImmersion (ι ≫ H.hom.left) :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ ι hι H.hom.left hH
  have hlocal : j ≫ (f ≫ first e s).hom.left = (ι ≫ H.hom.left) ≫ (first e (s+r)).hom.left := by
    calc
      _ = (j ≫ f.hom.left) ≫ (first e s).hom.left := (Category.assoc _ _ _).symm
      _ = (ι ≫ (first d r).hom.left) ≫ (first e s).hom.left := congrArg (fun a => a ≫ (first e s).hom.left) hsq
      _ = ι ≫ (first d r ≫ first e s).hom.left := Category.assoc _ _ _
      _ = ι ≫ (H ≫ first e (s+r)).hom.left := congrArg (fun a => ι ≫ a.hom.left) hproj.symm
      _ = _ := (Category.assoc _ _ _).symm
  exact isSmoothAt_of_product_immersion (f ≫ first e s) e (s+r) (productOpen d r O)
    j (ι ≫ H.hom.left) hj htarget hlocal x hx

theorem nativeProjection_isSmooth (e : LocalEmbedding Y) (r : ℕ) (P : Opens e.ambient)
    (W : Opens (productAmbient e r)) (hWP : MapsTo (Prod.fst : productAmbient e r → e.ambient) W P) :
    IsSmoothMorphism (nativeProjection e r P W hWP) :=
  isSmoothMorphism_subspaceMorphism (ambientProjection_isSubmersion e r P W hWP)
    (windowCarrier_analytic e r W) (targetCarrier_analytic e P) rfl

private theorem exists_native_open_lift {B C D : SourceReducedComplexSpace} (i : B ⟶ D) (a : C ⟶ D)
    (hi : LocallyRingedSpace.IsOpenImmersion i.hom.left)
    (ha : LocallyRingedSpace.IsOpenImmersion a.hom.left)
    (hr : range a.hom.left.base ⊆ range i.hom.left.base) :
    ∃ k : C ⟶ B, LocallyRingedSpace.IsOpenImmersion k.hom.left ∧ k ≫ i = a := by
  let : LocallyRingedSpace.IsOpenImmersion i.hom.left := hi
  let : LocallyRingedSpace.IsOpenImmersion a.hom.left := ha
  let l := LocallyRingedSpace.IsOpenImmersion.lift i.hom.left a.hom.left hr
  have hfac : l ≫ i.hom.left = a.hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  have hp : l ≫ B.obj.hom = C.obj.hom := by
    calc
      _ = l ≫ (i.hom.left ≫ D.obj.hom) := congrArg (fun t => l ≫ t) (Over.w i.hom).symm
      _ = (l ≫ i.hom.left) ≫ D.obj.hom := (Category.assoc _ _ _).symm
      _ = a.hom.left ≫ D.obj.hom := congrArg (fun t => t ≫ D.obj.hom) hfac
      _ = _ := Over.w a.hom
  let k : C ⟶ B := ObjectProperty.homMk (Over.homMk l hp)
  refine ⟨k,lift_isOpenImmersion i.hom.left a.hom.left hr,?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hfac

/-- Composition from ordinary native smoothness alone, on the SAME original full maps. -/
theorem isSmoothAt_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.obj.left)
    (hf : IsSmoothAt f x) (hg : IsSmoothAt g (f.hom.left.base x)) : IsSmoothAt (f ≫ g) x := by
  obtain ⟨e,s,P,W,hWP,iG,sG,hiG,hsG,_hGrange,_hGtarget,hGsq,_hGsub,_hGideal⟩ :=
    exists_ambient_representation g (f.hom.left.base x) hg ⊤ ⊤ (mem_univ _) (mem_univ _)
  let T : Opens Y.obj.left := ⟨range iG.hom.left.base,hiG.base_open.isOpen_range⟩
  have hxT : f.hom.left.base x ∈ T := ⟨sG,hsG⟩
  obtain ⟨d,r,Q,V,hVQ,iF,sF,hiF,hsF,_hFrange,hFtarget,hFsq,_hFsub,_hFideal⟩ :=
    exists_ambient_representation f x hf ⊤ T (mem_univ _) hxT
  obtain ⟨k,hk,hki⟩ := exists_native_open_lift iG (targetInclusion d Q) hiG
    (targetInclusion_isOpenImmersion d Q) hFtarget
  let h := (nativeProjection d r Q V hVQ ≫ k) ≫ windowInclusion e s W
  have hh : IsSmoothMorphism h := isSmoothMorphism_postcomp_openImmersion
    (nativeProjection d r Q V hVQ ≫ k) (windowInclusion e s W)
    (isSmoothMorphism_postcomp_openImmersion (nativeProjection d r Q V hVQ) k
      (nativeProjection_isSmooth d r Q V hVQ) hk) (windowInclusion_isOpenImmersion e s W)
  have hcomp : IsSmoothAt (h ≫ first e s) sF := isSmoothAt_comp_first e s h sF (hh sF)
  have hGfirst : iG ≫ g = windowFirst e s W := hGsq.trans (nativeProjection_square e s P W hWP)
  have hfull : iF ≫ (f ≫ g) = h ≫ first e s := by
    calc
      _ = (iF ≫ f) ≫ g := (Category.assoc _ _ _).symm
      _ = (nativeProjection d r Q V hVQ ≫ targetInclusion d Q) ≫ g := congrArg (fun a => a ≫ g) hFsq
      _ = (nativeProjection d r Q V hVQ ≫ (k ≫ iG)) ≫ g :=
        congrArg (fun a => (nativeProjection d r Q V hVQ ≫ a) ≫ g) hki.symm
      _ = (nativeProjection d r Q V hVQ ≫ k) ≫ (iG ≫ g) := by simp only [Category.assoc]
      _ = (nativeProjection d r Q V hVQ ≫ k) ≫ windowFirst e s W :=
        congrArg (fun a => (nativeProjection d r Q V hVQ ≫ k) ≫ a) hGfirst
      _ = (nativeProjection d r Q V hVQ ≫ k) ≫ (windowInclusion e s W ≫ first e s) :=
        congrArg (fun a => (nativeProjection d r Q V hVQ ≫ k) ≫ a) (window_first_square e s W).symm
      _ = _ := (Category.assoc _ _ _).symm
  have hlocal : IsSmoothAt (iF ≫ (f ≫ g)) sF :=
    Eq.mp (congrArg (fun a => IsSmoothAt a sF) hfull.symm) hcomp
  have hsource : IsSmoothAt (f ≫ g) (iF.hom.left.base sF) :=
    isSmoothAt_of_precomp_openImmersion iF (f ≫ g) hiF sF hlocal
  exact Eq.mp (congrArg (fun a => IsSmoothAt (f ≫ g) a) hsF) hsource

theorem isSmoothMorphism_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsSmoothMorphism f) (hg : IsSmoothMorphism g) : IsSmoothMorphism (f ≫ g) :=
  fun x => isSmoothAt_comp f g x (hf x) (hg (f.hom.left.base x))

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothComposition
