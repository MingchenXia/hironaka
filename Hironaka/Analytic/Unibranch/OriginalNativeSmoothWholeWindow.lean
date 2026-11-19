import Hironaka.Analytic.Unibranch.OriginalNativeManifoldOpenImage
import Hironaka.Analytic.Unibranch.OriginalLocalCanonicalResolutionCover

/-! Ordinary smoothness at a regular image constructs genuine whole manifold windows.
Blueprint first: `original-native-smooth-whole-window.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothWholeWindow
noncomputable section
open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicComplexAnalyticRegularLocus SourceReducedComplexSpace OriginalNativeModification
  OriginalNativeProductWindow OriginalNativeProductTransport OriginalNativeSmoothLocalProduct
  OriginalNativeSmoothOpenLocality OriginalLocalCanonicalResolutionCover
open scoped ProductComplexManifold

variable {X Y : SourceReducedComplexSpace}

private def carrierEqIso {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {C D : Set M}
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D) (hCD : C = D) :
    ofClosedAnalytic C hC ≅ ofClosedAnalytic D hD := by
  cases hCD
  exact Iso.refl _

private theorem carrierEqIso_point {n : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M] {C D : Set M}
    (hC : IsComplexAnalyticSubset (n := n) C) (hD : IsComplexAnalyticSubset (n := n) D)
    (hCD : C = D) (z : C) : ((carrierEqIso hC hD hCD).hom.hom.left.base z).val = z.val := by
  cases hCD
  rfl

def wholeChartIso (e : LocalEmbedding Y) (he : e.carrier = univ) :
    wholeModel (n := e.dim) e.ambient ≅ chartSpace e :=
  carrierEqIso (isComplexAnalyticSubset_univ (n := e.dim)) e.analytic he.symm

def wholeWindowIso (e : LocalEmbedding Y) (he : e.carrier = univ) (r : ℕ)
    (W : Opens (productAmbient e r)) : wholeModel (n := e.dim+r) W ≅ windowSpace e r W :=
  carrierEqIso (isComplexAnalyticSubset_univ (n := e.dim+r)) (windowCarrier_analytic e r W)
    (by simp only [windowCarrier,productCarrier,he,Set.preimage_univ])

private theorem wholeChartIso_point (e : LocalEmbedding Y) (he : e.carrier = univ)
    (z : (univ : Set e.ambient)) : ((wholeChartIso e he).hom.hom.left.base z).val = z.val :=
  carrierEqIso_point _ _ _ z

private theorem wholeWindowIso_point (e : LocalEmbedding Y) (he : e.carrier = univ) (r : ℕ)
    (W : Opens (productAmbient e r)) (z : (univ : Set W)) :
    ((wholeWindowIso e he r W).hom.hom.left.base z).val = z.val :=
  carrierEqIso_point _ _ _ z

/-- Actual geometric output with whole source/target models and the SAME full original square. -/
structure WholeWindow (f : X ⟶ Y) (x : X.obj.left) where
  target : LocalEmbedding Y
  whole : target.carrier = univ
  rank : ℕ
  window : Opens (productAmbient target rank)
  sourceMap : wholeModel (n := target.dim+rank) window ⟶ X
  targetMap : wholeModel (n := target.dim) target.ambient ⟶ Y
  source_open : LocallyRingedSpace.IsOpenImmersion sourceMap.hom.left
  target_open : LocallyRingedSpace.IsOpenImmersion targetMap.hom.left
  sourcePoint : window
  point : sourceMap.hom.left.base ⟨sourcePoint,mem_univ _⟩ = x
  square : sourceMap ≫ f = nativeMorphism (windowProjection_holomorphic target rank window) ≫ targetMap

private theorem lift_isOpenImmersion {B C D : LocallyRingedSpace}
    (i : B ⟶ D) (a : C ⟶ D) [LocallyRingedSpace.IsOpenImmersion i]
    [LocallyRingedSpace.IsOpenImmersion a] (hr : range a.base ⊆ range i.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift i a hr) := by
  let : IsIso (CategoryTheory.Limits.pullback.snd i a) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset i a hr
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

/-- No chart, product window or representation is supplied as an input. -/
theorem exists_whole_window (f : X ⟶ Y) (x : X.obj.left) (hsm : IsSmoothAt f x)
    (hreg : f.hom.left.base x ∈ intrinsicRegularLocus Y.obj) : Nonempty (WholeWindow f x) := by
  obtain ⟨d,r,O,j,hj,hsq,u,hu⟩ := hsm
  let c : d.carrier := ⟨u.val.val.1,u.val.property⟩
  have hc : d.toPoint c = f.hom.left.base x :=
    (congrArg (fun a => a.base u) hsq).symm.trans (congrArg f.hom.left.base hu)
  let T : Opens Y.obj.left := ⟨range d.toPoint,d.isOpenEmbedding_toPoint.isOpen_range⟩
  obtain ⟨e,cE,hcE,hrE,he⟩ := exists_whole_localEmbedding_of_regular Y (f.hom.left.base x) hreg T ⟨c,hc⟩
  obtain ⟨B,hB,hBfac⟩ := exists_native_open_lift (chartInclusion d) (chartInclusion e)
    d.isOpenImmersion e.isOpenImmersion hrE
  have hBc : B.hom.left.base cE = c := d.toPoint_injective
    ((congrArg (fun a => a.hom.left.base cE) hBfac).trans (hcE.trans hc.symm))
  let PM := productMap e d r B
  have hPM : LocallyRingedSpace.IsOpenImmersion PM.hom.left := productMap_isOpenImmersion e d r B hB
  let p₀ : (productSpace e r).obj.left := ⟨(cE.val,u.val.val.2),cE.property⟩
  have hp₀ : PM.hom.left.base p₀ = u.val := by
    apply Subtype.ext
    exact (productMap_point e d r B p₀).trans (Prod.ext (congrArg Subtype.val hBc) rfl)
  let Opre : Opens (productSpace e r).obj.left :=
    ⟨PM.hom.left.base ⁻¹' (O : Set (productSpace d r).obj.left),
      O.isOpen.preimage PM.hom.left.base.hom.continuous⟩
  have hpO : p₀ ∈ Opre := Eq.mpr (congrArg (fun a => a ∈ O) hp₀) u.property
  obtain ⟨W,hW,hWpoint⟩ := exists_window_of_native_open e r Opre
  let s : (windowSpace e r W).obj.left := ⟨⟨p₀.val,hWpoint p₀ hpO⟩,p₀.property⟩
  let M := windowInclusion e r W ≫ PM
  have hM : LocallyRingedSpace.IsOpenImmersion M.hom.left :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (windowInclusion e r W).hom.left
      (windowInclusion_isOpenImmersion e r W) PM.hom.left hPM
  let ι := productOpenInclusion d r O
  have hι : LocallyRingedSpace.IsOpenImmersion ι :=
    PresheafedSpace.IsOpenImmersion.ofRestrict (productSpace d r).obj.left.toPresheafedSpace O.isOpenEmbedding
  let : LocallyRingedSpace.IsOpenImmersion ι := hι
  let : LocallyRingedSpace.IsOpenImmersion M.hom.left := hM
  have hr : range M.hom.left.base ⊆ range ι.base := by
    rintro _ ⟨w,rfl⟩
    have hw : (windowInclusion e r W).hom.left.base w ∈ Opre :=
      (Set.ext_iff.mp hW _).mp ⟨w,rfl⟩
    exact ⟨⟨M.hom.left.base w,hw⟩,rfl⟩
  let l := LocallyRingedSpace.IsOpenImmersion.lift ι M.hom.left hr
  have hl : LocallyRingedSpace.IsOpenImmersion l := lift_isOpenImmersion ι M.hom.left hr
  have hfac : l ≫ ι = M.hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  have hjscalar := local_product_scalar f d r O j hsq
  have hscalar : (l ≫ j) ≫ X.obj.hom = (windowSpace e r W).obj.hom := by
    calc
      _ = l ≫ (j ≫ X.obj.hom) := Category.assoc _ _ _
      _ = l ≫ (ι ≫ (productSpace d r).obj.hom) := congrArg (fun a => l ≫ a) hjscalar
      _ = (l ≫ ι) ≫ (productSpace d r).obj.hom := (Category.assoc _ _ _).symm
      _ = M.hom.left ≫ (productSpace d r).obj.hom := congrArg (fun a => a ≫ (productSpace d r).obj.hom) hfac
      _ = _ := Over.w M.hom
  let iS : windowSpace e r W ⟶ X := ObjectProperty.homMk (Over.homMk (l ≫ j) hscalar)
  have hiS : LocallyRingedSpace.IsOpenImmersion iS.hom.left :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ l hl j hj
  have hPMfirst : PM ≫ first d r = first e r := by
    calc
      _ = (PM ≫ firstToChart d r) ≫ chartInclusion d := (Category.assoc _ _ _).symm
      _ = (firstToChart e r ≫ B) ≫ chartInclusion d :=
        congrArg (fun a => a ≫ chartInclusion d) (productMap_first e d r B)
      _ = _ := (Category.assoc _ _ _).trans (congrArg (fun a => firstToChart e r ≫ a) hBfac)
  have hnative : iS ≫ f = windowFirst e r W := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    calc
      _ = l ≫ (j ≫ f.hom.left) := Category.assoc _ _ _
      _ = l ≫ (ι ≫ (first d r).hom.left) := congrArg (fun a => l ≫ a) hsq
      _ = (l ≫ ι) ≫ (first d r).hom.left := (Category.assoc _ _ _).symm
      _ = M.hom.left ≫ (first d r).hom.left := congrArg (fun a => a ≫ (first d r).hom.left) hfac
      _ = (windowInclusion e r W ≫ (PM ≫ first d r)).hom.left := Category.assoc _ _ _
      _ = (windowInclusion e r W ≫ first e r).hom.left :=
        congrArg (fun a => (windowInclusion e r W ≫ a).hom.left) hPMfirst
      _ = _ := congrArg (fun a => a.hom.left) (window_first_square e r W)
  have hls : l.base s = u := hι.base_open.injective
    ((congrArg (fun a => a.base s) hfac).trans hp₀)
  have hs : iS.hom.left.base s = x := (congrArg j.base hls).trans hu
  let i := (wholeWindowIso e he r W).hom ≫ iS
  let k := (wholeChartIso e he).hom ≫ chartInclusion e
  have hi : LocallyRingedSpace.IsOpenImmersion i.hom.left := by
    have hI : LocallyRingedSpace.IsOpenImmersion (wholeWindowIso e he r W).hom.hom.left := by
      change LocallyRingedSpace.IsOpenImmersion (isoLeft (wholeWindowIso e he r W)).hom
      infer_instance
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ hI _ hiS
  have hk : LocallyRingedSpace.IsOpenImmersion k.hom.left := by
    have hK : LocallyRingedSpace.IsOpenImmersion (wholeChartIso e he).hom.hom.left := by
      change LocallyRingedSpace.IsOpenImmersion (isoLeft (wholeChartIso e he)).hom
      infer_instance
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ hK _ e.isOpenImmersion
  have hwholeSquare : i ≫ f = nativeMorphism (windowProjection_holomorphic e r W) ≫ k := by
    calc
      _ = (wholeWindowIso e he r W).hom ≫ windowFirst e r W :=
        (Category.assoc _ _ _).trans (congrArg (fun a => (wholeWindowIso e he r W).hom ≫ a) hnative)
      _ = _ := by
        apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
        intro z
        apply congrArg e.toPoint
        apply Subtype.ext
        exact (congrArg (fun w : W => w.val.1) (wholeWindowIso_point e he r W z)).trans
          (wholeChartIso_point e he ((nativeMorphism (windowProjection_holomorphic e r W)).hom.left.base z)).symm
  have hipoint : i.hom.left.base ⟨s.val,mem_univ _⟩ = x := by
    have hsp : (wholeWindowIso e he r W).hom.hom.left.base ⟨s.val,mem_univ _⟩ = s :=
      Subtype.ext (wholeWindowIso_point e he r W ⟨s.val,mem_univ _⟩)
    exact (congrArg iS.hom.left.base hsp).trans hs
  exact ⟨⟨e,he,r,W,i,k,hi,hk,s.val,hipoint,hwholeSquare⟩⟩

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothWholeWindow
