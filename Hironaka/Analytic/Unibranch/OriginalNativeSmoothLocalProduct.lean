import Hironaka.Analytic.Unibranch.OriginalNativeProductWindow
import Hironaka.Resolution.HironakaSmoothSubmersionHistoricalCompanionMasks

/-! Standard native local-product analytic smoothness and actual ambient
submersion representations. No centre/history/algorithm field is included.
Blueprint first: `original-native-smooth-local-product.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeSmoothLocalProduct
noncomputable section
open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaActualSingularSubmersionPullback HironakaAuxiliaryGraphGeometry
  HironakaSmoothSubmersionHistoricalCompanionMasks HironakaSmoothSubmersionContactParameterCharts
  SourceReducedComplexSpace OriginalNativeProductWindow
open scoped ProductComplexManifold

variable {X Y : SourceReducedComplexSpace}

def productOpen (e : LocalEmbedding Y) (r : ℕ) (O : Opens (productSpace e r).obj.left) :
    LocallyRingedSpace := (productSpace e r).obj.left.restrict O.isOpenEmbedding

def productOpenInclusion (e : LocalEmbedding Y) (r : ℕ) (O : Opens (productSpace e r).obj.left) :
    productOpen e r O ⟶ (productSpace e r).obj.left :=
  (productSpace e r).obj.left.ofRestrict O.isOpenEmbedding

/-- Standard local-product smoothness, with full native maps and no ambient
representation, ideal comparison or algorithmic history as a field. -/
def IsSmoothAt (f : X ⟶ Y) (x : X.obj.left) : Prop :=
  ∃ (e : LocalEmbedding Y) (r : ℕ) (O : Opens (productSpace e r).obj.left)
    (j : productOpen e r O ⟶ X.obj.left),
    LocallyRingedSpace.IsOpenImmersion j ∧
      j ≫ f.hom.left = productOpenInclusion e r O ≫ (first e r).hom.left ∧ x ∈ range j.base

def IsSmoothMorphism (f : X ⟶ Y) : Prop := ∀ x : X.obj.left, IsSmoothAt f x

theorem local_product_scalar (f : X ⟶ Y) (e : LocalEmbedding Y) (r : ℕ)
    (O : Opens (productSpace e r).obj.left) (j : productOpen e r O ⟶ X.obj.left)
    (hsq : j ≫ f.hom.left = productOpenInclusion e r O ≫ (first e r).hom.left) :
    j ≫ X.obj.hom = productOpenInclusion e r O ≫ (productSpace e r).obj.hom := by
  calc
    _ = j ≫ (f.hom.left ≫ Y.obj.hom) := congrArg (fun k => j ≫ k) (Over.w f.hom).symm
    _ = (j ≫ f.hom.left) ≫ Y.obj.hom := (Category.assoc _ _ _).symm
    _ = (productOpenInclusion e r O ≫ (first e r).hom.left) ≫ Y.obj.hom :=
      congrArg (fun k => k ≫ Y.obj.hom) hsq
    _ = _ := (Category.assoc _ _ _).trans
      (congrArg (fun k => productOpenInclusion e r O ≫ k) (Over.w (first e r).hom))

private theorem openImmersion_lift_isOpenImmersion {A B C : LocallyRingedSpace}
    (a : A ⟶ C) (b : B ⟶ C) [LocallyRingedSpace.IsOpenImmersion a]
    [LocallyRingedSpace.IsOpenImmersion b] (hr : range b.base ⊆ range a.base) :
    LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift a b hr) := by
  let : IsIso (CategoryTheory.Limits.pullback.snd a b) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset a b hr
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

def targetCarrier (e : LocalEmbedding Y) (P : Opens e.ambient) : Set P :=
  (Subtype.val : P → e.ambient) ⁻¹' e.carrier

theorem targetCarrier_analytic (e : LocalEmbedding Y) (P : Opens e.ambient) :
    IsComplexAnalyticSubset (n := e.dim) (targetCarrier e P) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val e.analytic

def targetSpace (e : LocalEmbedding Y) (P : Opens e.ambient) : SourceReducedComplexSpace :=
  ofClosedAnalytic (targetCarrier e P) (targetCarrier_analytic e P)

def targetToChart (e : LocalEmbedding Y) (P : Opens e.ambient) : targetSpace e P ⟶ chartSpace e :=
  ObjectProperty.homMk (Over.homMk (actualOpenSubspaceMap e.carrier P)
    (actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)))

def targetInclusion (e : LocalEmbedding Y) (P : Opens e.ambient) : targetSpace e P ⟶ Y :=
  targetToChart e P ≫ chartInclusion e

theorem targetInclusion_isOpenImmersion (e : LocalEmbedding Y) (P : Opens e.ambient) :
    LocallyRingedSpace.IsOpenImmersion (targetInclusion e P).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion (actualOpenSubspaceMap e.carrier P ≫ e.map)
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (actualOpenSubspaceMap e.carrier P)
    (actualOpenSubspaceMap_isOpenImmersion e.carrier P) e.map e.isOpenImmersion

def ambientProjection (e : LocalEmbedding Y) (r : ℕ) (P : Opens e.ambient)
    (W : Opens (productAmbient e r)) (hWP : MapsTo (Prod.fst : productAmbient e r → e.ambient) W P) :
    W → P := fun w => ⟨w.val.1,hWP w.property⟩

theorem ambientProjection_isSubmersion (e : LocalEmbedding Y) (r : ℕ) (P : Opens e.ambient)
    (W : Opens (productAmbient e r)) (hWP : MapsTo (Prod.fst : productAmbient e r → e.ambient) W P) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (e.dim+r)) 𝓘(ℂ,ComplexModel e.dim) ∞
      (ambientProjection e r P W hWP) :=
  restrictedOpenMap_isSubmersion
    (X := BlowupTowers.CMfd.of (n := e.dim) e.ambient)
    (Y := BlowupTowers.CMfd.of (n := e.dim+r) (productAmbient e r))
    (isSubmersion_fst (n := e.dim) (m := r) (X := e.ambient) (Y := ComplexModel r)) W P hWP

def nativeProjection (e : LocalEmbedding Y) (r : ℕ) (P : Opens e.ambient)
    (W : Opens (productAmbient e r)) (hWP : MapsTo (Prod.fst : productAmbient e r → e.ambient) W P) :
    windowSpace e r W ⟶ targetSpace e P :=
  ObjectProperty.homMk (Over.homMk
    (actualSubspaceMap (ambientProjection_isSubmersion e r P W hWP).contMDiff (fun _ hx => hx))
    (actualSubspaceMap_point (ambientProjection_isSubmersion e r P W hWP).contMDiff (fun _ hx => hx)))

theorem nativeProjection_square (e : LocalEmbedding Y) (r : ℕ) (P : Opens e.ambient)
    (W : Opens (productAmbient e r)) (hWP : MapsTo (Prod.fst : productAmbient e r → e.ambient) W P) :
    nativeProjection e r P W hWP ≫ targetInclusion e P = windowFirst e r W := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  change actualSubspaceMap (ambientProjection_isSubmersion e r P W hWP).contMDiff (fun _ hx => hx) ≫
      (actualOpenSubspaceMap e.carrier P ≫ e.map) =
    actualSubspaceMap (windowProjection_holomorphic e r W) (fun _ hx => hx) ≫ e.map
  have hcomp := actualSubspaceMap_comp (n := e.dim+r) (m := e.dim) (p := e.dim)
    (C := windowCarrier e r W) (D := targetCarrier e P) (E := e.carrier)
    (f := ambientProjection e r P W hWP) (g := (Subtype.val : P → e.ambient))
    (ambientProjection_isSubmersion e r P W hWP).contMDiff contMDiff_subtype_val
    (fun _ hx => hx) (fun _ hx => hx)
  exact (Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ e.map) hcomp.symm)

theorem ambientProjection_whole_ideal (e : LocalEmbedding Y) (r : ℕ) (P : Opens e.ambient)
    (W : Opens (productAmbient e r)) (hWP : MapsTo (Prod.fst : productAmbient e r → e.ambient) W P) :
    GermIdeal.pullback (m := e.dim+r) (ambientProjection e r P W hWP)
        (vanishingIdeal (n := e.dim) (targetCarrier e P)) =
      vanishingIdeal (n := e.dim+r) (windowCarrier e r W) :=
  HironakaActualSingularSubmersionPullback.pullback_vanishingIdeal_submersion
    (ambientProjection_isSubmersion e r P W hWP) (targetCarrier e P)

/-- Ordinary native smoothness internally produces the actual ambient
submersion, full native maps, points, prescribed ranges and WHOLE ideals. -/
theorem exists_ambient_representation (f : X ⟶ Y) (x : X.obj.left)
    (hsm : IsSmoothAt f x) (V : Opens X.obj.left) (T : Opens Y.obj.left)
    (hxV : x ∈ V) (hfxT : f.hom.left.base x ∈ T) :
    ∃ (e : LocalEmbedding Y) (r : ℕ) (P : Opens e.ambient) (W : Opens (productAmbient e r))
      (hWP : MapsTo (Prod.fst : productAmbient e r → e.ambient) W P)
      (iS : windowSpace e r W ⟶ X) (s : (windowSpace e r W).obj.left),
      LocallyRingedSpace.IsOpenImmersion iS.hom.left ∧ iS.hom.left.base s = x ∧
      range iS.hom.left.base ⊆ (V : Set X.obj.left) ∧
      range (targetInclusion e P).hom.left.base ⊆ (T : Set Y.obj.left) ∧
      iS ≫ f = nativeProjection e r P W hWP ≫ targetInclusion e P ∧
      Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (e.dim+r)) 𝓘(ℂ,ComplexModel e.dim) ∞
        (ambientProjection e r P W hWP) ∧
      GermIdeal.pullback (m := e.dim+r) (ambientProjection e r P W hWP)
          (vanishingIdeal (n := e.dim) (targetCarrier e P)) =
        vanishingIdeal (n := e.dim+r) (windowCarrier e r W) := by
  classical
  obtain ⟨e,r,O,j,hj,hsq,u,hux⟩ := hsm
  let ι := productOpenInclusion e r O
  have hι : LocallyRingedSpace.IsOpenImmersion ι := by
    exact PresheafedSpace.IsOpenImmersion.ofRestrict
      (productSpace e r).obj.left.toPresheafedSpace O.isOpenEmbedding
  let : LocallyRingedSpace.IsOpenImmersion ι := hι
  let : LocallyRingedSpace.IsOpenImmersion j := hj
  let p₀ : (productSpace e r).obj.left := ι.base u
  let c : e.carrier := (pointEquiv e r p₀).1
  have hc : e.toPoint c = f.hom.left.base x := by
    have hp := congrArg (fun k => k.base u) hsq
    exact (first_point e r p₀).symm.trans (hp.symm.trans (congrArg f.hom.left.base hux))
  have htargetOpen : IsOpen (e.toPoint ⁻¹' (T : Set Y.obj.left)) :=
    T.isOpen.preimage e.isOpenEmbedding_toPoint.continuous
  obtain ⟨Pset,hPset,hPtrace⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp htargetOpen
  let P : Opens e.ambient := ⟨Pset,hPset⟩
  have hcP : c.val ∈ P := by
    change c ∈ (Subtype.val : e.carrier → e.ambient) ⁻¹' Pset
    rw [hPtrace]
    change e.toPoint c ∈ T
    rw [hc]
    exact hfxT
  let Vj : Opens (productOpen e r O) :=
    ⟨j.base ⁻¹' (V : Set X.obj.left),V.isOpen.preimage j.base.hom.continuous⟩
  let k := (productOpen e r O).ofRestrict Vj.isOpenEmbedding
  let g := k ≫ ι
  have hg : LocallyRingedSpace.IsOpenImmersion g := by
    dsimp only [g,k]
    infer_instance
  have hfirstContinuous : Continuous (fun p : (productSpace e r).obj.left => p.val.1) := by
    change Continuous (fun p : productCarrier e r => p.val.1)
    exact continuous_fst.comp continuous_subtype_val
  let Q : Opens (productSpace e r).obj.left :=
    ⟨range g.base ∩ {p | p.val.1 ∈ P},
      hg.base_open.isOpen_range.inter (P.isOpen.preimage hfirstContinuous)⟩
  have hp₀Q : p₀ ∈ Q := by
    refine ⟨?_,hcP⟩
    have hu : u ∈ Vj := by
      change j.base u ∈ V
      rw [hux]
      exact hxV
    exact ⟨(⟨u,hu⟩ : Vj),rfl⟩
  obtain ⟨W₀,hW₀,hW₀point⟩ := exists_window_of_native_open e r Q
  let WP : Opens (productAmbient e r) := ⟨Prod.fst ⁻¹' (P : Set e.ambient),
    P.isOpen.preimage continuous_fst⟩
  let W := W₀ ⊓ WP
  have hWP : MapsTo (Prod.fst : productAmbient e r → e.ambient) W P := fun _ hw => hw.2
  have hp₀W : p₀.val ∈ W := ⟨hW₀point p₀ hp₀Q,hp₀Q.2⟩
  let s : (windowSpace e r W).obj.left := ⟨⟨p₀.val,hp₀W⟩,p₀.property⟩
  let jW := (windowInclusion e r W).hom.left
  let : LocallyRingedSpace.IsOpenImmersion jW := windowInclusion_isOpenImmersion e r W
  have hrQ : range jW.base ⊆ (Q : Set (productSpace e r).obj.left) := by
    rintro _ ⟨w,rfl⟩
    change windowCarrier e r W at w
    let w₀ : windowCarrier e r W₀ := ⟨⟨w.val.val,w.val.property.1⟩,w.property⟩
    exact (Set.ext_iff.mp hW₀ _).mp ⟨w₀,rfl⟩
  have hrO : range jW.base ⊆ range ι.base := by
    intro p hp
    obtain ⟨v,hv⟩ := (hrQ hp).1
    exact ⟨k.base v,hv⟩
  let l := LocallyRingedSpace.IsOpenImmersion.lift ι jW hrO
  have hl : LocallyRingedSpace.IsOpenImmersion l := openImmersion_lift_isOpenImmersion ι jW hrO
  have hfac : l ≫ ι = jW := LocallyRingedSpace.IsOpenImmersion.lift_fac ι jW hrO
  have hjScalar := local_product_scalar f e r O j hsq
  have hsourceScalar : (l ≫ j) ≫ X.obj.hom = (windowSpace e r W).obj.hom := by
    calc
      _ = l ≫ (j ≫ X.obj.hom) := Category.assoc _ _ _
      _ = l ≫ (ι ≫ (productSpace e r).obj.hom) := congrArg (fun a => l ≫ a) hjScalar
      _ = (l ≫ ι) ≫ (productSpace e r).obj.hom := (Category.assoc _ _ _).symm
      _ = jW ≫ (productSpace e r).obj.hom :=
        congrArg (fun a => a ≫ (productSpace e r).obj.hom) hfac
      _ = _ := Over.w (windowInclusion e r W).hom
  let iS : windowSpace e r W ⟶ X := ObjectProperty.homMk (Over.homMk (l ≫ j) hsourceScalar)
  have hiS : LocallyRingedSpace.IsOpenImmersion iS.hom.left :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ l hl j hj
  have hs : iS.hom.left.base s = x := by
    have hls : l.base s = u := hι.base_open.injective (congrArg (fun a => a.base s) hfac)
    change j.base (l.base s) = x
    rw [hls]
    exact hux
  have hrV : range iS.hom.left.base ⊆ (V : Set X.obj.left) := by
    rintro _ ⟨w,rfl⟩
    obtain ⟨v,hv⟩ := (hrQ (show jW.base w ∈ range jW.base from ⟨w,rfl⟩)).1
    have he : l.base w = k.base v :=
      hι.base_open.injective ((congrArg (fun a => a.base w) hfac).trans hv.symm)
    change j.base (l.base w) ∈ V
    rw [he]
    exact v.property
  have hrT : range (targetInclusion e P).hom.left.base ⊆ (T : Set Y.obj.left) := by
    rintro _ ⟨p,rfl⟩
    change targetCarrier e P at p
    have hpC : p.val.val ∈ e.carrier := p.property
    have hp : (⟨p.val.val,hpC⟩ : e.carrier) ∈
        (Subtype.val : e.carrier → e.ambient) ⁻¹' Pset := p.val.property
    exact (Set.ext_iff.mp hPtrace _).mp hp
  have hnative : iS ≫ f = nativeProjection e r P W hWP ≫ targetInclusion e P := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    calc
      _ = l ≫ (j ≫ f.hom.left) := Category.assoc _ _ _
      _ = l ≫ (ι ≫ (first e r).hom.left) := congrArg (fun a => l ≫ a) hsq
      _ = (l ≫ ι) ≫ (first e r).hom.left := (Category.assoc _ _ _).symm
      _ = jW ≫ (first e r).hom.left := congrArg (fun a => a ≫ (first e r).hom.left) hfac
      _ = (windowFirst e r W).hom.left := congrArg (fun a => a.hom.left) (window_first_square e r W)
      _ = _ := congrArg (fun a => a.hom.left) (nativeProjection_square e r P W hWP).symm
  exact ⟨e,r,P,W,hWP,iS,s,hiS,hs,hrV,hrT,hnative,
    ambientProjection_isSubmersion e r P W hWP,ambientProjection_whole_ideal e r P W hWP⟩

theorem isSmoothMorphism_empty (f : X ⟶ Y) [IsEmpty X.obj.left] : IsSmoothMorphism f :=
  fun x => isEmptyElim x

/-- Actual native open immersions are the zero-free-dimensional local products. -/
theorem isSmoothMorphism_of_isOpenImmersion (f : X ⟶ Y)
    (hf : LocallyRingedSpace.IsOpenImmersion f.hom.left) : IsSmoothMorphism f := by
  intro x
  classical
  let : LocallyRingedSpace.IsOpenImmersion f.hom.left := hf
  let e := LocalEmbedding.ofPoint Y (f.hom.left.base x)
  obtain ⟨c,hc⟩ := LocalEmbedding.mem_range_ofPoint Y (f.hom.left.base x)
  let p : (productSpace e 0).obj.left := ⟨(c.val,0),c.property⟩
  have hp : (first e 0).hom.left.base p = f.hom.left.base x := (first_point e 0 p).trans hc
  let O : Opens (productSpace e 0).obj.left :=
    ⟨(first e 0).hom.left.base ⁻¹' range f.hom.left.base,
      hf.base_open.isOpen_range.preimage (first e 0).hom.left.base.hom.continuous⟩
  let ι := productOpenInclusion e 0 O
  have hι : LocallyRingedSpace.IsOpenImmersion ι :=
    PresheafedSpace.IsOpenImmersion.ofRestrict (productSpace e 0).obj.left.toPresheafedSpace
      O.isOpenEmbedding
  let : LocallyRingedSpace.IsOpenImmersion ι := hι
  let a := ι ≫ (first e 0).hom.left
  have ha : LocallyRingedSpace.IsOpenImmersion a :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ ι hι (first e 0).hom.left
      (zero_first_isOpenImmersion e)
  let : LocallyRingedSpace.IsOpenImmersion a := ha
  have hr : range a.base ⊆ range f.hom.left.base := by
    rintro _ ⟨q,rfl⟩
    change O at q
    exact q.property
  let j := LocallyRingedSpace.IsOpenImmersion.lift f.hom.left a hr
  have hj : LocallyRingedSpace.IsOpenImmersion j := openImmersion_lift_isOpenImmersion f.hom.left a hr
  have hsq : j ≫ f.hom.left = a := LocallyRingedSpace.IsOpenImmersion.lift_fac f.hom.left a hr
  let u : productOpen e 0 O := ⟨p,⟨x,hp.symm⟩⟩
  have hu : j.base u = x :=
    hf.base_open.injective ((congrArg (fun k => k.base u) hsq).trans hp)
  exact ⟨e,0,O,j,hj,hsq,u,hu⟩

theorem isSmoothMorphism_identity (X : SourceReducedComplexSpace) : IsSmoothMorphism (𝟙 X) := by
  apply isSmoothMorphism_of_isOpenImmersion
  change LocallyRingedSpace.IsOpenImmersion (𝟙 X.obj.left)
  infer_instance

end
end Hironaka.Analytic.Unibranch.OriginalNativeSmoothLocalProduct
