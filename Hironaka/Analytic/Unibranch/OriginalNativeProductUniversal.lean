import Hironaka.Analytic.Unibranch.OriginalNativeSmoothAmbientConverse
import Hironaka.Analytic.Unibranch.SourceMorphismExt

/-! The actual native reduced cylinder has the ordinary full product universal
property. Blueprint first: `original-native-product-universal.tex`. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeProductUniversal
noncomputable section
open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaActualAnalyticSubspaceLocalFunctions
  HironakaReducedComplexAnalyticSpaces HironakaResolutionSpaceComplex HironakaAuxiliaryGraphGeometry
  HironakaIntrinsicMorphismGluing HironakaIntrinsicMorphismGluingAnalytic
  SourceReducedComplexSpace OriginalNativeModification OriginalNativeProductWindow
open scoped ProductComplexManifold

variable {X A : SourceReducedComplexSpace} (e : LocalEmbedding X) (r : ℕ)
  (F : A ⟶ chartSpace e) (G : A ⟶ wholeModel (n := r) (ComplexModel r))

/-- Ordinary full native maps internally construct true local quotient pairs. -/
theorem exists_local_pair (x : A.obj.left) :
    ∃ (P : ReducedComplexAnalyticSpace) (j : P.obj.left ⟶ A.obj.left)
      (K : P.obj.left ⟶ (productSpace e r).obj.left),
      LocallyRingedSpace.IsOpenImmersion j ∧ x ∈ range j.base ∧
      j ≫ A.obj.hom = P.obj.hom ∧ K ≫ (productSpace e r).obj.hom = P.obj.hom ∧
      K ≫ (firstToChart e r).hom.left = j ≫ F.hom.left ∧
      K ≫ (second e r).hom.left = j ≫ G.hom.left := by
  let a := LocalEmbedding.ofPoint A x
  obtain ⟨c,hcx⟩ := LocalEmbedding.mem_range_ofPoint A x
  let ef : LocalEmbedding (chartSpace e) :=
    ⟨e.dim,e.ambient,e.carrier,e.analytic,𝟙 _,by
      change LocallyRingedSpace.IsOpenImmersion (𝟙 (actualSubspaceLocallyRingedSpace (n := e.dim) e.carrier))
      infer_instance,Category.id_comp _⟩
  let eg := LocalEmbedding.ofChart (univ : Set (ComplexModel r))
    (isComplexAnalyticSubset_univ (n := r)) (G.hom.left.base x).val
  have hFp : (a.map ≫ F.hom.left) ≫ (chartSpace e).obj.hom = subspacePointMap (n := a.dim) a.carrier :=
    (Category.assoc _ _ _).trans ((congrArg (fun t => a.map ≫ t) (Over.w F.hom)).trans a.overPoint)
  have hGp : (a.map ≫ G.hom.left) ≫ (wholeModel (n := r) (ComplexModel r)).obj.hom =
      subspacePointMap (n := a.dim) a.carrier :=
    (Category.assoc _ _ _).trans ((congrArg (fun t => a.map ≫ t) (Over.w G.hom)).trans a.overPoint)
  have hcF : (a.map ≫ F.hom.left).base c ∈ range ef.toPoint := ⟨F.hom.left.base (a.map.base c),rfl⟩
  have hcG : (a.map ≫ G.hom.left).base c ∈ range eg.toPoint := by
    change G.hom.left.base (a.toPoint c) ∈ range eg.toPoint
    rw [hcx]
    exact mem_range_chartModelMap (n := r) univ (G.hom.left.base x).property
  obtain ⟨OF,hcFopen,f,hf,hfpoint⟩ := LocalEmbedding.exists_contMDiff_factor
    (a.map ≫ F.hom.left) hFp ef c hcF
  obtain ⟨OG,hcGopen,g,hg,hgpoint⟩ := LocalEmbedding.exists_contMDiff_factor
    (a.map ≫ G.hom.left) hGp eg c hcG
  let O := OF ⊓ OG
  let S : Set O := (Subtype.val : O → a.ambient) ⁻¹' a.carrier
  let j₀ := actualOpenSubspaceMap (n := a.dim) a.carrier O
  let j := j₀ ≫ a.map
  have hj : LocallyRingedSpace.IsOpenImmersion j :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ j₀
      (actualOpenSubspaceMap_isOpenImmersion a.carrier O) a.map a.isOpenImmersion
  have hjp : j ≫ A.obj.hom = subspacePointMap (n := a.dim) S :=
    (Category.assoc _ _ _).trans ((congrArg (fun t => j₀ ≫ t) a.overPoint).trans
      (actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx)))
  have hP : hasAnalyticCharts (Over.mk (subspacePointMap (n := a.dim) S)) :=
    @hasAnalyticCharts_of_openImmersion _ _ (subspacePointMap (n := a.dim) S)
      (subspacePointMap (n := a.dim) a.carrier)
      (hasAnalyticCharts_model a.ambient a.carrier a.analytic) j₀
      (actualOpenSubspaceMap_isOpenImmersion a.carrier O)
      (actualSubspaceMap_point contMDiff_subtype_val (fun _ hx => hx))
  let P : ReducedComplexAnalyticSpace := ⟨Over.mk (subspacePointMap (n := a.dim) S),hP⟩
  let f₀ : O → e.ambient := f ∘ Opens.inclusion inf_le_left
  let g₀ : O → ComplexModel r := fun u =>
    ((chartDiffeo (n := r) (G.hom.left.base x).val).symm (g (Opens.inclusion inf_le_right u))).val
  have hf₀ : ContMDiff 𝓘(ℂ,ComplexModel a.dim) 𝓘(ℂ,ComplexModel e.dim) ∞ f₀ :=
    hf.comp (contMDiff_inclusion inf_le_left)
  have hg₀ : ContMDiff 𝓘(ℂ,ComplexModel a.dim) 𝓘(ℂ,ComplexModel r) ∞ g₀ :=
    contMDiff_subtype_val.comp ((chartDiffeo (n := r) (G.hom.left.base x).val).symm.contMDiff.comp
      (hg.comp (contMDiff_inclusion inf_le_right)))
  have hf₀point (s : S) : f₀ s.val = (F.hom.left.base (j.base s)).val := by
    obtain ⟨z,hzf,hzF⟩ := hfpoint (j₀.base s) s.val.property.1
    exact hzf.symm.trans (congrArg Subtype.val hzF)
  have hg₀point (s : S) : g₀ s.val = (G.hom.left.base (j.base s)).val := by
    obtain ⟨z,hzg,hzG⟩ := hgpoint (j₀.base s) s.val.property.2
    have hzg' : g (Opens.inclusion inf_le_right s.val) = z.val := hzg.symm
    have hcoordinate : g₀ s.val = (eg.toPoint z).val :=
      congrArg (fun v : eg.ambient =>
        ((chartDiffeo (n := r) (G.hom.left.base x).val).symm v).val) hzg'
    exact hcoordinate.trans (congrArg Subtype.val hzG)
  let k : O → productAmbient e r := fun u => (f₀ u,g₀ u)
  have hk : ContMDiff 𝓘(ℂ,ComplexModel a.dim) 𝓘(ℂ,ComplexModel (e.dim+r)) ∞ k :=
    ProductComplexManifold.contMDiff_prodMk hf₀ hg₀
  have hland : ∀ u ∈ S, k u ∈ productCarrier e r := by
    intro u hu
    change f₀ u ∈ e.carrier
    rw [hf₀point ⟨u,hu⟩]
    exact (F.hom.left.base (j.base (⟨u,hu⟩ : S))).property
  let K : P.obj.left ⟶ (productSpace e r).obj.left := actualSubspaceMap hk hland
  have hKp : K ≫ (productSpace e r).obj.hom = P.obj.hom := actualSubspaceMap_point hk hland
  have hfirst : K ≫ (firstToChart e r).hom.left = j ≫ F.hom.left := by
    apply actualSubspaceMap_eq_of_base_eq
    · exact (Category.assoc _ _ _).trans ((congrArg (fun t => K ≫ t) (Over.w (firstToChart e r).hom)).trans hKp)
    · exact (Category.assoc _ _ _).trans ((congrArg (fun t => j ≫ t) (Over.w F.hom)).trans hjp)
    · ext s
      exact Subtype.ext (hf₀point s)
  have hsecond : K ≫ (second e r).hom.left = j ≫ G.hom.left := by
    apply actualSubspaceMap_eq_of_base_eq
    · exact (Category.assoc _ _ _).trans ((congrArg (fun t => K ≫ t) (Over.w (second e r).hom)).trans hKp)
    · exact (Category.assoc _ _ _).trans ((congrArg (fun t => j ≫ t) (Over.w G.hom)).trans hjp)
    · ext s
      exact Subtype.ext (hg₀point s)
  exact ⟨P,j,K,hj,⟨⟨⟨c.val,⟨hcFopen,hcGopen⟩⟩,c.property⟩,hcx⟩,hjp,hKp,hfirst,hsecond⟩

/-- The actual cylinder is a full native product, with ordinary arbitrary original source. -/
theorem exists_unique_pair : ∃! H : A ⟶ productSpace e r,
    H ≫ firstToChart e r = F ∧ H ≫ second e r = G := by
  classical
  choose P j K hj hx hjp hKp hfirst hsecond using exists_local_pair e r F G
  let : ∀ x, LocallyRingedSpace.IsOpenImmersion (j x) := hj
  have hcover : ∀ z : A.obj.left, ∃ (x : A.obj.left) (u : (P x).obj.left), (j x).base u = z := by
    intro z
    obtain ⟨u,hu⟩ := hx z
    exact ⟨z,u,hu⟩
  have hcompat (x y : A.obj.left) : pullback.fst (j x) (j y) ≫ K x =
      pullback.snd (j x) (j y) ≫ K y := by
    let l := pullback.fst (j x) (j y)
    let q := pullback.snd (j x) (j y)
    let σ := l ≫ (P x).obj.hom
    have hcharts : hasAnalyticCharts (Over.mk σ) :=
      hasAnalyticCharts_of_openImmersion σ (P x).obj.hom (P x).property l rfl
    have hleft : (l ≫ K x) ≫ (productSpace e r).obj.hom = σ :=
      (Category.assoc _ _ _).trans (congrArg (fun a => l ≫ a) (hKp x))
    have hright : (q ≫ K y) ≫ (productSpace e r).obj.hom = σ := by
      calc
        _ = q ≫ (P y).obj.hom := (Category.assoc _ _ _).trans (congrArg (fun a => q ≫ a) (hKp y))
        _ = q ≫ (j y ≫ A.obj.hom) := congrArg (fun a => q ≫ a) (hjp y).symm
        _ = (q ≫ j y) ≫ A.obj.hom := (Category.assoc _ _ _).symm
        _ = (l ≫ j x) ≫ A.obj.hom := congrArg (fun a => a ≫ A.obj.hom) pullback.condition.symm
        _ = _ := (Category.assoc _ _ _).trans (congrArg (fun a => l ≫ a) (hjp x))
    have hfst : (l ≫ K x) ≫ (firstToChart e r).hom.left =
        (q ≫ K y) ≫ (firstToChart e r).hom.left := by
      calc
        _ = (l ≫ j x) ≫ F.hom.left :=
          (Category.assoc _ _ _).trans ((congrArg (fun a => l ≫ a) (hfirst x)).trans (Category.assoc _ _ _).symm)
        _ = (q ≫ j y) ≫ F.hom.left := congrArg (fun a => a ≫ F.hom.left) pullback.condition
        _ = _ := ((Category.assoc _ _ _).trans
          ((congrArg (fun a => q ≫ a) (hfirst y)).trans (Category.assoc _ _ _).symm)).symm
    have hsnd : (l ≫ K x) ≫ (second e r).hom.left =
        (q ≫ K y) ≫ (second e r).hom.left := by
      calc
        _ = (l ≫ j x) ≫ G.hom.left :=
          (Category.assoc _ _ _).trans ((congrArg (fun a => l ≫ a) (hsecond x)).trans (Category.assoc _ _ _).symm)
        _ = (q ≫ j y) ≫ G.hom.left := congrArg (fun a => a ≫ G.hom.left) pullback.condition
        _ = _ := ((Category.assoc _ _ _).trans
          ((congrArg (fun a => q ≫ a) (hsecond y)).trans (Category.assoc _ _ _).symm)).symm
    apply HironakaIntrinsicMorphismGluingAnalytic.morphism_eq_of_base_eq σ hcharts
      (l ≫ K x) (q ≫ K y) hleft hright
    ext z
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val (congrArg (fun a => a.base z) hfst)
    · exact congrArg Subtype.val (congrArg (fun a => a.base z) hsnd)
  have hpoint (x : A.obj.left) : K x ≫ (productSpace e r).obj.hom = j x ≫ A.obj.hom :=
    (hKp x).trans (hjp x).symm
  obtain ⟨H,hH,_⟩ := exists_unique_over (fun x => (P x).obj.left) j hcover A.obj.hom
    (productSpace e r).obj.hom K hcompat hpoint
  let HH : A ⟶ productSpace e r := ObjectProperty.homMk H
  have hHF : HH ≫ firstToChart e r = F := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply HironakaIntrinsicMorphismGluing.hom_ext (fun x => (P x).obj.left) j hcover
    intro x
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ (firstToChart e r).hom.left) (hH x)).trans (hfirst x))
  have hHG : HH ≫ second e r = G := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply HironakaIntrinsicMorphismGluing.hom_ext (fun x => (P x).obj.left) j hcover
    intro x
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ (second e r).hom.left) (hH x)).trans (hsecond x))
  refine ⟨HH,⟨hHF,hHG⟩,?_⟩
  intro H' hH'
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg Subtype.val
      (congrArg (fun a => a.hom.left.base z) (hH'.1.trans hHF.symm))
  · exact congrArg Subtype.val
      (congrArg (fun a => a.hom.left.base z) (hH'.2.trans hHG.symm))

end
end Hironaka.Analytic.Unibranch.OriginalNativeProductUniversal
