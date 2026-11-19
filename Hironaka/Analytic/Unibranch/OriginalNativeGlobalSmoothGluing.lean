import Hironaka.Analytic.Unibranch.OriginalNativeGlobalSmoothSiteLift
import Hironaka.Analytic.Unibranch.OriginalNativeHSGlobalLiftUniqueness
import Hironaka.Analytic.Unibranch.HironakaG10GenGluing

/-! The actual global smooth lift, glued from the genuine computed sites.
Blueprint first: original-native-global-smooth-gluing.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeGlobalSmoothGluing
noncomputable section
open Hironaka SourceReducedComplexSpace
  HironakaIntrinsicComplexAnalyticRegularLocus OriginalNativeSmoothLocalProduct
  OriginalNativeSmoothComposition OriginalNativeSmoothOpenLocality
  OriginalNativeSmoothSingularLocus OriginalNativeGlobalSmoothAtlasSites

variable {X Y : SourceReducedComplexSpace} (f : X ⟶ Y) (hf : IsSmoothMorphism f)

abbrev siteInclusion (s : Site f) : sourceChart f s ⟶ OriginalNativeHSGlobalResolution.source X :=
  sourceChartInclusion f s

instance siteInclusion_open (s : Site f) :
    LocallyRingedSpace.IsOpenImmersion (siteInclusion f s).hom.left := sourceChart_isOpenImmersion f s

def siteMap (s : Site f) : sourceChart f s ⟶ OriginalNativeHSGlobalResolution.source Y :=
  OriginalNativeGlobalSmoothSiteLift.map f s ≫
    OriginalNativeHSResolutionProperAtlas.localInclusion Y s.targetIndex

private theorem siteMap_square (s : Site f) : siteMap f s ≫ OriginalNativeHSGlobalResolution.projection Y =
    siteInclusion f s ≫ OriginalNativeHSGlobalResolution.projection X ≫ f := by
  have hp := OriginalNativeHSResolutionProperAtlas.localInclusion_projection Y s.targetIndex
  change OriginalNativeHSResolutionProperAtlas.localInclusion Y s.targetIndex ≫
      OriginalNativeHSGlobalResolution.projection Y =
    OriginalNativeHSResolutionAtlasChoice.projection s.targetIndex ≫
      OriginalNativeHSResolutionAtlasChoice.baseInclusion s.targetIndex at hp
  have hs := OriginalNativeGlobalSmoothSiteLift.original_square f s
  have hi := sourceChart_projection f s
  change siteInclusion f s ≫ OriginalNativeHSGlobalResolution.projection X = _ at hi
  dsimp only [siteMap]
  calc
    _ = OriginalNativeGlobalSmoothSiteLift.map f s ≫
        (OriginalNativeHSResolutionAtlasChoice.projection s.targetIndex ≫
          OriginalNativeHSResolutionAtlasChoice.baseInclusion s.targetIndex) := by rw [Category.assoc, hp]
    _ = (OriginalNativeHSResolutionAtlasChoice.projection s.sourceIndex ≫
        OriginalNativeHSResolutionAtlasChoice.baseInclusion s.sourceIndex) ≫ f := hs
    _ = (siteInclusion f s ≫ OriginalNativeHSGlobalResolution.projection X) ≫ f :=
      congrArg (fun z => z ≫ f) hi.symm

private theorem siteMap_smooth (s : Site f) : IsSmoothMorphism (siteMap f s) :=
  isSmoothMorphism_comp _ _ (OriginalNativeGlobalSmoothSiteLift.map_smooth f s)
    (isSmoothMorphism_of_isOpenImmersion _
      (OriginalNativeHSResolutionProperAtlas.localInclusion_isOpenImmersion Y s.targetIndex))

include hf in
private theorem compatible (s t : Site f) :
    pullback.fst (siteInclusion f s).hom.left (siteInclusion f t).hom.left ≫ (siteMap f s).hom.left =
      pullback.snd (siteInclusion f s).hom.left (siteInclusion f t).hom.left ≫ (siteMap f t).hom.left := by
  let j := (siteInclusion f s).hom.left
  let k := (siteInclusion f t).hom.left
  let : LocallyRingedSpace.IsOpenImmersion j := sourceChart_isOpenImmersion f s
  let : LocallyRingedSpace.IsOpenImmersion k := sourceChart_isOpenImmersion f t
  let a := pullback.fst j k
  let b := pullback.snd j k
  let v := a ≫ j
  let F := a ≫ (siteMap f s).hom.left
  let H := b ≫ (siteMap f t).hom.left
  let : LocallyRingedSpace.IsOpenImmersion v := by dsimp only [v,a]; infer_instance
  have hF : F ≫ (OriginalNativeHSGlobalResolution.projection Y).hom.left =
      v ≫ (OriginalNativeHSGlobalResolution.projection X).hom.left ≫ f.hom.left := by
    have hs := congrArg (fun h => h.hom.left) (siteMap_square f s)
    change (siteMap f s).hom.left ≫ (OriginalNativeHSGlobalResolution.projection Y).hom.left =
      ((siteInclusion f s).hom.left ≫ (OriginalNativeHSGlobalResolution.projection X).hom.left) ≫ f.hom.left at hs
    dsimp only [F,v,a,j]
    rw [Category.assoc, hs, Category.assoc, Category.assoc]
  have hH : H ≫ (OriginalNativeHSGlobalResolution.projection Y).hom.left =
      v ≫ (OriginalNativeHSGlobalResolution.projection X).hom.left ≫ f.hom.left := by
    have hs := congrArg (fun h => h.hom.left) (siteMap_square f t)
    change (siteMap f t).hom.left ≫ (OriginalNativeHSGlobalResolution.projection Y).hom.left =
      ((siteInclusion f t).hom.left ≫ (OriginalNativeHSGlobalResolution.projection X).hom.left) ≫ f.hom.left at hs
    dsimp only [H,v,b,a,j,k]
    rw [Category.assoc, hs]
    simp only [← Category.assoc]
    rw [← pullback.condition]
  have hbase : ∀ z, (OriginalNativeHSGlobalResolution.projection Y).hom.left.base (F.base z) =
      (OriginalNativeHSGlobalResolution.projection Y).hom.left.base (H.base z) :=
    fun z => congrArg (fun p => p.base z) (hF.trans hH.symm)
  let D := v.base ⁻¹' ((OriginalNativeHSGlobalResolution.projection X).hom.left.base ⁻¹'
    intrinsicRegularLocus X.obj)
  have hv : LocallyRingedSpace.IsOpenImmersion v := inferInstance
  have hD : Dense D := (OriginalNativeHSGlobalResolution.dense_originalReg X).preimage hv.base_open.isOpenMap
  have hGood : ∀ z ∈ D, (OriginalNativeHSGlobalResolution.projection Y).hom.left.base (F.base z) ∈
      intrinsicRegularLocus Y.obj := by
    intro z hz
    have hp := congrArg (fun p => p.base z) hF
    change (OriginalNativeHSGlobalResolution.projection Y).hom.left.base (F.base z) =
      f.hom.left.base ((OriginalNativeHSGlobalResolution.projection X).hom.left.base (v.base z)) at hp
    rw [hp]
    exact (smoothAt_regular_iff f _ (hf _)).mp hz
  have hpoints : F.base = H.base := by
    ext z
    exact congrFun (HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense
      (OriginalNativeHSGlobalResolution.originalReg Y) F.base.hom.continuous H.base.hom.continuous
      hbase hD hGood) z
  apply HironakaG10GenGluing.lrs_hom_eq_of_base_eq (A := OriginalNativeHSGlobalResolution.source X)
    (B := OriginalNativeHSGlobalResolution.source Y) v F H
  · dsimp only [F,v,a,j]
    rw [Category.assoc, Over.w (siteMap f s).hom, Category.assoc, Over.w (siteInclusion f s).hom]
  · dsimp only [H,v,b,a,j,k]
    rw [Category.assoc, Over.w (siteMap f t).hom, ← Over.w (siteInclusion f t).hom,
      ← Category.assoc, ← pullback.condition]
  · exact hpoints

include hf in
/-- The actual computed site maps give one global smooth arrow and its full square. -/
theorem exists_unique_map : ∃! g : OriginalNativeHSGlobalResolution.source X ⟶
    OriginalNativeHSGlobalResolution.source Y,
    IsSmoothMorphism g ∧
    g ≫ OriginalNativeHSGlobalResolution.projection Y = OriginalNativeHSGlobalResolution.projection X ≫ f ∧
    ∀ s : Site f, siteInclusion f s ≫ g = siteMap f s := by
  let V (s : Site f) := (sourceChart f s).obj.left
  let j (s : Site f) := (siteInclusion f s).hom.left
  let : ∀ s, LocallyRingedSpace.IsOpenImmersion (j s) := fun s => sourceChart_isOpenImmersion f s
  have hcover : ∀ z : (OriginalNativeHSGlobalResolution.source X).obj.left,
      ∃ s u, (j s).base u = z := sourceChart_cover f hf
  have hscalar : ∀ s, (siteMap f s).hom.left ≫ (OriginalNativeHSGlobalResolution.source Y).obj.hom =
      j s ≫ (OriginalNativeHSGlobalResolution.source X).obj.hom := by
    intro s
    rw [Over.w (siteMap f s).hom, Over.w (siteInclusion f s).hom]
  obtain ⟨g,hg,_⟩ := HironakaIntrinsicMorphismGluing.exists_unique_over V j hcover
    (OriginalNativeHSGlobalResolution.source X).obj.hom
    (OriginalNativeHSGlobalResolution.source Y).obj.hom (fun s => (siteMap f s).hom.left)
    (compatible f hf) hscalar
  let gn : OriginalNativeHSGlobalResolution.source X ⟶ OriginalNativeHSGlobalResolution.source Y :=
    ObjectProperty.homMk g
  have hlocal (s : Site f) : siteInclusion f s ≫ gn = siteMap f s := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact hg s
  have hsquare : gn ≫ OriginalNativeHSGlobalResolution.projection Y =
      OriginalNativeHSGlobalResolution.projection X ≫ f := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply HironakaIntrinsicMorphismGluing.hom_ext V j hcover
    intro s
    have hs := congrArg (fun h => h.hom.left) (siteMap_square f s)
    change (siteMap f s).hom.left ≫ (OriginalNativeHSGlobalResolution.projection Y).hom.left =
      ((siteInclusion f s).hom.left ≫ (OriginalNativeHSGlobalResolution.projection X).hom.left) ≫ f.hom.left at hs
    change j s ≫ (g.left ≫ (OriginalNativeHSGlobalResolution.projection Y).hom.left) = _
    rw [← Category.assoc, hg s, hs]
    simp only [Category.assoc]
    rfl
  have hsmooth : IsSmoothMorphism gn := by
    intro z
    obtain ⟨s,u,hu⟩ := hcover z
    have hh : IsSmoothAt (siteInclusion f s ≫ gn) u := (hlocal s).symm ▸ siteMap_smooth f s u
    exact hu ▸ isSmoothAt_of_precomp_openImmersion (siteInclusion f s) gn (sourceChart_isOpenImmersion f s) u hh
  refine ⟨gn, ⟨hsmooth, hsquare, hlocal⟩, ?_⟩
  intro g' hg'
  exact OriginalNativeHSGlobalLiftUniqueness.raw_maps_eq X Y f hf g' gn hg'.2.1 hsquare

include f hf in
/-- The lift on the actual global resolution, chosen from the proved gluing theorem. -/
def map : OriginalNativeHSGlobalResolution.source X ⟶ OriginalNativeHSGlobalResolution.source Y :=
  (exists_unique_map f hf).exists.choose

theorem map_smooth : IsSmoothMorphism (map f hf) :=
  (exists_unique_map f hf).exists.choose_spec.1

theorem map_square : map f hf ≫ OriginalNativeHSGlobalResolution.projection Y =
    OriginalNativeHSGlobalResolution.projection X ≫ f :=
  (exists_unique_map f hf).exists.choose_spec.2.1

theorem map_site (s : Site f) : siteInclusion f s ≫ map f hf = siteMap f s :=
  (exists_unique_map f hf).exists.choose_spec.2.2 s

theorem map_eq (g : OriginalNativeHSGlobalResolution.source X ⟶ OriginalNativeHSGlobalResolution.source Y)
    (hg : g ≫ OriginalNativeHSGlobalResolution.projection Y = OriginalNativeHSGlobalResolution.projection X ≫ f) :
    g = map f hf :=
  OriginalNativeHSGlobalLiftUniqueness.raw_maps_eq X Y f hf g (map f hf) hg (map_square f hf)

theorem map_identity : map (𝟙 X) (isSmoothMorphism_identity X) = 𝟙 _ := by
  apply OriginalNativeHSGlobalLiftUniqueness.raw_identity X
  simpa only [Category.comp_id] using map_square (𝟙 X) (isSmoothMorphism_identity X)

theorem map_composition {Z : SourceReducedComplexSpace} (g : Y ⟶ Z) (hg : IsSmoothMorphism g) :
    map f hf ≫ map g hg = map (f ≫ g) (isSmoothMorphism_comp f g hf hg) :=
  OriginalNativeHSGlobalLiftUniqueness.raw_composition X Y f hf Z g hg (map f hf) (map g hg)
    (map (f ≫ g) (isSmoothMorphism_comp f g hf hg)) (map_square f hf) (map_square g hg)
    (map_square (f ≫ g) (isSmoothMorphism_comp f g hf hg))

end
end Hironaka.Analytic.Unibranch.OriginalNativeGlobalSmoothGluing
