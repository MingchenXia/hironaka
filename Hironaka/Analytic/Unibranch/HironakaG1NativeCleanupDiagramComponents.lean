import Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupDiagramIso

/-! # Arbitrary-component cleanup under actual native diagram isomorphisms

Component labels and full native component isomorphisms are DERIVED from
the actual given v. Genuine component models and ordinary resolution data
then construct the actual terminal comparison. Entire native original-Sing
total ideals retain both literal structure-unit inclusion triangles.
Blueprint precedes source; arbitrary smooth-map naturality is separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupDiagramComponents

open Hironaka Hironaka
  HironakaEmbeddedNativeMorphism HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaIntrinsicReducedCentreIdealSheaf HironakaNativePulledIdealSheaf
  HironakaNativePulledIdealStalk HironakaNativePulledIdealComposition HironakaSingularModuleSheafStalk
  SourceReducedComplexSpace OriginalNativeModification OriginalIntrinsicSingularLocus OriginalNativeSmoothReducedIdealPullback
  OriginalNativeSmoothSingularLocus HironakaG1NativeCleanupModelIndependence
  HironakaG1NativeCleanupComponentModelIndependence HironakaG1NativeCleanupDiagramIso

noncomputable section

variable {X X' Y Y' : SourceReducedComplexSpace}

private def componentPreimage (v : Y' ≅ Y) (c : ConnectedComponents Y.obj.left) : Set Y'.obj.left :=
  (isoHomeomorph v) ⁻¹' OriginalSmoothComponents.componentSet c

private theorem componentPreimage_clopen (v : Y' ≅ Y) (h : Y.IsSmooth)
    (c : ConnectedComponents Y.obj.left) : IsClopen (componentPreimage v c) :=
  (OriginalSmoothComponents.component_isClopen h c).preimage (isoHomeomorph v).continuous

private theorem componentPreimage_disjoint (v : Y' ≅ Y) :
    Pairwise fun c d : ConnectedComponents Y.obj.left =>
      Disjoint (componentPreimage v c) (componentPreimage v d) :=
  fun _ _ hcd => (OriginalSmoothComponents.componentSet_pairwise_disjoint hcd).preimage _

private theorem componentPreimage_cover (v : Y' ≅ Y) : ⋃ c, componentPreimage v c = univ := by
  apply eq_univ_of_forall
  intro y
  exact mem_iUnion.mpr ⟨ConnectedComponents.mk ((isoHomeomorph v) y), rfl⟩

private theorem componentPreimage_connected (v : Y' ≅ Y)
    (c : ConnectedComponents Y.obj.left) : IsConnected (componentPreimage v c) :=
  (isoHomeomorph v).isConnected_preimage.mpr (OriginalSmoothComponents.component_isConnected c)

/-- The actual component bijection derived from the actual native homeomorphism. -/
def componentEquiv (v : Y' ≅ Y) (h : Y.IsSmooth) :
    ConnectedComponents Y'.obj.left ≃ ConnectedComponents Y.obj.left :=
  ConnectedComponents.equivOfIsClopenOfIsConnected (componentPreimage_clopen v h)
    (componentPreimage_disjoint v) (componentPreimage_cover v) (componentPreimage_connected v)

/-- Its literal original-point formula; no pairing packet is an input. -/
theorem componentEquiv_mk (v : Y' ≅ Y) (h : Y.IsSmooth) (y : Y'.obj.left) :
    componentEquiv v h (ConnectedComponents.mk y) = ConnectedComponents.mk (v.hom.hom.left.base y) :=
  ConnectedComponents.equivOfIsClopenOfIsConnected_mk (componentPreimage_clopen v h)
    (componentPreimage_disjoint v) (componentPreimage_cover v) (componentPreimage_connected v) y rfl

/-- Exact ENTIRE original component preimages, without compactness or countability. -/
theorem componentEquiv_preimage (v : Y' ≅ Y) (h : Y.IsSmooth)
    (c : ConnectedComponents Y'.obj.left) :
    v.hom.hom.left.base ⁻¹' OriginalSmoothComponents.componentSet (componentEquiv v h c) =
      OriginalSmoothComponents.componentSet c := by
  ext y
  change ConnectedComponents.mk (v.hom.hom.left.base y) = componentEquiv v h c ↔
    ConnectedComponents.mk y = c
  rw [← componentEquiv_mk v h y]
  exact (componentEquiv v h).injective.eq_iff

private theorem componentRange (h' : Y'.IsSmooth) (h : Y.IsSmooth) (v : Y' ≅ Y)
    (c : ConnectedComponents Y'.obj.left) :
    range ((HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c).hom.left ≫
        v.hom.hom.left).base =
      range (HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentEquiv v h c)).hom.left.base := by
  let j' := HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c
  let j := HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentEquiv v h c)
  let f := j'.hom.left ≫ v.hom.hom.left
  have hr : range f.base = range j.hom.left.base := by
    rw [HironakaG1NoncompactSmoothComponentModel.componentInclusion_range]
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      change v.hom.hom.left.base z.val ∈ OriginalSmoothComponents.componentSet (componentEquiv v h c)
      exact Set.ext_iff.mp (componentEquiv_preimage v h c) z.val |>.mpr z.property
    · intro hy
      have hz : (isoHomeomorph v).symm y ∈ OriginalSmoothComponents.componentSet c := by
        rw [← componentEquiv_preimage v h c]
        change (isoHomeomorph v) ((isoHomeomorph v).symm y) ∈ OriginalSmoothComponents.componentSet (componentEquiv v h c)
        rw [(isoHomeomorph v).apply_symm_apply]
        exact hy
      refine ⟨⟨(isoHomeomorph v).symm y, hz⟩, ?_⟩
      exact (isoHomeomorph v).apply_symm_apply y
  exact hr


private def rawComponentIso (h' : Y'.IsSmooth) (h : Y.IsSmooth) (v : Y' ≅ Y)
    (c : ConnectedComponents Y'.obj.left) :
    (HironakaG1NoncompactSmoothComponentModel.componentObject h' c).obj.left ≅
      (HironakaG1NoncompactSmoothComponentModel.componentObject h (componentEquiv v h c)).obj.left :=
  openImmersionIsoOfRangeEq
    ((HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c).hom.left ≫ v.hom.hom.left)
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentEquiv v h c)).hom.left
    (componentRange h' h v c)

private theorem rawComponentIso_fac (h' : Y'.IsSmooth) (h : Y.IsSmooth) (v : Y' ≅ Y)
    (c : ConnectedComponents Y'.obj.left) :
    (rawComponentIso h' h v c).hom ≫
        (HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentEquiv v h c)).hom.left =
      (HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c).hom.left ≫ v.hom.hom.left :=
  openImmersionIsoOfRangeEq_hom_fac _ _ (componentRange h' h v c)

private theorem rawComponentIso_scalar (h' : Y'.IsSmooth) (h : Y.IsSmooth) (v : Y' ≅ Y)
    (c : ConnectedComponents Y'.obj.left) :
    (rawComponentIso h' h v c).hom ≫
        (HironakaG1NoncompactSmoothComponentModel.componentObject h (componentEquiv v h c)).obj.hom =
      (HironakaG1NoncompactSmoothComponentModel.componentObject h' c).obj.hom := by
  change (rawComponentIso h' h v c).hom ≫
    ((HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentEquiv v h c)).hom.left ≫
      Y.obj.hom) =
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c).hom.left ≫ Y'.obj.hom
  rw [← Category.assoc, rawComponentIso_fac, Category.assoc, Over.w v.hom.hom]

private def nativeIsoOfLRSIso {A B : SourceReducedComplexSpace}
    (e : A.obj.left ≅ B.obj.left) (hs : e.hom ≫ B.obj.hom = A.obj.hom) : A ≅ B where
  hom := ObjectProperty.homMk (Over.homMk e.hom hs)
  inv := ObjectProperty.homMk (Over.homMk e.inv (by
    rw [← hs, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]))
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact e.hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    exact e.inv_hom_id

/-- Actual native component isomorphism with its internally derived scalar triangle. -/
def componentIso (h' : Y'.IsSmooth) (h : Y.IsSmooth) (v : Y' ≅ Y)
    (c : ConnectedComponents Y'.obj.left) :
    HironakaG1NoncompactSmoothComponentModel.componentObject h' c ≅
      HironakaG1NoncompactSmoothComponentModel.componentObject h (componentEquiv v h c) :=
  nativeIsoOfLRSIso (rawComponentIso h' h v c) (rawComponentIso_scalar h' h v c)

/-- The SAME full original native inclusion square over v. -/
theorem componentIso_square (h' : Y'.IsSmooth) (h : Y.IsSmooth) (v : Y' ≅ Y)
    (c : ConnectedComponents Y'.obj.left) :
    (componentIso h' h v c).hom ≫
        HironakaG1NoncompactSmoothComponentModel.componentInclusion h (componentEquiv v h c) =
      HironakaG1NoncompactSmoothComponentModel.componentInclusion h' c ≫ v.hom := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact rawComponentIso_fac h' h v c

private def backwardsPiece {ι κ : Type} {Z : ι → SourceReducedComplexSpace}
    {W : κ → SourceReducedComplexSpace} (s : ι ≃ κ) (e : ∀ i, Z i ≅ W (s i))
    (j : κ) : W j ⟶ HironakaG1NativeDisjointCoproduct.coproduct Z :=
  (eqToIso (congrArg W (s.apply_symm_apply j))).inv ≫
    (e (s.symm j)).inv ≫ HironakaG1NativeDisjointCoproduct.inclusion Z (s.symm j)

private theorem backwardsPiece_apply {ι κ : Type} {Z : ι → SourceReducedComplexSpace}
    {W : κ → SourceReducedComplexSpace} (s : ι ≃ κ) (e : ∀ i, Z i ≅ W (s i)) (i : ι) :
    backwardsPiece s e (s i) = (e i).inv ≫ HironakaG1NativeDisjointCoproduct.inclusion Z i := by
  change eqToHom ((congrArg W (s.apply_symm_apply (s i))).symm) ≫ ((e (s.symm (s i))).inv ≫
    HironakaG1NativeDisjointCoproduct.inclusion Z (s.symm (s i))) = _
  have H := eqToHom_naturality (f := fun k => W (s k))
    (g := fun _ => HironakaG1NativeDisjointCoproduct.coproduct Z)
    (fun k => (e k).inv ≫ HironakaG1NativeDisjointCoproduct.inclusion Z k)
    (s.symm_apply_apply i).symm
  simpa only [eqToHom_refl, Category.comp_id] using H.symm

private def coproductReindexedIso {ι κ : Type} {Z : ι → SourceReducedComplexSpace}
    {W : κ → SourceReducedComplexSpace} (s : ι ≃ κ) (e : ∀ i, Z i ≅ W (s i)) :
    HironakaG1NativeDisjointCoproduct.coproduct Z ≅ HironakaG1NativeDisjointCoproduct.coproduct W where
  hom := HironakaG1NativeDisjointCoproduct.desc Z
    (fun i => (e i).hom ≫ HironakaG1NativeDisjointCoproduct.inclusion W (s i))
  inv := HironakaG1NativeDisjointCoproduct.desc W (backwardsPiece s e)
  hom_inv_id := by
    apply HironakaG1NativeDisjointCoproduct.hom_ext
    intro i
    rw [← Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc, Category.assoc,
      HironakaG1NativeDisjointCoproduct.inclusion_desc, backwardsPiece_apply,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp, Category.comp_id]
  inv_hom_id := by
    apply HironakaG1NativeDisjointCoproduct.hom_ext
    intro j
    obtain ⟨i, rfl⟩ := s.surjective j
    rw [← Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc, backwardsPiece_apply,
      Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp, Category.comp_id]

private theorem coproductReindexedIso_desc {ι κ : Type} {Z : ι → SourceReducedComplexSpace}
    {W : κ → SourceReducedComplexSpace} (s : ι ≃ κ) (e : ∀ i, Z i ≅ W (s i))
    (F : ∀ i, Z i ⟶ Y') (G : ∀ j, W j ⟶ Y) (v : Y' ⟶ Y)
    (he : ∀ i, (e i).hom ≫ G (s i) = F i ≫ v) :
    (coproductReindexedIso s e).hom ≫ HironakaG1NativeDisjointCoproduct.desc W G =
      HironakaG1NativeDisjointCoproduct.desc Z F ≫ v := by
  apply HironakaG1NativeDisjointCoproduct.hom_ext
  intro i
  change HironakaG1NativeDisjointCoproduct.inclusion Z i ≫
      (HironakaG1NativeDisjointCoproduct.desc Z
        (fun j => (e j).hom ≫ HironakaG1NativeDisjointCoproduct.inclusion W (s j)) ≫
          HironakaG1NativeDisjointCoproduct.desc W G) =
    HironakaG1NativeDisjointCoproduct.inclusion Z i ≫ (HironakaG1NativeDisjointCoproduct.desc Z F ≫ v)
  rw [← Category.assoc, HironakaG1NativeDisjointCoproduct.inclusion_desc, Category.assoc,
    HironakaG1NativeDisjointCoproduct.inclusion_desc, ← Category.assoc,
    HironakaG1NativeDisjointCoproduct.inclusion_desc]
  exact he i

variable (p' : Y' ⟶ X') (p : Y ⟶ X) (hp' : IsResolution p') (hp : IsResolution p)

/-- The ACTUAL arbitrary-component terminal cleanup isomorphism over the full
given native resolution diagram. No pairing/ideal/terminal comparison is input. -/
theorem exists_cleanup_diagram_iso
    (u : X' ≅ X) (v : Y' ≅ Y) (hdiag : p' ≫ u.hom = v.hom ≫ p)
    (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c) :
    ∃ e : cleanupSource p' hp' A' ≅ cleanupSource p hp A,
      e.hom ≫ cleanupProjection p hp A = cleanupProjection p' hp' A' ≫ v.hom ∧
      e.hom ≫ cleanupMorphism p hp A = cleanupMorphism p' hp' A' ≫ u.hom ∧
      e.hom.hom.left.base ⁻¹'
          ((cleanupMorphism p hp A).hom.left.base ⁻¹' intrinsicRegularLocus X.obj) =
        (cleanupMorphism p' hp' A').hom.left.base ⁻¹' intrinsicRegularLocus X'.obj := by
  classical
  let s := componentEquiv v hp.1
  have hcomp (c : ConnectedComponents Y'.obj.left) :
      ∃ e : wholeModel (n := (A' c).dimension) (componentTerminal p' hp' A' c) ≅
          wholeModel (n := (A (s c)).dimension) (componentTerminal p hp A (s c)),
        e.hom ≫ componentCleanupMap p hp A (s c) = componentCleanupMap p' hp' A' c ≫ v.hom := by
    let : ConnectedSpace (HironakaG1NoncompactSmoothComponentModel.componentObject hp'.1 c).obj.left :=
      isConnected_iff_connectedSpace.mp (OriginalSmoothComponents.component_isConnected c)
    have hc : (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp'.1 c ≫ p') ≫ u.hom =
        (componentIso hp'.1 hp.1 v c).hom ≫
          (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 (s c) ≫ p) := by
      rw [Category.assoc, hdiag, ← Category.assoc, ← componentIso_square, Category.assoc]
    obtain ⟨_, e, _, hs, _, _, _⟩ := exists_cleanup_diagram_iso_of_thin
      (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp'.1 c ≫ p')
      (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 (s c) ≫ p)
      (componentThin p' hp' c) (componentThin p hp (s c)) u (componentIso hp'.1 hp.1 v c) hc
      (A' c).model (A (s c)).model
    refine ⟨e, ?_⟩
    change e.hom ≫ (_ ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 (s c)) =
      (_ ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hp'.1 c) ≫ v.hom
    rw [← Category.assoc, hs, Category.assoc, componentIso_square, ← Category.assoc]
  choose e he using hcomp
  let Z : ConnectedComponents Y'.obj.left → SourceReducedComplexSpace :=
    fun c => wholeModel (n := (A' c).dimension) (componentTerminal p' hp' A' c)
  let W : ConnectedComponents Y.obj.left → SourceReducedComplexSpace :=
    fun c => wholeModel (n := (A c).dimension) (componentTerminal p hp A c)
  let E := coproductReindexedIso (Z := Z) (W := W) s e
  have hY : E.hom ≫ cleanupProjection p hp A = cleanupProjection p' hp' A' ≫ v.hom := by
    exact coproductReindexedIso_desc (Z := Z) (W := W) s e (componentCleanupMap p' hp' A')
      (componentCleanupMap p hp A) v.hom he
  have hX : E.hom ≫ cleanupMorphism p hp A = cleanupMorphism p' hp' A' ≫ u.hom := by
    change E.hom ≫ (cleanupProjection p hp A ≫ p) = (cleanupProjection p' hp' A' ≫ p') ≫ u.hom
    rw [← Category.assoc, hY, Category.assoc, ← hdiag, ← Category.assoc]
  refine ⟨E, hY, hX, ?_⟩
  ext z
  have hz := congrArg (fun f : cleanupSource p' hp' A' ⟶ X => f.hom.left.base z) hX
  change (cleanupMorphism p hp A).hom.left.base (E.hom.hom.left.base z) =
    u.hom.hom.left.base ((cleanupMorphism p' hp' A').hom.left.base z) at hz
  change (cleanupMorphism p hp A).hom.left.base (E.hom.hom.left.base z) ∈ intrinsicRegularLocus X.obj ↔ _
  rw [hz]
  exact Set.ext_iff.mp (preimage_intrinsicRegularLocus u.hom (nativeIso_smooth u)) _

private theorem baseSingular_stalk {Z : LocallyRingedSpace.{0}}
    (u : X' ≅ X) (F : Z ⟶ X'.obj.left) (z : Z) :
    nativePulledIdealStalkIdeal (F ≫ u.hom.hom.left)
      (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
      (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) z =
    nativePulledIdealStalkIdeal F
      (intrinsicReducedCentreIdealModule X'.obj.left (intrinsicSingularLocus X'.obj))
      (intrinsicReducedCentreIdealInclusion X'.obj.left (intrinsicSingularLocus X'.obj)) z := by
  let B := intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj)
  let b := intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)
  have hK := smooth_pulled_stalkIdeal_eq u.hom (F.base z) (nativeIso_smooth u (F.base z))
    (isAnalyticSubset_intrinsicSingularLocus X)
  rw [preimage_intrinsicSingularLocus u.hom (nativeIso_smooth u)] at hK
  calc
    _ = nativePulledIdealStalkIdeal F (nativePulledIdealModule u.hom.hom.left B b)
        (nativePulledIdealInclusion u.hom.hom.left B b) z :=
      (stalkIdeal_comp u.hom.hom.left F B b z).symm
    _ = _ := congrArg (Ideal.map (F.stalkMap z).hom)
      ((nativePulledIdealStalkInclusion_range u.hom.hom.left B b (F.base z)).trans hK)

private theorem baseSingular_submodule {Z : LocallyRingedSpace.{0}}
    (u : X' ≅ X) (F : Z ⟶ X'.obj.left) :
    nativePulledIdealSubmodule (F ≫ u.hom.hom.left)
      (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
      (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) =
    nativePulledIdealSubmodule F
      (intrinsicReducedCentreIdealModule X'.obj.left (intrinsicSingularLocus X'.obj))
      (intrinsicReducedCentreIdealInclusion X'.obj.left (intrinsicSingularLocus X'.obj)) := by
  apply PresheafOfModules.Submodule.ext
  intro U
  ext t
  constructor
  · intro ht z hz
    rw [← baseSingular_stalk u F z]
    exact ht z hz
  · intro ht z hz
    rw [baseSingular_stalk u F z]
    exact ht z hz

private theorem totalIdealSubmodule_eq
    (u : X' ≅ X) (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c)
    (e : cleanupSource p' hp' A' ≅ cleanupSource p hp A)
    (hs : e.hom ≫ cleanupMorphism p hp A = cleanupMorphism p' hp' A' ≫ u.hom) :
    nativePulledIdealSubmodule e.hom.hom.left (totalIdealModule p hp A) (totalIdealInclusion p hp A) =
      nativePulledIdealSubmodule (cleanupMorphism p' hp' A').hom.left
        (intrinsicReducedCentreIdealModule X'.obj.left (intrinsicSingularLocus X'.obj))
        (intrinsicReducedCentreIdealInclusion X'.obj.left (intrinsicSingularLocus X'.obj)) := by
  have hF : e.hom.hom.left ≫ (cleanupMorphism p hp A).hom.left =
      (cleanupMorphism p' hp' A').hom.left ≫ u.hom.hom.left :=
    congrArg (fun f : cleanupSource p' hp' A' ⟶ X => f.hom.left) hs
  change nativePulledIdealSubmodule e.hom.hom.left
    (nativePulledIdealModule (cleanupMorphism p hp A).hom.left _ _)
    (nativePulledIdealInclusion (cleanupMorphism p hp A).hom.left _ _) = _
  rw [submodule_comp, hF]
  exact baseSingular_submodule u (cleanupMorphism p' hp' A').hom.left

/-- ENTIRE original native totalideal transport through the SAME actual u/e square. -/
def totalIdealIso_of_diagram
    (u : X' ≅ X) (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c)
    (e : cleanupSource p' hp' A' ≅ cleanupSource p hp A)
    (hs : e.hom ≫ cleanupMorphism p hp A = cleanupMorphism p' hp' A' ≫ u.hom) :
    nativePulledIdealModule e.hom.hom.left (totalIdealModule p hp A) (totalIdealInclusion p hp A) ≅
      totalIdealModule p' hp' A' where
  hom := ⟨PresheafOfModules.Submodule.homOfLE (totalIdealSubmodule_eq p' p hp' hp u A' A e hs).le⟩
  inv := ⟨PresheafOfModules.Submodule.homOfLE (totalIdealSubmodule_eq p' p hp' hp u A' A e hs).ge⟩
  hom_inv_id := by ext U t; rfl
  inv_hom_id := by ext U t; rfl

/-- Forward literal original structure-unit inclusion triangle. -/
theorem totalIdealIso_hom_comp_inclusion
    (u : X' ≅ X) (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c)
    (e : cleanupSource p' hp' A' ≅ cleanupSource p hp A)
    (hs : e.hom ≫ cleanupMorphism p hp A = cleanupMorphism p' hp' A' ≫ u.hom) :
    (totalIdealIso_of_diagram p' p hp' hp u A' A e hs).hom ≫ totalIdealInclusion p' hp' A' =
      nativePulledIdealInclusion e.hom.hom.left (totalIdealModule p hp A) (totalIdealInclusion p hp A) := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (totalIdealSubmodule_eq p' p hp' hp u A' A e hs).le

/-- Inverse literal original structure-unit inclusion triangle. -/
theorem totalIdealIso_inv_comp_inclusion
    (u : X' ≅ X) (A' : ∀ c, ComponentModel hp'.1 c) (A : ∀ c, ComponentModel hp.1 c)
    (e : cleanupSource p' hp' A' ≅ cleanupSource p hp A)
    (hs : e.hom ≫ cleanupMorphism p hp A = cleanupMorphism p' hp' A' ≫ u.hom) :
    (totalIdealIso_of_diagram p' p hp' hp u A' A e hs).inv ≫
        nativePulledIdealInclusion e.hom.hom.left (totalIdealModule p hp A) (totalIdealInclusion p hp A) =
      totalIdealInclusion p' hp' A' := by
  apply SheafOfModules.hom_ext
  exact PresheafOfModules.Submodule.homOfLE_ι (totalIdealSubmodule_eq p' p hp' hp u A' A e hs).ge

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupDiagramComponents
