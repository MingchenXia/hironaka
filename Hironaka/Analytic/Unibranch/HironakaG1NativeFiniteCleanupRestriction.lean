import Hironaka.Analytic.Unibranch.HironakaG1FiniteClopenModification
import Hironaka.Analytic.Unibranch.HironakaG1NativeFiniteTerminalRestriction
import Hironaka.Analytic.Unibranch.HironakaG1NativeStrongCleanupFunctor
import Hironaka.Analytic.Unibranch.OriginalRelativelyCompactRestriction

/-! # Real finite cleanup on literal compact-closure native restrictions

All component/window geometry is constructed from the original resolution,
genuine model witnesses and prescribed open. No finite-cover/comparison packet
is an input. The SAME chosen strong projection is retained. Blueprint first;
initial singular-target canonical histories remain separate.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Function TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeFiniteCleanupRestriction

open Hironaka Hironaka
  Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceOpenRestriction
  HironakaIntrinsicComplexAnalyticRegularLocus
  SourceReducedComplexSpace OriginalNativeModification SmoothCentreModification
  HironakaG1NativeCleanupModelIndependence HironakaG1NativeCleanupComponentModelIndependence
  HironakaG1NativeModificationIsoTransport HironakaG1NativeFiniteTerminalRestriction
open _root_.Hironaka.ResolutionInvariantSpec (IsInvDomain)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

noncomputable section

private def liftOpen {A B C : SourceReducedComplexSpace} (j : B ⟶ C)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (F : A ⟶ C)
    (hr : range F.hom.left.base ⊆ range j.hom.left.base) : A ⟶ B := by
  let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
  let a := LocallyRingedSpace.IsOpenImmersion.lift j.hom.left F.hom.left hr
  have ha : a ≫ j.hom.left = F.hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr
  apply ObjectProperty.homMk
  refine Over.homMk a ?_
  calc
    a ≫ B.obj.hom = a ≫ (j.hom.left ≫ C.obj.hom) :=
      congrArg (fun f => a ≫ f) (Over.w j.hom).symm
    _ = (a ≫ j.hom.left) ≫ C.obj.hom := (Category.assoc _ _ _).symm
    _ = F.hom.left ≫ C.obj.hom := congrArg (fun f => f ≫ C.obj.hom) ha
    _ = A.obj.hom := Over.w F.hom

private theorem liftOpen_fac {A B C : SourceReducedComplexSpace} (j : B ⟶ C)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (F : A ⟶ C)
    (hr : range F.hom.left.base ⊆ range j.hom.left.base) : liftOpen j hj F hr ≫ j = F := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ hr

private theorem liftOpen_isOpenImmersion {A B C : SourceReducedComplexSpace} (j : B ⟶ C)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) (F : A ⟶ C)
    (hF : LocallyRingedSpace.IsOpenImmersion F.hom.left)
    (hr : range F.hom.left.base ⊆ range j.hom.left.base) :
    LocallyRingedSpace.IsOpenImmersion (liftOpen j hj F hr).hom.left := by
  let : LocallyRingedSpace.IsOpenImmersion j.hom.left := hj
  let : LocallyRingedSpace.IsOpenImmersion F.hom.left := hF
  let : IsIso (pullback.snd j.hom.left F.hom.left) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset _ _ hr
  change LocallyRingedSpace.IsOpenImmersion (LocallyRingedSpace.IsOpenImmersion.lift j.hom.left F.hom.left hr)
  dsimp only [LocallyRingedSpace.IsOpenImmersion.lift]
  infer_instance

private theorem cancelOpen {A B C : SourceReducedComplexSpace} (j : B ⟶ C)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) {f g : A ⟶ B} (h : f ≫ j = g ≫ j) : f = g := by
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro a
  exact hj.base_open.injective (congrArg (fun F : A ⟶ C => F.hom.left.base a) h)

private theorem openModelInclusion_isOpenImmersion {n : ℕ} {M : CMfd.{0} n} (U : Opens M) :
    LocallyRingedSpace.IsOpenImmersion
      (nativeMorphism (n := n) (m := n) (M := U) (N := M) contMDiff_subtype_val).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion (actualOpenSubspaceMap (n := n) (univ : Set M) U)
  exact actualOpenSubspaceMap_isOpenImmersion _ _

variable {X Y : SourceReducedComplexSpace} (p : Y ⟶ X) (hp : IsResolution p)
  (A : ∀ c, ComponentModel hp.1 c)

private def family (c : ConnectedComponents Y.obj.left) : SourceReducedComplexSpace :=
  wholeModel (n := (A c).dimension) (componentTerminal p hp A c)

private def jMap (c : ConnectedComponents Y.obj.left) :
    wholeModel (n := (A c).dimension) (A c).manifold ⟶ Y :=
  HironakaG1NativeCleanupComparisonLaws.componentModelMap p hp A c

private def qMap (c : ConnectedComponents Y.obj.left) :
    family p hp A c ⟶ wholeModel (n := (A c).dimension) (A c).manifold :=
  HironakaG1NativeCleanupComparisonLaws.componentPrincipalMap p hp A c

private theorem jMap_open (c : ConnectedComponents Y.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (jMap p hp A c).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion ((A c).model.hom.hom.left ≫
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c).hom.left)
  infer_instance

private theorem jMap_range (c : ConnectedComponents Y.obj.left) :
    range (jMap p hp A c).hom.left.base = OriginalSmoothComponents.componentSet c := by
  change range ((HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c).hom.left.base ∘
    (A c).model.hom.hom.left.base) = _
  have he : range (A c).model.hom.hom.left.base = univ :=
    range_eq_univ.mpr (isoHomeomorph (A c).model).surjective
  rw [range_comp, he, image_univ]
  exact HironakaG1NoncompactSmoothComponentModel.componentInclusion_range hp.1 c

private theorem jMap_cover (y : Y.obj.left) :
    ∃ (c : ConnectedComponents Y.obj.left)
      (m : (wholeModel (n := (A c).dimension) (A c).manifold).obj.left),
        (jMap p hp A c).hom.left.base m = y := by
  obtain ⟨c, t, ht⟩ := HironakaG1NoncompactSmoothComponentModel.componentInclusion_jointly_surjective hp.1 y
  obtain ⟨m, hm⟩ := (isoHomeomorph (A c).model).surjective t
  refine ⟨c, m, ?_⟩
  change (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c).hom.left.base
    ((A c).model.hom.hom.left.base m) = y
  exact (congrArg (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c).hom.left.base hm).trans ht

private theorem jMap_disjoint : Pairwise (fun c d =>
    Disjoint (range (jMap p hp A c).hom.left.base) (range (jMap p hp A d).hom.left.base)) := by
  simpa only [jMap_range] using (OriginalSmoothComponents.componentSet_pairwise_disjoint (X := Y))

private theorem family_square (c : ConnectedComponents Y.obj.left) :
    HironakaG1NativeDisjointCoproduct.inclusion (family p hp A) c ≫ cleanupProjection p hp A =
      qMap p hp A c ≫ jMap p hp A c := by
  change HironakaG1NativeDisjointCoproduct.inclusion (family p hp A) c ≫
    HironakaG1NativeDisjointCoproduct.desc (family p hp A) (componentCleanupMap p hp A) = _
  rw [HironakaG1NativeDisjointCoproduct.inclusion_desc]
  exact Category.assoc _ _ _

/-- Actual component proper principalizations give properness of the SAME generic cleanup. -/
theorem cleanupProjection_isProperMap : IsProperMap (cleanupProjection p hp A).hom.left.base := by
  have h := HironakaG1NativeDisjointCoproduct.desc_isProperMap_of_disjoint_cover (family p hp A)
    (jMap p hp A) (jMap_open p hp A) (jMap_cover p hp A) (jMap_disjoint p hp A)
    (qMap p hp A) (fun c => (HironakaG1NativeCleanupComparisonLaws.component_principal_geometry p hp A c).1.1)
  have heq : HironakaG1NativeDisjointCoproduct.desc (family p hp A)
      (fun c => qMap p hp A c ≫ jMap p hp A c) = cleanupProjection p hp A := by
    apply HironakaG1NativeDisjointCoproduct.hom_ext (family p hp A)
    intro c
    rw [HironakaG1NativeDisjointCoproduct.inclusion_desc]
    exact (family_square p hp A c).symm
  rwa [heq] at h

private def jPoint (c : ConnectedComponents Y.obj.left) (x : (A c).manifold) : Y.obj.left :=
  (jMap p hp A c).hom.left.base ⟨x, mem_univ x⟩

private theorem jPoint_closed (c : ConnectedComponents Y.obj.left) :
    IsClosedEmbedding (jPoint p hp A c) := by
  let H := (Homeomorph.Set.univ (A c).manifold).symm.trans (isoHomeomorph (A c).model)
  change IsClosedEmbedding ((HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c).hom.left.base ∘ H)
  exact (OriginalSmoothComponents.component_isClopen hp.1 c).1.isClosedEmbedding_subtypeVal.comp H.isClosedEmbedding

private def modelOpen (U : Opens Y.obj.left) (c : ConnectedComponents Y.obj.left) : Opens (A c).manifold :=
  ⟨(jPoint p hp A c) ⁻¹' (U : Set Y.obj.left), U.isOpen.preimage (jPoint_closed p hp A c).continuous⟩

private theorem modelOpen_compactClosure (U : Opens Y.obj.left)
    (hU : IsCompact (closure (U : Set Y.obj.left))) (c : ConnectedComponents Y.obj.left) :
    IsCompact (closure (modelOpen p hp A U c : Set (A c).manifold)) := by
  let : T2Space Y.obj.left := Y.property.1
  have hK := (jPoint_closed p hp A c).isProperMap.isCompact_preimage hU
  apply hK.of_isClosed_subset isClosed_closure
  exact closure_minimal (fun x hx => subset_closure hx)
    (isClosed_closure.preimage (jPoint_closed p hp A c).continuous)

private def componentRecord (c : ConnectedComponents Y.obj.left) :
    MarkedIdeal (A c).dimension (A c).manifold :=
  modelMarkedIdeal (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p) (A c).model

private theorem componentDomain (c : ConnectedComponents Y.obj.left) :
    IsInvDomain (A c).dimension (componentRecord p hp A c) :=
  modelMarkedDomain (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p)
    (componentThin p hp c) (A c).model

private def sourceOpen (U : Opens Y.obj.left) (c : ConnectedComponents Y.obj.left) :
    Opens (componentTerminal p hp A c) :=
  HironakaG1OriginalTerminalOpenRestriction.terminalPreimageOpen
    (componentRecord p hp A c) (componentDomain p hp A c) (modelOpen p hp A U c)

private def targetPiece (U : Opens Y.obj.left) (c : ConnectedComponents Y.obj.left) : SourceReducedComplexSpace :=
  wholeModel (n := (A c).dimension) (modelOpen p hp A U c)

private def sourcePiece (U : Opens Y.obj.left) (c : ConnectedComponents Y.obj.left) : SourceReducedComplexSpace :=
  wholeModel (n := (A c).dimension) (sourceOpen p hp A U c)

private def pieceProjection (U : Opens Y.obj.left) (c : ConnectedComponents Y.obj.left) :
    sourcePiece p hp A U c ⟶ targetPiece p hp A U c :=
  restrictedProjection (X := (A c).manifold) (componentRecord p hp A c)
    (componentDomain p hp A c) (modelOpen p hp A U c)

private theorem pieceProjection_finite (U : Opens Y.obj.left)
    (hU : IsCompact (closure (U : Set Y.obj.left))) (c : ConnectedComponents Y.obj.left) :
    IsModification (pieceProjection p hp A U c) :=
  restrictedProjection_isModification (X := (A c).manifold) (componentRecord p hp A c)
    (componentDomain p hp A c) (modelOpen p hp A U c) (modelOpen_compactClosure p hp A U hU c)

private def targetOriginal (U : Opens Y.obj.left) (c : ConnectedComponents Y.obj.left) :
    targetPiece p hp A U c ⟶ Y :=
  nativeMorphism (n := (A c).dimension) (m := (A c).dimension)
    (M := modelOpen p hp A U c) (N := (A c).manifold) contMDiff_subtype_val ≫ jMap p hp A c

private def sourceOriginal (U : Opens Y.obj.left) (c : ConnectedComponents Y.obj.left) :
    sourcePiece p hp A U c ⟶ cleanupSource p hp A :=
  nativeMorphism (n := (A c).dimension) (m := (A c).dimension)
    (M := sourceOpen p hp A U c) (N := componentTerminal p hp A c) contMDiff_subtype_val ≫
      HironakaG1NativeDisjointCoproduct.inclusion (family p hp A) c

private theorem targetOriginal_open (U : Opens Y.obj.left) (c : ConnectedComponents Y.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (targetOriginal p hp A U c).hom.left := by
  let : LocallyRingedSpace.IsOpenImmersion (nativeMorphism (n := (A c).dimension) (m := (A c).dimension)
    (M := modelOpen p hp A U c) (N := (A c).manifold) contMDiff_subtype_val).hom.left :=
    openModelInclusion_isOpenImmersion (modelOpen p hp A U c)
  let : LocallyRingedSpace.IsOpenImmersion (jMap p hp A c).hom.left := jMap_open p hp A c
  change LocallyRingedSpace.IsOpenImmersion (_ ≫ (jMap p hp A c).hom.left)
  infer_instance

private theorem sourceOriginal_open (U : Opens Y.obj.left) (c : ConnectedComponents Y.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (sourceOriginal p hp A U c).hom.left := by
  let : LocallyRingedSpace.IsOpenImmersion (nativeMorphism (n := (A c).dimension) (m := (A c).dimension)
    (M := sourceOpen p hp A U c) (N := componentTerminal p hp A c) contMDiff_subtype_val).hom.left :=
    openModelInclusion_isOpenImmersion (sourceOpen p hp A U c)
  let : LocallyRingedSpace.IsOpenImmersion
      (HironakaG1NativeDisjointCoproduct.inclusion (family p hp A) c).hom.left :=
    HironakaG1NativeDisjointCoproduct.inclusion_isOpenImmersion (family p hp A) c
  change LocallyRingedSpace.IsOpenImmersion (_ ≫
    (HironakaG1NativeDisjointCoproduct.inclusion (family p hp A) c).hom.left)
  infer_instance

private theorem pieceOriginal_square (U : Opens Y.obj.left) (c : ConnectedComponents Y.obj.left) :
    sourceOriginal p hp A U c ≫ cleanupProjection p hp A =
      pieceProjection p hp A U c ≫ targetOriginal p hp A U c := by
  have hs := restrictedProjection_square (X := (A c).manifold) (componentRecord p hp A c)
    (componentDomain p hp A c) (modelOpen p hp A U c)
  change pieceProjection p hp A U c ≫
      nativeMorphism (n := (A c).dimension) (m := (A c).dimension)
        (M := modelOpen p hp A U c) (N := (A c).manifold) contMDiff_subtype_val =
    nativeMorphism (n := (A c).dimension) (m := (A c).dimension)
      (M := sourceOpen p hp A U c) (N := componentTerminal p hp A c) contMDiff_subtype_val ≫ qMap p hp A c at hs
  change (nativeMorphism _ ≫ HironakaG1NativeDisjointCoproduct.inclusion (family p hp A) c) ≫ _ = _
  rw [Category.assoc, family_square, ← Category.assoc, ← hs, Category.assoc]
  rfl

private theorem targetOriginal_mem (U : Opens Y.obj.left) (c : ConnectedComponents Y.obj.left)
    (b : (targetPiece p hp A U c).obj.left) : (targetOriginal p hp A U c).hom.left.base b ∈ U := by
  exact b.val.property

private def sourceRestriction (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left))) :
    SourceReducedComplexSpace :=
  OriginalRelativelyCompactRestriction.preimageRestriction U (cleanupProjection p hp A) hU
    (cleanupProjection_isProperMap p hp A)

private def sourceInclusion (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left))) :
    sourceRestriction p hp A U hU ⟶ cleanupSource p hp A :=
  OriginalRelativelyCompactRestriction.inclusion (cleanupSource p hp A)
    (OriginalRelativelyCompactRestriction.preimageOpen U (cleanupProjection p hp A))
    (OriginalRelativelyCompactRestriction.isCompact_closure_preimage U (cleanupProjection p hp A) hU
      (cleanupProjection_isProperMap p hp A))

private theorem sourceInclusion_open (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left))) :
    LocallyRingedSpace.IsOpenImmersion (sourceInclusion p hp A U hU).hom.left := by
  apply OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion

private def rawProjection (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left))) :
    sourceRestriction p hp A U hU ⟶ OriginalRelativelyCompactRestriction.restriction Y U hU :=
  OriginalRelativelyCompactRestriction.restrictionProjection U (cleanupProjection p hp A) hU
    (cleanupProjection_isProperMap p hp A)

private theorem rawProjection_square (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left))) :
    rawProjection p hp A U hU ≫ OriginalRelativelyCompactRestriction.inclusion Y U hU =
      sourceInclusion p hp A U hU ≫ cleanupProjection p hp A :=
  OriginalRelativelyCompactRestriction.restrictionProjection_inclusion U (cleanupProjection p hp A) hU
    (cleanupProjection_isProperMap p hp A)

private theorem targetOriginal_range (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left)))
    (c : ConnectedComponents Y.obj.left) : range (targetOriginal p hp A U c).hom.left.base ⊆
      range (OriginalRelativelyCompactRestriction.inclusion Y U hU).hom.left.base := by
  rw [OriginalRelativelyCompactRestriction.inclusion_range]
  rintro _ ⟨b, rfl⟩
  exact targetOriginal_mem p hp A U c b

private theorem sourceOriginal_range (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left)))
    (c : ConnectedComponents Y.obj.left) : range (sourceOriginal p hp A U c).hom.left.base ⊆
      range (sourceInclusion p hp A U hU).hom.left.base := by
  change range (sourceOriginal p hp A U c).hom.left.base ⊆ range
    (OriginalRelativelyCompactRestriction.inclusion (cleanupSource p hp A)
      (OriginalRelativelyCompactRestriction.preimageOpen U (cleanupProjection p hp A)) _).hom.left.base
  rw [OriginalRelativelyCompactRestriction.inclusion_range]
  rintro _ ⟨a, rfl⟩
  have hs := congrArg (fun F : sourcePiece p hp A U c ⟶ Y => F.hom.left.base a) (pieceOriginal_square p hp A U c)
  change (cleanupProjection p hp A).hom.left.base ((sourceOriginal p hp A U c).hom.left.base a) =
    (targetOriginal p hp A U c).hom.left.base ((pieceProjection p hp A U c).hom.left.base a) at hs
  change (cleanupProjection p hp A).hom.left.base ((sourceOriginal p hp A U c).hom.left.base a) ∈ U
  rw [hs]
  exact targetOriginal_mem p hp A U c ((pieceProjection p hp A U c).hom.left.base a)

private def targetEmbedding (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left)))
    (c : ConnectedComponents Y.obj.left) : targetPiece p hp A U c ⟶ OriginalRelativelyCompactRestriction.restriction Y U hU :=
  liftOpen (OriginalRelativelyCompactRestriction.inclusion Y U hU)
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion Y U hU)
    (targetOriginal p hp A U c) (targetOriginal_range p hp A U hU c)

private def sourceEmbedding (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left)))
    (c : ConnectedComponents Y.obj.left) : sourcePiece p hp A U c ⟶ sourceRestriction p hp A U hU :=
  liftOpen (sourceInclusion p hp A U hU) (sourceInclusion_open p hp A U hU)
    (sourceOriginal p hp A U c) (sourceOriginal_range p hp A U hU c)

private theorem targetEmbedding_fac (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left)))
    (c : ConnectedComponents Y.obj.left) : targetEmbedding p hp A U hU c ≫
      OriginalRelativelyCompactRestriction.inclusion Y U hU = targetOriginal p hp A U c :=
  liftOpen_fac _ _ _ _

private theorem sourceEmbedding_fac (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left)))
    (c : ConnectedComponents Y.obj.left) : sourceEmbedding p hp A U hU c ≫
      sourceInclusion p hp A U hU = sourceOriginal p hp A U c := liftOpen_fac _ _ _ _

private theorem targetEmbedding_open (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left)))
    (c : ConnectedComponents Y.obj.left) : LocallyRingedSpace.IsOpenImmersion (targetEmbedding p hp A U hU c).hom.left :=
  liftOpen_isOpenImmersion _ _ _ (targetOriginal_open p hp A U c) _

private theorem sourceEmbedding_open (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left)))
    (c : ConnectedComponents Y.obj.left) : LocallyRingedSpace.IsOpenImmersion (sourceEmbedding p hp A U hU c).hom.left :=
  liftOpen_isOpenImmersion _ _ _ (sourceOriginal_open p hp A U c) _

private theorem local_square (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left)))
    (c : ConnectedComponents Y.obj.left) : sourceEmbedding p hp A U hU c ≫ rawProjection p hp A U hU =
      pieceProjection p hp A U c ≫ targetEmbedding p hp A U hU c := by
  apply cancelOpen (OriginalRelativelyCompactRestriction.inclusion Y U hU)
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion Y U hU)
  rw [Category.assoc, rawProjection_square, ← Category.assoc, sourceEmbedding_fac,
    Category.assoc, targetEmbedding_fac]
  exact pieceOriginal_square p hp A U c

private theorem targetEmbedding_range (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left)))
    (c : ConnectedComponents Y.obj.left) :
    range (targetEmbedding p hp A U hU c).hom.left.base =
      (Subtype.val : (OriginalRelativelyCompactRestriction.restriction Y U hU).obj.left → Y.obj.left) ⁻¹'
        OriginalSmoothComponents.componentSet c := by
  ext y
  constructor
  · rintro ⟨b, rfl⟩
    have hf := congrArg (fun F : targetPiece p hp A U c ⟶ Y => F.hom.left.base b)
      (targetEmbedding_fac p hp A U hU c)
    change ((targetEmbedding p hp A U hU c).hom.left.base b).val =
      (targetOriginal p hp A U c).hom.left.base b at hf
    change ((targetEmbedding p hp A U hU c).hom.left.base b).val ∈ OriginalSmoothComponents.componentSet c
    rw [hf, ← jMap_range p hp A c]
    let m : (wholeModel (n := (A c).dimension) (A c).manifold).obj.left := ⟨b.val.val, mem_univ _⟩
    exact ⟨m, rfl⟩
  · intro hy
    change y.val ∈ OriginalSmoothComponents.componentSet c at hy
    rw [← jMap_range p hp A c] at hy
    obtain ⟨m, hm⟩ := hy
    have hm' : jPoint p hp A c m.val = y.val := by
      have hη : (⟨m.val, mem_univ _⟩ : (wholeModel (n := (A c).dimension) (A c).manifold).obj.left) = m :=
        Subtype.ext rfl
      exact (congrArg (jMap p hp A c).hom.left.base hη).trans hm
    have hx : m.val ∈ modelOpen p hp A U c := by
      change jPoint p hp A c m.val ∈ U
      rw [hm']
      exact y.property
    let b : (targetPiece p hp A U c).obj.left := ⟨⟨m.val, hx⟩, mem_univ _⟩
    refine ⟨b, ?_⟩
    apply (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion Y U hU).base_open.injective
    have hf := congrArg (fun F : targetPiece p hp A U c ⟶ Y => F.hom.left.base b)
      (targetEmbedding_fac p hp A U hU c)
    exact hf.trans hm'

private theorem targetEmbedding_closed (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left)))
    (c : ConnectedComponents Y.obj.left) : IsClosed (range (targetEmbedding p hp A U hU c).hom.left.base) := by
  rw [targetEmbedding_range]
  exact (OriginalSmoothComponents.component_isClopen hp.1 c).1.preimage
    (OriginalRelativelyCompactRestriction.inclusion Y U hU).hom.left.base.hom.continuous

private theorem targetEmbeddings_disjoint {N : ℕ} (U : Opens Y.obj.left)
    (hU : IsCompact (closure (U : Set Y.obj.left))) (κ : Fin N → ConnectedComponents Y.obj.left)
    (hκ : Injective κ) : Pairwise (fun i k =>
      Disjoint (range (targetEmbedding p hp A U hU (κ i)).hom.left.base)
        (range (targetEmbedding p hp A U hU (κ k)).hom.left.base)) := by
  intro i k hik
  rw [targetEmbedding_range, targetEmbedding_range]
  exact (OriginalSmoothComponents.componentSet_pairwise_disjoint (X := Y) (hκ.ne hik)).preimage _

private theorem targetEmbeddings_cover {N : ℕ} (U : Opens Y.obj.left)
    (hU : IsCompact (closure (U : Set Y.obj.left))) (κ : Fin N → ConnectedComponents Y.obj.left)
    (hcover : ∀ y ∈ U, ∃ i, y ∈ OriginalSmoothComponents.componentSet (κ i))
    (y : (OriginalRelativelyCompactRestriction.restriction Y U hU).obj.left) :
    ∃ (i : Fin N) (b : (targetPiece p hp A U (κ i)).obj.left),
      (targetEmbedding p hp A U hU (κ i)).hom.left.base b = y := by
  obtain ⟨i, hi⟩ := hcover y.val y.property
  have hr : y ∈ range (targetEmbedding p hp A U hU (κ i)).hom.left.base := by
    rw [targetEmbedding_range]
    exact hi
  obtain ⟨b, hb⟩ := hr
  exact ⟨i, b, hb⟩

private theorem sourceEmbeddings_cover {N : ℕ} (U : Opens Y.obj.left)
    (hU : IsCompact (closure (U : Set Y.obj.left))) (κ : Fin N → ConnectedComponents Y.obj.left)
    (hcover : ∀ y ∈ U, ∃ i, y ∈ OriginalSmoothComponents.componentSet (κ i))
    (z : (sourceRestriction p hp A U hU).obj.left) :
    ∃ (i : Fin N) (a : (sourcePiece p hp A U (κ i)).obj.left),
      (sourceEmbedding p hp A U hU (κ i)).hom.left.base a = z := by
  obtain ⟨c, y, hy⟩ := HironakaG1NativeDisjointCoproduct.inclusion_jointly_surjective (family p hp A) z.val
  have hpt := congrArg (fun F : family p hp A c ⟶ Y => F.hom.left.base y) (family_square p hp A c)
  change (cleanupProjection p hp A).hom.left.base
      ((HironakaG1NativeDisjointCoproduct.inclusion (family p hp A) c).hom.left.base y) =
    (jMap p hp A c).hom.left.base ((qMap p hp A c).hom.left.base y) at hpt
  have hcy : (cleanupProjection p hp A).hom.left.base z.val ∈ OriginalSmoothComponents.componentSet c := by
    rw [← jMap_range p hp A c]
    exact ⟨(qMap p hp A c).hom.left.base y,
      hpt.symm.trans (congrArg (cleanupProjection p hp A).hom.left.base hy)⟩
  obtain ⟨i, hi⟩ := hcover _ z.property
  change ConnectedComponents.mk ((cleanupProjection p hp A).hom.left.base z.val) = c at hcy
  change ConnectedComponents.mk ((cleanupProjection p hp A).hom.left.base z.val) = κ i at hi
  have hc : c = κ i := hcy.symm.trans hi
  clear hcy hi
  subst c
  have hx : originalTerminalGluedProjection (X := (A (κ i)).manifold)
      (componentRecord p hp A (κ i)) (componentDomain p hp A (κ i)) y.val ∈ modelOpen p hp A U (κ i) := by
    change jPoint p hp A (κ i) (originalTerminalGluedProjection (X := (A (κ i)).manifold)
      (componentRecord p hp A (κ i)) (componentDomain p hp A (κ i)) y.val) ∈ U
    change (cleanupProjection p hp A).hom.left.base
      ((HironakaG1NativeDisjointCoproduct.inclusion (family p hp A) (κ i)).hom.left.base y) =
      jPoint p hp A (κ i) (originalTerminalGluedProjection (X := (A (κ i)).manifold)
        (componentRecord p hp A (κ i)) (componentDomain p hp A (κ i)) y.val) at hpt
    rw [← hpt, hy]
    exact z.property
  let a : (sourcePiece p hp A U (κ i)).obj.left := ⟨⟨y.val, hx⟩, mem_univ _⟩
  refine ⟨i, a, ?_⟩
  apply (sourceInclusion_open p hp A U hU).base_open.injective
  have hf := congrArg (fun F : sourcePiece p hp A U (κ i) ⟶ cleanupSource p hp A => F.hom.left.base a)
    (sourceEmbedding_fac p hp A U hU (κ i))
  have hg : (sourceOriginal p hp A U (κ i)).hom.left.base a = z.val := by
    change (HironakaG1NativeDisjointCoproduct.inclusion (family p hp A) (κ i)).hom.left.base
      ⟨y.val, mem_univ _⟩ = z.val
    exact (congrArg (HironakaG1NativeDisjointCoproduct.inclusion (family p hp A) (κ i)).hom.left.base
      (Subtype.ext rfl)).trans hy
  exact hf.trans hg

/-- Ordinary compact closure internally constructs REAL finite cleanup pieces,
covering the SAME literal native target and inverse-open source. -/
theorem exists_finite_cleanup_window_cover (U : Opens Y.obj.left)
    (hU : IsCompact (closure (U : Set Y.obj.left))) :
    ∃ (N : ℕ) (B D : Fin N → SourceReducedComplexSpace)
      (j : ∀ i, B i ⟶ OriginalRelativelyCompactRestriction.restriction Y U hU)
      (L : ∀ i, D i ⟶ sourceRestriction p hp A U hU) (q : ∀ i, D i ⟶ B i),
      (∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left) ∧
      (∀ i, IsClosed (range (j i).hom.left.base)) ∧
      Pairwise (fun i k => Disjoint (range (j i).hom.left.base) (range (j k).hom.left.base)) ∧
      (∀ y, ∃ i b, (j i).hom.left.base b = y) ∧
      (∀ i, LocallyRingedSpace.IsOpenImmersion (L i).hom.left) ∧
      (∀ z, ∃ i a, (L i).hom.left.base a = z) ∧
      (∀ i, IsModification (q i)) ∧
      (∀ i, L i ≫ rawProjection p hp A U hU = q i ≫ j i) := by
  classical
  obtain ⟨s, hs⟩ := hU.elim_finite_subcover
    (fun c : ConnectedComponents Y.obj.left => OriginalSmoothComponents.componentSet c)
    (fun c => (OriginalSmoothComponents.component_isClopen hp.1 c).2)
    (by intro y _; exact mem_iUnion.mpr ⟨ConnectedComponents.mk y, rfl⟩)
  let e : Fin (Fintype.card s) ≃ s := (Fintype.equivFin s).symm
  let κ : Fin (Fintype.card s) → ConnectedComponents Y.obj.left := fun i => (e i).val
  have hκ : Injective κ := fun i k h => e.injective (Subtype.ext h)
  have hcover : ∀ y ∈ U, ∃ i, y ∈ OriginalSmoothComponents.componentSet (κ i) := by
    intro y hy
    obtain ⟨c, hcs, hcy⟩ := mem_iUnion₂.mp (hs (subset_closure hy))
    refine ⟨e.symm ⟨c, hcs⟩, ?_⟩
    change y ∈ OriginalSmoothComponents.componentSet ((e (e.symm ⟨c, hcs⟩)).val)
    rw [e.apply_symm_apply]
    exact hcy
  exact ⟨Fintype.card s, (fun i => targetPiece p hp A U (κ i)), (fun i => sourcePiece p hp A U (κ i)),
    (fun i => targetEmbedding p hp A U hU (κ i)), (fun i => sourceEmbedding p hp A U hU (κ i)),
    (fun i => pieceProjection p hp A U (κ i)),
    (fun i => targetEmbedding_open p hp A U hU (κ i)),
    (fun i => targetEmbedding_closed p hp A U hU (κ i)), targetEmbeddings_disjoint p hp A U hU κ hκ,
    targetEmbeddings_cover p hp A U hU κ hcover, (fun i => sourceEmbedding_open p hp A U hU (κ i)),
    sourceEmbeddings_cover p hp A U hU κ hcover, (fun i => pieceProjection_finite p hp A U hU (κ i)),
    (fun i => local_square p hp A U hU (κ i))⟩

/-- REAL finite modification on the SAME literal generic cleanup inverse-open projection. -/
theorem cleanupProjection_restriction_isModification (U : Opens Y.obj.left)
    (hU : IsCompact (closure (U : Set Y.obj.left))) :
    IsModification (OriginalRelativelyCompactRestriction.restrictionProjection U (cleanupProjection p hp A) hU
      (cleanupProjection_isProperMap p hp A)) := by
  obtain ⟨N, B, D, j, L, q, hj, hjc, hdisj, hjcover, hL, hLcover, hq, hsq⟩ :=
    exists_finite_cleanup_window_cover p hp A U hU
  exact HironakaG1FiniteClopenModification.isModification_of_finite_clopen_cover
    (rawProjection p hp A U hU) j L q hj hjc hdisj hjcover hL hLcover hq hsq

private theorem exists_restrictedSourceIso {Z Z' : SourceReducedComplexSpace}
    (f : Z ⟶ Y) (f' : Z' ⟶ Y) (hf : IsProperMap f.hom.left.base) (hf' : IsProperMap f'.hom.left.base)
    (E : Z' ≅ Z) (hE : E.hom ≫ f = f')
    (U : Opens Y.obj.left) (hU : IsCompact (closure (U : Set Y.obj.left))) :
    ∃ e : OriginalRelativelyCompactRestriction.preimageRestriction U f' hU hf' ≅
        OriginalRelativelyCompactRestriction.preimageRestriction U f hU hf,
      e.hom ≫ OriginalRelativelyCompactRestriction.restrictionProjection U f hU hf =
        OriginalRelativelyCompactRestriction.restrictionProjection U f' hU hf' := by
  let I : OriginalRelativelyCompactRestriction.preimageRestriction U f hU hf ⟶ Z :=
    OriginalRelativelyCompactRestriction.inclusion Z (OriginalRelativelyCompactRestriction.preimageOpen U f)
      (OriginalRelativelyCompactRestriction.isCompact_closure_preimage U f hU hf)
  let I' : OriginalRelativelyCompactRestriction.preimageRestriction U f' hU hf' ⟶ Z' :=
    OriginalRelativelyCompactRestriction.inclusion Z' (OriginalRelativelyCompactRestriction.preimageOpen U f')
      (OriginalRelativelyCompactRestriction.isCompact_closure_preimage U f' hU hf')
  have hI : LocallyRingedSpace.IsOpenImmersion I.hom.left :=
    OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _
  have hI' : LocallyRingedSpace.IsOpenImmersion I'.hom.left :=
    OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion _ _ _
  have hEinv : E.inv ≫ f' = f := by rw [← hE, Iso.inv_hom_id_assoc]
  have hr : range (I' ≫ E.hom).hom.left.base ⊆ range I.hom.left.base := by
    have hIr : range I.hom.left.base = f.hom.left.base ⁻¹' (U : Set Y.obj.left) :=
      OriginalRelativelyCompactRestriction.inclusion_range _ _ _
    rw [hIr]
    rintro _ ⟨z, rfl⟩
    change f.hom.left.base (E.hom.hom.left.base z.val) ∈ U
    have ht := congrArg (fun g : Z' ⟶ Y => g.hom.left.base z.val) hE
    change f.hom.left.base (E.hom.hom.left.base z.val) = f'.hom.left.base z.val at ht
    rw [ht]
    exact z.property
  have hr' : range (I ≫ E.inv).hom.left.base ⊆ range I'.hom.left.base := by
    have hIr : range I'.hom.left.base = f'.hom.left.base ⁻¹' (U : Set Y.obj.left) :=
      OriginalRelativelyCompactRestriction.inclusion_range _ _ _
    rw [hIr]
    rintro _ ⟨z, rfl⟩
    change f'.hom.left.base (E.inv.hom.left.base z.val) ∈ U
    have ht := congrArg (fun g : Z ⟶ Y => g.hom.left.base z.val) hEinv
    change f'.hom.left.base (E.inv.hom.left.base z.val) = f.hom.left.base z.val at ht
    rw [ht]
    exact z.property
  let L := liftOpen I hI (I' ≫ E.hom) hr
  let K := liftOpen I' hI' (I ≫ E.inv) hr'
  have hL : L ≫ I = I' ≫ E.hom := liftOpen_fac _ _ _ _
  have hK : K ≫ I' = I ≫ E.inv := liftOpen_fac _ _ _ _
  let e : OriginalRelativelyCompactRestriction.preimageRestriction U f' hU hf' ≅
      OriginalRelativelyCompactRestriction.preimageRestriction U f hU hf :=
    { hom := L
      inv := K
      hom_inv_id := by
        apply cancelOpen I' hI'
        rw [Category.assoc, hK, ← Category.assoc, hL, Category.assoc,
          Iso.hom_inv_id, Category.comp_id, Category.id_comp]
      inv_hom_id := by
        apply cancelOpen I hI
        rw [Category.assoc, hL, ← Category.assoc, hK, Category.assoc,
          Iso.inv_hom_id, Category.comp_id, Category.id_comp] }
  refine ⟨e, ?_⟩
  apply cancelOpen (OriginalRelativelyCompactRestriction.inclusion Y U hU)
    (OriginalRelativelyCompactRestriction.inclusion_isOpenImmersion Y U hU)
  change (L ≫ OriginalRelativelyCompactRestriction.restrictionProjection U f hU hf) ≫
      OriginalRelativelyCompactRestriction.inclusion Y U hU = _
  rw [Category.assoc, OriginalRelativelyCompactRestriction.restrictionProjection_inclusion,
    ← Category.assoc, hL, Category.assoc, hE]
  exact (OriginalRelativelyCompactRestriction.restrictionProjection_inclusion U f' hU hf').symm

/-- REAL finite modification of the LITERAL restriction of the SAME chosen strong projection. -/
theorem strongRefinement_restriction_isModification
    (hReg : IsIsoOver p (intrinsicRegularLocus X.obj)) (U : Opens Y.obj.left)
    (hU : IsCompact (closure (U : Set Y.obj.left))) :
    IsModification (OriginalRelativelyCompactRestriction.restrictionProjection U
      (HironakaG1NativeStrongCleanup.strongRefinement p hp) hU
      (HironakaG1NativeStrongCleanup.strong_geometry p hp hReg).2.1) := by
  let A' := HironakaG1NativeStrongCleanupFunctor.strongModels p hp
  let f := cleanupProjection p hp A'
  let f' := HironakaG1NativeStrongCleanup.strongRefinement p hp
  let hf := cleanupProjection_isProperMap p hp A'
  let hf' := (HironakaG1NativeStrongCleanup.strong_geometry p hp hReg).2.1
  obtain ⟨e, he⟩ := exists_restrictedSourceIso f f' hf hf'
    (HironakaG1NativeStrongCleanupFunctor.alignment p hp)
    (HironakaG1NativeStrongCleanupFunctor.alignment_overY p hp) U hU
  have hfinite := isModification_precomp_iso (cleanupProjection_restriction_isModification p hp A' U hU) e
  exact he ▸ hfinite

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeFiniteCleanupRestriction
