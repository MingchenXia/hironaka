import Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupComponentModelIndependence
import Hironaka.Analytic.Unibranch.HironakaG1NativeIsoOverDisjointCover
import Hironaka.Analytic.Unibranch.HironakaG11LiftUniqueness
import Hironaka.Analytic.Unibranch.SourceMorphismExt
import Hironaka.Resolution.HironakaOriginalGlobalProperModification

/-! # Unique actual native cleanup comparisons

The good open is the complement of the WHOLE inverse ORIGINAL singular
ideal, not all of the already smooth source Y. Actual component
principalizations derive proper-bimeromorphicity, full native good-locus
isomorphisms and source density. Held dense-lift uniqueness and full native
morphism faithfulness then derive comparison identity and cocycle laws.
Blueprint is written before this source.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupComparisonLaws

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaReducedComplexAnalyticSpaces
  HironakaEmbeddedNativeMorphism HironakaOriginalTerminalAtlas HironakaOriginalTerminalManifold
  HironakaOriginalGlobalPrincipalization HironakaOriginalGlobalProperModification
  HironakaOriginalGlobalOffZero HironakaIntrinsicComplexAnalyticRegularLocus
  HironakaResolutionSpaceComplex HironakaG10ChowGermIdealDictionary
  HironakaNativePulledIdealSheaf
  SourceReducedComplexSpace OriginalNativeModification OriginalIntrinsicSingularLocus
  HironakaG1OriginalSingularCleanup HironakaG1NativeCleanupModelIndependence
  HironakaG1NativeCleanupComponentModelIndependence
open ResolutionInvariantSpec (IsInvDomain)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

noncomputable section

variable {X Y : SourceReducedComplexSpace} (p : Y ⟶ X) (hp : IsResolution p)

/-- The full actual model map to its SAME original connected component in Y. -/
def componentModelMap (A : ∀ c, ComponentModel hp.1 c) (c : ConnectedComponents Y.obj.left) :
    wholeModel (n := (A c).dimension) (A c).manifold ⟶ Y :=
  (A c).model.hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c

/-- The actual native terminal principalization arrow before the component model. -/
def componentPrincipalMap (A : ∀ c, ComponentModel hp.1 c)
    (c : ConnectedComponents Y.obj.left) :
    wholeModel (n := (A c).dimension) (componentTerminal p hp A c) ⟶
      wholeModel (n := (A c).dimension) (A c).manifold :=
  nativeMorphism (originalTerminalGluedProjection_contMDiff
    (modelMarkedIdeal (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p)
      (A c).model)
    (modelMarkedDomain (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p)
      (componentThin p hp c) (A c).model))

private theorem componentModelMap_open (A : ∀ c, ComponentModel hp.1 c)
    (c : ConnectedComponents Y.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (componentModelMap p hp A c).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion ((A c).model.hom.hom.left ≫
    (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c).hom.left)
  infer_instance

private theorem componentModelMap_range (A : ∀ c, ComponentModel hp.1 c)
    (c : ConnectedComponents Y.obj.left) :
    range (componentModelMap p hp A c).hom.left.base = OriginalSmoothComponents.componentSet c := by
  change range ((HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c).hom.left.base ∘
    (A c).model.hom.hom.left.base) = _
  have he : range (A c).model.hom.hom.left.base = univ :=
    range_eq_univ.mpr (isoHomeomorph (A c).model).surjective
  rw [range_comp, he, image_univ]
  exact HironakaG1NoncompactSmoothComponentModel.componentInclusion_range hp.1 c

private theorem componentModelMap_cover (A : ∀ c, ComponentModel hp.1 c) (y : Y.obj.left) :
    ∃ (c : ConnectedComponents Y.obj.left)
      (u : (wholeModel (n := (A c).dimension) (A c).manifold).obj.left),
        (componentModelMap p hp A c).hom.left.base u = y := by
  obtain ⟨c, t, ht⟩ := HironakaG1NoncompactSmoothComponentModel.componentInclusion_jointly_surjective hp.1 y
  obtain ⟨u, hu⟩ := (isoHomeomorph (A c).model).surjective t
  refine ⟨c, u, ?_⟩
  change (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c).hom.left.base
    ((A c).model.hom.hom.left.base u) = y
  change (A c).model.hom.hom.left.base u = t at hu
  rw [hu]
  exact ht

private theorem componentModelMap_disjoint (A : ∀ c, ComponentModel hp.1 c) :
    Pairwise fun c d : ConnectedComponents Y.obj.left =>
      Disjoint (range (componentModelMap p hp A c).hom.left.base)
        (range (componentModelMap p hp A d).hom.left.base) := by
  simpa only [componentModelMap_range] using
    (OriginalSmoothComponents.componentSet_pairwise_disjoint (X := Y))

private theorem actualTerminal_isIsoOver {n : ℕ} {M : CMfd.{0} n}
    (T : MarkedIdeal n M) (hT : IsInvDomain n T) (hN : T.N = univ) (hd : T.d = 1) :
    IsIsoOver (nativeMorphism (originalTerminalGluedProjection_contMDiff T hT))
      ((Subtype.val : ↥(univ : Set M) → M) ⁻¹' T.ideal.zeroLocus)ᶜ := by
  let U := originalTerminalOffZeroBaseOpen T hT
  let V := originalTerminalOffZeroSourceOpen T hT
  let e := originalTerminalOffZeroBiholomorphism T hT hN hd
  let E := actualSubspaceBiholomorphicIso e (univ : Set V) (univ : Set U) (fun _ => Iff.rfl)
  let J := actualOpenSubspaceMap (n := n) (univ : Set (originalTerminalManifold T hT)) V
  let K := actualOpenSubspaceMap (n := n) (univ : Set M) U
  have hJ : LocallyRingedSpace.IsOpenImmersion J :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set (originalTerminalManifold T hT)) V
  have hK : LocallyRingedSpace.IsOpenImmersion K :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set M) U
  have hfacCat : nativeMorphism (M := V) (N := originalTerminalManifold T hT) contMDiff_subtype_val ≫
      nativeMorphism (originalTerminalGluedProjection_contMDiff T hT) =
      nativeMorphism e.contMDiff ≫ nativeMorphism (M := U) (N := M) contMDiff_subtype_val := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact (originalTerminalOffZeroBiholomorphism_point T hT hN hd z.val).symm
  have hfac : J ≫ (nativeMorphism (originalTerminalGluedProjection_contMDiff T hT)).hom.left =
      E.hom ≫ K :=
    congrArg (fun H : wholeModel (n := n) V ⟶ wholeModel (n := n) M => H.hom.left) hfacCat
  refine ⟨_, J, hJ, ?_, ?_, ?_⟩
  · exact (range_actualOpenSubspaceMap (n := n) (univ : Set (originalTerminalManifold T hT)) V).trans
      (by rfl)
  · rw [hfac]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ E.hom (inferInstance) K hK
  · exact (congrArg (fun H : actualSubspaceLocallyRingedSpace (n := n)
        (univ : Set V) ⟶ (wholeModel (n := n) M).obj.left => range H.base) hfac).trans
      ((range_iso_hom_comp_base E K).trans
        ((range_actualOpenSubspaceMap (n := n) (univ : Set M) U).trans (by rfl)))

/-- Proper-bimeromorphicity and the precise native good-locus/density clauses
are derived from the ACTUAL terminal principalization, with no output packet. -/
theorem component_principal_geometry (A : ∀ c, ComponentModel hp.1 c)
    (c : ConnectedComponents Y.obj.left) :
    IsProperBimeromorphic (componentPrincipalMap p hp A c) ∧
    IsIsoOver (componentPrincipalMap p hp A c)
      ((componentModelMap p hp A c).hom.left.base ⁻¹'
        (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj)) ∧
    interior ((componentPrincipalMap p hp A c).hom.left.base ⁻¹'
      ((componentModelMap p hp A c).hom.left.base ⁻¹'
        (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj))) = ∅ := by
  let T := modelMarkedIdeal (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p)
    (A c).model
  let hT := modelMarkedDomain (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p)
    (componentThin p hp c) (A c).model
  let D := originalTerminalPrincipalizationDivisor T hT rfl rfl
  obtain ⟨hhol, hproper, ⟨hAc, hAa, hAt, hBc, hBa, hBt, hpre⟩, s, hs, hfs, hsf⟩ :=
    originalTerminalGlobalProperModification_geometry T hT rfl rfl
  have hmod : AnalyticModificationLocalDiscrepancy.IsAnalyticModification
      (n := (A c).dimension) (originalTerminalGluedProjection T hT) :=
    ⟨hhol, hproper, D.support, T.ideal.zeroLocus, s,
      hAc, hAa, hAt, hBc, hBa, hBt, hpre, hs, hfs, hsf⟩
  have hq : IsProperBimeromorphic (componentPrincipalMap p hp A c) :=
    nativeMorphism_isProperBimeromorphic hmod
  have hzero : (Subtype.val : ↥(univ : Set (A c).manifold) → (A c).manifold) ⁻¹' T.ideal.zeroLocus =
      (componentModelMap p hp A c).hom.left.base ⁻¹'
        (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj) := by
    ext u
    change u.val ∈ (originalSingularGermIdeal X ((A c).model.hom ≫
      (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p))).zeroLocus ↔ _
    rw [originalSingularGermIdeal_zeroLocus]
    have hu : modelPoint u.val = u := Subtype.ext rfl
    change ((A c).model.hom ≫
      (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c ≫ p)).hom.left.base
        (modelPoint u.val) ∈ intrinsicSingularLocus X.obj ↔ _
    rw [hu]
    rfl
  have hgood := actualTerminal_isIsoOver T hT rfl rfl
  rw [hzero] at hgood
  have hqgood : IsIsoOver (componentPrincipalMap p hp A c)
      ((componentModelMap p hp A c).hom.left.base ⁻¹'
        (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj)) := by
    have hset : (componentModelMap p hp A c).hom.left.base ⁻¹'
        (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) =
        ((componentModelMap p hp A c).hom.left.base ⁻¹'
          (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj))ᶜ := by
      ext u
      change p.hom.left.base ((componentModelMap p hp A c).hom.left.base u) ∈
        intrinsicRegularLocus X.obj ↔
        p.hom.left.base ((componentModelMap p hp A c).hom.left.base u) ∉ intrinsicSingularLocus X.obj
      simp only [intrinsicSingularLocus, mem_compl_iff, not_not]
    rw [hset]
    exact hgood
  have hthinModel : interior ((componentModelMap p hp A c).hom.left.base ⁻¹'
      (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj)) = ∅ := by
    obtain ⟨_, Z, _, _, hpre, hiso⟩ := hp.2
    have ht := hiso.interior_preimage_eq_empty hpre (interior_intrinsicSingularLocus_eq_empty X)
    have hi := (componentModelMap_open p hp A c).base_open.isOpenMap.preimage_interior_eq_interior_preimage
      (componentModelMap p hp A c).hom.left.base.hom.continuous
      (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj)
    exact hi.symm.trans (by rw [ht, preimage_empty])
  refine ⟨hq, hqgood, ?_⟩
  obtain ⟨_, Z, _, _, hpre, hiso⟩ := hq
  exact hiso.interior_preimage_eq_empty hpre hthinModel

private def terminalFamily (A : ∀ c, ComponentModel hp.1 c)
    (c : ConnectedComponents Y.obj.left) : SourceReducedComplexSpace :=
  wholeModel (n := (A c).dimension) (componentTerminal p hp A c)

private def terminalInclusion (A : ∀ c, ComponentModel hp.1 c)
    (c : ConnectedComponents Y.obj.left) : terminalFamily p hp A c ⟶ cleanupSource p hp A :=
  HironakaG1NativeDisjointCoproduct.inclusion (terminalFamily p hp A) c

private theorem terminal_square (A : ∀ c, ComponentModel hp.1 c)
    (c : ConnectedComponents Y.obj.left) :
    terminalInclusion p hp A c ≫ cleanupProjection p hp A =
      componentPrincipalMap p hp A c ≫ componentModelMap p hp A c := by
  change HironakaG1NativeDisjointCoproduct.inclusion _ c ≫
    HironakaG1NativeDisjointCoproduct.desc _ (componentCleanupMap p hp A) = _
  rw [HironakaG1NativeDisjointCoproduct.inclusion_desc]
  exact Category.assoc _ _ _

/-- The ACTUAL global native good locus; this does NOT say iso over all smooth Y. -/
theorem cleanupProjection_isIsoOver (A : ∀ c, ComponentModel hp.1 c) :
    IsIsoOver (cleanupProjection p hp A) (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) :=
  HironakaG1NativeIsoOverDisjointCover.isIsoOver_of_disjoint_cover
    (cleanupProjection p hp A) (componentModelMap p hp A) (terminalInclusion p hp A)
    (componentPrincipalMap p hp A) (componentModelMap_open p hp A)
    (fun c => HironakaG1NativeDisjointCoproduct.inclusion_isOpenImmersion (terminalFamily p hp A) c)
    (componentModelMap_cover p hp A)
    (HironakaG1NativeDisjointCoproduct.inclusion_jointly_surjective (terminalFamily p hp A))
    (componentModelMap_disjoint p hp A) (terminal_square p hp A) _
    ((isOpen_intrinsicRegularLocus X.obj).preimage p.hom.left.base.hom.continuous)
    (fun c => (component_principal_geometry p hp A c).2.1)

/-- Global thinness comes from the ACTUAL terminal component maps and cover. -/
theorem cleanupOriginalSingularPreimage_thin (A : ∀ c, ComponentModel hp.1 c) :
    interior ((cleanupMorphism p hp A).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅ := by
  have hlocal (c : ConnectedComponents Y.obj.left) :
      interior ((terminalInclusion p hp A c).hom.left.base ⁻¹'
        ((cleanupMorphism p hp A).hom.left.base ⁻¹' intrinsicSingularLocus X.obj)) = ∅ := by
    have hX : terminalInclusion p hp A c ≫ cleanupMorphism p hp A =
        componentPrincipalMap p hp A c ≫ (componentModelMap p hp A c ≫ p) := by
      change terminalInclusion p hp A c ≫ (cleanupProjection p hp A ≫ p) = _
      rw [← Category.assoc, terminal_square, Category.assoc]
    change interior ((terminalInclusion p hp A c ≫ cleanupMorphism p hp A).hom.left.base ⁻¹'
      intrinsicSingularLocus X.obj) = ∅
    rw [hX]
    exact (component_principal_geometry p hp A c).2.2
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨c, u, hu⟩ := HironakaG1NativeDisjointCoproduct.inclusion_jointly_surjective
    (terminalFamily p hp A) z
  have hz' : (terminalInclusion p hp A c).hom.left.base u ∈
      interior ((cleanupMorphism p hp A).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) := by
    rw [show (terminalInclusion p hp A c).hom.left.base u = z from hu]
    exact hz
  have hm : u ∈ interior ((terminalInclusion p hp A c).hom.left.base ⁻¹'
      ((cleanupMorphism p hp A).hom.left.base ⁻¹' intrinsicSingularLocus X.obj)) :=
    interior_maximal (preimage_mono interior_subset)
      (isOpen_interior.preimage (terminalInclusion p hp A c).hom.left.base.hom.continuous) hz'
  rw [hlocal] at hm
  exact hm

/-- The actual complement of the original-Sing pullback is dense, also for empty sources. -/
theorem cleanupGood_dense (A : ∀ c, ComponentModel hp.1 c) :
    Dense ((cleanupMorphism p hp A).hom.left.base ⁻¹' intrinsicSingularLocus X.obj)ᶜ :=
  interior_eq_empty_iff_dense_compl.mp (cleanupOriginalSingularPreimage_thin p hp A)

/-- ANY two full native cleanup lifts over Y coincide. The existing generic
dense-lift theorem and original native faithfulness are reused unchanged. -/
theorem cleanupLift_eq (A B : ∀ c, ComponentModel hp.1 c)
    (f g : cleanupSource p hp A ⟶ cleanupSource p hp B)
    (hf : f ≫ cleanupProjection p hp B = cleanupProjection p hp A)
    (hg : g ≫ cleanupProjection p hp B = cleanupProjection p hp A) : f = g := by
  have hbase : ∀ z, (cleanupProjection p hp B).hom.left.base (f.hom.left.base z) =
      (cleanupProjection p hp B).hom.left.base (g.hom.left.base z) := fun z =>
    congrArg (fun F : cleanupSource p hp A ⟶ Y => F.hom.left.base z) (hf.trans hg.symm)
  have hD := cleanupGood_dense p hp A
  have hDU (z : (cleanupSource p hp A).obj.left)
      (hz : z ∈ ((cleanupMorphism p hp A).hom.left.base ⁻¹' intrinsicSingularLocus X.obj)ᶜ) :
      (cleanupProjection p hp B).hom.left.base (f.hom.left.base z) ∈
        p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj := by
    have hpt := congrArg (fun F : cleanupSource p hp A ⟶ Y => F.hom.left.base z) hf
    change (cleanupProjection p hp B).hom.left.base (f.hom.left.base z) =
      (cleanupProjection p hp A).hom.left.base z at hpt
    rw [hpt]
    change (cleanupMorphism p hp A).hom.left.base z ∈ intrinsicRegularLocus X.obj
    exact not_not.mp hz
  have heq := HironakaG11LiftUniqueness.eq_of_comp_eq_of_dense
    (cleanupProjection_isIsoOver p hp B) f.hom.left.base.hom.continuous
    g.hom.left.base.hom.continuous hbase hD hDU
  apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
  intro z
  exact congrFun heq z

/-- An already-proved actual comparison; uniqueness below removes its choice. -/
def comparison (A B : ∀ c, ComponentModel hp.1 c) : cleanupSource p hp A ≅ cleanupSource p hp B :=
  Classical.choose (exists_cleanup_comparison p hp A B)

/-- The SAME full native projection square over Y. -/
theorem comparison_overY (A B : ∀ c, ComponentModel hp.1 c) :
    (comparison p hp A B).hom ≫ cleanupProjection p hp B = cleanupProjection p hp A :=
  (Classical.choose_spec (exists_cleanup_comparison p hp A B)).1

/-- The SAME full native original-X square, hence its entire pulled ideal transport. -/
theorem comparison_overX (A B : ∀ c, ComponentModel hp.1 c) :
    (comparison p hp A B).hom ≫ cleanupMorphism p hp B = cleanupMorphism p hp A :=
  (Classical.choose_spec (exists_cleanup_comparison p hp A B)).2.1

/-- Identity is DERIVED from full-lift uniqueness, not a comparison-law input. -/
theorem comparison_id (A : ∀ c, ComponentModel hp.1 c) :
    comparison p hp A A = Iso.refl (cleanupSource p hp A) := by
  apply Iso.ext
  apply cleanupLift_eq p hp A A
  · exact comparison_overY p hp A A
  · exact Category.id_comp _

/-- Actual composition/cocycle across THREE independent genuine model collections. -/
theorem comparison_trans (A B C : ∀ c, ComponentModel hp.1 c) :
    (comparison p hp A B).trans (comparison p hp B C) = comparison p hp A C := by
  apply Iso.ext
  apply cleanupLift_eq p hp A C
  · change ((comparison p hp A B).hom ≫ (comparison p hp B C).hom) ≫
      cleanupProjection p hp C = cleanupProjection p hp A
    rw [Category.assoc, comparison_overY, comparison_overY]
  · exact comparison_overY p hp A C

/-- The actual inverse equals the comparison with reversed ordinary models. -/
theorem comparison_symm (A B : ∀ c, ComponentModel hp.1 c) :
    (comparison p hp A B).symm = comparison p hp B A := by
  apply Iso.ext
  apply cleanupLift_eq p hp B A
  · rw [← comparison_overY p hp A B, ← Category.assoc, Iso.symm_hom, Iso.inv_hom_id,
      Category.id_comp]
  · exact comparison_overY p hp B A

/-- The SAME chosen comparison transports the ENTIRE native total ideal,
with BOTH literal original structure-unit inclusion triangles. -/
theorem comparison_totalIdeal_transport (A B : ∀ c, ComponentModel hp.1 c) :
    ∃ I : nativePulledIdealModule (comparison p hp A B).hom.hom.left
        (totalIdealModule p hp B) (totalIdealInclusion p hp B) ≅ totalIdealModule p hp A,
      I.hom ≫ totalIdealInclusion p hp A =
        nativePulledIdealInclusion (comparison p hp A B).hom.hom.left
          (totalIdealModule p hp B) (totalIdealInclusion p hp B) ∧
      I.inv ≫ nativePulledIdealInclusion (comparison p hp A B).hom.hom.left
        (totalIdealModule p hp B) (totalIdealInclusion p hp B) = totalIdealInclusion p hp A :=
  ⟨totalIdealIso_of_square p hp A B (comparison p hp A B) (comparison_overX p hp A B),
    totalIdealIso_hom_comp_inclusion p hp A B (comparison p hp A B) (comparison_overX p hp A B),
    totalIdealIso_inv_comp_inclusion p hp A B (comparison p hp A B) (comparison_overX p hp A B)⟩

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeCleanupComparisonLaws
