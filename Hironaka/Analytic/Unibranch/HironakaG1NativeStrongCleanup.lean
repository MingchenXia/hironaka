import Hironaka.Analytic.Unibranch.HironakaG1OriginalSingularCleanup
import Hironaka.Analytic.Unibranch.HironakaG1NoncompactSmoothComponentModel
import Hironaka.Analytic.Unibranch.HironakaG1NativeDisjointCoproduct
import Hironaka.Analytic.Unibranch.HironakaG1NativeIsoOverDisjointCover
import Hironaka.Analytic.Unibranch.EmbeddedCommonResolutionGeneral
import Hironaka.Resolution.HironakaOriginalGlobalProperModification
import Hironaka.Resolution.HironakaOriginalGlobalSNCPrincipalization

/-! # Strong refinement of an arbitrary given native smooth resolution

All actual component models, disjoint analytic source and proper global map
are internally constructed. The SAME composite retains its entire original
singular ideal, prescribed original-Reg native isomorphism, and genuine
saturated-range SNC/unit-monomial readout. No compactness, common dimension,
countability, model packet, or global blowup schedule is assumed.
Blueprint first: `hironaka-g1-native-strong-cleanup.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1NativeStrongCleanup

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaResolutionSpaceComplex
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaIntrinsicReducedCentreIdealSheaf
  HironakaNativePulledIdealSheaf HironakaG10ChowGermIdealDictionary
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaOriginalTerminalAtlas
  HironakaOriginalTerminalManifold HironakaOriginalTerminalLocalBiholomorphism
  HironakaOriginalGlobalPrincipalization HironakaOriginalGlobalOffZero
  HironakaOriginalGlobalProperModification HironakaOriginalGlobalSNCPrincipalization
  SourceReducedComplexSpace OriginalNativeModification HironakaG11SingularCentreModification
  OriginalIntrinsicSingularLocus HironakaG1OriginalSingularCleanup
open Hironaka.ResolutionInvariantSpec (IsInvDomain)

attribute [local instance] originalTerminalChartedSpace originalTerminalGluedSpace_isComplexManifold

noncomputable section

section ThinManifold
variable {n : ℕ} {M : CMfd.{0} n} (X : SourceReducedComplexSpace)
  (p : wholeModel (n := n) M ⟶ X)
  (hp : interior (originalSingularGermIdeal X p).zeroLocus = ∅)

/-- The mark-one whole original singular ideal, with genuinely empty boundary. -/
private def originalSingularMarkedIdeal : MarkedIdeal n M :=
  ⟨univ, [], originalSingularGermIdeal X p, 1⟩

include hp

/-- Ordinary proper-bimeromorphic geometry internally gives the true domain. -/
private theorem originalSingularMarkedDomain : IsInvDomain n (originalSingularMarkedIdeal X p) :=
  HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor
    (originalSingularGermIdeal_coherent X p)
    (PrescribedBlowupDomination.isNonzeroAlongAt_of_interior_zeroLocus_eq_empty
      (originalSingularGermIdeal_coherent X p) hp)
    (isSNCDivisor_nil (n := n) (M := M))

/-- The genuine held global terminal manifold of this exact original ideal. -/
private def cleanupSource : CMfd.{0} n :=
  originalTerminalManifold (originalSingularMarkedIdeal X p) (originalSingularMarkedDomain X p hp)

/-- The same actual terminal projection, with no compactness assumption. -/
private def cleanupProjection : cleanupSource X p hp → M :=
  originalTerminalGluedProjection (originalSingularMarkedIdeal X p)
    (originalSingularMarkedDomain X p hp)

/-- Its entire total-transform effective divisor. -/
private def cleanupDivisor : EffectiveDivisor n (cleanupSource X p hp) :=
  originalTerminalPrincipalizationDivisor (originalSingularMarkedIdeal X p)
    (originalSingularMarkedDomain X p hp) rfl rfl

private theorem cleanupProjection_contMDiff :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (cleanupProjection X p hp) :=
  originalTerminalGluedProjection_contMDiff _ _

/-- The full native original morphism induced by that same projection. -/
private def cleanupNativeProjection : wholeModel (n := n) (cleanupSource X p hp) ⟶ wholeModel (n := n) M :=
  nativeMorphism (cleanupProjection_contMDiff X p hp)

private theorem cleanupNativeProjection_isIsoOver :
    IsIsoOver (cleanupNativeProjection X p hp)
      ((Subtype.val : ↥(univ : Set M) → M) ⁻¹' (originalSingularGermIdeal X p).zeroLocus)ᶜ := by
  let A := originalSingularMarkedIdeal X p
  let hA := originalSingularMarkedDomain X p hp
  let U := originalTerminalOffZeroBaseOpen A hA
  let V := originalTerminalOffZeroSourceOpen A hA
  let e := originalTerminalOffZeroBiholomorphism A hA rfl rfl
  let E := actualSubspaceBiholomorphicIso e (univ : Set V) (univ : Set U) (fun _ => Iff.rfl)
  let J := actualOpenSubspaceMap (n := n) (univ : Set (cleanupSource X p hp)) V
  let K := actualOpenSubspaceMap (n := n) (univ : Set M) U
  have hJ : LocallyRingedSpace.IsOpenImmersion J :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set (cleanupSource X p hp)) V
  have hK : LocallyRingedSpace.IsOpenImmersion K :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set M) U
  have hfacCat : nativeMorphism (M := V) (N := cleanupSource X p hp) contMDiff_subtype_val ≫
      cleanupNativeProjection X p hp =
      nativeMorphism e.contMDiff ≫ nativeMorphism (M := U) (N := M) contMDiff_subtype_val := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    exact (originalTerminalOffZeroBiholomorphism_point A hA rfl rfl z.val).symm
  have hfac : J ≫ (cleanupNativeProjection X p hp).hom.left = E.hom ≫ K :=
    congrArg (fun H : wholeModel (n := n) V ⟶ wholeModel (n := n) M => H.hom.left) hfacCat
  refine ⟨_, J, hJ, ?_, ?_, ?_⟩
  · exact (range_actualOpenSubspaceMap (n := n) (univ : Set (cleanupSource X p hp)) V).trans (by rfl)
  · rw [hfac]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ E.hom (inferInstance) K hK
  · exact (congrArg (fun H : actualSubspaceLocallyRingedSpace (n := n)
        (univ : Set V) ⟶ (wholeModel (n := n) M).obj.left => range H.base) hfac).trans
      ((range_iso_hom_comp_base E K).trans
        ((range_actualOpenSubspaceMap (n := n) (univ : Set M) U).trans (by rfl)))

/-- The actual global projection is proper bimeromorphic, surjective, and a full
native isomorphism over the prescribed original ideal complement. -/
private theorem cleanupNativeProjection_geometry :
    IsProperBimeromorphic (cleanupNativeProjection X p hp) ∧
    IsProperMap (cleanupNativeProjection X p hp).hom.left.base ∧
    Function.Surjective (cleanupNativeProjection X p hp).hom.left.base ∧
    IsIsoOver (cleanupNativeProjection X p hp)
      ((Subtype.val : ↥(univ : Set M) → M) ⁻¹' (originalSingularGermIdeal X p).zeroLocus)ᶜ := by
  obtain ⟨hhol, hproper, ⟨hAc, hAa, hAt, hBc, hBa, hBt, hpre⟩, s, hs, hfs, hsf⟩ :=
    originalTerminalGlobalProperModification_geometry (originalSingularMarkedIdeal X p)
      (originalSingularMarkedDomain X p hp) rfl rfl
  have hmod : AnalyticModificationLocalDiscrepancy.IsAnalyticModification
      (n := n) (cleanupProjection X p hp) :=
    ⟨hhol, hproper, (cleanupDivisor X p hp).support,
      (originalSingularGermIdeal X p).zeroLocus, s,
      hAc, hAa, hAt, hBc, hBa, hBt, hpre, hs, hfs, hsf⟩
  have hq : IsProperBimeromorphic (cleanupNativeProjection X p hp) :=
    nativeMorphism_isProperBimeromorphic hmod
  exact ⟨hq, hq.1, hq.surjective, cleanupNativeProjection_isIsoOver X p hp⟩

/-- The actual whole original ideal and both full native scalar maps. -/
private theorem cleanupNativeProjection_wholeStalk (x : (univ : Set (cleanupSource X p hp))) :
    Ideal.map ((actualSubspaceInclusion (n := n) (univ : Set (cleanupSource X p hp))).stalkMap x).hom
      (actualWholeSheafStalkIdeal (cleanupDivisor X p hp).ideal x.val) =
      nativePulledIdealStalkIdeal ((cleanupNativeProjection X p hp) ≫ p).hom.left
        (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
        (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) x := by
  let := IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType
    X (intrinsicSingularLocus X.obj) (isAnalyticSubset_intrinsicSingularLocus X)
  exact map_wholeIdeal_pullback_modelGermIdeal _ _ p.hom.left
    (cleanupProjection_contMDiff X p hp) x

/-- The actual divisor support is the inverse ORIGINAL singular locus under
the same original native composite. -/
private theorem cleanupDivisor_originalSingularSupport :
    (cleanupDivisor X p hp).support =
      {z | ((cleanupNativeProjection X p hp) ≫ p).hom.left.base (modelPoint z) ∈
        intrinsicSingularLocus X.obj} := by
  have hs := originalTerminalPrincipalizationDivisor_support (originalSingularMarkedIdeal X p)
    (originalSingularMarkedDomain X p hp) rfl rfl
  exact hs.trans (by
    ext z
    exact Set.ext_iff.mp (originalSingularGermIdeal_zeroLocus X p) (cleanupProjection X p hp z))

/-- Genuine saturated ranges cover the SAME cleanup source.  Every range is the
actual finite canonical terminal space, with its full ordered SNC boundary and
its exact inverse ORIGINAL singular support.  No local-finiteness assertion is
made about this point-indexed covering family. -/
private theorem cleanup_saturated_range_readout :
    let A := originalSingularMarkedIdeal X p
    let hA := originalSingularMarkedDomain X p hp
    let a := actualLocalTerminalAtlas A hA
    (∀ z : cleanupSource X p hp, ∃ i : M, z ∈ originalTerminalLocalRangeOpen A hA i) ∧
    ∀ i : M,
      (originalTerminalLocalRangeOpen A hA i : Set (originalTerminalManifold A hA)) =
        cleanupProjection X p hp ⁻¹' (a.openSet i : Set M) ∧
      ResolutionInvariantSpec.IsCanonical
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : a.openSet i → M) A)
        ((CanonicalCentres.canonicalInvariant n).inv
          (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : a.openSet i → M) A))
        (a.tower i) ∧
      IsGeoResolution
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : a.openSet i → M) A)
        (a.tower i) ∧
      (∀ z : originalTerminalLocalRangeOpen A hA i,
        originalTerminalLocalRangeProjection A hA i z =
          (a.tower i).proj ((originalTerminalLocalBiholomorphism A hA i).symm z)) ∧
      IsSNCDivisor n (originalTerminalRangeBoundary A hA i) ∧
      (originalTerminalRangePrincipalizationDivisor A hA rfl rfl i).support =
        ⋃ H ∈ originalTerminalRangeBoundary A hA i, H ∧
      (originalTerminalRangePrincipalizationDivisor A hA rfl rfl i).support =
        {z | ((cleanupNativeProjection X p hp) ≫ p).hom.left.base (modelPoint z.val) ∈
          intrinsicSingularLocus X.obj} := by
  dsimp only
  let A := originalSingularMarkedIdeal X p
  let hA := originalSingularMarkedDomain X p hp
  refine ⟨?_, fun i => ⟨originalTerminalLocalInclusion_range A hA i,
    (actualLocalTerminalAtlas A hA).canonical i, (actualLocalTerminalAtlas A hA).terminal i,
    originalTerminalLocalRangeProjection_inverse A hA i,
    originalTerminalRangeBoundary_isSNCDivisor A hA i,
    originalTerminalRangePrincipalizationDivisor_support A hA rfl rfl rfl i, ?_⟩⟩
  · intro z
    obtain ⟨i, y, rfl⟩ := originalTerminalLocalInclusion_jointly_surjective A hA z
    exact ⟨i, ⟨y, rfl⟩⟩
  · change (GermIdeal.pullback (m := n)
      (Subtype.val : originalTerminalLocalRangeOpen A hA i → cleanupSource X p hp)
      (cleanupDivisor X p hp).ideal).zeroLocus = _
    have hcoh : (cleanupDivisor X p hp).ideal.IsCoherent :=
      GermIdealPullbackCalculus.isCoherent_pullback (cleanupProjection_contMDiff X p hp)
        (originalSingularGermIdeal_coherent X p)
    rw [BlowupExceptionalDivisor.zeroLocus_pullback contMDiff_subtype_val hcoh,
      ← EffectiveDivisor.support, cleanupDivisor_originalSingularSupport]
    rfl

/-- On each actual saturated native range the ENTIRE original ideal is the
literal restricted divisor ideal, with the full original composite scalar map. -/
private theorem cleanup_range_wholeStalk (i : M)
    (x : (univ : Set (originalTerminalLocalRangeOpen
      (originalSingularMarkedIdeal X p) (originalSingularMarkedDomain X p hp) i))) :
    let A := originalSingularMarkedIdeal X p
    let hA := originalSingularMarkedDomain X p hp
    let R := originalTerminalLocalRangeOpen A hA i
    Ideal.map ((actualSubspaceInclusion (n := n) (univ : Set R)).stalkMap x).hom
      (actualWholeSheafStalkIdeal
        (originalTerminalRangePrincipalizationDivisor A hA rfl rfl i).ideal x.val) =
      nativePulledIdealStalkIdeal
        ((nativeMorphism (M := R) (N := cleanupSource X p hp) contMDiff_subtype_val) ≫
          (cleanupNativeProjection X p hp ≫ p)).hom.left
        (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
        (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) x := by
  dsimp only
  let A := originalSingularMarkedIdeal X p
  let hA := originalSingularMarkedDomain X p hp
  let R := originalTerminalLocalRangeOpen A hA i
  let := IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType
    X (intrinsicSingularLocus X.obj) (isAnalyticSubset_intrinsicSingularLocus X)
  have hid : (originalTerminalRangePrincipalizationDivisor A hA rfl rfl i).ideal =
      GermIdeal.pullback (m := n)
        (cleanupProjection X p hp ∘ (Subtype.val : R → cleanupSource X p hp))
        (originalSingularGermIdeal X p) :=
    (GermIdealTotalTransform.pullback_comp (cleanupProjection_contMDiff X p hp)
      contMDiff_subtype_val (originalSingularGermIdeal_coherent X p)).symm
  rw [hid]
  have he : nativeMorphism ((cleanupProjection_contMDiff X p hp).comp
        (contMDiff_subtype_val (U := R))) ≫ p =
      nativeMorphism (M := R) (N := cleanupSource X p hp) contMDiff_subtype_val ≫
        (cleanupNativeProjection X p hp ≫ p) :=
    SourceReducedComplexSpace.morphism_eq_of_pointwise_eq _ _ fun _ => rfl
  rw [← he]
  exact map_wholeIdeal_pullback_modelGermIdeal
    (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
    (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) p.hom.left
    ((cleanupProjection_contMDiff X p hp).comp (contMDiff_subtype_val (U := R))) x

/-- Adapted holomorphic unit-monomial generators of the SAME whole original
singular ideal on every actual saturated terminal range. -/
private theorem cleanup_range_unit_monomial_generator (i : M)
    (x : originalTerminalLocalRangeOpen (originalSingularMarkedIdeal X p)
      (originalSingularMarkedDomain X p hp) i) :
    let A := originalSingularMarkedIdeal X p
    let hA := originalSingularMarkedDomain X p hp
    let R := originalTerminalLocalRangeOpen A hA i
    let E := originalTerminalRangeBoundary A hA i
    ∃ U : Set R, IsOpen U ∧ x ∈ U ∧ ∃ g : R → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g U ∧
      (∀ W : Set R, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0) ∧
      (∀ y ∈ U, ∀ f : R → ℂ,
        (GermIdeal.pullback (m := n) (Subtype.val : R → cleanupSource X p hp)
          (cleanupDivisor X p hp).ideal).mem y f ↔ IsInSpanAt (n := n) (· = g) y f) ∧
      ∃ (S : Fin E.length → Finset (Fin n))
        (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)),
        Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
        Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
        (∀ j, x ∈ E.get j → (S j).card = 1) ∧ Set.InjOn S {j | x ∈ E.get j} ∧
        (∀ j, x ∈ E.get j → ∀ {y : R}, y ∈ (complexChartAt (n := n) x).val.source →
          (complexChartAt (n := n) x).val y ∈ Φ.source →
          (y ∈ E.get j ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S j))) ∧
        ∃ (a : Fin n → ℕ) (H : ComplexModel n → ℂ),
          (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z) ∧ H 0 ≠ 0 ∧
          (fun z => g ((complexChartAt (n := n) x).val.symm (Φ.invFun z))) =ᶠ[𝓝 0]
            fun z => H z * ∏ j : Fin n, z j ^ a j :=
  exists_originalTerminalRange_unit_monomial_generator (originalSingularMarkedIdeal X p)
    (originalSingularMarkedDomain X p hp) rfl rfl rfl i x

end ThinManifold

section Native

variable {X Y : SourceReducedComplexSpace} (p : Y ⟶ X) (hp : IsResolution p)

private def componentModelData (c : ConnectedComponents Y.obj.left) :
    Σ n : ℕ, Σ M : CMfd.{0} n,
      wholeModel (n := n) M ≅ HironakaG1NoncompactSmoothComponentModel.componentObject hp.1 c := by
  let h := HironakaG1NoncompactSmoothComponentModel.exists_component_manifold_model hp.1 c
  exact ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choice (Classical.choose_spec (Classical.choose_spec h))⟩

/-- Each actual original component has its own internally derived dimension. -/
def componentDimension (c : ConnectedComponents Y.obj.left) : ℕ :=
  (componentModelData p hp c).1

/-- Its genuine manifold model, internally constructed from native smoothness. -/
def componentManifold (c : ConnectedComponents Y.obj.left) : CMfd.{0} (componentDimension p hp c) :=
  (componentModelData p hp c).2.1

private def componentIso (c : ConnectedComponents Y.obj.left) :
    wholeModel (n := componentDimension p hp c) (componentManifold p hp c) ≅
      HironakaG1NoncompactSmoothComponentModel.componentObject hp.1 c :=
  (componentModelData p hp c).2.2

/-- The full native component map, including its original scalar triangle. -/
def componentModelMap (c : ConnectedComponents Y.obj.left) :
    wholeModel (n := componentDimension p hp c) (componentManifold p hp c) ⟶ Y :=
  (componentIso p hp c).hom ≫ HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c

private theorem componentModelMap_open (c : ConnectedComponents Y.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (componentModelMap p hp c).hom.left := by
  let j := HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c
  change LocallyRingedSpace.IsOpenImmersion ((componentIso p hp c).hom.hom.left ≫ j.hom.left)
  infer_instance

private theorem componentModelMap_range (c : ConnectedComponents Y.obj.left) :
    range (componentModelMap p hp c).hom.left.base = OriginalSmoothComponents.componentSet c := by
  change range ((HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c).hom.left.base ∘
    (componentIso p hp c).hom.hom.left.base) = _
  have he : range (componentIso p hp c).hom.hom.left.base = univ :=
    range_eq_univ.mpr (show Function.Surjective (componentIso p hp c).hom.hom.left.base from
      (isoHomeomorph (componentIso p hp c)).surjective)
  rw [range_comp, he, image_univ]
  exact HironakaG1NoncompactSmoothComponentModel.componentInclusion_range hp.1 c

private theorem componentModelMap_cover (y : Y.obj.left) :
    ∃ (c : ConnectedComponents Y.obj.left)
      (u : (wholeModel (n := componentDimension p hp c) (componentManifold p hp c)).obj.left),
        (componentModelMap p hp c).hom.left.base u = y := by
  obtain ⟨c, t, ht⟩ := HironakaG1NoncompactSmoothComponentModel.componentInclusion_jointly_surjective hp.1 y
  obtain ⟨u, hu⟩ := (isoHomeomorph (componentIso p hp c)).surjective t
  refine ⟨c, u, ?_⟩
  change (componentIso p hp c).hom.hom.left.base u = t at hu
  change (HironakaG1NoncompactSmoothComponentModel.componentInclusion hp.1 c).hom.left.base
    ((componentIso p hp c).hom.hom.left.base u) = y
  rw [hu]
  exact ht

private theorem componentModelMap_disjoint : Pairwise fun c d : ConnectedComponents Y.obj.left =>
    Disjoint (range (componentModelMap p hp c).hom.left.base)
      (range (componentModelMap p hp d).hom.left.base) := by
  simpa only [componentModelMap_range] using
    (OriginalSmoothComponents.componentSet_pairwise_disjoint (X := Y))

private theorem componentOriginalIdeal_thin (c : ConnectedComponents Y.obj.left) :
    interior (originalSingularGermIdeal X (componentModelMap p hp c ≫ p)).zeroLocus = ∅ := by
  obtain ⟨_, E, _, _, hpre, hiso⟩ := hp.2
  have ht := hiso.interior_preimage_eq_empty hpre (interior_intrinsicSingularLocus_eq_empty X)
  have hj := componentModelMap_open p hp c
  have hs := hj.base_open.isOpenMap.preimage_interior_eq_interior_preimage
    (componentModelMap p hp c).hom.left.base.hom.continuous
    (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj)
  have hcomp : interior ((componentModelMap p hp c).hom.left.base ⁻¹'
      (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj)) = ∅ :=
    hs.symm.trans (by rw [ht, preimage_empty])
  rw [originalSingularGermIdeal_zeroLocus]
  change interior ((Homeomorph.Set.univ (componentManifold p hp c)).symm ⁻¹'
    ((componentModelMap p hp c).hom.left.base ⁻¹'
      (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj))) = ∅
  rw [← (Homeomorph.Set.univ (componentManifold p hp c)).symm.preimage_interior,
    hcomp, preimage_empty]

/-- The actual global terminal manifold over each derived original component. -/
def cleanupComponent (c : ConnectedComponents Y.obj.left) : CMfd.{0} (componentDimension p hp c) :=
  cleanupSource X (componentModelMap p hp c ≫ p) (componentOriginalIdeal_thin p hp c)

/-- Its SAME actual terminal projection to the internally derived model. -/
def cleanupComponentProjection (c : ConnectedComponents Y.obj.left) :
    cleanupComponent p hp c → componentManifold p hp c :=
  cleanupProjection X (componentModelMap p hp c ≫ p) (componentOriginalIdeal_thin p hp c)

/-- The entire original singular ideal's total-transform effective divisor. -/
def cleanupComponentDivisor (c : ConnectedComponents Y.obj.left) :
    EffectiveDivisor (componentDimension p hp c) (cleanupComponent p hp c) :=
  cleanupDivisor X (componentModelMap p hp c ≫ p) (componentOriginalIdeal_thin p hp c)

/-- The full original native projection induced by that same actual function. -/
def cleanupComponentMap (c : ConnectedComponents Y.obj.left) :
    wholeModel (n := componentDimension p hp c) (cleanupComponent p hp c) ⟶
      wholeModel (n := componentDimension p hp c) (componentManifold p hp c) :=
  cleanupNativeProjection X (componentModelMap p hp c ≫ p) (componentOriginalIdeal_thin p hp c)

/-- Ordinary component maps need only the inherited genuine thin pullback;
they are never assumed surjective resolutions of the entire original X. -/
theorem component_cleanup_geometry (c : ConnectedComponents Y.obj.left) :
    IsProperBimeromorphic (cleanupComponentMap p hp c) ∧
    IsProperMap (cleanupComponentMap p hp c).hom.left.base ∧
    Function.Surjective (cleanupComponentMap p hp c).hom.left.base ∧
    IsIsoOver (cleanupComponentMap p hp c)
      ((Subtype.val : ↥(univ : Set (componentManifold p hp c)) → componentManifold p hp c) ⁻¹'
        (originalSingularGermIdeal X (componentModelMap p hp c ≫ p)).zeroLocus)ᶜ ∧
    (cleanupComponentDivisor p hp c).support =
      {z | (cleanupComponentMap p hp c ≫ (componentModelMap p hp c ≫ p)).hom.left.base
        (modelPoint z) ∈ intrinsicSingularLocus X.obj} ∧
    interior (cleanupComponentDivisor p hp c).support = ∅ := by
  obtain ⟨hb, hpr, hsur, hi⟩ := cleanupNativeProjection_geometry X
    (componentModelMap p hp c ≫ p) (componentOriginalIdeal_thin p hp c)
  exact ⟨hb, hpr, hsur, hi,
    cleanupDivisor_originalSingularSupport X (componentModelMap p hp c ≫ p)
      (componentOriginalIdeal_thin p hp c),
    originalTerminalPrincipalizationDivisor_interior_support_eq_empty _ _ rfl rfl⟩

/-- The genuine arbitrary native disjoint source, without countable index or
common dimension assumptions. -/
private abbrev cleanupNativeFamily : ConnectedComponents Y.obj.left → SourceReducedComplexSpace :=
  fun c => wholeModel (n := componentDimension p hp c) (cleanupComponent p hp c)

def strongSource : SourceReducedComplexSpace :=
  HironakaG1NativeDisjointCoproduct.coproduct (cleanupNativeFamily p hp)

/-- Full native descent of the actual component cleanup projections. -/
def strongRefinement : strongSource p hp ⟶ Y :=
  HironakaG1NativeDisjointCoproduct.desc (cleanupNativeFamily p hp)
    (fun c => cleanupComponentMap p hp c ≫ componentModelMap p hp c)

/-- The SAME actual original composite with the given resolution. -/
def strongMorphism : strongSource p hp ⟶ X := strongRefinement p hp ≫ p

/-- The full genuine native coproduct component inclusion. -/
def strongComponentInclusion (c : ConnectedComponents Y.obj.left) :
    wholeModel (n := componentDimension p hp c) (cleanupComponent p hp c) ⟶ strongSource p hp :=
  HironakaG1NativeDisjointCoproduct.inclusion (cleanupNativeFamily p hp) c

private theorem strongComponentInclusion_square (c : ConnectedComponents Y.obj.left) :
    strongComponentInclusion p hp c ≫ strongRefinement p hp =
      cleanupComponentMap p hp c ≫ componentModelMap p hp c :=
  HironakaG1NativeDisjointCoproduct.inclusion_desc (cleanupNativeFamily p hp)
    (fun d => cleanupComponentMap p hp d ≫ componentModelMap p hp d) c

private theorem strongComponentInclusion_original_square (c : ConnectedComponents Y.obj.left) :
    strongComponentInclusion p hp c ≫ strongMorphism p hp =
      cleanupComponentMap p hp c ≫ (componentModelMap p hp c ≫ p) := by
  change strongComponentInclusion p hp c ≫ (strongRefinement p hp ≫ p) = _
  rw [← Category.assoc, strongComponentInclusion_square, Category.assoc]

/-- Actual clopen native source coverage and the literal SAME full-map squares. -/
theorem strong_component_cover :
    (∀ c : ConnectedComponents Y.obj.left,
      LocallyRingedSpace.IsOpenImmersion (strongComponentInclusion p hp c).hom.left ∧
      IsClosed (range (strongComponentInclusion p hp c).hom.left.base) ∧
      strongComponentInclusion p hp c ≫ strongRefinement p hp =
        cleanupComponentMap p hp c ≫ componentModelMap p hp c) ∧
    (∀ z : (strongSource p hp).obj.left, ∃ (c : ConnectedComponents Y.obj.left)
      (u : (wholeModel (n := componentDimension p hp c) (cleanupComponent p hp c)).obj.left),
        (strongComponentInclusion p hp c).hom.left.base u = z) ∧
    Pairwise (fun c d : ConnectedComponents Y.obj.left =>
      Disjoint (range (strongComponentInclusion p hp c).hom.left.base)
        (range (strongComponentInclusion p hp d).hom.left.base)) := by
  refine ⟨fun c => ⟨HironakaG1NativeDisjointCoproduct.inclusion_isOpenImmersion (cleanupNativeFamily p hp) c, ?_,
    strongComponentInclusion_square p hp c⟩,
    HironakaG1NativeDisjointCoproduct.inclusion_jointly_surjective (cleanupNativeFamily p hp),
    HironakaG1NativeDisjointCoproduct.inclusion_pairwise_disjoint (cleanupNativeFamily p hp)⟩
  let Z := fun c : ConnectedComponents Y.obj.left =>
    wholeModel (n := componentDimension p hp c) (cleanupComponent p hp c)
  let e := HironakaG1NativeDisjointCoproduct.pointHomeomorph Z
  have he : range (strongComponentInclusion p hp c).hom.left.base =
      e ⁻¹' range (fun u : (Z c).obj.left => (⟨c, u⟩ : Σ d, (Z d).obj.left)) := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u, (HironakaG1NativeDisjointCoproduct.pointHomeomorph_inclusion Z c u).symm⟩
    · rintro ⟨u, hu⟩
      exact ⟨u, e.injective
        ((HironakaG1NativeDisjointCoproduct.pointHomeomorph_inclusion Z c u).trans hu)⟩
  rw [he]
  exact isClosed_range_sigmaMk.preimage e.continuous

private theorem strongRefinement_proper : IsProperMap (strongRefinement p hp).hom.left.base :=
  HironakaG1NativeDisjointCoproduct.desc_isProperMap_of_disjoint_cover (cleanupNativeFamily p hp)
    (componentModelMap p hp) (componentModelMap_open p hp) (componentModelMap_cover p hp)
    (componentModelMap_disjoint p hp) (cleanupComponentMap p hp)
    (fun c => (component_cleanup_geometry p hp c).2.1)

private theorem strongOriginalSingularPullback_thin :
    interior ((strongMorphism p hp).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) = ∅ := by
  have hlocal (c : ConnectedComponents Y.obj.left) :
      interior ((strongComponentInclusion p hp c).hom.left.base ⁻¹'
        ((strongMorphism p hp).hom.left.base ⁻¹' intrinsicSingularLocus X.obj)) = ∅ := by
    obtain ⟨_, _, _, _, hs, ht⟩ := component_cleanup_geometry p hp c
    have he : (strongComponentInclusion p hp c).hom.left.base ⁻¹'
        ((strongMorphism p hp).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) =
        (Subtype.val : ↥(univ : Set (cleanupComponent p hp c)) → cleanupComponent p hp c) ⁻¹'
          (cleanupComponentDivisor p hp c).support := by
      ext u
      rw [hs]
      have hsq := congrArg
        (fun f : wholeModel (n := componentDimension p hp c) (cleanupComponent p hp c) ⟶ X =>
          f.hom.left.base u) (strongComponentInclusion_original_square p hp c)
      have hu : modelPoint u.val = u := Subtype.ext rfl
      change (strongMorphism p hp).hom.left.base
          ((strongComponentInclusion p hp c).hom.left.base u) =
        (cleanupComponentMap p hp c ≫ (componentModelMap p hp c ≫ p)).hom.left.base u at hsq
      change (strongMorphism p hp).hom.left.base
        ((strongComponentInclusion p hp c).hom.left.base u) ∈ intrinsicSingularLocus X.obj ↔ _
      simpa only [mem_preimage, mem_ofPred_eq, hu] using
        iff_of_eq (congrArg (fun x => x ∈ intrinsicSingularLocus X.obj) hsq)
    rw [he]
    have hi := isOpen_univ.isOpenMap_subtype_val.preimage_interior_eq_interior_preimage
      (continuous_subtype_val : Continuous
        (Subtype.val : ↥(univ : Set (cleanupComponent p hp c)) → cleanupComponent p hp c))
      (cleanupComponentDivisor p hp c).support
    exact hi.symm.trans (by rw [ht, preimage_empty])
  apply eq_empty_iff_forall_notMem.mpr
  intro z hz
  obtain ⟨c, u, hu⟩ := (strong_component_cover p hp).2.1 z
  have hz' : (strongComponentInclusion p hp c).hom.left.base u ∈
      interior ((strongMorphism p hp).hom.left.base ⁻¹' intrinsicSingularLocus X.obj) := by
    rw [hu]
    exact hz
  have hmem : u ∈ interior ((strongComponentInclusion p hp c).hom.left.base ⁻¹'
      ((strongMorphism p hp).hom.left.base ⁻¹' intrinsicSingularLocus X.obj)) :=
    interior_maximal (preimage_mono interior_subset)
      (isOpen_interior.preimage (strongComponentInclusion p hp c).hom.left.base.hom.continuous)
      hz'
  rw [hlocal] at hmem
  exact hmem

/-- The actual arbitrary native source is smooth, its refinement proper, and
the SAME composite is a proper surjective original-Reg-preserving resolution. -/
theorem strong_geometry (hreg : IsIsoOver p (intrinsicRegularLocus X.obj)) :
    (strongSource p hp).IsSmooth ∧ IsProperMap (strongRefinement p hp).hom.left.base ∧
    IsResolution (strongMorphism p hp) ∧
    IsProperMap (strongMorphism p hp).hom.left.base ∧
    Function.Surjective (strongMorphism p hp).hom.left.base ∧
    IsIsoOver (strongMorphism p hp) (intrinsicRegularLocus X.obj) := by
  have hsm : (strongSource p hp).IsSmooth :=
    HironakaG1NativeDisjointCoproduct.isSmooth_coproduct (cleanupNativeFamily p hp)
      (fun _ => isSmooth_wholeModel)
  have hqgood : ∀ c : ConnectedComponents Y.obj.left,
      IsIsoOver (cleanupComponentMap p hp c) ((componentModelMap p hp c).hom.left.base ⁻¹'
        (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj)) := by
    intro c
    have hi := (component_cleanup_geometry p hp c).2.2.2.1
    convert hi using 1
    ext u
    change p.hom.left.base ((componentModelMap p hp c).hom.left.base u) ∈
      intrinsicRegularLocus X.obj ↔
        u.val ∉ (originalSingularGermIdeal X (componentModelMap p hp c ≫ p)).zeroLocus
    rw [originalSingularGermIdeal_zeroLocus]
    have hu : modelPoint u.val = u := Subtype.ext rfl
    simp only [mem_ofPred_eq, hu, intrinsicSingularLocus, mem_compl_iff, not_not]
    rfl
  have hiρ : IsIsoOver (strongRefinement p hp) (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) :=
    HironakaG1NativeIsoOverDisjointCover.isIsoOver_of_disjoint_cover
      (strongRefinement p hp) (componentModelMap p hp) (strongComponentInclusion p hp)
      (cleanupComponentMap p hp) (componentModelMap_open p hp)
      (fun c => (strong_component_cover p hp).1 c |>.1) (componentModelMap_cover p hp)
      ((strong_component_cover p hp).2.1) (componentModelMap_disjoint p hp)
      (strongComponentInclusion_square p hp) _
      ((isOpen_intrinsicRegularLocus X.obj).preimage p.hom.left.base.hom.continuous) hqgood
  have hir : IsIsoOver (strongMorphism p hp) (intrinsicRegularLocus X.obj) := hreg.comp hiρ
  have hpr : IsProperMap (strongMorphism p hp).hom.left.base :=
    hp.2.1.comp (strongRefinement_proper p hp)
  have hr : IsResolution (strongMorphism p hp) := by
    refine ⟨hsm, hpr, intrinsicSingularLocus X.obj, isAnalyticSubset_intrinsicSingularLocus X,
      interior_intrinsicSingularLocus_eq_empty X, strongOriginalSingularPullback_thin p hp, ?_⟩
    simpa only [intrinsicSingularLocus, compl_compl] using hir
  exact ⟨hsm, strongRefinement_proper p hp, hr, hpr, hr.2.surjective, hir⟩

/-- The actual inverse ORIGINAL singular support and ENTIRE original stalk
ideal, with the scalar map of this SAME global native composite. -/
theorem strong_component_wholeStalk (c : ConnectedComponents Y.obj.left) :
    (cleanupComponentDivisor p hp c).support =
      {z | (strongComponentInclusion p hp c ≫ strongMorphism p hp).hom.left.base
        (modelPoint z) ∈ intrinsicSingularLocus X.obj} ∧
    ∀ x : (univ : Set (cleanupComponent p hp c)),
      Ideal.map ((actualSubspaceInclusion (n := componentDimension p hp c)
        (univ : Set (cleanupComponent p hp c))).stalkMap x).hom
        (actualWholeSheafStalkIdeal (cleanupComponentDivisor p hp c).ideal x.val) =
        nativePulledIdealStalkIdeal
          (strongComponentInclusion p hp c ≫ strongMorphism p hp).hom.left
          (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
          (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) x := by
  rw [strongComponentInclusion_original_square]
  exact ⟨(component_cleanup_geometry p hp c).2.2.2.2.1,
    fun x => cleanupNativeProjection_wholeStalk X (componentModelMap p hp c ≫ p)
      (componentOriginalIdeal_thin p hp c) x⟩

/-- Genuine covering saturated finite canonical terminal ranges, with the
full ordered SNC family and exact support for the SAME global native map. -/
theorem strong_saturated_range_readout (c : ConnectedComponents Y.obj.left) :
    let n := componentDimension p hp c
    let M := componentManifold p hp c
    let A := originalSingularMarkedIdeal X (componentModelMap p hp c ≫ p)
    let hA := originalSingularMarkedDomain X (componentModelMap p hp c ≫ p) (componentOriginalIdeal_thin p hp c)
    let a := actualLocalTerminalAtlas A hA
    (∀ z : cleanupComponent p hp c, ∃ i : M, z ∈ originalTerminalLocalRangeOpen A hA i) ∧
    ∀ i : M,
      (originalTerminalLocalRangeOpen A hA i : Set (originalTerminalManifold A hA)) =
        cleanupComponentProjection p hp c ⁻¹' (a.openSet i : Set M) ∧
      ResolutionInvariantSpec.IsCanonical
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : a.openSet i → M) A)
        ((CanonicalCentres.canonicalInvariant n).inv
          (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : a.openSet i → M) A))
        (a.tower i) ∧
      IsGeoResolution
        (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : a.openSet i → M) A)
        (a.tower i) ∧
      (∀ z : originalTerminalLocalRangeOpen A hA i,
        originalTerminalLocalRangeProjection A hA i z =
          (a.tower i).proj ((originalTerminalLocalBiholomorphism A hA i).symm z)) ∧
      IsSNCDivisor n (originalTerminalRangeBoundary A hA i) ∧
      (originalTerminalRangePrincipalizationDivisor A hA rfl rfl i).support =
        ⋃ H ∈ originalTerminalRangeBoundary A hA i, H ∧
      (originalTerminalRangePrincipalizationDivisor A hA rfl rfl i).support =
        {z | (strongComponentInclusion p hp c ≫ strongMorphism p hp).hom.left.base (modelPoint z.val) ∈
          intrinsicSingularLocus X.obj} := by
  dsimp only
  rw [strongComponentInclusion_original_square]
  exact cleanup_saturated_range_readout X (componentModelMap p hp c ≫ p)
    (componentOriginalIdeal_thin p hp c)

/-- The ENTIRE original ideal and original scalar map on each actual native
saturated terminal range, retaining the same global refinement square. -/
theorem strong_range_wholeStalk (c : ConnectedComponents Y.obj.left)
    (i : componentManifold p hp c)
    (x : (univ : Set (originalTerminalLocalRangeOpen
      (originalSingularMarkedIdeal X (componentModelMap p hp c ≫ p))
      (originalSingularMarkedDomain X (componentModelMap p hp c ≫ p)
        (componentOriginalIdeal_thin p hp c)) i))) :
    let n := componentDimension p hp c
    let A := originalSingularMarkedIdeal X (componentModelMap p hp c ≫ p)
    let hA := originalSingularMarkedDomain X (componentModelMap p hp c ≫ p) (componentOriginalIdeal_thin p hp c)
    let R := originalTerminalLocalRangeOpen A hA i
    Ideal.map ((actualSubspaceInclusion (n := n) (univ : Set R)).stalkMap x).hom
      (actualWholeSheafStalkIdeal
        (originalTerminalRangePrincipalizationDivisor A hA rfl rfl i).ideal x.val) =
      nativePulledIdealStalkIdeal
        ((nativeMorphism (M := R) (N := cleanupComponent p hp c) contMDiff_subtype_val) ≫
          (strongComponentInclusion p hp c ≫ strongMorphism p hp)).hom.left
        (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
        (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) x := by
  dsimp only
  rw [strongComponentInclusion_original_square]
  exact cleanup_range_wholeStalk X (componentModelMap p hp c ≫ p)
    (componentOriginalIdeal_thin p hp c) i x

/-- Actual adapted holomorphic unit-monomial generators of the SAME whole
original singular ideal on all genuine saturated terminal ranges. -/
theorem strong_range_unit_monomial_generator (c : ConnectedComponents Y.obj.left)
    (i : componentManifold p hp c)
    (x : originalTerminalLocalRangeOpen
      (originalSingularMarkedIdeal X (componentModelMap p hp c ≫ p))
      (originalSingularMarkedDomain X (componentModelMap p hp c ≫ p)
        (componentOriginalIdeal_thin p hp c)) i) :
    let n := componentDimension p hp c
    let A := originalSingularMarkedIdeal X (componentModelMap p hp c ≫ p)
    let hA := originalSingularMarkedDomain X (componentModelMap p hp c ≫ p) (componentOriginalIdeal_thin p hp c)
    let R := originalTerminalLocalRangeOpen A hA i
    let E := originalTerminalRangeBoundary A hA i
    ∃ U : Set R, IsOpen U ∧ x ∈ U ∧ ∃ g : R → ℂ,
      MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) g U ∧
      (∀ W : Set R, IsOpen W → W ⊆ U → W.Nonempty → ∃ y ∈ W, g y ≠ 0) ∧
      (∀ y ∈ U, ∀ f : R → ℂ,
        (GermIdeal.pullback (m := n) (Subtype.val : R → cleanupComponent p hp c)
          (cleanupComponentDivisor p hp c).ideal).mem y f ↔ IsInSpanAt (n := n) (· = g) y f) ∧
      ∃ (S : Fin E.length → Finset (Fin n))
        (Φ : LocalHolomorphicEquivAt (n := n) ((complexChartAt (n := n) x).val x)),
        Φ.source ⊆ (complexChartAt (n := n) x).val.target ∧
        Φ.toFun ((complexChartAt (n := n) x).val x) = 0 ∧
        (∀ j, x ∈ E.get j → (S j).card = 1) ∧ Set.InjOn S {j | x ∈ E.get j} ∧
        (∀ j, x ∈ E.get j → ∀ {y : R}, y ∈ (complexChartAt (n := n) x).val.source →
          (complexChartAt (n := n) x).val y ∈ Φ.source →
          (y ∈ E.get j ↔ Φ.toFun ((complexChartAt (n := n) x).val y) ∈ coordSubspace (S j))) ∧
        ∃ (a : Fin n → ℕ) (H : ComplexModel n → ℂ),
          (∀ᶠ z in 𝓝 0, DifferentiableAt ℂ H z) ∧ H 0 ≠ 0 ∧
          (fun z => g ((complexChartAt (n := n) x).val.symm (Φ.invFun z))) =ᶠ[𝓝 0]
            fun z => H z * ∏ j : Fin n, z j ^ a j :=
  cleanup_range_unit_monomial_generator X (componentModelMap p hp c ≫ p)
    (componentOriginalIdeal_thin p hp c) i x


end Native

end
end Hironaka.Analytic.Unibranch.HironakaG1NativeStrongCleanup
