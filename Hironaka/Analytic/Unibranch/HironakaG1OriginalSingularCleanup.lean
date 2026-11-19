import Hironaka.Analytic.Unibranch.HironakaG11SingularCentreModification
import Hironaka.Analytic.Unibranch.OriginalNativeModification
import Hironaka.Analytic.Unibranch.RIsoAModification
import Hironaka.Analytic.Unibranch.OriginalSmoothCentreBlowup
import Hironaka.Resolution.HironakaG10ChowGermIdealDictionary
import Hironaka.Resolution.HironakaOriginalEmptyHeadPrefix
import Hironaka.Analytic.PrescribedBlowupDomination

/-! # SNC cleanup of the same original singular-locus pullback

The given original resolution source is an actual compact manifold of fixed
dimension.  Its whole pulled original singular ideal is canonically
principalized; the native composite, the entire ideal and the full ordered
boundary are retained.  This is an existential refinement of the given native
map, not an intrinsic canonical resolution assignment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.HironakaG1OriginalSingularCleanup

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction
  HironakaResolutionSpaceComplex
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaIntrinsicReducedCentreIdealSheaf
  HironakaNativePulledIdealSheaf HironakaG10ChowGermIdealDictionary
  HironakaIntrinsicComplexAnalyticRegularLocus HironakaOriginalBoundaryCanonicalPrincipalization
  HironakaOriginalEmptyHeadPrefix RestrictEmptyTower BlowupRestrictOpen
  SourceReducedComplexSpace OriginalNativeModification HironakaG11SingularCentreModification
  OriginalIntrinsicSingularLocus SmoothCentreModification

noncomputable section

variable {n : ℕ} {M : CMfd.{0} n} (X : SourceReducedComplexSpace)

/-- The original intrinsic singular ideal, pulled along the actual native map. -/
def originalSingularGermIdeal (p : wholeModel (n := n) M ⟶ X) : GermIdeal n M :=
  modelGermIdeal
    (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
    (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) p.hom.left

/-- Coherence follows from ordinary original analyticity and the whole native dictionary. -/
theorem originalSingularGermIdeal_coherent (p : wholeModel (n := n) M ⟶ X) :
    (originalSingularGermIdeal X p).IsCoherent := by
  let := IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType
    X (intrinsicSingularLocus X.obj) (isAnalyticSubset_intrinsicSingularLocus X)
  exact isCoherent_modelGermIdeal _ _ p.hom.left

/-- The whole pulled ideal has the exact inverse ORIGINAL singular locus. -/
theorem originalSingularGermIdeal_zeroLocus (p : wholeModel (n := n) M ⟶ X) :
    (originalSingularGermIdeal X p).zeroLocus =
      {x : M | p.hom.left.base (modelPoint x) ∈ intrinsicSingularLocus X.obj} := by
  unfold originalSingularGermIdeal
  erw [zeroLocus_modelGermIdeal]
  have hu := OriginalSmoothCentreBlowup.intrinsic_ideal_unitLocus_eq_compl
    X (intrinsicSingularLocus X.obj) (isAnalyticSubset_intrinsicSingularLocus X)
  ext x
  have hx := Set.ext_iff.mp hu (p.hom.left.base (modelPoint x))
  exact (not_congr hx).trans not_not

/-- The ENTIRE original singular ideal, with its actual native scalar map. -/
theorem originalSingularGermIdeal_wholeStalk (p : wholeModel (n := n) M ⟶ X)
    (x : (univ : Set M)) :
    Ideal.map ((actualSubspaceInclusion (n := n) (univ : Set M)).stalkMap x).hom
      (actualWholeSheafStalkIdeal (originalSingularGermIdeal X p) x.val) =
      nativePulledIdealStalkIdeal p.hom.left
        (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
        (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) x :=
  map_wholeIdeal_modelGermIdeal _ _ p.hom.left x

private theorem originalSingularGermIdeal_thin (p : wholeModel (n := n) M ⟶ X)
    (hp : IsSingularCentreModification p) :
    interior (originalSingularGermIdeal X p).zeroLocus = ∅ := by
  rw [originalSingularGermIdeal_zeroLocus]
  change interior ((Homeomorph.Set.univ M).symm ⁻¹'
    (p.hom.left.base ⁻¹' intrinsicSingularLocus X.obj)) = ∅
  have ht := hp.interior_preimage_intrinsicSingularLocus
  change interior ((p.hom.left.base : ↥(univ : Set M) → X.obj.left) ⁻¹'
    intrinsicSingularLocus X.obj) = ∅ at ht
  rw [← (Homeomorph.Set.univ M).symm.preimage_interior, ht, preimage_empty]

section NativeTower

variable {D : CMfd.{0} n}

/-- Every actual manifold tower with centres over a closed set is an original
native isomorphism off that same set, including all sheaf maps. -/
theorem nativeTower_isIsoOver_of_centresOver (T : BlowupTower M D) (F : Set M)
    (hF : IsClosed F) (hT : CentresOver F T) :
    IsIsoOver (nativeMorphism T.contMDiff_proj)
      ((Subtype.val : ↥(univ : Set M) → M) ⁻¹' F)ᶜ := by
  let U : Opens M := ⟨Fᶜ, hF.isOpen_compl⟩
  let V := openPreimage T U
  have he := isEmptyTower_restrict_of_centresOver U disjoint_compl_left T hT
  obtain ⟨e, he⟩ := exists_empty_tower_projection (restrict U T) he
  let E := actualSubspaceBiholomorphicIso e (univ : Set V) (univ : Set U)
    (fun _ => Iff.rfl)
  let J := actualOpenSubspaceMap (n := n) (univ : Set D) V
  let K := actualOpenSubspaceMap (n := n) (univ : Set M) U
  have hJ : LocallyRingedSpace.IsOpenImmersion J :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set D) V
  have hK : LocallyRingedSpace.IsOpenImmersion K :=
    actualOpenSubspaceMap_isOpenImmersion (n := n) (univ : Set M) U
  have hfacCat : nativeMorphism (M := V) (N := D) contMDiff_subtype_val ≫
      nativeMorphism T.contMDiff_proj =
      nativeMorphism e.contMDiff ≫ nativeMorphism (M := U) (N := M) contMDiff_subtype_val := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro z
    apply Subtype.ext
    change T.proj z.val.val = (e z.val).val
    have hh := congrArg Subtype.val (he z.val)
    rw [proj_restrict] at hh
    exact hh.symm
  have hfac : J ≫ (nativeMorphism T.contMDiff_proj).hom.left = E.hom ≫ K :=
    congrArg (fun H : wholeModel (n := n) V ⟶ wholeModel (n := n) M => H.hom.left) hfacCat
  refine ⟨_, J, hJ, ?_, ?_, ?_⟩
  · exact (range_actualOpenSubspaceMap (n := n) (univ : Set D) V).trans (by rfl)
  · rw [hfac]
    exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ E.hom (inferInstance) K hK
  · exact (congrArg (fun H : actualSubspaceLocallyRingedSpace (n := n)
        (univ : Set V) ⟶ (wholeModel (n := n) M).obj.left => range H.base) hfac).trans
      ((range_iso_hom_comp_base E K).trans
        ((range_actualOpenSubspaceMap (n := n) (univ : Set M) U).trans (by rfl)))

private theorem nativeTower_isModification (T : BlowupTower M D) :
    IsModification (nativeMorphism T.contMDiff_proj) := by
  obtain ⟨q, hq, hpt⟩ := RIsoAModification.isModification_of_isBlowupSequence T.isBlowupSequence
  have he : q = nativeMorphism T.contMDiff_proj := by
    apply SourceReducedComplexSpace.morphism_eq_of_pointwise_eq
    intro x
    exact Subtype.ext (hpt x)
  exact he ▸ hq

end NativeTower

section Cleanup

variable [CompactSpace M]

/-- The genuine canonical cleanup retains the entire original singular ideal,
the SAME projection, and the whole indexed SNC boundary. -/
theorem exists_original_singular_snc_cleanup (p : wholeModel (n := n) M ⟶ X)
    (hp : IsSingularCentreModification p) :
    let I := originalSingularGermIdeal X p
    let A : MarkedIdeal n M := ⟨univ, [], I, 1⟩
    ∃ (D : CMfd.{0} n) (T : BlowupTower M D),
      ResolutionInvariantSpec.IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) T ∧
      IsGeoResolution A T ∧ CentresOver I.zeroLocus T ∧
      GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal ∧
      IsSNCDivisor n (geoTransformAlong A T).E ∧
      (exceptionalDivisor T).support = ⋃ H ∈ (geoTransformAlong A T).E, H ∧
      (exceptionalDivisor T).support =
        {z : D | p.hom.left.base (modelPoint (T.proj z)) ∈ intrinsicSingularLocus X.obj} ∧
      ∀ x : (univ : Set D),
        Ideal.map ((actualSubspaceInclusion (n := n) (univ : Set D)).stalkMap x).hom
          (actualWholeSheafStalkIdeal (exceptionalDivisor T).ideal x.val) =
          nativePulledIdealStalkIdeal ((nativeMorphism T.contMDiff_proj) ≫ p).hom.left
            (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
            (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) x := by
  let I := originalSingularGermIdeal X p
  have hI := originalSingularGermIdeal_coherent X p
  have hnz := PrescribedBlowupDomination.isNonzeroAlongAt_of_interior_zeroLocus_eq_empty
    hI (originalSingularGermIdeal_thin X p hp)
  have hK : IsCompact I.zeroLocus := (OrderTaylor.isClosed_zeroLocus_of_isCoherent hI).isCompact
  let A : MarkedIdeal n M := ⟨univ, [], I, 1⟩
  let hA := HironakaPrincipalizationBoundary.isInvDomain_univ_of_isSNCDivisor
    hI hnz (isSNCDivisor_nil (n := n) (M := M))
  let hcos : IsCompact A.cosupp := (HironakaAdmissibleSequence.cosupp_univ_one hI).symm ▸ hK
  let P := compactCosupportCanonicalTower A hA hcos
  let T := P.2.val
  have h := canonical_boundary_principalization I hI hnz hK []
    (isSNCDivisor_nil (n := n) (M := M))
  obtain ⟨hc, hr, _, _, _, hover, _, hpb, hE, hsupp, hpre, _, _, _⟩ := h
  refine ⟨P.1, T, hc, hr, hover, hpb, hE, ?_, ?_, ?_⟩
  · simpa only [List.length_nil, List.drop_zero] using hsupp
  · exact hpre.trans (by
      ext z
      exact Set.ext_iff.mp (originalSingularGermIdeal_zeroLocus X p) (T.proj z))
  · intro x
    let := IntrinsicAnalyticCentreFiniteType.intrinsicReducedCentreIdealModule_isFiniteType
      X (intrinsicSingularLocus X.obj) (isAnalyticSubset_intrinsicSingularLocus X)
    rw [← hpb]
    exact map_wholeIdeal_pullback_modelGermIdeal _ _ p.hom.left T.contMDiff_proj x

/-- All strong endpoint properties refer to the SAME native cleanup composite.
The given resolution source has an explicit compact manifold presentation. -/
theorem exists_same_native_strong_endpoint (p : wholeModel (n := n) M ⟶ X)
    (hp : IsSingularCentreModification p) :
    ∃ (D : CMfd.{0} n) (T : BlowupTower M D),
      let I := originalSingularGermIdeal X p
      let A : MarkedIdeal n M := ⟨univ, [], I, 1⟩
      let q := nativeMorphism T.contMDiff_proj
      let r := q ≫ p
      ResolutionInvariantSpec.IsCanonical A ((CanonicalCentres.canonicalInvariant n).inv A) T ∧
      IsGeoResolution A T ∧ CentresOver I.zeroLocus T ∧
      IsModification q ∧ IsModification r ∧ (wholeModel (n := n) D).IsSmooth ∧
      IsResolution r ∧ Function.Surjective r.hom.left.base ∧ IsProperMap r.hom.left.base ∧
      IsIsoOver r (intrinsicRegularLocus X.obj) ∧
      IsSNCDivisor n (geoTransformAlong A T).E ∧
      ((Subtype.val : ↥(univ : Set D) → D) ⁻¹' (⋃ H ∈ (geoTransformAlong A T).E, H)) =
        r.hom.left.base ⁻¹' intrinsicSingularLocus X.obj ∧
      GermIdeal.pullback (m := n) T.proj I = (exceptionalDivisor T).ideal ∧
      ∀ x : (univ : Set D),
        Ideal.map ((actualSubspaceInclusion (n := n) (univ : Set D)).stalkMap x).hom
          (actualWholeSheafStalkIdeal (exceptionalDivisor T).ideal x.val) =
          nativePulledIdealStalkIdeal r.hom.left
            (intrinsicReducedCentreIdealModule X.obj.left (intrinsicSingularLocus X.obj))
            (intrinsicReducedCentreIdealInclusion X.obj.left (intrinsicSingularLocus X.obj)) x := by
  obtain ⟨D, T, hc, hgeo, hover, hpb, hE, hsupp, hpre, hwhole⟩ :=
    exists_original_singular_snc_cleanup X p hp
  let q := nativeMorphism T.contMDiff_proj
  let r := q ≫ p
  have hq : IsModification q := nativeTower_isModification T
  have hr : IsModification r := hq.comp hp.toIsModification
  have hsm : (wholeModel (n := n) D).IsSmooth := isSmooth_wholeModel
  have hIq := nativeTower_isIsoOver_of_centresOver T (originalSingularGermIdeal X p).zeroLocus
    (OrderTaylor.isClosed_zeroLocus_of_isCoherent (originalSingularGermIdeal_coherent X p)) hover
  have hIq' : IsIsoOver q (p.hom.left.base ⁻¹' intrinsicRegularLocus X.obj) := by
    convert hIq using 1
    ext x
    change p.hom.left.base x ∈ intrinsicRegularLocus X.obj ↔
      x.val ∉ (originalSingularGermIdeal X p).zeroLocus
    rw [originalSingularGermIdeal_zeroLocus]
    have hx : modelPoint x.val = x := Subtype.ext rfl
    simp only [mem_ofPred_eq, hx, intrinsicSingularLocus, mem_compl_iff, not_not]
  have hiso : IsIsoOver r (intrinsicRegularLocus X.obj) :=
    hp.isIsoOver_intrinsicRegularLocus.comp hIq'
  have hres : IsResolution r := by
    refine ⟨hsm, hr.isProperMap, intrinsicSingularLocus X.obj,
      isAnalyticSubset_intrinsicSingularLocus X, interior_intrinsicSingularLocus_eq_empty X,
      hr.interior_preimage_eq_empty (interior_intrinsicSingularLocus_eq_empty X), ?_⟩
    simpa only [intrinsicSingularLocus, compl_compl] using hiso
  refine ⟨D, T, hc, hgeo, hover, hq, hr, hsm, hres, hr.surjective, hr.isProperMap, hiso,
    hE, ?_, hpb, hwhole⟩
  rw [← hsupp, hpre]
  rfl

end Cleanup
end
end Hironaka.Analytic.Unibranch.HironakaG1OriginalSingularCleanup
