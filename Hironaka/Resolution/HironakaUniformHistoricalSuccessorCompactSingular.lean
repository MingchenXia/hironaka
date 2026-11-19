import Hironaka.Resolution.HironakaG8CompactFootprintMaxProfile
import Hironaka.Resolution.HironakaActualCompactHSMaximalProfile
import Hironaka.Resolution.HironakaResolutionSpaceSingular
import Hironaka.Resolution.HironakaActualHistoricalOriginalSingularReference
import Hironaka.Resolution.HironakaActualHSConstantCentreBennett

/-! ORIGINAL compact singular-maximal footprint and a genuinely global
closed first centre, with no pure-dimension hypothesis. This is NOT a
whole historical clearing block or repeated-phase termination certificate.
Blueprint: `hironaka-uniform-historical-successor-compact-singular.tex`. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaUniformHistoricalSuccessorCompactSingular
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualCompactHSMaximalProfile HironakaResolutionSpaceSingular
  HironakaG8CompactFootprintMaxProfile
  HironakaActualHistoricalOriginalSingularReference HironakaActualWholeAmbientHSSuperlevel
  HironakaActualHSConstantCentreBennett HironakaActualReferenceHSSingularCentre
  HironakaHolomorphicJetChartInvariance HironakaEmbeddedAnalytic
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings SimultaneousNormalCrossings
  BlowupTowers BlowupTowerTransforms ResolutionDriver
open ResolutionInvariantSpec (IsInvDomain)
variable {n : ℕ} {X : CMfd.{u} n}

/-- A compact original singular locus supplies its whole highest singular
Hilbert–Samuel stratum and an actual all-order upper neighbourhood. -/
theorem exists_compact_singular_maximal_stratum_of_compact_singular {W : Set X}
    (hW : IsComplexAnalyticSubset (n:=n) W) (hK : IsCompact (singularSet (n:=n) W))
    (hns : ¬ IsClosedSubmanifold n W) :
    ∃a∈singularSet (n:=n) W,
      (∀x∈singularSet (n:=n) W,toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) x)≤
        toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) a)) ∧
      let D:=singularSet (n:=n) W∩actualWholeAmbientHSSuperlevel (vanishingIdeal (n:=n) W)
        (hilbertSamuelAt (vanishingIdeal (n:=n) W) a)
      D.Nonempty ∧ IsComplexAnalyticSubset (n:=n) D ∧ IsCompact D ∧ interior D=∅ ∧
      D={x | ∀ell,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ell=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) a ell} ∧
      ∃U : Opens X,D⊆U ∧
        (∀x∈U,∀ell,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ell≤
          hilbertSamuelAt (vanishingIdeal (n:=n) W) a ell) ∧
        actualWholeAmbientHSSuperlevel (vanishingIdeal (n:=n) W)
          (hilbertSamuelAt (vanishingIdeal (n:=n) W) a)∩(U : Set X)=D  := by
  have hSingA := isComplexAnalyticSubset_singularSet hW
  have hSingNe : (singularSet (n:=n) W).Nonempty := by
    by_contra hEmpty
    apply hns
    refine ⟨hW.isClosed,fun x hx=>?_⟩
    by_contra hNo
    exact hEmpty ⟨x,mem_singularSet_iff.mpr ⟨hx,fun d hd=>hNo ⟨d,hd⟩⟩⟩
  let A := vanishingIdeal (n:=n) W
  have hA : A.IsCoherent := CartanIrreducible.cartanCoherence W hW
  obtain ⟨a,ha,hMax,hDne,hDK,hDEqK,U,hDU,hUpperU,hSuperU⟩ :=
    exists_compact_footprint_maximal_hs_window A hA (singularSet (n:=n) W) hK hSingNe
  let D := singularSet (n:=n) W ∩ actualWholeAmbientHSSuperlevel A (hilbertSamuelAt A a)
  have hDA : IsComplexAnalyticSubset (n:=n) D :=
    hSingA.inter (isComplexAnalyticSubset_actualWholeAmbientHSSuperlevel A hA _)
  have hConst (x : X) (hx : x ∈ D) : ∀ ell, hilbertSamuelAt A x ell = hilbertSamuelAt A a ell :=
    ((Set.ext_iff.mp hDEqK x).mp hx).2
  have hDEq : D = {x | ∀ ell, hilbertSamuelAt A x ell = hilbertSamuelAt A a ell} := by
    ext x
    constructor
    · exact hConst x
    · intro hx
      exact ⟨actual_original_singular_profile_locus_subset_current_singular W hW a ha W hW hx,
        fun ell => (hx ell).ge⟩
  have hDThin : interior D = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hxD : x ∈ D := interior_subset hx
    have hWn : W ∈ 𝓝 x := mem_of_superset (mem_interior_iff_mem_nhds.mp hx)
      (fun _ hz => singularSet_subset W hz.1)
    exact (mem_singularSet_iff.mp hxD.1).2 n (EmbeddedFromResolution.regularAtDim_of_mem_nhds hWn)
  have hFinal : actualWholeAmbientHSSuperlevel A (hilbertSamuelAt A a) ∩ (U : Set X) = D := by
    rw [hSuperU]
    ext x
    constructor
    · rintro ⟨_hxU,hxEq⟩
      exact (Set.ext_iff.mp hDEq x).mpr hxEq
    · intro hx
      exact ⟨hDU hx,hConst x hx⟩
  exact ⟨a,ha,hMax,hDne,hDA,hDK,hDThin,hDEq,U,hDU,hUpperU,hFinal⟩

/-- Actual compact mixed-dimensional geometry selects the WHOLE maximal
SINGULAR HS stratum and ONE genuine all-order upper open before any CAN. -/
theorem exists_compact_singular_maximal_stratum {W : Set X}
    (hW : IsComplexAnalyticSubset (n:=n) W) (hK : IsCompact W)
    (hns : ¬ IsClosedSubmanifold n W) :
    ∃a∈singularSet (n:=n) W,
      (∀x∈singularSet (n:=n) W,toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) x)≤
        toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) a)) ∧
      let D:=singularSet (n:=n) W∩actualWholeAmbientHSSuperlevel (vanishingIdeal (n:=n) W)
        (hilbertSamuelAt (vanishingIdeal (n:=n) W) a)
      D.Nonempty ∧ IsComplexAnalyticSubset (n:=n) D ∧ IsCompact D ∧ interior D=∅ ∧
      D={x | ∀ell,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ell=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) a ell} ∧
      ∃U : Opens X,D⊆U ∧
        (∀x∈U,∀ell,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ell≤
          hilbertSamuelAt (vanishingIdeal (n:=n) W) a ell) ∧
        actualWholeAmbientHSSuperlevel (vanishingIdeal (n:=n) W)
          (hilbertSamuelAt (vanishingIdeal (n:=n) W) a)∩(U : Set X)=D  := by
  exact exists_compact_singular_maximal_stratum_of_compact_singular hW
    (hK.of_isClosed_subset (isClosed_singularSet hW.isClosed) (singularSet_subset _)) hns

/-- No purity: the ACTUAL compact maximal singular stratum supplies one
GLOBAL compact closed canonical auxiliary centre, a proper original-regular
protected blowup, whole E/next geometry and genuine all-order Bennett.
This chooses ONLY a first centre, not a historical reduced-ideal restart. -/
theorem exists_compact_singular_maximal_first_centre {W : Set X}
    (hW : IsComplexAnalyticSubset (n:=n) W) (hK : IsCompact W)
    (hns : ¬ IsClosedSubmanifold n W) (E : List (Set X)) (hE : IsSNCDivisor n E) :
    ∃(a : X)(U : Opens X),a∈singularSet (n:=n) W ∧
      (∀x∈singularSet (n:=n) W,toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) x)≤
        toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) a)) ∧
      let D:=singularSet (n:=n) W∩actualWholeAmbientHSSuperlevel (vanishingIdeal (n:=n) W)
        (hilbertSamuelAt (vanishingIdeal (n:=n) W) a)
      D.Nonempty ∧ IsComplexAnalyticSubset (n:=n) D ∧ IsCompact D ∧
      D={x | ∀ell,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ell=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) a ell} ∧ D⊆U ∧
      (∀x∈U,∀ell,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ell≤
        hilbertSamuelAt (vanishingIdeal (n:=n) W) a ell) ∧
      let Q : MarkedIdeal n X:=⟨univ,E,vanishingIdeal (n:=n) D,1⟩
      IsInvDomain n Q ∧ Q.cosupp=D ∧
      ∃(C : Set X)(Y : CMfd.{u} n)(pi : Y → X)(_hpi : IsBlowupAlong n C pi),
        C.Nonempty ∧ IsCompact C ∧ C⊆D ∧ C⊆singularSet (n:=n) W ∧
        (⟨univ,E,vanishingIdeal (n:=n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C ∧
        C=maxLocus ((CanonicalCentres.canonicalInvariant n).inv Q (.refl : BlowupTower X X)) Q.cosupp ∧
        IsProperMap pi ∧ IsIsomorphismOver n pi (singularSet (n:=n) W)ᶜ ∧
        IsSNCDivisor n (E.map (BlowupStrictSubmanifold.geoStrictTransform pi C)++[pi ⁻¹' C]) ∧
        IsComplexAnalyticSubset (n:=n) (strictTransform n pi W) ∧ IsCompact (strictTransform n pi W) ∧
        ∀y ell,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n pi W)) y ell≤
          hilbertSamuelAt (vanishingIdeal (n:=n) W) (pi y) ell := by
  obtain ⟨a,ha,hMaxSing,hDne,hDA,hDK,hDThin,hDEq,U,hDU,hUpperU,_hSuperU⟩:=
    exists_compact_singular_maximal_stratum hW hK hns
  let D:=singularSet (n:=n) W∩actualWholeAmbientHSSuperlevel (vanishingIdeal (n:=n) W)
    (hilbertSamuelAt (vanishingIdeal (n:=n) W) a)
  let Q : MarkedIdeal n X:=⟨univ,E,vanishingIdeal (n:=n) D,1⟩
  let R:=CanonicalCentres.canonicalInvariant.{u} n
  have hDom : IsInvDomain n Q:=HironakaEmbeddedBoundary.isInvDomain_boundary hDA hDThin hE
  have hCos : Q.cosupp=D:=HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hDA.isClosed E
  have hUsc:=R.isInvValue.usc Q hDom (.refl : BlowupTower X X) trivial
  rw [geoTransformAlong_refl] at hUsc
  obtain ⟨c,hc,hMax⟩:=hUsc.exists_isMaxOn (hCos.symm ▸ hDK) (hCos.symm ▸ hDne)
  let C:=maxLocus (R.inv Q (.refl : BlowupTower X X)) Q.cosupp
  have hAdm:=R.isInvValue.isAdmissibleCentre_maxLocus hDom (.refl : BlowupTower X X) trivial trivial
  rw [geoTransformAlong_refl] at hAdm
  have hCD : C⊆D:=hCos ▸ hAdm.2.1
  have hCS : C⊆singularSet (n:=n) W:=hCD.trans inter_subset_left
  have hKC : IsCompact C:=hDK.of_isClosed_subset hAdm.1.1 hCD
  have hAdmW : (⟨univ,E,vanishingIdeal (n:=n) W,1⟩ : MarkedIdeal n X).IsAdmissibleCentre C := by
    refine ⟨hAdm.1,?_,hAdm.2.2⟩
    rw [HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW.isClosed E]
    exact hCS.trans (singularSet_subset W)
  have hIntC : interior C=∅:=eq_empty_of_subset_empty ((interior_mono hCD).trans hDThin.subset)
  obtain ⟨Y,pi,hpi⟩:=exists_blowup C hAdm.1 hIntC
  have hSub : (singularSet (n:=n) W)ᶜ⊆Cᶜ:=fun _ hx hy=>hx (hCS hy)
  have hIsoC:=BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hpi
  have hIso : IsIsomorphismOver n pi (singularSet (n:=n) W)ᶜ := by
    refine ⟨⟨fun _ hz=>hz,?_,?_⟩,hIsoC.2.mono_left (preimage_mono hSub)⟩
    · exact hIsoC.1.2.1.mono (preimage_mono hSub)
    · intro x hx
      obtain ⟨y,_hy,he⟩:=hIsoC.1.2.2 (hSub hx)
      exact ⟨y,by change pi y∈(singularSet (n:=n) W)ᶜ;rwa [he],he⟩
  have hWell : (⟨univ,E,vanishingIdeal (n:=n) W,1⟩ : MarkedIdeal n X).IsWellFormed:=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,CartanIrreducible.cartanCoherence W hW,
      hE,isTransverse_univ_of_isSNCDivisor hE⟩
  have hEnext:=(GeoTransformWellFormed.isWellFormed_geoTransform_of_isAdmissibleCentre hWell hAdmW hpi).isSNCDivisor
  have hWnext:=HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong hpi hW
  have hKnext : IsCompact (strictTransform n pi W):=
    (HironakaLocalPrincipalization.isCompact_preimage_of_isBlowupAlong hpi hK).of_isClosed_subset
      isClosed_closure (closure_minimal sdiff_subset (hW.isClosed.preimage hpi.contMDiff.continuous))
  refine ⟨a,U,ha,hMaxSing,hDne,hDA,hDK,hDEq,hDU,hUpperU,hDom,hCos,C,Y,pi,hpi,⟨c,hc,hMax⟩,hKC,hCD,hCS,hAdmW,rfl,
    HironakaLocalPrincipalization.isProperMap_of_isBlowupAlong hpi,hIso,hEnext,hWnext,hKnext,?_⟩
  apply hilbertSamuelAt_actual_hs_constant_smooth_centre_blowup_le hpi hAdm.1 hW
  intro x hx y hy ell
  exact (((Set.ext_iff.mp hDEq x).mp (hCD hx)) ell).trans
    (((Set.ext_iff.mp hDEq y).mp (hCD hy)) ell).symm

end
end Hironaka.HironakaUniformHistoricalSuccessorCompactSingular
