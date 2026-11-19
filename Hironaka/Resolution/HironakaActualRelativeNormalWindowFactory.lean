import Hironaka.Resolution.HironakaActualNormalBlockCoordinateDictionary

/-! Actual original coordinate restrictions and normal-window factory.
Blueprint: hironaka-actual-relative-normal-window-factory-20261102.tex. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualRelativeNormalWindowFactory
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaActualOpenZeroSectionDifferentials HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaActualRelativeNormalGeometry
  HironakaActualIteratedRelativeNormalHistory HironakaActualNormalBlockCoordinateDictionary
  HironakaActualZeroCoordinateContactSeed HironakaSmoothSubmersionCoefficientIdeals
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaSmoothSubmersionRelativeRestriction
  ResolutionInvariantSpec InvDomainTowerAlong RelativePrincipalizationSpan GermIdealPullbackCalculus
  RestrictedIdealExtension

private abbrev model {m : ℕ} (U : Opens (ComplexModel m)) : CMfd.{0} m:=CMfd.of (n:=m) U

def baseInclusion {n : ℕ} {A U : Opens (ComplexModel n)} (hAU : A ≤ U) : A → U:=
  fun x=>⟨x.val,hAU x.property⟩

theorem baseInclusion_contMDiff {n : ℕ} {A U : Opens (ComplexModel n)} (hAU : A ≤ U) :
    ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (baseInclusion hAU):=
  contMDiff_inclusion hAU

def restrictedIdeal {n : ℕ} {U : Opens (ComplexModel n)} (I : GermIdeal n U)
    {A : Opens (ComplexModel n)} (hAU : A ≤ U) : GermIdeal n A:=
  GermIdeal.pullback (m:=n) (baseInclusion hAU) I

/-- The genuine smaller coordinate open inherits its ORIGINAL domain. -/
theorem restricted_original_domain {n q : ℕ} {A U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hM : IsInvDomain q (relativeBaseMarked I)) (hAU : A ≤ U) :
    IsInvDomain q (relativeBaseMarked (restrictedIdeal I hAU)):=by
  let W:=MaxLocusLocal.nestedOpens U A
  let Φ:=(MaxLocusLocal.nestedOpensDiffeo (n:=n) hAU).symm
  have h:=isInvDomain_pullback Φ (isInvDomain_pullback_val W hM)
  have hIdeal : GermIdeal.pullback (m:=n) Φ
      (GermIdeal.pullback (m:=n) (Subtype.val : W → U) I)=restrictedIdeal I hAU:=by
    rw [←coherent_pullback_comp contMDiff_subtype_val Φ.contMDiff I hM.isWellFormed.isCoherent]
    rfl
  have hWhole : MarkedIdeal.pullback Φ
      (MarkedIdeal.pullback (Subtype.val : W → U) (relativeBaseMarked I))=
        relativeBaseMarked (restrictedIdeal I hAU):=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hIdeal rfl
  exact hWhole ▸ h

theorem iteratedOpen_mono {n : ℕ} {A U : Opens (ComplexModel n)} (hAU : A ≤ U) (r : ℕ) :
    iteratedOpen A r ≤ iteratedOpen U r:=by
  intro z hz
  exact (mem_iteratedOpen_iff U r z).mpr (hAU ((mem_iteratedOpen_iff A r z).mp hz))

def normalInclusion {n : ℕ} {A U : Opens (ComplexModel n)} (hAU : A ≤ U) (r : ℕ) :
    iteratedOpen A r → iteratedOpen U r:=baseInclusion (iteratedOpen_mono hAU r)

theorem normalInclusion_contMDiff {n : ℕ} {A U : Opens (ComplexModel n)} (hAU : A ≤ U) (r : ℕ) :
    ContMDiff 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel (n+r)) ∞ (normalInclusion hAU r):=
  baseInclusion_contMDiff (iteratedOpen_mono hAU r)

theorem normalInclusion_zeroSection {n : ℕ} {A U : Opens (ComplexModel n)}
    (hAU : A ≤ U) (r : ℕ) (x : A) :
    normalInclusion hAU r (iteratedZeroSection A r x)=iteratedZeroSection U r (baseInclusion hAU x):=by
  apply Subtype.ext
  change (iteratedZeroSection A r x).val=(iteratedZeroSection U r (baseInclusion hAU x)).val
  rw [iteratedZeroSection_val,iteratedZeroSection_val]
  rfl

private theorem iteratedIdeal_coherent {n : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hI : I.IsCoherent) (r : ℕ) : (iteratedIdeal I r).IsCoherent:=by
  induction r with
  | zero=>exact hI
  | succ r ih=>exact relativeNormalIdeal_isCoherent ih

private abbrev planeIdeal (n : ℕ) : GermIdeal (n+1) (ComplexModel (n+1)):=
  vanishingIdeal (n:=n+1) (HironakaActualZeroCoordinateContactSeed.zeroPlane n)

private theorem planeIdeal_coherent (n : ℕ) : (planeIdeal n).IsCoherent:=by
  apply CartanIrreducible.cartanCoherence
  exact AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (actualJointNormalProjection n 1).contMDiff
    (FibreDimensionLowerBound.isComplexAnalyticSubset_singleton (0 : ComplexModel 1))

private theorem normalPullback_coherent {n : ℕ} (U : Opens (ComplexModel n)) :
    (GermIdeal.pullback (m:=n+1) (Subtype.val : productOpen U → ComplexModel (n+1)) (planeIdeal n)).IsCoherent:=
  isCoherent_pullback contMDiff_subtype_val (planeIdeal_coherent n)

/-- ENTIRE iterated ideal commutes with the ACTUAL original open restriction. -/
theorem iteratedIdeal_restrict {n : ℕ} {A U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hI : I.IsCoherent) (hAU : A ≤ U) (r : ℕ) :
    GermIdeal.pullback (m:=n+r) (normalInclusion hAU r) (iteratedIdeal I r)=
      iteratedIdeal (restrictedIdeal I hAU) r:=by
  induction r with
  | zero=>rfl
  | succ r ih=>
    have hIr:=(iteratedIdeal_coherent hI r)
    have hBase : GermIdeal.pullback (m:=n+(r+1)) (normalInclusion hAU (r+1))
        (GermIdeal.pullback (m:=n+(r+1)) (projection (iteratedOpen U r)) (iteratedIdeal I r))=
        GermIdeal.pullback (m:=n+(r+1)) (projection (iteratedOpen A r))
          (iteratedIdeal (restrictedIdeal I hAU) r):=by
      have hComp : projection (iteratedOpen U r)∘normalInclusion hAU (r+1)=
          normalInclusion hAU r∘projection (iteratedOpen A r):=rfl
      exact ((coherent_pullback_comp (projection_contMDiff (iteratedOpen U r))
        (normalInclusion_contMDiff hAU (r+1)) (iteratedIdeal I r) hIr).symm.trans
          (congrArg (fun f=>GermIdeal.pullback (m:=n+(r+1)) f (iteratedIdeal I r)) hComp)).trans
        ((coherent_pullback_comp (normalInclusion_contMDiff hAU r)
          (projection_contMDiff (iteratedOpen A r)) (iteratedIdeal I r) hIr).trans
            (congrArg (fun J=>GermIdeal.pullback (m:=n+(r+1)) (projection (iteratedOpen A r)) J) ih))
    have hNormal : GermIdeal.pullback (m:=n+(r+1)) (normalInclusion hAU (r+1))
        (GermIdeal.pullback (m:=n+(r+1))
          (Subtype.val : iteratedOpen U (r+1) → ComplexModel (n+(r+1))) (planeIdeal (n+r)))=
        GermIdeal.pullback (m:=n+(r+1))
          (Subtype.val : iteratedOpen A (r+1) → ComplexModel (n+(r+1))) (planeIdeal (n+r)):=by
      exact (coherent_pullback_comp contMDiff_subtype_val (normalInclusion_contMDiff hAU (r+1))
        (planeIdeal (n+r)) (planeIdeal_coherent (n+r))).symm
    exact (pullback_sumIdeal_dimensions (normalInclusion_contMDiff hAU (r+1))
      (isCoherent_pullback (projection_contMDiff (iteratedOpen U r)) hIr)
      (normalPullback_coherent (iteratedOpen U r))).trans
        (congrArg₂ (fun J K : GermIdeal (n+(r+1)) (productOpen (iteratedOpen A r))=>sumIdeal J K) hBase hNormal)

theorem iteratedMarked_restrict {n : ℕ} {A U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hI : I.IsCoherent) (hAU : A ≤ U) (r : ℕ) :
    MarkedIdeal.pullback (normalInclusion hAU r) (iteratedMarked I r)=
      iteratedMarked (restrictedIdeal I hAU) r:=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl (iteratedIdeal_restrict hI hAU r) rfl

private def coordinateImageOpen {d : ℕ} (P : Opens (ComplexModel d)) (S : Opens P) :
    Opens (ComplexModel d):=
  ⟨(Subtype.val : P → ComplexModel d) '' S,
    P.isOpen.isOpenEmbedding_subtypeVal.isOpenMap S S.isOpen⟩

/-- The ACTUAL coordinate base window is defined from the genuine ambient
window itself, with no incoming zero-plane containment hypothesis. -/
def sourceWindow {n : ℕ} (U : Opens (ComplexModel n)) (r : ℕ)
    (S : Opens (iteratedOpen U r)) : Opens (ComplexModel n):=
  ⟨tangentInclusion n r ⁻¹' coordinateImageOpen (iteratedOpen U r) S,
    (coordinateImageOpen (iteratedOpen U r) S).isOpen.preimage (tangentInclusion n r).continuous⟩

theorem sourceWindow_le {n : ℕ} (U : Opens (ComplexModel n)) (r : ℕ)
    (S : Opens (iteratedOpen U r)) : sourceWindow U r S ≤ U:=by
  intro x hx
  change tangentInclusion n r x∈(Subtype.val : iteratedOpen U r → ComplexModel (n+r)) '' S at hx
  obtain ⟨z,_hz,he⟩:=hx
  have h:=(mem_iteratedOpen_iff U r z.val).mp z.property
  rw [he,tangentProjection_tangentInclusion] at h
  exact h

theorem mem_sourceWindow_iff {n : ℕ} (U : Opens (ComplexModel n)) (r : ℕ)
    (S : Opens (iteratedOpen U r)) (x : U) :
    x.val∈sourceWindow U r S ↔ iteratedZeroSection U r x∈S:=by
  change (tangentInclusion n r x.val∈(Subtype.val : iteratedOpen U r → ComplexModel (n+r)) '' S) ↔ _
  constructor
  · rintro ⟨z,hz,he⟩
    have hzx : z=iteratedZeroSection U r x:=
      Subtype.ext (he.trans (iteratedZeroSection_val U r x).symm)
    exact hzx ▸ hz
  · intro hx
    exact ⟨iteratedZeroSection U r x,hx,iteratedZeroSection_val U r x⟩

def normalWindow {n : ℕ} (U : Opens (ComplexModel n)) (r : ℕ)
    (S : Opens (iteratedOpen U r)) : Opens (iteratedOpen (sourceWindow U r S) r):=
  ⟨normalInclusion (sourceWindow_le U r S) r ⁻¹' S,
    S.isOpen.preimage (normalInclusion_contMDiff (sourceWindow_le U r S) r).continuous⟩

/-- The actual generated product window contains its ENTIRE literal zero section. -/
theorem normalWindow_zeroSection {n : ℕ} (U : Opens (ComplexModel n)) (r : ℕ)
    (S : Opens (iteratedOpen U r)) (x : sourceWindow U r S) :
    iteratedZeroSection (sourceWindow U r S) r x∈normalWindow U r S:=by
  change normalInclusion (sourceWindow_le U r S) r
    (iteratedZeroSection (sourceWindow U r S) r x)∈S
  rw [normalInclusion_zeroSection]
  exact (mem_sourceWindow_iff U r S (baseInclusion (sourceWindow_le U r S) x)).mp x.property

def normalWindowInclusion {n : ℕ} (U : Opens (ComplexModel n)) (r : ℕ)
    (S : Opens (iteratedOpen U r)) : normalWindow U r S → iteratedOpen U r:=
  fun z=>normalInclusion (sourceWindow_le U r S) r z.val

/-- Original input constructs the actual window domain, with no supplied
restricted domain or initial-record identity. -/
theorem normalWindow_original_domain {n q : ℕ} {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hM : IsInvDomain q (relativeBaseMarked I)) (r : ℕ)
    (S : Opens (iteratedOpen U r)) :
    IsInvDomain (q+r) (MarkedIdeal.pullback
      (Subtype.val : normalWindow U r S → iteratedOpen (sourceWindow U r S) r)
      (iteratedMarked (restrictedIdeal I (sourceWindow_le U r S)) r)):=
  isInvDomain_pullback_val (normalWindow U r S)
    (original_iterated_domain (restricted_original_domain hM (sourceWindow_le U r S)) r)

/-- ENTIRE actual window record under the SAME genuine composite inclusion. -/
theorem normalWindow_entire_initial_record {n : ℕ} {U : Opens (ComplexModel n)} {I : GermIdeal n U}
    (hI : I.IsCoherent) (r : ℕ) (S : Opens (iteratedOpen U r)) :
    MarkedIdeal.pullback (normalWindowInclusion U r S) (iteratedMarked I r)=
      MarkedIdeal.pullback
        (Subtype.val : normalWindow U r S → iteratedOpen (sourceWindow U r S) r)
        (iteratedMarked (restrictedIdeal I (sourceWindow_le U r S)) r):=by
  have hIdeal : GermIdeal.pullback (m:=n+r) (normalWindowInclusion U r S) (iteratedIdeal I r)=
      GermIdeal.pullback (m:=n+r)
        (Subtype.val : normalWindow U r S → iteratedOpen (sourceWindow U r S) r)
        (iteratedIdeal (restrictedIdeal I (sourceWindow_le U r S)) r):=
    (coherent_pullback_comp (normalInclusion_contMDiff (sourceWindow_le U r S) r)
      contMDiff_subtype_val (iteratedIdeal I r) (iteratedIdeal_coherent hI r)).trans
        (congrArg (fun J=>GermIdeal.pullback (m:=n+r)
          (Subtype.val : normalWindow U r S → iteratedOpen (sourceWindow U r S) r) J)
          (iteratedIdeal_restrict hI (sourceWindow_le U r S) r))
  exact MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl hIdeal rfl

end
end Hironaka.HironakaActualRelativeNormalWindowFactory
