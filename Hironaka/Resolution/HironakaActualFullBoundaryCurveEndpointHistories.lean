import Hironaka.Resolution.HironakaG3CentresOverGenericFactor
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Invariant.RestrictEmptyTower
import Hironaka.Resolution.HironakaBoundaryContainedSharpBad
import Hironaka.Resolution.HironakaOneDimensionalCanonicalSuperlevels
import Hironaka.Resolution.HironakaSharpActualCurveGlobalExceptionalBirthSupport
import Hironaka.Resolution.HironakaActualEndpointOpenRefinement
import Hironaka.Invariant.DropMembers

/-! Actual nested-open and history transport for the internally constructed
full-boundary curve recipe family. Original and born boundary positions
must stay on the SAME actual towers. No global finite-length bound or
supplied resolving/comparison family is a source premise.
Blueprint: `hironaka-actual-full-boundary-curve-endpoint-histories-20261101.tex`.
-/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Topology Manifold ContDiff
universe u

namespace Hironaka.HironakaActualFullBoundaryCurveEndpointHistories
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves BlowupTowers
  BlowupTowerIsomorphism BlowupTowerTransforms RestrictEmptyTower
  HironakaSharpOriginalMultiBoundaryBadLocus NormalCrossings
  AnalyticDimensionBasics CoefficientIdealRestriction HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossingsInvariance
  MarkedIdealTowerTransport MarkedIdealBiholomorphism MarkedIdealRestrictOpen BlowupRestrictOpen
  HironakaSharpActualFiniteChronologicalHistory IdealWeightPowers SimultaneousNormalCrossings
  HironakaSharpActualCurveOriginalRecipeAtlas HironakaSharpActualCurveFullAmbientBoundary
  HironakaSharpActualCurveWholeBoundaryTransversality HironakaSharpOriginalMemberProductDomain
  HironakaSharpOriginalMemberProduct HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpActualCurveGlobalExceptionalBirthSupport HironakaSharpActualCurveInitialGoodPreservation
  HironakaSharpActualCurveExceptionalDifference HironakaActualEndpointOpenRefinement
  HironakaSharpOriginalAllBoundaryCentre NormalCrossingsComparison
  BlowupTowerIsoTail BlowupTowerSplitIso MaxLocusLocal HironakaAdmissibleCalculus
  HironakaSharpActualCurveTopologicalGluing HironakaSharpActualCurveOverlapMaps
  HironakaSharpActualCurveEndpointGeometry HironakaSharpActualCurveCommonOpenCocycle
  HironakaSharpActualCurveEmptyPadding HironakaSharpActualCurveChosenOverlapCocycle BlowupTowerSplit
open ResolutionInvariantSpec (IsInvDomain)

variable {n : ℕ} {X : CMfd.{u} n}

/-- The actual ambient image of an open inside a true open. -/
def ambientOpen (U : Opens X) (V : Opens (CMfd.of (n := n) U)) : Opens X :=
  ⟨(Subtype.val : U → X) '' (V : Set U),U.isOpen.isOpenMap_subtype_val _ V.isOpen⟩

private theorem ambientOpen_subset (U : Opens X) (V : Opens (CMfd.of (n := n) U)) :
    (ambientOpen U V : Set X)⊆U := by
  rintro x ⟨y,_hy,rfl⟩
  exact y.property

/-- Canonical actual flattening, using exactly the original subtype points. -/
def flattenOpenEquiv (U : Opens X) (V : Opens (CMfd.of (n := n) U)) :
    CMfd.of (n := n) V
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) (ambientOpen U V) := by
  let B := ambientOpen U V
  let f : V → B := fun p => ⟨p.val.val,⟨p.val,p.property,rfl⟩⟩
  let g : B → U := fun p => ⟨p.val,ambientOpen_subset U V p.property⟩
  have hg : ∀p : B,g p∈V := by
    intro p
    obtain ⟨q,hq,hqp⟩ := p.property
    have heq : g p=q := Subtype.ext hqp.symm
    rw [heq]
    exact hq
  let inv : B → V := fun p => ⟨g p,hg p⟩
  have hgCont : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ g :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val
      (fun p => ambientOpen_subset U V p.property)
  refine ⟨⟨f,inv,?_,?_⟩,?_,?_⟩
  · intro p
    apply Subtype.ext
    exact Subtype.ext rfl
  · intro p
    exact Subtype.ext rfl
  · exact BlowupRestrictOpen.contMDiff_opens_mk (V := B) (f := fun p : V => p.val.val)
      (contMDiff_subtype_val.comp contMDiff_subtype_val)
      (fun p => ⟨p.val,p.property,rfl⟩)
  · exact BlowupRestrictOpen.contMDiff_opens_mk hgCont hg

theorem flattenOpenEquiv_apply (U : Opens X) (V : Opens (CMfd.of (n := n) U)) (p : V) :
    (flattenOpenEquiv U V p).val=p.val.val := rfl

theorem flattenOpenEquiv_symm_apply (U : Opens X) (V : Opens (CMfd.of (n := n) U))
    (p : ambientOpen U V) : ((flattenOpenEquiv U V).symm p).val.val=p.val := rfl

/-- Genuine empty histories produce their actual stagewise comparison;
no last-stage map is supplied and no empty chronological step is erased. -/
theorem exists_empty_tower_comparison {X' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X) :
    ∀{Y' Y : CMfd.{u} n}(T' : BlowupTower X' Y')(T : BlowupTower X Y),
      ResolutionInvariantExt.IsEmptyTower T' → ResolutionInvariantExt.IsEmptyTower T →
      T'.length=T.length →
      ∃χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
        IsTowerIso Φ T' T χ
  | _,_,.refl,.refl,_hE',_hE,_hLen => ⟨Φ,IsTowerIso.refl⟩
  | _,_,.refl,.step T _ _ _,_hE',_hE,hLen => by
    change 0=T.length+1 at hLen
    omega
  | _,_,.step T' _ _ _,.refl,_hE',_hE,hLen => by
    change T'.length+1=0 at hLen
    omega
  | Z',Z,.step T' C' π' hπ',.step T C π hπ,hE',hE,hLen => by
    obtain ⟨χ,hχ⟩ := exists_empty_tower_comparison Φ T' T hE'.1 hE.1 (Nat.succ.inj hLen)
    have hCentres : χ ⁻¹' C=C' := by rw [hE.2,hE'.2,preimage_empty]
    have hπTransport := MarkedIdealBiholomorphism.isBlowupAlong_comp_inverse
      χ.contMDiff χ.symm.contMDiff χ.apply_symm_apply χ.symm_apply_apply hπ
    rw [hCentres] at hπTransport
    obtain ⟨e,f,he,hf,hπe,_hπf,hfe,hef⟩ :=
      BlowupUniqueness.exists_biholomorphism_over hπ' hπTransport
    let χ₁ : Z' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Z :=
      ⟨⟨e,f,congrFun hfe,congrFun hef⟩,he,hf⟩
    refine ⟨χ₁,IsTowerIso.step hχ hπ' hπ χ₁ ?_ hCentres⟩
    intro z
    change π (e z)=χ (π' z)
    have h : χ.symm (π (e z))=π' z := congrFun hπe z
    have h' := congrArg χ h
    simpa only [χ.apply_symm_apply] using h'

/-- The SAME original full-boundary bad set is genuinely analytic and
zero dimensional, hence closed discrete, even on boundary-contained curves. -/
theorem original_curve_bad_analytic_dimzero_discrete
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hr : ∀x∈W,RegularAtDim (n := n) W x 1) :
    IsComplexAnalyticSubset (n := n) (originalSharpBadLocus (n := n) W E) ∧
      DimLE (n := n) (originalSharpBadLocus (n := n) W E) 0 ∧
      IsClosed (originalSharpBadLocus (n := n) W E) ∧
      IsDiscrete (originalSharpBadLocus (n := n) W E) := by
  obtain ⟨hBad,hThin⟩ := HironakaBoundaryContainedSharpBad.original_sharp_bad_analytic_and_thin hW hE
  have hDimW : DimLE (n := n) W 1 := by
    intro y k hy
    exact (RegularPointDimension.eq_of_regularAtDim hy (hr y hy.2.1)).le
  have hDim : DimLE (n := n) (originalSharpBadLocus (n := n) W E) 0 :=
    ThinDimensionDrop.dimLE_pred_of_thin
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold hW)
      (fun _ hy => hy.1) hThin hDimW
  exact ⟨hBad,hDim,hBad.isClosed,
    HironakaOneDimensionalCanonicalSuperlevels.isDiscrete_of_analytic_dimLE_zero hBad hDim⟩

private theorem centresOver_mono {F B : Set X} (hFB : F⊆B) :
    ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),CentresOver F T → CentresOver B T
  | _,.refl,_ => trivial
  | _,.step T _ _ _,h => ⟨centresOver_mono hFB T h.1,fun _ hy => hFB (h.2 hy)⟩

private theorem centresOver_restrict (U : Opens X) (F : Set X) :
    ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),CentresOver F T →
      CentresOver ((Subtype.val : U → X) ⁻¹' F) (restrict U T) := fun T h => HironakaG3CentresOverGenericFactor.centresOver_restrict U F T h

private theorem centresOver_of_isTowerIso {X' Y' Y : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (F : Set X) :
    CentresOver F T → CentresOver (Φ ⁻¹' F) T' := HironakaG3CentresOverGenericFactor.centresOver_of_isTowerIso hiso F

private theorem centresIn_restrict (U : Opens X) (W : Set X) :
    ∀{Y : CMfd.{u} n}(T : BlowupTower X Y),CentresIn W T →
      CentresIn ((Subtype.val : U → X) ⁻¹' W) (restrict U T)
  | _,.refl,_ => trivial
  | _,.step T _ _ _,h => by
    refine ⟨centresIn_restrict U W T h.1,?_⟩
    intro y hy
    rw [strictAlong_restrict]
    exact h.2 hy

private theorem centresIn_of_isTowerIso {X' Y' Y : CMfd.{u} n}
    {Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (W : Set X) :
    CentresIn W T → CentresIn (Φ ⁻¹' W) T' := by
  induction hiso with
  | refl => exact fun _ => trivial
  | @step Y' Y Z' Z T' T χ hiso C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro h
    refine ⟨ih h.1,?_⟩
    intro y hy
    rw [hiso.strictAlong_eq W]
    have hyC : χ y∈C := by change y∈χ ⁻¹' C;rw [hC];exact hy
    exact h.2 hyC

private theorem pullback_template {Y : CMfd.{u} n} (f : Y → X) (E : List (Set X)) :
    MarkedIdeal.pullback f (geometricTemplate (univ : Set X) E)=
      geometricTemplate (univ : Set Y) (E.map (f ⁻¹' ·)) := by
  simp [MarkedIdeal.pullback,geometricTemplate,BlowupExceptionalDivisor.pullback_unitIdeal]

private theorem full_geometry_restrictIso {Y X' Y' : CMfd.{u} n}
    (W : Set X) (E : List (Set X)) (hE : IsSNCDivisor n E)
    (T : BlowupTower X Y) (hC : CentresIn W T)
    (hT : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSmooth : IsClosedSubmanifold n (strictAlong T W))
    (hNC : HasNormalCrossings n (strictAlong T W)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E)
    (U : Opens X) (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ CMfd.of (n := n) U)
    (T' : BlowupTower X' Y')
    (χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U))
    (hIso : IsTowerIso Φ T' (restrict U T) χ) :
    let W' := Φ ⁻¹' ((Subtype.val : U → X) ⁻¹' W)
    let E' := (E.map ((Subtype.val : U → X) ⁻¹' ·)).map (Φ ⁻¹' ·)
    CentresIn W' T' ∧
      IsGeoTestTower (geometricTemplate (univ : Set X') E') T' ∧
      IsClosedSubmanifold n (strictAlong T' W') ∧
      IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set X') E') T').E ∧
      HasNormalCrossings n (strictAlong T' W')
        (geoTransformAlong (geometricTemplate (univ : Set X') E') T').E := by
  dsimp only
  let A : MarkedIdeal n X:=geometricTemplate (univ : Set X) E
  let EU:=E.map ((Subtype.val : U → X) ⁻¹' ·)
  let AU : MarkedIdeal n (CMfd.of (n := n) U):=geometricTemplate (univ : Set U) EU
  have hA : A.IsWellFormed:=⟨isClosedSubmanifold_univ,isCoherent_unitIdeal,hE,
    isTransverse_univ_of_isSNCDivisor hE⟩
  have hTU := isGeoTestTower_restrict U isClosedSubmanifold_univ isCoherent_unitIdeal T hT
  rw [pullback_template (Y := CMfd.of (n := n) U) (Subtype.val : U → X) E] at hTU
  have hNew := (IsTowerIso.isGeoTestTower_iff (𝔪 := AU) Φ
    isClosedSubmanifold_univ isCoherent_unitIdeal hIso).mpr hTU
  rw [pullback_template (X := CMfd.of (n := n) U) (Y := X') Φ EU] at hNew
  have hRecU:=geoTransformAlong_restrict U isClosedSubmanifold_univ isCoherent_unitIdeal T hT
  rw [pullback_template (Y := CMfd.of (n := n) U) (Subtype.val : U → X) E] at hRecU
  have hEU : (geoTransformAlong AU (restrict U T)).E=
      (geoTransformAlong A T).E.map ((Subtype.val : openPreimage T U → Y) ⁻¹' ·) := by
    exact congrArg MarkedIdeal.E hRecU
  have hRecNew:=IsTowerIso.geoTransformAlong_eq (𝔪 := AU) Φ
    isClosedSubmanifold_univ isCoherent_unitIdeal hIso hTU
  rw [pullback_template (X := CMfd.of (n := n) U) (Y := X') Φ EU] at hRecNew
  have hENew :
      (geoTransformAlong (geometricTemplate (univ : Set X') (EU.map (Φ ⁻¹' ·))) T').E=
        (geoTransformAlong AU (restrict U T)).E.map (χ ⁻¹' ·) :=
    congrArg MarkedIdeal.E hRecNew
  have hStrict:=hIso.strictAlong_eq ((Subtype.val : U → X) ⁻¹' W)
  have hSmoothU:=isClosedSubmanifold_preimage_val hSmooth (openPreimage T U)
  rw [←strictAlong_restrict U T W] at hSmoothU
  have hSmoothNew:=(isClosedSubmanifold_preimage_iff χ).mpr hSmoothU
  rw [←hStrict] at hSmoothNew
  have hNCU:=hasNormalCrossings_preimage (pullsBackCoordinates_val (openPreimage T U)) hNC
  rw [←strictAlong_restrict U T W,←hEU] at hNCU
  have hNCNew:=hasNormalCrossings_preimage (pullsBackCoordinates χ) hNCU
  rw [←hStrict,←hENew] at hNCNew
  have hSNCU:=isSNCDivisor_map_preimage (pullsBackCoordinates_val (openPreimage T U))
    continuous_subtype_val (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hA T hT).isSNCDivisor
  rw [←hEU] at hSNCU
  have hSNCNew:=isSNCDivisor_map_preimage (pullsBackCoordinates χ) χ.continuous hSNCU
  rw [←hENew] at hSNCNew
  exact ⟨centresIn_of_isTowerIso hIso _ (centresIn_restrict U W T hC),hNew,
    hSmoothNew,hSNCNew,hNCNew⟩

private theorem dense_preimage_val {W : Set X} {E : List (Set X)}
    (h : W⊆closure (W\⋃H∈E,H)) (U : Opens X) :
    (Subtype.val : U → X) ⁻¹' W⊆closure
      (((Subtype.val : U → X) ⁻¹' W)\⋃H∈E.map ((Subtype.val : U → X) ⁻¹' ·),H) := by
  intro y hy
  have hp : y∈(Subtype.val : U → X) ⁻¹' closure (W\⋃H∈E,H):=h hy
  have hcl : (Subtype.val : U → X) ⁻¹' closure (W\⋃H∈E,H)=
      closure ((Subtype.val : U → X) ⁻¹' (W\⋃H∈E,H)) :=
    U.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      (show Continuous (Subtype.val : U → X) from continuous_subtype_val) _
  rw [hcl] at hp
  convert hp using 1
  congr 1
  ext z
  simp

/-- ONLY original smooth-curve/full-boundary geometry constructs the SAME
actual finite recipe over an isolated original bad point. All true centre
footprints and whole boundary positions are derived from retained recipes. -/
theorem exists_actual_point_supported_curve_recipe
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hr : ∀x∈W,RegularAtDim (n := n) W x 1)
    {b : X} (hb : b∈originalSharpBadLocus (n := n) W E) :
    ∃ V : Opens X,b∈V ∧
      (V : Set X)∩originalSharpBadLocus (n := n) W E={b} ∧
      ∃(Y : CMfd.{u} n)(T : BlowupTower (CMfd.of (n := n) V) Y),
        let WV : Set V:=(Subtype.val : V → X) ⁻¹' W
        let EV:=E.map ((Subtype.val : V → X) ⁻¹' ·)
        CentresOver ((Subtype.val : V → X) ⁻¹' {b}) T ∧
        CentresIn WV T ∧ IsGeoTestTower (geometricTemplate (univ : Set V) EV) T ∧
        IsClosedSubmanifold n (strictAlong T WV) ∧
        IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set V) EV) T).E ∧
        HasNormalCrossings n (strictAlong T WV)
          (geoTransformAlong (geometricTemplate (univ : Set V) EV) T).E ∧
        (geoTransformAlong (geometricTemplate (univ : Set V) EV) T).E=
          EV.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate WV []) T).E ∧
        IsProperMap T.proj ∧ IsIsomorphismOver n T.proj
          ((Subtype.val : V → X) ⁻¹' originalGoodLocus (n := n) W E) := by
  classical
  have hn : 0<n:=by have h:=(hr b hb.1).1;omega
  obtain ⟨_hAna,_hDim,_hClosed,hDiscrete⟩:=original_curve_bad_analytic_dimzero_discrete hW hE hr
  obtain ⟨Oset,hOo,hOB⟩:=(isDiscrete_iff_forall_mem_exists_isOpen.mp hDiscrete) b hb
  let O : Opens X:=⟨Oset,hOo⟩
  have hbO : b∈O:=((Set.ext_iff.mp hOB b).mpr (mem_singleton b)).1
  obtain ⟨U,F,hbU,hFE,_hMem,hOmitted,hDenseU,hBad⟩:=
    HironakaBoundaryContainedSharpBad.exists_actual_component_boundary_window hn hW hE hb.1
  let WU : Set U:=(Subtype.val : U → X) ⁻¹' W
  let EU:=E.map ((Subtype.val : U → X) ⁻¹' ·)
  let FU:=F.map ((Subtype.val : U → X) ⁻¹' ·)
  have hWU:=isClosedSubmanifold_preimage_val hW U
  have hEU : IsSNCDivisor n EU:=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val U) continuous_subtype_val hE
  have hFEU : FU.Sublist EU:=hFE.map ((Subtype.val : U → X) ⁻¹' ·)
  have hFU:=isSNCDivisor_of_sublist hEU hFEU
  have hrU : ∀y∈WU,RegularAtDim (n := n) WU y 1:=
    fun y hy=>AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hr y.val hy)
  let A:=originalEndpointHistories (X := CMfd.of (n := n) U) (W := WU) (E := FU)
    hn hWU hFU hDenseU hrU
  let p : U:=⟨b,hbU⟩
  let V₀:=A.openSet p
  let P:=A.prefixTower p
  let S:=A.tail p
  let T₀:=P.append S
  let W₀ : Set V₀:=(Subtype.val : V₀ → U) ⁻¹' WU
  let E₀:=EU.map ((Subtype.val : V₀ → U) ⁻¹' ·)
  let F₀:=FU.map ((Subtype.val : V₀ → U) ⁻¹' ·)
  let M:=originalMemberProductMarked (X := CMfd.of (n := n) V₀) W₀ F₀ 1
  obtain ⟨π,hπ,hFirst,_hPB,hSteps,hTest,_hZ,_hD,_hProper,hDom,_hSNCF,hTransF,_hIsoF⟩:=
    originalEndpointHistories_geometric_dictionary (X := CMfd.of (n := n) U)
      (W := WU) (E := FU) hn hWU hFU hDenseU hrU p
  change IsGeoTestTower M T₀ at hTest
  have hW₀:=isClosedSubmanifold_preimage_val hWU V₀
  have hE₀ : IsSNCDivisor n E₀:=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val V₀) continuous_subtype_val hEU
  have hFE₀ : F₀.Sublist E₀:=hFEU.map ((Subtype.val : V₀ → U) ⁻¹' ·)
  have hF₀:=isSNCDivisor_of_sublist hE₀ hFE₀
  have hr₀ : ∀y∈W₀,RegularAtDim (n := n) W₀ y 1:=
    fun y hy=>AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hrU y.val hy)
  have hDense₀:=dense_preimage_val (X := CMfd.of (n := n) U) hDenseU V₀
  have hM : IsInvDomain 1 M:=
    ⟨⟨hW₀,isCoherent_originalMemberProduct hn hF₀,isSNCDivisor_nil,
        isTransverse_nil_of_isClosedSubmanifold hW₀⟩,
      (fun y hy=>⟨1,le_rfl,hr₀ y hy⟩),le_rfl,
      (fun _ hy=>originalMemberProduct_isNonzeroAlongAt hn hF₀ hDense₀ hy)⟩
  have hCentres : CentresIn W₀ T₀:=centresIn_of_isGeoTestTower_withN M W₀ T₀ hTest
  have hFiltered:=(actual_domain_one_history_ambient_template M hM F₀ hF₀ T₀ hTest).2.1
  let A₀ : MarkedIdeal n (CMfd.of (n := n) V₀):=geometricTemplate (univ : Set V₀) E₀
  have hA₀ : A₀.IsWellFormed:=⟨isClosedSubmanifold_univ,isCoherent_unitIdeal,hE₀,
    isTransverse_univ_of_isSNCDivisor hE₀⟩
  have hContains : ∀H∈E₀,H∉F₀ → W₀⊆H:=by
    rintro H hH hNot
    obtain ⟨B,hBEU,rfl⟩:=List.mem_map.mp hH
    obtain ⟨G,hGE,rfl⟩:=List.mem_map.mp hBEU
    have hNotG : G∉F:=by
      intro hGF
      exact hNot (List.mem_map.mpr
        ⟨(Subtype.val : U → X) ⁻¹' G,List.mem_map.mpr ⟨G,hGF,rfl⟩,rfl⟩)
    exact fun y hy=>hOmitted G hGE hNotG ⟨hy,y.val.property⟩
  have hDrop:=DropMembers.isGeoTestTower_withE_iff_of_centresIn A₀ hA₀
    (E' := F₀) (S := W₀) (fun _ hH=>hFE₀.subset hH) hContains T₀ hCentres
  have hFull:=hDrop.1.mp hFiltered
  have hSNC:=(MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hA₀ T₀ hFull).isSNCDivisor
  have hN : (geoTransformAlong (geometricTemplate W₀ []) T₀).N=strictAlong T₀ W₀:=
    N_geoTransformAlong _ T₀
  have hNCF : HasNormalCrossings n (strictAlong T₀ W₀)
      (geoTransformAlong (geometricTemplate (univ : Set V₀) F₀) T₀).E:=by
    rw [actual_whole_ambient_boundary_ordered_dictionary W₀ F₀ T₀,←hN]
    exact hTransF.hasNormalCrossings
  have hNC:=(hasNormalCrossings_iff_of_forall_mem hSNC hDrop.2.1 hDrop.2.2).mp hNCF
  have hSmooth:=hDom.isWellFormed.isClosedSubmanifold_N
  rw [N_geoTransformAlong] at hSmooth
  let C₀:=chronologicalDistinctDefect W₀ F₀
    (.refl : BlowupTower (CMfd.of (n := n) V₀) (CMfd.of (n := n) V₀))
  have hFirstTest:=((isGeoTestTower_append_iff M P S).mp hTest).1
  have hOverC : CentresOver C₀ T₀:=by
    have hFT : IsGeoTestTower M (.step .refl C₀ π hπ):=hFirst ▸ hFirstTest
    have hST : HironakaSharpActualCurveFiniteAmbientDifferencePhase.actualAmbientDifferenceSteps
        W₀ F₀ (.step .refl C₀ π hπ) S:=hFirst ▸ hSteps
    have ho:=first_difference_recipe_centresOver hn hW₀ hF₀ hDense₀ hr₀ hπ hFT S hST
    change CentresOver C₀ (P.append S)
    rw [show P=BlowupTower.step .refl C₀ π hπ from hFirst]
    exact ho
  have hBadC : C₀⊆(Subtype.val : V₀ → U) ⁻¹' originalSharpBadLocus (n := n) WU FU:=by
    intro y hy
    rw [originalSharpBadLocus_eq_compl_good]
    intro hg
    exact original_curve_initial_good_subset_first_defect_complement hn hW₀ hF₀ hDense₀ hr₀
      (HironakaSharpActualCurveGlobalGoodIsomorphism.originalGoodLocus_preimage_val V₀ y hg) hy
  have hOver : CentresOver ((Subtype.val : V₀ → U) ⁻¹'
      ((Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E)) T₀:=by
    apply centresOver_mono (T := T₀) (F := C₀) ?_ hOverC
    intro y hy
    have h:=hBadC hy
    rw [hBad] at h
    exact h
  let V : U→Opens U:=fun i=>A.openSet i⊓nestedOpens U O
  have hV : ∀i,V i≤A.openSet i:=fun _=>inf_le_left
  let PR:=prefixRefinement A V hV p
  let SR:=tailRefinement A V hV p
  let T₁:=PR.tower.append SR.tower
  let B:=ambientOpen U (V p)
  let flat:=(flattenOpenEquiv U (V p)).symm
  let Q:=transport flat T₁
  let I:=nestedOpens V₀ (V p)
  let Ψ:=(nestedOpensDiffeo (n := n) (hV p)).symm
  let Φ:=flat.trans Ψ
  have hRef:=wholeRefinement_isTowerIso A V hV p
  have hAppend:=isTowerIso_restrict_append I P S
  have hRefWhole:=BlowupTowerSplitIso.IsTowerIso.congr_base (hRef.trans hAppend.symm)
    (Φ' := Ψ) (fun _=>rfl)
  have hIso:=(transport_isTowerIso flat T₁).trans hRefWhole
  have hGeom:=full_geometry_restrictIso W₀ E₀ hE₀ T₀ hCentres hFull hSmooth hNC
    I Φ Q.tower _ hIso
  have hWFlat : Φ ⁻¹' ((Subtype.val : I → V₀) ⁻¹' W₀)=
      (Subtype.val : B → X) ⁻¹' W:=by ext y;rfl
  have hEFlat : (E₀.map ((Subtype.val : I → V₀) ⁻¹' ·)).map (Φ ⁻¹' ·)=
      E.map ((Subtype.val : B → X) ⁻¹' ·):=by
    simp only [E₀,EU,List.map_map]
    apply List.map_congr_left
    intro H _hH
    ext y
    rfl
  rw [hWFlat,hEFlat] at hGeom
  have hOverQ:=centresOver_of_isTowerIso hIso _ (centresOver_restrict I _ T₀ hOver)
  change CentresOver ((Subtype.val : B → X) ⁻¹'
    originalSharpBadLocus (n := n) W E) Q.tower at hOverQ
  have hBO : (B : Set X)⊆O:=by
    rintro y ⟨z,hz,rfl⟩
    exact hz.2
  have hbV : p∈V p:=⟨originalEndpointHistories_point_mem (X := CMfd.of (n := n) U)
    (W := WU) (E := FU) hn hWU hFU hDenseU hrU p,hbO⟩
  have hbB : b∈B:=⟨p,hbV,rfl⟩
  have hBbad : (B : Set X)∩originalSharpBadLocus (n := n) W E={b}:=by
    apply Subset.antisymm
    · exact fun y hy=>(Set.ext_iff.mp hOB y).mp ⟨hBO hy.1,hy.2⟩
    · intro y hy
      rw [mem_singleton_iff.mp hy]
      exact ⟨hbB,hb⟩
  have hOverPoint : CentresOver ((Subtype.val : B → X) ⁻¹' {b}) Q.tower:=
    centresOver_mono (X := CMfd.of (n := n) B)
      (F := (Subtype.val : B → X) ⁻¹' originalSharpBadLocus (n := n) W E)
      (B := (Subtype.val : B → X) ⁻¹' {b})
      (fun y hy=>(Set.ext_iff.mp hBbad y.val).mp ⟨y.property,hy⟩) Q.tower hOverQ
  have hAdm:=HironakaAdmissibleSequence.isAdmissibleBlowupSequence_proj
    (geometricTemplate (X := CMfd.of (n := n) B) (univ : Set B)
      (E.map ((Subtype.val : B → X) ⁻¹' ·)))
    ((Subtype.val : B → X) ⁻¹' originalSharpBadLocus (n := n) W E)
    Q.tower hGeom.2.1 hOverQ
  have hGoodIso:=HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.isIsomorphismOver_compl hAdm
  have hGood : ((Subtype.val : B → X) ⁻¹' originalSharpBadLocus (n := n) W E)ᶜ=
      (Subtype.val : B → X) ⁻¹' originalGoodLocus (n := n) W E:=by
    rw [originalSharpBadLocus_eq_compl_good,preimage_compl,compl_compl]
  rw [hGood] at hGoodIso
  exact ⟨B,hbB,hBbad,Q.target,Q.tower,hOverPoint,hGeom.1,hGeom.2.1,hGeom.2.2.1,
    hGeom.2.2.2.1,hGeom.2.2.2.2,
    actual_whole_ambient_boundary_ordered_dictionary _ _ Q.tower,
    HironakaAdmissibleCalculus.isProperMap_of_isBlowupSequence Q.tower.isBlowupSequence,hGoodIso⟩

private theorem local_refl_padded_empty (U O : Opens X) (F : Set X)
    {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) U) Y) (L : ℕ)
    (hOver : CentresOver ((Subtype.val : U → X) ⁻¹' F) T)
    (hOF : Disjoint (O : Set X) F) :
    ResolutionInvariantExt.IsEmptyTower
      (localPaddedHistory U O (.refl : BlowupTower (CMfd.of (n := n) U) (CMfd.of (n := n) U)) T L) := by
  have hDisj : Disjoint (nestedOpens U O : Set U) ((Subtype.val : U → X) ⁻¹' F):=
    disjoint_left.mpr fun _ hyO hyF=>disjoint_left.mp hOF hyO hyF
  have hEmpty:=isEmptyTower_restrict_of_centresOver (nestedOpens U O) hDisj T hOver
  change ResolutionInvariantExt.IsEmptyTower
    ((BlowupTower.refl : BlowupTower (CMfd.of (n := n) (nestedOpens U O))
      (CMfd.of (n := n) (nestedOpens U O))).append
      ((restrict (nestedOpens U O) T).append
        (identityEmptyTail _ (L-(restrict (nestedOpens U O) T).length))))
  rw [BlowupTower.refl_append]
  exact (isEmptyTower_append_iff _ _).mpr ⟨hEmpty,identityEmptyTail_isEmptyTower _ _⟩

/-- Original geometry constructs the WHOLE actual full-boundary recipe
family and its genuine stagewise comparisons, with no atlas or schedule
input. Real histories are chosen once per actual isolated bad point. -/
theorem exists_actual_full_boundary_curve_endpoint_histories
    {W : Set X} {E : List (Set X)} (hW : IsClosedSubmanifold n W)
    (hE : IsSNCDivisor n E) (hr : ∀x∈W,RegularAtDim (n := n) W x 1) :
    ∃ A : ActualEndpointHistories X (Option {b : X // b∈originalSharpBadLocus (n := n) W E}),
      (∀x : X,∃i,x∈A.openSet i) ∧
      (∀i,(A.prefixTower i).length=0) ∧
      ∀i,
        let U:=A.openSet i
        let WV : Set U:=(Subtype.val : U → X) ⁻¹' W
        let EV:=E.map ((Subtype.val : U → X) ⁻¹' ·)
        let T:=(A.prefixTower i).append (A.tail i)
        CentresOver ((Subtype.val : U → X) ⁻¹' originalSharpBadLocus (n := n) W E) T ∧
        CentresIn WV T ∧ IsGeoTestTower (geometricTemplate (univ : Set U) EV) T ∧
        IsClosedSubmanifold n (strictAlong T WV) ∧
        IsSNCDivisor n (geoTransformAlong (geometricTemplate (univ : Set U) EV) T).E ∧
        HasNormalCrossings n (strictAlong T WV)
          (geoTransformAlong (geometricTemplate (univ : Set U) EV) T).E ∧
        (geoTransformAlong (geometricTemplate (univ : Set U) EV) T).E=
          EV.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate WV []) T).E ∧
        IsProperMap T.proj ∧ IsIsomorphismOver n T.proj
          ((Subtype.val : U → X) ⁻¹' originalGoodLocus (n := n) W E) := by
  classical
  let B:=originalSharpBadLocus (n := n) W E
  have hRecipes:=fun b : B=>exists_actual_point_supported_curve_recipe hW hE hr b.property
  choose U hUb hIsolate Y T hData using hRecipes
  let G : Opens X:=⟨originalGoodLocus (n := n) W E,isOpen_originalGoodLocus hW.1 hE.1⟩
  let base : Option B→Opens X
    | none=>G
    | some b=>U b
  let target : Option B→CMfd.{u} n
    | none=>CMfd.of (n := n) G
    | some b=>Y b
  let tower : ∀i : Option B,BlowupTower (CMfd.of (n := n) (base i)) (target i)
    | none=>.refl
    | some b=>T b
  have hOver : ∀i : Option B,CentresOver ((Subtype.val : base i → X) ⁻¹' B) (tower i):=by
    intro i
    cases i with
    | none=>trivial
    | some b=>
      apply centresOver_mono (X := CMfd.of (n := n) (U b))
        (F := (Subtype.val : U b → X) ⁻¹' {b.val}) (B := (Subtype.val : U b → X) ⁻¹' B)
        ?_ (T b) (hData b).1
      intro y hy
      change y.val∈B
      rw [mem_singleton_iff.mp hy]
      exact b.property
  have hDisjoint : ∀i j : Option B,i≠j → Disjoint (base i⊓base j : Set X) B:=by
    intro i j hij
    cases i with
    | none=>
      apply disjoint_left.mpr
      intro x hx hxB
      have hxGood : x∈originalGoodLocus (n := n) W E:=hx.1
      change x∈originalSharpBadLocus (n := n) W E at hxB
      rw [originalSharpBadLocus_eq_compl_good] at hxB
      exact hxB hxGood
    | some b=>
      cases j with
      | none=>
        apply disjoint_left.mpr
        intro x hx hxB
        have hxGood : x∈originalGoodLocus (n := n) W E:=hx.2
        change x∈originalSharpBadLocus (n := n) W E at hxB
        rw [originalSharpBadLocus_eq_compl_good] at hxB
        exact hxB hxGood
      | some c=>
        apply disjoint_left.mpr
        intro x hx hxB
        have hxb : x=b.val:=mem_singleton_iff.mp
          ((Set.ext_iff.mp (hIsolate b) x).mp ⟨hx.1,hxB⟩)
        have hxc : x=c.val:=mem_singleton_iff.mp
          ((Set.ext_iff.mp (hIsolate c) x).mp ⟨hx.2,hxB⟩)
        exact hij (congrArg Option.some (Subtype.ext (hxb.symm.trans hxc)))
  have hComp : ∀i j : Option B,∃e :
      localEndpoint (base i) (base i⊓base j) .refl (tower i)
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          localEndpoint (base j) (base i⊓base j) .refl (tower j),
      IsTowerIso (commonOpenBase (base i) (base j) (base i⊓base j) inf_le_left inf_le_right)
        (localPaddedHistory (base i) (base i⊓base j) .refl (tower i)
          ((tower i).length+(tower j).length))
        (localPaddedHistory (base j) (base i⊓base j) .refl (tower j)
          ((tower i).length+(tower j).length)) e:=by
    intro i j
    by_cases hij : i=j
    · subst j
      refine ⟨Diffeomorph.refl _ _ _,?_⟩
      rw [commonOpenBase_self]
      exact IsTowerIso.refl_self _
    · have hiEmpty:=local_refl_padded_empty (X := X) (base i) (base i⊓base j) B
        (tower i) ((tower i).length+(tower j).length) (hOver i) (hDisjoint i j hij)
      have hjEmpty:=local_refl_padded_empty (X := X) (base j) (base i⊓base j) B
        (tower j) ((tower i).length+(tower j).length) (hOver j) (hDisjoint i j hij)
      apply exists_empty_tower_comparison _ _ _ hiEmpty hjEmpty
      simp only [localPaddedHistory,paddedHistory,BlowupTower.length_append,length_restrict,
        BlowupTower.length_refl,identityEmptyTail_length]
      omega
  let A : ActualEndpointHistories X (Option B):={
    openSet:=base
    prefixSpace:=fun i=>CMfd.of (n := n) (base i)
    finalSpace:=target
    prefixTower:=fun _=>.refl
    tail:=tower
    cut:=fun i j=>(tower i).length+(tower j).length
    left_bound:=fun _ _=>Nat.le_add_right _ _
    right_bound:=fun _ _=>Nat.le_add_left _ _
    comparison:=fun i j=>Classical.choose (hComp i j)
    stagewise:=fun i j=>Classical.choose_spec (hComp i j)}
  refine ⟨A,?_,fun _=>rfl,?_⟩
  · intro x
    by_cases hx : x∈B
    · exact ⟨some ⟨x,hx⟩,hUb ⟨x,hx⟩⟩
    · refine ⟨none,?_⟩
      change x∈originalGoodLocus (n := n) W E
      by_contra hNot
      exact hx (show x∈originalSharpBadLocus (n := n) W E from by
        rw [originalSharpBadLocus_eq_compl_good];exact hNot)
  · intro i
    cases i with
    | some b=>
      simpa only [A,base,target,tower,BlowupTower.refl_append] using
        And.intro (hOver (some b)) (hData b).2
    | none=>
      let WG : Set G:=(Subtype.val : G → X) ⁻¹' W
      let EG:=E.map ((Subtype.val : G → X) ⁻¹' ·)
      have hWG:=isClosedSubmanifold_preimage_val hW G
      have hEG : IsSNCDivisor n EG:=
        isSNCDivisor_map_preimage (pullsBackCoordinates_val G) continuous_subtype_val hE
      have hNCG : HasNormalCrossings n WG EG:=by
        intro y hy
        apply normalCrossingsAt_preimage_val_iff.mpr
        rcases y.property with hNot | ⟨_hW,hNC⟩
        · exact False.elim (hNot hy)
        · exact hNC
      have hIdIso : IsIsomorphismOver n (id : G → G)
          ((Subtype.val : G → X) ⁻¹' originalGoodLocus (n := n) W E):=by
        refine ⟨⟨fun _ hy=>hy,fun _ _ _ _ heq=>heq,fun y hy=>⟨y,hy,rfl⟩⟩,?_⟩
        rw [exceptionalLocus_id]
        simp
      change CentresOver _ (BlowupTower.refl : BlowupTower (CMfd.of (n := n) G) (CMfd.of (n := n) G)) ∧ _
      exact ⟨trivial,trivial,trivial,hWG,hEG,hNCG,
        actual_whole_ambient_boundary_ordered_dictionary (X := CMfd.of (n := n) G) WG EG .refl,
        isProperMap_id,hIdIso⟩

end
end Hironaka.HironakaActualFullBoundaryCurveEndpointHistories
