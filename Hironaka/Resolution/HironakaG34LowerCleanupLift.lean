import Hironaka.Resolution.HironakaG34LowerCentreStrata
import Hironaka.Resolution.HironakaActualOriginalProcessedSharpCleanupAllDimensions

/-! # The lower phase of a row as ONE lift of a certified lower cleanup (G4K1B, route (L); T-L)

Lane G34 (run 0080, round 5).  Blueprint: `hironaka-g34-resume-lower-cleanup-lift.tex`.
Route note: `work/hironaka-resume-20261111/G34/TL-ROUTE.md`.

The r3/r4 lower phase of row `j` iterated recomputed rounds whose termination (T-L) does not follow from
any held invariant.  Here the lower phase of row `j` is ONE lower cleanup `R` of the lower problem
`(Z, F) = (S_j, F_j)`, i.e. the conclusion of the smaller-dimensional sharp theorem, lifted by the held
`actual_original_selected_lower_boundary_history`; termination of the driver is then the structural
induction on the number of unprepared rows.

* `certified_original_row_step`, `actual_row_prepared_step_of_certificate`: ANY centre `C ⊆ N` that,
  at every point of `C ∩ S_i`, has normal crossings with a protected configuration `Haux :: F_i`
  (`ProtectedWindowAt`) keeps the prepared row `i` prepared (the held
  `processed_original_row_same_maximum_step` with its special centre replaced by this certificate).
* `actual_rows_prepared_of_protected_tail`: the same along a tail (`ProtectedTail`, stagewise certificate).
* `actual_lower_tail_row_order`, `actual_lower_cleanup_row_prepared`: along a lower test tail the row
  `j` keeps order `≤ 1`; at the end of a lower cleanup (normal crossings and density of the lower
  problem) row `j` is prepared.
* `actual_lower_tail_current_sharp`: lower sharp centres are upper sharp centres.
* `actual_row_step_of_certified_lower_cleanup`: one row of the driver.
* `exists_actual_prefix_all_rows_prepared`, `exists_actual_sharp_cleanup_of_certified_lower_cleanups`:
  the fold over the rows and K3, from `CertifiedLowerCleanupsExist` (the residual of T-L: the
  smaller-dimensional sharp cleanup with protection near prepared rows, at every lower entry).
-/

set_option autoImplicit false
open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaG34LowerCleanupLift
noncomputable section

section CopiedOne
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  Hironaka.RegularLocusDense BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealRestrictOpen MarkedIdealBiholomorphism RestrictedIdealExtension
  RelativePrincipalizationSpan GermIdealOrder HironakaG4PreparedCentreCoordinates
  MonomialPartAlong DivisorExponentAlong HironakaSharpOriginalProductTraceOrder
  HironakaG4RecordedTowerResidualCompatibility HironakaG4ResidualInductionInputs
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaG4GeneralSharpBadLocus
  HironakaNormalCrossingsBoundaryTransform HironakaSharpActualCurveWholeBoundaryTransversality
  HironakaOriginalNCMarkedStratumHistoryValue HironakaOriginalNCMarkedStratumNativeFields
  HironakaOriginalNCMarkedStratumCanonicalHistory HironakaOriginalNCMarkedStratumAdmissibleLevels
  HironakaOriginalNCMarkedStratumStepDrop HironakaOriginalOldBranchOpenHistory
  HironakaG4OriginalSelectedLowerBoundaryHistory HironakaG4OriginalSelectedLowerBadHistory
  HironakaG4SharpBadFootprint HironakaActualSharpBadMaximumProcessedSlice
  HironakaActualProtectedOtherRowLocalStep HironakaG4SmoothSubcarrierResidualStep
  HironakaSharpActualChronologicalStrictStep HironakaSharpOriginalFirstBlowupOpenComparison
  HironakaSharpActualRelativeSaturationOpenNaturality
open HironakaG4OriginalSelectedResidualTail HironakaSharpActualFirstAmbientStrictExponent
  HironakaSharpActualTraceIncidence HironakaSharpActualChronologicalResidualDictionary
  HironakaActualCleanupDensityCompactness BlowupFlatCoordinates RegularPatchPushforward
  BlowupRestrictOpen HironakaSharpNormalCrossingsOpenLocus
open InvertibleIdealQuotient IdealWeightPowers BlowupSNCTransform
open HomogenizedGlueingTower HironakaNormalCrossingsSNCBlockCarrier
  HironakaG4CompactWholeMonomialMaskPhase HironakaSharpActualMixedCentreWholeStrictTraceGeometry
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
open NonmonomialTransformAlong RestrictEmptyTower
open ResolutionDriver
open HironakaActualSharpBadFirstMaximumBlowup (nc_slice_same_centre_relative_strict)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-! Private verbatim copies from `HironakaActualSharpBadFirstMaximumBlowup` (private there). -/

private theorem pullback_comp_val_mem_iff (U : Opens X) {I : GermIdeal n X}
    (hI : I.IsCoherent) (x : U) (g : X→ℂ) :
    (GermIdeal.pullback (m:=n) (Subtype.val : U→X) I).mem x (g ∘ Subtype.val) ↔ I.mem x.val g := by
  rw [MarkedIdealRestrictOpen.mem_pullback_val_iff U hI]
  have he : extendOpens U (g ∘ (Subtype.val : U→X)) =ᶠ[𝓝 x.val] g := by
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    exact extendOpens_val U (g ∘ (Subtype.val : U→X)) ⟨y,hy⟩
  exact ⟨fun h=>HomogenizedIdeal.mem_congr hI h he,
    fun h=>HomogenizedIdeal.mem_congr hI h he.symm⟩

private theorem mem_iff_holomorphic_of_one {I : GermIdeal n X} (hI : I.IsCoherent)
    {x : X} (hOne : I.mem x 1) (g : X→ℂ) : I.mem x g ↔ HolomorphicAt n g x := by
  refine ⟨fun h=>GermIdeal.IsCoherent.holomorphicAt_mem hI h,fun hg=>?_⟩
  apply HomogenizedIdeal.mem_of_isInSpanAt hI
  exact isInSpanAt_of_eq_mul hOne hg hg (Eventually.of_forall fun y=>by simp)

-- PRIVATE composition of already constructed actual local outputs. Its caller
-- derives every local field from source NC windows and the SAME actual pi.
private theorem global_from_actual_local
    (hn : 0<n) {S : Set X} {pi : Y→X} {Nnext Snext : Set Y}
    (hSnext : IsClosed Snext) (hProj : Snext⊆pi ⁻¹' S)
    (hNnext : IsClosedSubmanifold n Nnext) (I : GermIdeal n Y)
    (hI : I.IsCoherent) (hnzI : ∀y∈Nnext,IsNonzeroAlongAt Nnext I y)
    (F : List (Set Y))
    (hUnitOff : ∀y : Y,pi y∉S → I.mem y 1)
    (hLocal : ∀y : Y,pi y∈S → ∃V : Opens Y,y∈V ∧
      IsClosedSubmanifold n ((Subtype.val : V→Y) ⁻¹' Snext) ∧
      GermIdeal.pullback (m:=n) (Subtype.val : V→Y) I=
        vanishingIdeal (n:=n) ((Subtype.val : V→Y) ⁻¹' Snext) ∧
      HasNormalCrossings n ((Subtype.val : V→Y) ⁻¹' Snext)
        (F.map ((Subtype.val : V→Y) ⁻¹' ·)) ∧
      ((Subtype.val : V→Y) ⁻¹' Snext)⊆closure
        (((Subtype.val : V→Y) ⁻¹' Snext) \ ⋃D∈F.map ((Subtype.val : V→Y) ⁻¹' ·),D) ∧
      ∀z∈(Subtype.val : V→Y) ⁻¹' Nnext,
        ordinaryTraceOrder (X:=CMfd.of (n:=n) V) ((Subtype.val : V→Y) ⁻¹' Nnext)
          (GermIdeal.pullback (m:=n) (Subtype.val : V→Y) I) z≤1) :
    IsClosedSubmanifold n Snext ∧ I=vanishingIdeal (n:=n) Snext ∧
      HasNormalCrossings n Snext F ∧ Snext⊆closure (Snext \ ⋃D∈F,D) ∧
      ∀y∈Nnext,ordinaryTraceOrder Nnext I y≤1 := by
  have hSmooth : IsClosedSubmanifold n Snext := by
    refine ⟨hSnext,?_⟩
    intro y hy
    obtain ⟨V,hyV,hSm,_hIdeal,_hNC,_hDense,_hOrd⟩:=hLocal y (hProj hy)
    obtain ⟨k,hk⟩:=hSm.2 (⟨y,hyV⟩ : V) hy
    exact ⟨k,AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hk⟩
  have hcS:=(VanishingIdealCoherent.isCoherent_vanishingIdeal hSmooth)
  have hWhole : I=vanishingIdeal (n:=n) Snext := by
    ext y g
    by_cases hyS : pi y∈S
    · obtain ⟨V,hyV,_hSm,hIdeal,_hNC,_hDense,_hOrd⟩:=hLocal y hyS
      rw [←SmoothCentreHomogeneity.pullback_val_vanishingIdeal V Snext] at hIdeal
      have hh:=congrArg (fun K : GermIdeal n V=>K.mem ⟨y,hyV⟩ (g ∘ (Subtype.val : V→Y))) hIdeal
      rw [pullback_comp_val_mem_iff V hI,pullback_comp_val_mem_iff V hcS] at hh
      exact Iff.of_eq hh
    · have hyOff : y∉Snext:=fun h=>hyS (hProj h)
      have hOne : (vanishingIdeal (n:=n) Snext).mem y 1 := by
        refine ⟨holomorphicAt_const 1,?_⟩
        filter_upwards [hSnext.isOpen_compl.mem_nhds hyOff] with z hz hzS
        exact (hz hzS).elim
      exact (mem_iff_holomorphic_of_one hI (hUnitOff y hyS) g).trans
        (mem_iff_holomorphic_of_one hcS hOne g).symm
  have hNC : HasNormalCrossings n Snext F := by
    intro y hy
    obtain ⟨V,hyV,_hSm,_hIdeal,hNC,_hDense,_hOrd⟩:=hLocal y (hProj hy)
    exact HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mp
      (hNC (⟨y,hyV⟩ : V) hy)
  have hDense : Snext⊆closure (Snext \ ⋃D∈F,D) := by
    intro y hy
    obtain ⟨V,hyV,_hSm,_hIdeal,_hNC,hDense,_hOrd⟩:=hLocal y (hProj hy)
    have hUnion : (Subtype.val : V→Y) ⁻¹' (⋃D∈F,D)=
        ⋃D∈F.map ((Subtype.val : V→Y) ⁻¹' ·),D := by ext z;simp
    have hSet : ((Subtype.val : V→Y) ⁻¹' Snext) \ (⋃D∈F.map ((Subtype.val : V→Y) ⁻¹' ·),D)=
        (Subtype.val : V→Y) ⁻¹' (Snext \ ⋃D∈F,D) := by rw [←hUnion];rfl
    have hCl:=hDense (show (⟨y,hyV⟩ : V)∈(Subtype.val : V→Y) ⁻¹' Snext from hy)
    rw [hSet] at hCl
    exact closure_mono (image_preimage_subset (Subtype.val : V→Y) _)
      (image_closure_subset_closure_image continuous_subtype_val ⟨⟨y,hyV⟩,hCl,rfl⟩)
  have hOrd : ∀y∈Nnext,ordinaryTraceOrder Nnext I y≤1 := by
    intro y hyN
    by_cases hyS : pi y∈S
    · obtain ⟨V,hyV,_hSm,_hIdeal,_hNC,_hDense,hOne⟩:=hLocal y hyS
      have hOp:=HironakaSharpActualMixedCurveContactEvolution.actual_ordinary_trace_order_pullback_open
        hn hNnext hI hnzI V (⟨y,hyV⟩ : V)
      rw [←hOp]
      exact hOne _ hyN
    · by_contra hgt
      have hCos:=(ordinaryTraceOrder_cosupport_iff hNnext hI hnzI hyN 1).mpr (by omega)
      exact one_ne_zero ((vanishesToOrderOn_one_iff hyN (holomorphicAt_const 1)).mp
        (hCos.2 1 (hUnitOff y hyS)))
  exact ⟨hSmooth,hWhole,hNC,hDense,hOrd⟩

private theorem next_relative_one {N C : Set X} {I : GermIdeal n X}
    (hI : I.IsCoherent) {pi : Y→X} (hpi : IsBlowupAlong n C pi)
    (y : Y) (hOne : I.mem (pi y) 1) : (nextRelativeStrict N I C pi).mem y 1 := by
  have hcP:=GermIdealPullbackCalculus.isCoherent_pullback hpi.contMDiff hI
  have hP : (GermIdeal.pullback (m:=n) pi I).mem y 1 :=
    GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨(1 : X→ℂ),hOne,rfl⟩ (holomorphicAt_const 1))
  refine ⟨0,holomorphicAt_const 1,?_⟩
  intro a ha
  change HolomorphicAt n a y at ha
  have hProd : (GermIdeal.pullback (m:=n) pi I).mem y (a*1) :=
    (mem_iff_holomorphic_of_one hcP hP (a*1)).mpr (ha.mul (holomorphicAt_const 1))
  exact ⟨hProd.1,IsInSpanAt.restrict (isInSpanAt_self hProd hProd.1)⟩

-- Source windows only. Every future local field is constructed for the SAME
-- actual pi, using genuine restriction and the public NC-slice connector.
private theorem same_step_of_source_windows
    (hn : 0<n) {N S C : Set X} (I : GermIdeal n X)
    (hN : IsClosedSubmanifold n N) (hS : IsClosedSubmanifold n S)
    (hI : I.IsCoherent) (hIS : I=vanishingIdeal (n:=n) S)
    (hnz : ∀x∈N,IsNonzeroAlongAt N I x)
    (hpr : ∀x∈N,∃ f : X→ℂ,HolomorphicAt n f x ∧
      ∀g,I.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n:=n) N (·=f) x g)
    (F : List (Set X)) {pi : Y→X} (hpi : IsBlowupAlong n C pi) (hCN : C⊆N)
    (hWindows : ∀x∈S,∃(U : Opens X),x∈U ∧ ∃Haux : Set U,
      (Subtype.val : U→X) ⁻¹' S=(Subtype.val : U→X) ⁻¹' N∩Haux ∧
      IsSNCDivisor n (Haux::F.map ((Subtype.val : U→X) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U→X) ⁻¹' N) (Haux::F.map ((Subtype.val : U→X) ⁻¹' ·)) ∧
      HasNormalCrossings n ((Subtype.val : U→X) ⁻¹' C) (Haux::F.map ((Subtype.val : U→X) ⁻¹' ·))) :
    let Nnext:=geoStrictTransform pi C N
    let Snext:=geoStrictTransform pi C S
    let Inext:=nextRelativeStrict N I C pi
    let Fnext:=F.map (geoStrictTransform pi C)++[pi ⁻¹' C]
    IsClosedSubmanifold n Snext ∧ Inext=vanishingIdeal (n:=n) Snext ∧
      HasNormalCrossings n Snext Fnext ∧ Snext⊆closure (Snext \ ⋃D∈Fnext,D) ∧
      ∀y∈Nnext,ordinaryTraceOrder Nnext Inext y≤1 := by
  dsimp only
  let Nnext:=geoStrictTransform pi C N
  let Snext:=geoStrictTransform pi C S
  let Inext:=nextRelativeStrict N I C pi
  let Fnext:=F.map (geoStrictTransform pi C)++[pi ⁻¹' C]
  have hNnext : IsClosedSubmanifold n Nnext:=
    BlowupStrictIdeal.isClosedSubmanifold_geoStrictTransform_of_isClosedSubmanifold hpi hN hCN
  have hGeo:=nextRelativeStrict_actual_geometry hn hN hI hnz hpr hpi hCN
  have hcNext : Inext.IsCoherent:=hGeo.2.1
  have hnzNext : ∀y∈Nnext,IsNonzeroAlongAt Nnext Inext y:=hGeo.2.2.1
  apply global_from_actual_local hn (pi:=pi) (S:=S) (Nnext:=Nnext) (Snext:=Snext)
    isClosed_closure (geoStrictTransform_subset_preimage hpi.contMDiff.continuous hS.1)
    hNnext Inext hcNext hnzNext Fnext
  · intro y hy
    apply next_relative_one hI hpi y
    rw [hIS]
    refine ⟨holomorphicAt_const 1,?_⟩
    filter_upwards [hS.1.isOpen_compl.mem_nhds hy] with z hz hzS
    exact (hz hzS).elim
  · intro y hy
    obtain ⟨U,hyU,Haux,hSlice,hEU,hTU,hCU⟩:=hWindows (pi y) hy
    let V:=firstBlowupSourceOpen hpi U
    let rho:=firstBlowupOpenProjection hpi U
    let NU:=(Subtype.val : U→X) ⁻¹' N
    let CU:=(Subtype.val : U→X) ⁻¹' C
    let FU:=F.map ((Subtype.val : U→X) ⁻¹' ·)
    have hrho : IsBlowupAlong n CU rho:=BlowupRestrictOpen.isBlowupAlong_restrict hpi U V.isOpen
    have hNU : IsClosedSubmanifold n NU:=BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN U
    have hCNU : CU⊆NU:=fun _ hx=>hCN hx
    obtain ⟨hSm,hWh,hNC,hDen,hOne⟩:=nc_slice_same_centre_relative_strict (X:=CMfd.of (n:=n) U)
      (Y:=CMfd.of (n:=n) V) (N:=NU) (H:=Haux) (C:=CU) (F:=FU)
      (pi:=rho) hn hNU hEU hTU hCNU hCU hrho
    have hEqN : geoStrictTransform rho CU NU=(Subtype.val : V→Y) ⁻¹' Nnext:=
      MarkedIdealRestrictOpen.geoStrictTransform_restrict U V.isOpen N
    have hEqS : geoStrictTransform rho CU (NU∩Haux)=(Subtype.val : V→Y) ⁻¹' Snext := by
      rw [←hSlice]
      exact MarkedIdealRestrictOpen.geoStrictTransform_restrict U V.isOpen S
    have hFmap : FU.map (geoStrictTransform rho CU)++[rho ⁻¹' CU]=
        Fnext.map ((Subtype.val : V→Y) ⁻¹' ·) := by
      simp only [FU,Fnext,List.map_append,List.map_singleton,List.map_map]
      congr 1
      · apply List.map_congr_left
        intro D _hD
        exact MarkedIdealRestrictOpen.geoStrictTransform_restrict U V.isOpen D
    have hPullI : GermIdeal.pullback (m:=n) (Subtype.val : U→X) I=
        vanishingIdeal (n:=n) (NU∩Haux) := by
      rw [hIS,SmoothCentreHomogeneity.pullback_val_vanishingIdeal U S,hSlice]
    have hPullNext : GermIdeal.pullback (m:=n) (Subtype.val : V→Y) Inext=
        vanishingIdeal (n:=n) ((Subtype.val : V→Y) ⁻¹' Snext) := by
      change GermIdeal.pullback (m:=n) (Subtype.val : V→Y) (nextRelativeStrict N I C pi)=_
      rw [nextRelativeStrict_open hn hN hI hnz hpr hpi hCN U,hPullI,hWh,hEqS]
    rw [hEqS] at hSm
    rw [hEqS,hFmap] at hNC hDen
    refine ⟨V,hyU,hSm,hPullNext,hNC,hDen,?_⟩
    rw [hEqN,hEqS] at hOne
    rw [hPullNext]
    exact hOne


end CopiedOne

section CopiedTwo
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers HomogenizedGlueingTower NormalCrossings MemberInterLocusAlong
  HironakaG4OriginalSelectedLowerBoundaryHistory HironakaG4ResidualInductionInputs
  HironakaG4RecordedTowerResidualCompatibility HironakaG4PreparedCentreCoordinates
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpOriginalProductTraceOrder
  HironakaSharpOriginalMultiBoundaryBadLocus HironakaSharpActualCurveGlobalBoundaryCoordinates
  HironakaSharpActualCurveWholeBoundaryTransversality
  RelativePrincipalizationSpan RestrictedIdealExtension MonomialPartAlong
  MarkedIdeals MarkedIdeals.MarkedIdeal
variable {n : ℕ} {X Y Q : CMfd.{u} n}

/-- Private verbatim copy from `HironakaG4OriginalSelectedLowerBadHistory` (private there). -/
private theorem actual_remaining_boundary_dictionary (W : Set X) (E : List (Set X))
    (i : ℕ) (T : BlowupTower X Y) (S : Set Y) (R : BlowupTower Y Q) :
    let B := geoTransformAlong (geometricTemplate W []) T
    (geoTransformAlong (geometricTemplate S ((E.map (strictAlong T)).eraseIdx i ++ B.E)) R).E=
      (E.map (strictAlong (T.append R))).eraseIdx i ++
        (geoTransformAlong (geometricTemplate W []) (T.append R)).E := by
  let B := geoTransformAlong (geometricTemplate W []) T
  let F := (E.map (strictAlong T)).eraseIdx i ++ B.E
  let K := geometricTemplate (univ : Set Y) []
  have hOld : (E.map (strictAlong T)).map (strictAlong R)=E.map (strictAlong (T.append R)) := by
    rw [List.map_map]
    exact congrArg (fun f : Set X → Set Q => E.map f)
      (funext fun H => (strictAlong_append T H R).symm)
  have hBorn : (geoTransformAlong (geometricTemplate W []) (T.append R)).E=
      B.E.map (strictAlong R) ++ (geoTransformAlong K R).E := by
    rw [geoTransformAlong_append]
    exact boundary_geoTransformAlong_decomposition B K rfl R
  calc
    (geoTransformAlong (geometricTemplate S F) R).E
        = F.map (strictAlong R) ++ (geoTransformAlong K R).E :=
      boundary_geoTransformAlong_decomposition (geometricTemplate S F) K rfl R
    _ = ((E.map (strictAlong T)).eraseIdx i).map (strictAlong R) ++
        (B.E.map (strictAlong R) ++ (geoTransformAlong K R).E) := by
      rw [List.map_append,List.append_assoc]
    _ = (E.map (strictAlong (T.append R))).eraseIdx i ++
        (B.E.map (strictAlong R) ++ (geoTransformAlong K R).E) := by
      rw [←List.eraseIdx_map,hOld]
    _ = _ := by rw [←hBorn]

end CopiedTwo

section Main
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold NormalCrossings
  SimultaneousNormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal GermIdealOrder
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpActualChronologicalDistinctDefect
  HironakaSharpOriginalProductTraceOrder HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaG34PreparedRowEmptyTail RestrictEmptyTower
  HomogenizedGlueingTower HironakaSharpActualChronologicalStrictStep
  HironakaG4RecordedTowerResidualCompatibility DivisorExponentAlong NormalCrossingsComparison
open ResolutionInvariantExt (IsEmptyTower)

variable {n : ℕ} {X Y : CMfd.{u} n}

/-- **The protected-window certificate** of a centre `C` at a point `x` of a support `S ⊆ N` with
boundary `F`: an open window `U ∋ x` and an auxiliary hypersurface `Haux` of `U` with `S ∩ U = N ∩ Haux`,
`Haux :: F` simple normal crossings on `U` and transverse to `N`, and `C ∩ U` with normal crossings
with `Haux :: F` (the hypotheses of `protection_of_nc_centre` on the window). -/
def ProtectedWindowAt (N S : Set Y) (F : List (Set Y)) (C : Set Y) (x : Y) : Prop :=
  ∃ U : Opens Y, x ∈ U ∧ ∃ Haux : Set U,
    (Subtype.val : U → Y) ⁻¹' S = (Subtype.val : U → Y) ⁻¹' N ∩ Haux ∧
    IsSNCDivisor n (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
    IsTransverse n ((Subtype.val : U → Y) ⁻¹' N) (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·)) ∧
    HasNormalCrossings n ((Subtype.val : U → Y) ⁻¹' C) (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·))

/-- **Strata-type protection gives the certificate**: on a protected window, a centre that is near
each of its points a stratum `N ∩ memberInter F Q` of the row's boundary (no `Haux` equation) has the
protected-window certificate (r3 `nc_centre_of_local_strata`). -/
theorem protectedWindowAt_of_window_strata (hn : 0 < n) {N S C : Set Y} {F : List (Set Y)} {x : Y}
    (U : Opens Y) (hxU : x ∈ U) (Haux : Set U)
    (hSlice : (Subtype.val : U → Y) ⁻¹' S = (Subtype.val : U → Y) ⁻¹' N ∩ Haux)
    (hSNC : IsSNCDivisor n (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·)))
    (hTr : IsTransverse n ((Subtype.val : U → Y) ⁻¹' N) (Haux :: F.map ((Subtype.val : U → Y) ⁻¹' ·)))
    (hLocal : ∀ z ∈ (Subtype.val : U → Y) ⁻¹' C,
      ∃ Q : Finset (Fin (F.map ((Subtype.val : U → Y) ⁻¹' ·)).length),
        z ∈ (Subtype.val : U → Y) ⁻¹' N ∩
          BoundaryCount.memberInter (F.map ((Subtype.val : U → Y) ⁻¹' ·)) Q ∧
        ∀ᶠ y in 𝓝 z, y ∈ (Subtype.val : U → Y) ⁻¹' C ↔ y ∈ (Subtype.val : U → Y) ⁻¹' N ∩
          BoundaryCount.memberInter (F.map ((Subtype.val : U → Y) ⁻¹' ·)) Q) :
    ProtectedWindowAt N S F C x :=
  ⟨U, hxU, Haux, hSlice, hSNC, hTr,
    (HironakaG34ProtectionNCCentre.nc_centre_of_local_strata (X := CMfd.of (n := n) U)
      hn hSNC hTr hLocal).2.2⟩

/-- **A certified centre keeps a prepared row prepared** (the held
`processed_original_row_same_maximum_step` with the special sharp-bad maximum replaced by ANY closed
centre `C ⊆ N` carrying the protected-window certificate at every point of `C ∩ S_i`).  Points of `S_i`
off `C` get their window from the held `protected_slice_window` inside `Cᶜ`. -/
theorem certified_original_row_step
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (i : Fin E.length)
    (hOrdi : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal y ≤ 1)
    (hNCi : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      HasNormalCrossings n Si
        ((E.map (strictAlong T)).eraseIdx i.val ++ A.E))
    (hDensei : let A := geoTransformAlong (geometricTemplate W []) T
      let Si := A.N ∩ (chronologicalMarked
        (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus
      Si ⊆ closure (Si \ ⋃ H ∈
        (E.map (strictAlong T)).eraseIdx i.val ++ A.E, H))
    (C : Set Y) (hCN : C ⊆ (geoTransformAlong (geometricTemplate W []) T).N)
    (hCert : ∀ x ∈ C ∩ ((geoTransformAlong (geometricTemplate W []) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus),
      ProtectedWindowAt (geoTransformAlong (geometricTemplate W []) T).N
        ((geoTransformAlong (geometricTemplate W []) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
        ((E.map (strictAlong T)).eraseIdx i.val ++ (geoTransformAlong (geometricTemplate W []) T).E)
        C x) :
    let A := geoTransformAlong (geometricTemplate W []) T
    let J := fun a : Fin E.length =>
      (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
    let Si := A.N ∩ (J i).zeroLocus
    ∀ {Q : CMfd.{u} n} (pi : Q→Y) (hpi : IsBlowupAlong n C pi),
      let Tnext : BlowupTower X Q:=.step T C pi hpi
      let Anext:=geoTransformAlong (geometricTemplate W []) Tnext
      let JiNext:=(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) Tnext).ideal
      let SiNext:=geoStrictTransform pi C Si
      let FiNext:=(E.map (strictAlong Tnext)).eraseIdx i.val++Anext.E
      IsClosedSubmanifold n SiNext ∧ JiNext=vanishingIdeal (n:=n) SiNext ∧
        Anext.N∩JiNext.zeroLocus=SiNext ∧ HasNormalCrossings n SiNext FiNext ∧
        SiNext⊆closure (SiNext \ ⋃D∈FiNext,D) ∧
        ∀z∈Anext.N,ordinaryTraceOrder Anext.N JiNext z≤1 := by
  dsimp only
  let A:=geoTransformAlong (geometricTemplate W []) T
  let old:=E.map (strictAlong T)
  let J:=fun a : Fin E.length=>
    (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal
  let Si:=A.N∩(J i).zeroLocus
  let Fi:=old.eraseIdx i.val++A.E
  intro Q pi hpi
  let Tnext : BlowupTower X Q:=.step T C pi hpi
  let Anext:=geoTransformAlong (geometricTemplate W []) Tnext
  have hRec:=actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hGi:=original_members_actual_finite_chronological_geometry hn hW hE hdense i T hT
  have hNi : (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N=A.N:=hGi.1
  have hOrdA : ∀ y ∈ A.N, ordinaryTraceOrder A.N (J i) y ≤ 1 := by
    simpa only [hNi] using hOrdi
  have hProtect:=HironakaG4ProtectedResidualEndpoint.actual_original_selected_endpoint_protection
    hn hW hE hdense i T hT hFull hOrdA hNCi hDensei
  have hSi : IsClosedSubmanifold n Si:=hProtect.1
  have hIS : J i=vanishingIdeal (n:=n) Si:=hProtect.2.1
  have hcI : (J i).IsCoherent:=hGi.2.2.2.1.isCoherent
  have hnz : ∀x∈A.N,IsNonzeroAlongAt A.N (J i) x:=by
    simpa only [hNi] using hGi.2.2.2.2.1
  have hpr : ∀x∈A.N,∃f : Y→ℂ,HolomorphicAt n f x ∧
      ∀g,(J i).mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n:=n) A.N (·=f) x g:=by
    simpa only [hNi] using hGi.2.2.2.2.2
  have hWindows : ∀x∈Si,∃(U : Opens Y),x∈U ∧ ∃Haux : Set U,
      (Subtype.val : U→Y) ⁻¹' Si=(Subtype.val : U→Y) ⁻¹' A.N∩Haux ∧
      IsSNCDivisor n (Haux::Fi.map ((Subtype.val : U→Y) ⁻¹' ·)) ∧
      IsTransverse n ((Subtype.val : U→Y) ⁻¹' A.N) (Haux::Fi.map ((Subtype.val : U→Y) ⁻¹' ·)) ∧
      HasNormalCrossings n ((Subtype.val : U→Y) ⁻¹' C) (Haux::Fi.map ((Subtype.val : U→Y) ⁻¹' ·)) := by
    intro x hx
    by_cases hxC : x∈C
    · exact hCert x ⟨hxC,hx⟩
    · have hx' : x∈(chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N∩(J i).zeroLocus:=by
        simpa only [hNi] using hx
      obtain ⟨U,hxU,hU,Haux,hEU,hTU,hSlice,_hI,_hOther⟩:=
        HironakaActualProtectedOtherRowLocalStep.protected_slice_window
        hn hW hE hdense i T hT hFull hOrdi hNCi hDensei hx'
        ⟨Cᶜ,hpi.1.1.isOpen_compl⟩ hxC
      refine ⟨U,hxU,Haux,hSlice,hEU,hTU,?_⟩
      have hEmpty : (Subtype.val : U→Y) ⁻¹' C=∅:=by
        apply eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hU z.property hz
      rw [hEmpty]
      intro z hz
      exact hz.elim
  obtain ⟨hSm,hWhole,hNC,hDen,hOne⟩:=same_step_of_source_windows
    (X:=Y) (Y:=Q) hn (J i) hRec.1 hSi hcI hIS hnz hpr Fi hpi hCN hWindows
  have hIdealNext : (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) Tnext).ideal=
      nextRelativeStrict A.N (J i) C pi := by
    change nextRelativeStrict (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N
      (J i) C pi=_
    rw [hNi]
  have hNnext : Anext.N=geoStrictTransform pi C A.N:=rfl
  have hFnext : (E.map (strictAlong Tnext)).eraseIdx i.val++Anext.E=
      Fi.map (geoStrictTransform pi C)++[pi ⁻¹' C] := by
    simp only [Fi,old,List.map_append,List.eraseIdx_map,List.map_map,List.append_assoc]
    rfl
  have hSub : geoStrictTransform pi C Si⊆Anext.N := by
    rw [hNnext]
    exact geoStrictTransform_mono pi C (inter_subset_left : Si⊆A.N)
  refine ⟨hSm,hIdealNext.trans hWhole,?_,?_,?_,?_⟩
  · rw [hIdealNext,hWhole,BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hSm.1]
    exact inter_eq_right.mpr hSub
  · rw [hFnext]
    exact hNC
  · rw [hFnext]
    exact hDen
  · rw [hNnext,hIdealNext]
    exact hOne

/-- **A certified centre keeps a prepared row prepared** (`ActualRowPrepared` form), and the new
support is the strict transform of the old one. -/
theorem actual_row_prepared_step_of_certificate
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (i : Fin E.length)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hPrep : ActualRowPrepared W E i T)
    (C : Set Y) (hCN : C ⊆ (geoTransformAlong (geometricTemplate W []) T).N)
    {Q : CMfd.{u} n} (pi : Q → Y) (hpi : IsBlowupAlong n C pi)
    (hCert : ∀ x ∈ C ∩ ((geoTransformAlong (geometricTemplate W []) T).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus),
      ProtectedWindowAt (geoTransformAlong (geometricTemplate W []) T).N
        ((geoTransformAlong (geometricTemplate W []) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus)
        ((E.map (strictAlong T)).eraseIdx i.val ++ (geoTransformAlong (geometricTemplate W []) T).E)
        C x) :
    ActualRowPrepared W E i (.step T C pi hpi) ∧
      (geoTransformAlong (geometricTemplate W []) (.step T C pi hpi)).N ∩
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (.step T C pi hpi)).ideal.zeroLocus =
        geoStrictTransform pi C ((geoTransformAlong (geometricTemplate W []) T).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal.zeroLocus) := by
  obtain ⟨hOrdi, hNCi, hDensei⟩ := hPrep
  obtain ⟨-, -, hS, hNC, hD, hO⟩ := certified_original_row_step hn hW hE hdense T hT hFull i hOrdi
    hNCi hDensei C hCN hCert pi hpi
  have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i))
    (.step T C pi hpi)).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (.step T C pi hpi)).N =
    (geoTransformAlong (geometricTemplate W []) (.step T C pi hpi)).N at hNi
  refine ⟨⟨?_, ?_, ?_⟩, hS⟩
  · rw [hNi]
    exact hO
  · dsimp only
    rw [hS]
    exact hNC
  · dsimp only
    rw [hS]
    exact hD

/-- **A protected tail** after `T` for the rows `P`: at every stage `T·R'` of `R`, the next centre
carries the protected-window certificate at every point of every prepared support `S_i`, `i ∈ P`
(read at that stage). -/
def ProtectedTail (W : Set X) (E : List (Set X)) (P : Finset (Fin E.length))
    (T : BlowupTower X Y) : {Q : CMfd.{u} n} → BlowupTower Y Q → Prop
  | _, .refl => True
  | _, .step R C _ _ => ProtectedTail W E P T R ∧
      ∀ i ∈ P, ∀ x ∈ C ∩ ((geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal.zeroLocus),
        ProtectedWindowAt (geoTransformAlong (geometricTemplate W []) (T.append R)).N
          ((geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
            (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) (T.append R)).ideal.zeroLocus)
          ((E.map (strictAlong (T.append R))).eraseIdx i.val ++
            (geoTransformAlong (geometricTemplate W []) (T.append R)).E) C x

/-- **Every prepared row stays prepared along a protected tail** (both geometric tests at the end). -/
theorem actual_rows_prepared_of_protected_tail
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (P : Finset (Fin E.length))
    (T : BlowupTower X Y) (hP : ∀ i ∈ P, ActualRowPrepared W E i T) :
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q),
      IsGeoTestTower (geometricTemplate W []) (T.append R) →
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R) →
      ProtectedTail W E P T R → ∀ i ∈ P, ActualRowPrepared W E i (T.append R)
  | _, .refl, _, _, _ => hP
  | _, .step R C π hπ, hTR, hFR, hProt => by
      have hTR' : IsGeoTestTower (geometricTemplate W []) (.step (T.append R) C π hπ) := hTR
      have hFR' : IsGeoTestTower (geometricTemplate (univ : Set X) E)
        (.step (T.append R) C π hπ) := hFR
      obtain ⟨hT0, hAdm⟩ := (isGeoTestTower_step_iff _ (T.append R) C π hπ).mp hTR'
      obtain ⟨hF0, -⟩ := (isGeoTestTower_step_iff _ (T.append R) C π hπ).mp hFR'
      have ih := actual_rows_prepared_of_protected_tail hn hW hE hdense P T hP R hT0 hF0 hProt.1
      intro i hi
      exact (actual_row_prepared_step_of_certificate hn hW hE hdense i (T.append R) hT0 hF0 (ih i hi)
        C (fun x hx => hAdm.subset_N hx) π hπ (hProt.2 i hi)).1

/-- **Along a lower test tail the selected row keeps order `≤ 1`.**  The selected residual is the
vanishing ideal of the strict lower carrier (held lift engine), so it has order exactly `1` along every
lower centre, and the equimultiple bound applies at every step. -/
theorem actual_lower_tail_row_order
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (j : Fin E.length)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T
    let B := geoTransformAlong (geometricTemplate W []) T
    let F := (E.map (strictAlong T)).eraseIdx j.val ++ B.E
    let Z := A.N ∩ A.ideal.zeroLocus
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q), IsGeoTestTower (geometricTemplate Z F) R →
      ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).N,
        ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).N
          (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).ideal y ≤ 1 := by
  intro A B F Z
  obtain ⟨_hZ, _hWhole, hTails⟩ :=
    HironakaG4OriginalSelectedLowerBoundaryHistory.actual_original_selected_lower_boundary_history
      hn hW hE hdense j T hT hFull hOrdj
  intro Q R
  induction R with
  | refl => intro _; exact hOrdj
  | @step Q₀ Q₁ R C π hπ ih =>
    intro hR
    obtain ⟨hR0, hAdm⟩ := (isGeoTestTower_step_iff _ R C π hπ).mp hR
    have hOrdR := ih hR0
    obtain ⟨hTR, _hFullR, _hNR, hZR, hSub, hChronN, hChronI⟩ := hTails R hR0
    let A' := chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)
    have hG := original_members_actual_finite_chronological_geometry hn hW hE hdense j (T.append R) hTR
    have hN' : IsClosedSubmanifold n A'.N := hG.2.2.2.1.isClosedSubmanifold_N
    have hI' : A'.ideal.IsCoherent := hG.2.2.2.1.isCoherent
    have hnz' : ∀ x ∈ A'.N, IsNonzeroAlongAt A'.N A'.ideal x := hG.2.2.2.2.1
    have hpr' : ∀ x ∈ A'.N, ∃ f : Q₀ → ℂ, HolomorphicAt n f x ∧
        ∀ g, A'.ideal.mem x g ↔ HolomorphicAt n g x ∧ IsInSpanOnAt (n := n) A'.N (·=f) x g :=
      hG.2.2.2.2.2
    have hCZ : C ⊆ strictAlong R Z := by
      intro x hx
      have h := hAdm.subset_N hx
      rwa [N_geoTransformAlong] at h
    have hCN : C ⊆ A'.N := by
      intro x hx
      change x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).N
      rw [hChronN]
      exact hSub (hCZ hx)
    have hOne : ∀ x ∈ C, ordinaryTraceOrder A'.N A'.ideal x = 1 := by
      intro x hx
      refine le_antisymm (hOrdR x (hCN hx)) ?_
      have hZero : x ∈ A'.ideal.zeroLocus := by
        change x ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).ideal.zeroLocus
        rw [hChronI, BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hZR.1]
        exact hCZ hx
      have hCos : x ∈ cosupport n A'.N A'.ideal 1 := by
        rw [cosupport_one (fun y g hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hI' hg)]
        exact ⟨hCN hx, hZero⟩
      exact (ordinaryTraceOrder_cosupport_iff hN' hI' hnz' (hCN hx) 1).mp hCos
    have hloc : ∀ x ∈ C, ∀ᶠ x' in 𝓝 x, x' ∈ C →
        ordinaryTraceOrder A'.N A'.ideal x' = ordinaryTraceOrder A'.N A'.ideal x :=
      fun x hx => Eventually.of_forall fun x' hx' => by rw [hOne x' hx', hOne x hx]
    change ∀ z ∈ (HironakaSharpActualChronologicalStrictStep.nextTotalMarked A'.N A'.ideal C π).N,
      ordinaryTraceOrder (HironakaSharpActualChronologicalStrictStep.nextTotalMarked A'.N A'.ideal C π).N
        (nextRelativeStrict A'.N A'.ideal C π) z ≤ 1
    intro z hz
    have hle := HironakaG4EquimultipleRelativeOrder.nextRelativeStrict_order_le_of_locally_constant_on_centre
      hn hN' hI' hnz' hpr' hπ hCN hloc hz
    have hzN : π z ∈ A'.N :=
      geoStrictTransform_subset_preimage (C := C) hπ.contMDiff.continuous hN'.1 hz
    exact hle.trans (hOrdR (π z) hzN)

/-- **The end of a lower cleanup prepares the selected row.**  If `R` is a lower test tail of the
lower problem `(Z, F) = (S_j, F_j)` at the end of which the lower carrier has normal crossings with
the lower boundary and is dense off it, then row `j` is prepared at `T·R`; its support is the strict
lower carrier. -/
theorem actual_lower_cleanup_row_prepared
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (j : Fin E.length)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T
    let B := geoTransformAlong (geometricTemplate W []) T
    let F := (E.map (strictAlong T)).eraseIdx j.val ++ B.E
    let Z := A.N ∩ A.ideal.zeroLocus
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q), IsGeoTestTower (geometricTemplate Z F) R →
      HasNormalCrossings n (geoTransformAlong (geometricTemplate Z F) R).N
        (geoTransformAlong (geometricTemplate Z F) R).E →
      (geoTransformAlong (geometricTemplate Z F) R).N ⊆
        closure ((geoTransformAlong (geometricTemplate Z F) R).N \
          ⋃ D ∈ (geoTransformAlong (geometricTemplate Z F) R).E, D) →
      ActualRowPrepared W E j (T.append R) ∧
        (geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
          (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).ideal.zeroLocus =
          strictAlong R Z := by
  intro A B F Z Q R hR hNC hDen
  obtain ⟨_hZ, _hWhole, hTails⟩ :=
    HironakaG4OriginalSelectedLowerBoundaryHistory.actual_original_selected_lower_boundary_history
      hn hW hE hdense j T hT hFull hOrdj
  obtain ⟨_hTR, _hFullR, _hNR, hZR, hSub, hChronN, hChronI⟩ := hTails R hR
  have hOrdR := actual_lower_tail_row_order hn hW hE hdense j T hT hFull hOrdj R hR
  have hGeoN : (geoTransformAlong (geometricTemplate W []) (T.append R)).N = strictAlong R A.N :=
    (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j))
      (T.append R)).1.symm.trans hChronN
  have hSupp : (geoTransformAlong (geometricTemplate W []) (T.append R)).N ∩
      (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append R)).ideal.zeroLocus =
      strictAlong R Z := by
    rw [hGeoN, hChronI, BlowupExceptionalDivisor.zeroLocus_vanishingIdeal hZR.1]
    exact inter_eq_right.mpr hSub
  have hLowN : (geoTransformAlong (geometricTemplate Z F) R).N = strictAlong R Z :=
    N_geoTransformAlong (geometricTemplate Z F) R
  have hLowE : (geoTransformAlong (geometricTemplate Z F) R).E =
      (E.map (strictAlong (T.append R))).eraseIdx j.val ++
        (geoTransformAlong (geometricTemplate W []) (T.append R)).E :=
    actual_remaining_boundary_dictionary W E j.val T Z R
  refine ⟨⟨hOrdR, ?_, ?_⟩, hSupp⟩
  · dsimp only
    rw [hSupp, ← hLowN, ← hLowE]
    exact hNC
  · dsimp only
    rw [hSupp, ← hLowN, ← hLowE]
    exact hDen

/-- **Lower sharp centres are upper sharp centres** along a lower test tail (the held
`actual_original_selected_lower_current_bad_subset` at every stage). -/
theorem actual_lower_tail_current_sharp
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (j : Fin E.length)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1) :
    let A := chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T
    let B := geoTransformAlong (geometricTemplate W []) T
    let F := (E.map (strictAlong T)).eraseIdx j.val ++ B.E
    let Z := A.N ∩ A.ideal.zeroLocus
    ∀ {Q : CMfd.{u} n} (R : BlowupTower Y Q), IsGeoTestTower (geometricTemplate Z F) R →
      CurrentSharpCentres Z F R → CurrentSharpCentres W E (T.append R) := by
  intro A B F Z Q R
  induction R with
  | refl => intro _ _; exact hSharp
  | @step Q₀ Q₁ R C π hπ ih =>
    intro hR hLS
    obtain ⟨hR0, _hAdm⟩ := (isGeoTestTower_step_iff _ R C π hπ).mp hR
    obtain ⟨hLS0, hC⟩ := hLS
    refine ⟨ih hR0 hLS0, ?_⟩
    have hBad := HironakaG4OriginalSelectedLowerBadHistory.actual_original_selected_lower_current_bad_subset
      hn hW hE hdense j T hT hFull hOrdj R hR0
    have hLowN : (geoTransformAlong (geometricTemplate Z F) R).N = strictAlong R Z :=
      N_geoTransformAlong (geometricTemplate Z F) R
    have hLowE : (geoTransformAlong (geometricTemplate Z F) R).E =
        (geoTransformAlong (geometricTemplate (univ : Set Y) F) R).E := by
      rw [HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
          (geometricTemplate Z F) (geometricTemplate (univ : Set Y) []) rfl R,
        HironakaSharpActualCurveGlobalBoundaryCoordinates.boundary_geoTransformAlong_decomposition
          (geometricTemplate (univ : Set Y) F) (geometricTemplate (univ : Set Y) []) rfl R]
      rfl
    have hUpN : (geoTransformAlong (geometricTemplate W []) (T.append R)).N =
        strictAlong (T.append R) W := N_geoTransformAlong (geometricTemplate W []) (T.append R)
    intro x hx
    have hx' := hC hx
    rw [← hLowN, ← hLowE] at hx'
    have hy := hBad hx'
    rw [hUpN] at hy
    exact hy

/-- **A certified lower cleanup of row `j` at the prefix `T`** (route (L) of T-L): a tail `R` of the
lower problem `(Z, F) = (S_j, F_j)` which is a lower test tail, has lower sharp centres
(`CurrentSharpCentres Z F`), ends with the lower carrier normal-crossing with and dense off the lower
boundary (the conclusions of the smaller-dimensional sharp theorem for `(Z, F)`), and is a protected
tail for the prepared rows `P`. -/
def CertifiedLowerCleanup (W : Set X) (E : List (Set X)) (P : Finset (Fin E.length))
    (j : Fin E.length) (T : BlowupTower X Y) {Q : CMfd.{u} n} (R : BlowupTower Y Q) : Prop :=
  let A := chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T
  let B := geoTransformAlong (geometricTemplate W []) T
  let F := (E.map (strictAlong T)).eraseIdx j.val ++ B.E
  let Z := A.N ∩ A.ideal.zeroLocus
  let L := geoTransformAlong (geometricTemplate Z F) R
  IsGeoTestTower (geometricTemplate Z F) R ∧ CurrentSharpCentres Z F R ∧
    HasNormalCrossings n L.N L.E ∧ L.N ⊆ closure (L.N \ ⋃ D ∈ L.E, D) ∧
    ProtectedTail W E P T R

/-- **One row of the sharp driver, route (L).**  From an actual prefix with current sharp centres,
prepared rows `P` and row `j` of order `≤ 1`, a certified lower cleanup `R` of row `j` gives again an
actual prefix `T·R` with current sharp centres at which every row of `insert j P` is prepared. -/
theorem actual_row_step_of_certified_lower_cleanup
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (P : Finset (Fin E.length)) (hP : ∀ i ∈ P, ActualRowPrepared W E i T)
    (j : Fin E.length)
    (hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) T).ideal y ≤ 1)
    {Q : CMfd.{u} n} (R : BlowupTower Y Q) (hR : CertifiedLowerCleanup W E P j T R) :
    IsGeoTestTower (geometricTemplate W []) (T.append R) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append R) ∧
      CurrentSharpCentres W E (T.append R) ∧
      ∀ i ∈ insert j P, ActualRowPrepared W E i (T.append R) := by
  obtain ⟨hLT, hLS, hNC, hDen, hProt⟩ := hR
  obtain ⟨_hZ, _hWhole, hTails⟩ :=
    HironakaG4OriginalSelectedLowerBoundaryHistory.actual_original_selected_lower_boundary_history
      hn hW hE hdense j T hT hFull hOrdj
  obtain ⟨hTR, hFullR, -⟩ := hTails R hLT
  have hSharpR := actual_lower_tail_current_sharp hn hW hE hdense j T hT hFull hSharp hOrdj R hLT hLS
  have hPR := actual_rows_prepared_of_protected_tail hn hW hE hdense P T hP R hTR hFullR hProt
  have hjR := (actual_lower_cleanup_row_prepared hn hW hE hdense j T hT hFull hOrdj R hLT hNC hDen).1
  refine ⟨hTR, hFullR, hSharpR, ?_⟩
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hiP
  · exact hjR
  · exact hPR i hiP

/-- **The residual of T-L under route (L)**, a named statement (NOT assumed anywhere as an axiom): at
every lower entry of the sharp driver for `(W, E)` (actual prefix with current sharp centres, every row
of order `≤ 1`, carrier pure of dimension `d + 1`, empty true distinct defect), for every set `P` of
prepared rows and every `j ∉ P`, the lower problem of row `j` admits a certified lower cleanup.  This is
the smaller-dimensional sharp theorem for `(S_j, F_j)` together with protection (normal crossings of
its centres with the protected configuration) near the prepared supports. -/
def CertifiedLowerCleanupsExist (W : Set X) (E : List (Set X)) (d : ℕ) : Prop :=
  ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
    IsGeoTestTower (geometricTemplate W []) T →
    IsGeoTestTower (geometricTemplate (univ : Set X) E) T →
    CurrentSharpCentres W E T →
    (∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N, ∀ a : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get a)) T).ideal x ≤ 1) →
    (∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N,
      RegularAtDim (n := n) (geoTransformAlong (geometricTemplate W []) T).N x (d+1)) →
    chronologicalDistinctDefect W E T = ∅ →
    ∀ (P : Finset (Fin E.length)), (∀ i ∈ P, ActualRowPrepared W E i T) →
    ∀ j : Fin E.length, j ∉ P →
    ∃ (Q : CMfd.{u} n) (R : BlowupTower Y Q), CertifiedLowerCleanup W E P j T R

/-- **One full row of the driver: carrier phase, then one certified lower cleanup.** -/
theorem exists_actual_row_step
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hIH : CertifiedLowerCleanupsExist W E d)
    (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T)
    (P : Finset (Fin E.length)) (hP : ∀ i ∈ P, ActualRowPrepared W E i T)
    (j : Fin E.length) (hj : j ∉ P) :
    ∃ (Q : CMfd.{u} n) (T' : BlowupTower X Q),
      IsGeoTestTower (geometricTemplate W []) T' ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T' ∧
      CurrentSharpCentres W E T' ∧
      ∀ i ∈ insert j P, ActualRowPrepared W E i T' := by
  obtain ⟨Z, Q, hTQ, hFullTQ, hSharpTQ, _hOver, hEmpty, hRows, hProt⟩ :=
    HironakaG34DefectEmptyOrder.exists_actual_carrier_phase_protected hn hW hE hdense d hRegW hK
      T hT hFull hSharp
  have hPQ : ∀ i ∈ P, ActualRowPrepared W E i (T.append Q) := by
    intro i hi
    obtain ⟨U, hSU, hEmptyU⟩ := hProt i (hP i hi).1 (hP i hi).2.1 (hP i hi).2.2
    exact (actual_prepared_row_empty_tail hn hW hE hdense i T hT hFull (hP i hi) U hSU Q hTQ
      hEmptyU).1
  have hRegQ := HironakaG34CarrierPureDimension.actual_carrier_regularAtDim hW d hRegW
    (T.append Q) hTQ
  obtain ⟨Q', R, hR⟩ := hIH (T.append Q) hTQ hFullTQ hSharpTQ hRows hRegQ hEmpty P hPQ j hj
  have hNj := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get j))
    (T.append Q)).1
  change (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).N =
    (geoTransformAlong (geometricTemplate W []) (T.append Q)).N at hNj
  have hOrdj : ∀ y ∈ (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).N,
      ordinaryTraceOrder (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get j)) (T.append Q)).ideal y ≤ 1 := by
    rw [hNj]
    exact fun y hy => hRows y hy j
  exact ⟨Q', (T.append Q).append R, actual_row_step_of_certified_lower_cleanup hn hW hE hdense
    (T.append Q) hTQ hFullTQ hSharpTQ P hPQ j hOrdj R hR⟩

/-- **The fold over the rows terminates**: from `CertifiedLowerCleanupsExist`, there is an actual
prefix with current sharp centres at which EVERY row is prepared (induction on the set of prepared
rows; one carrier phase and one certified lower cleanup per row). -/
theorem exists_actual_prefix_all_rows_prepared
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hIH : CertifiedLowerCleanupsExist W E d) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      ∀ i : Fin E.length, ActualRowPrepared W E i T := by
  have key : ∀ P : Finset (Fin E.length), ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      ∀ i ∈ P, ActualRowPrepared W E i T := by
    intro P
    induction P using Finset.induction_on with
    | empty =>
      exact ⟨X, .refl, trivial, trivial, trivial, fun i hi => absurd hi (Finset.notMem_empty i)⟩
    | insert j P hj ih =>
      obtain ⟨Y, T, hT, hFull, hSharp, hP⟩ := ih
      exact exists_actual_row_step hn hW hE hdense d hRegW hK hIH T hT hFull hSharp P hP j hj
  obtain ⟨Y, T, hT, hFull, hSharp, hP⟩ := key Finset.univ
  exact ⟨Y, T, hT, hFull, hSharp, fun i => hP i (Finset.mem_univ i)⟩

/-- **The sharp cleanup of `(W, E)` from certified lower cleanups** (route (L) of the G4K1B control
flow, terminating): the fold over the rows followed by K3 (`call633`, already Gamma). -/
theorem exists_actual_sharp_cleanup_of_certified_lower_cleanups
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (d : ℕ)
    (hRegW : ∀ x ∈ W, RegularAtDim (n := n) W x (d+1))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (hIH : CertifiedLowerCleanupsExist W E d) :
    ∃ (Y : CMfd.{u} n) (U : BlowupTower X Y),
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  obtain ⟨Y, T, hT, hFull, hSharp, hAll⟩ :=
    exists_actual_prefix_all_rows_prepared hn hW hE hdense d hRegW hK hIH
  have hOrd : ∀ x ∈ (geoTransformAlong (geometricTemplate W []) T).N, ∀ i : Fin E.length,
      ordinaryTraceOrder (geoTransformAlong (geometricTemplate W []) T).N
        (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).ideal x ≤ 1 := by
    intro x hx i
    have hNi := (chronologicalMarked_geometric_fields (originalRelativeMemberMarked W (E.get i)) T).1
    change (chronologicalMarked (originalRelativeMemberMarked W (E.get i)) T).N =
      (geoTransformAlong (geometricTemplate W []) T).N at hNi
    have h := (hAll i).1
    rw [hNi] at h
    exact h x hx
  obtain ⟨Z, R, hTR, hFullR, hSharpR, hOverR, -, hN, hF, hNC, hProper, hIso, -⟩ :=
    HironakaActualOriginalProcessedSharpCleanupAllDimensions.exists_actual_original_processed_sharp_cleanup_all_dimensions
      hW hE hdense T hT hFull hSharp hK hOrd (fun i => (hAll i).2.1) (fun i => (hAll i).2.2)
  exact ⟨Z, T.append R, hTR, hFullR, hSharpR, hOverR, hN, hF, hNC, hProper, hIso⟩

end Main

end
end Hironaka.HironakaG34LowerCleanupLift
