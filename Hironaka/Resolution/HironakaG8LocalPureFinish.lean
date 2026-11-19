import Hironaka.Resolution.HironakaG8PureSingularHistory
import Hironaka.Resolution.HironakaSaturatedMarkedPhase
import Hironaka.Resolution.HironakaG8UniverseDenseBoundary
import Hironaka.Resolution.HironakaG8CompactSharpFinish
import Hironaka.Resolution.HironakaG3CentresOverGenericFactor
import Hironaka.Resolution.HironakaG8DenseBoundaryReadback

/-! Finite full-boundary completion around a compact task for an actual
singular-centred history whose strict carrier is smooth and pure. -/

set_option autoImplicit false
open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8LocalPureFinish

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaAdmissibleSequence HironakaAdmissibleCalculus
  HironakaEmbeddedBoundary NormalCrossings NormalCrossingsInvariance MaxLocusLocal
  HironakaG8UniverseBMTransport HironakaG8UniverseDenseBoundary HironakaG8DenseBoundaryRestart
  HironakaActualSmoothBoundaryCleanup HironakaSaturatedTowerAppend HironakaSaturatedMarkedPhase
  HironakaG8PureSingularHistory HironakaG8CompactSharpFinish HironakaG8FiniteSingularTowerMerge
  HironakaG8IntrinsicSingularBlockSchedule HironakaG3CentresOverGenericFactor
  HironakaHypersurfaceMultiplicityDescent HironakaCoherentTransformExtension
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaBaseChange

theorem dense_complement_restrict {X : Type} [TopologicalSpace X]
    (W : Set X) (E : List (Set X)) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H)) (O : Opens X) :
    (Subtype.val : O → X) ⁻¹' W ⊆ closure
      ((Subtype.val : O → X) ⁻¹' W \ ⋃ H ∈ E.map ((Subtype.val : O → X) ⁻¹' ·), H) := by
  rw [← preimage_biUnion_list, ← preimage_sdiff]
  intro x hx
  exact (Set.ext_iff.mp (O.isOpen.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
    (continuous_subtype_val : Continuous (Subtype.val : O → X)) (W \ ⋃ H ∈ E, H)) x).mp (hDense hx)

/-- The final dense, transverse and proper geometry follows from the actual
admissible prefix conditions and final simultaneous normal crossings. -/
theorem dense_boundary_resolution_of_final_normalCrossings {n : ℕ} {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y) (hStages : BMStages W E T)
    (hAdm : IsAdmissibleBlowupSequence n X E (singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H))
      Y T.proj (geoTransformAlong (actualSmoothBoundaryMarked W E) T).E)
    (hSmooth : IsClosedSubmanifold n (strictTransform n T.proj W))
    (hSNC : IsSNCDivisor n (geoTransformAlong (actualSmoothBoundaryMarked W E) T).E)
    (hNC : HasNormalCrossings n (strictTransform n T.proj W)
      (geoTransformAlong (actualSmoothBoundaryMarked W E) T).E) :
    DenseBoundaryResolution W E T := by
  let D := singularSet (n := n) W
  let F := D ∪ (W ∩ ⋃ H ∈ E, H)
  have hProper := HironakaLocalPrincipalization.isProperMap_proj T
  have hSurj := HironakaLocalPrincipalization.IsBlowupSequence.surjective T.isBlowupSequence
  have hIso : IsIsomorphismOver n T.proj Fᶜ := IsAdmissibleBlowupSequence.isIsomorphismOver_compl hAdm
  obtain ⟨hDensity, hTrans, hImage⟩ :=
    HironakaG8DenseBoundaryReadback.terminal_dense_transverse_image hW E hE hDense T hAdm hNC
  refine ⟨hAdm, hStages, hSmooth, hSNC, hNC, hTrans, hDensity, T.contMDiff_proj,
    hProper, hSurj, hImage, hIso, ?_⟩
  intro hNil
  have hFD : F = D := by simp [F, hNil]
  rw [hFD] at hIso
  exact HironakaG8SurfaceLimitEndpoint.exceptionalLocus_eq_singular_preimage W hW.isClosed _
    T.contMDiff_proj hIso hSmooth

theorem smooth_positions_and_footprint {n d : ℕ} {X : CMfd.{0} n}
    (W : Set X) (hW : IsClosedSubmanifold n W) (E : List (Set X)) (hE : IsSNCDivisor n E)
    (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H)) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      IsGeoTestTower (actualSmoothBoundaryMarked W E) T → CentresAvoid (actualSmoothBoundaryOpen E hE) T →
      ActualSmoothBoundarySteps W E d T →
      CentresOver (W ∩ ⋃ H ∈ E, H) T ∧
      StageCentres (fun P C =>
        (IsClosedSubmanifold n (strictTransform n P.proj W) ∧
          C ⊆ strictTransform n P.proj W ∩ ⋃ H ∈ (geoTransformAlong (actualSmoothBoundaryMarked W E) P).E, H) ∧
        HasNormalCrossings n C (geoTransformAlong (actualSmoothBoundaryMarked W E) P).E) T
  | _, .refl, _, _, _ => ⟨trivial, trivial⟩
  | _, .step P C π hπ, hT, hAvoid, hSteps => by
    obtain ⟨hOver, hStage⟩ := smooth_positions_and_footprint W hW E hE hDense P hT.1 hAvoid.1 hSteps.1
    have hDenseGood : W ⊆ closure (W ∩ (actualSmoothBoundaryOpen E hE : Set X)) := by
      change W ⊆ closure (W ∩ (⋃ H ∈ E, H)ᶜ)
      exact hDense
    have hStrict := strictAlong_eq_library_of_avoid W hW.1 (actualSmoothBoundaryOpen E hE)
      hDenseGood P hAvoid.1
    have hClosed := hSteps.2.2.1
    have hCW := hSteps.2.2.2.2
    rw [hStrict] at hClosed hCW
    refine ⟨⟨hOver, ?_⟩, ⟨hStage, ⟨hClosed, hCW⟩, hT.2.2.2⟩⟩
    intro y hy
    refine ⟨strictTransform_subset_preimage P.contMDiff_proj.continuous hW.1 (hCW hy).1, ?_⟩
    by_contra hNo
    exact disjoint_left.mp hAvoid.2 hy hNo

set_option maxHeartbeats 2000000 in
theorem dense_finish_append_of_stage_geometry {m : ℕ} {X Y Z : CMfd.{0} (m + 1)}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (m + 1) E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (L : BlowupTower X Y) (R : BlowupTower Y Z)
    (hL : IsGeoTestTower (actualSmoothBoundaryMarked W E) L)
    (hLStage : StageCentres (fun P C => C ⊆ singularSet (n := m + 1) (strictTransform (m + 1) P.proj W)) L)
    (N : MarkedIdeal (m + 1) Y)
    (hNE : N.E = (geoTransformAlong (actualSmoothBoundaryMarked W E) L).E)
    (hR : IsGeoTestTower N R)
    (hOverTail : CentresOver (strictTransform (m + 1) L.proj W ∩ ⋃ H ∈ N.E, H) R)
    (hTailPos : StageCentres (fun P C =>
      (IsClosedSubmanifold (m + 1) (strictTransform (m + 1) P.proj (strictTransform (m + 1) L.proj W)) ∧
        C ⊆ strictTransform (m + 1) P.proj (strictTransform (m + 1) L.proj W) ∩
          ⋃ H ∈ (geoTransformAlong (actualSmoothBoundaryMarked (strictTransform (m + 1) L.proj W)
            (geoTransformAlong (actualSmoothBoundaryMarked W E) L).E) P).E, H) ∧
      HasNormalCrossings (m + 1) C
        (geoTransformAlong (actualSmoothBoundaryMarked (strictTransform (m + 1) L.proj W)
          (geoTransformAlong (actualSmoothBoundaryMarked W E) L).E) P).E) R)
    (hClosed : IsClosedSubmanifold (m + 1) (strictTransform (m + 1) (L.append R).proj W))
    (hSNC : IsSNCDivisor (m + 1) (geoTransformAlong (actualSmoothBoundaryMarked W E) (L.append R)).E)
    (hNC : HasNormalCrossings (m + 1) (strictTransform (m + 1) (L.append R).proj W)
      (geoTransformAlong (actualSmoothBoundaryMarked W E) (L.append R)).E) :
    DenseBoundaryResolution W E (L.append R) := by
  let n := m + 1
  let M := actualSmoothBoundaryMarked W E
  let A := strictTransform n L.proj W
  let F := singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H)
  let ET := (geoTransformAlong M L).E
  have hStages := stageCentres_embedded_position_append W E L R
    (singular_positions_with_boundary W M L hL hLStage) hTailPos
  let Osg : Opens X := ⟨(singularSet (n := n) W)ᶜ, (isClosed_singularSet hW.isClosed).isOpen_compl⟩
  have hLOver : CentresOver (singularSet (n := n) W) L := by
    have h := centresOver_compl_of_centresAvoid Osg L
      (intrinsic_singular_history_avoids_regular_open hW Osg disjoint_compl_right L hLStage)
    change CentresOver ((singularSet (n := n) W)ᶜ)ᶜ L at h
    rwa [compl_compl] at h
  have hAdmL := isAdmissibleBlowupSequence_proj M _ L hL hLOver
  have hTailFoot : A ∩ ⋃ H ∈ ET, H ⊆ L.proj ⁻¹' F := by
    rintro y ⟨hyA,hyE⟩
    have hyW := strictTransform_subset_preimage L.contMDiff_proj.continuous hW.isClosed hyA
    rcases IsAdmissibleBlowupSequence.biUnion_subset hAdmL hE.1 hyE with hyOld | hySing
    · exact Or.inr ⟨hyW,hyOld⟩
    · exact Or.inl hySing
  have hAdm : IsAdmissibleBlowupSequence n X E F Z (L.append R).proj (geoTransformAlong M (L.append R)).E := by
    have hFoot : A ∩ ⋃ H ∈ N.E, H ⊆ L.proj ⁻¹' F := hNE.symm ▸ hTailFoot
    have hAdmTail := (isAdmissibleBlowupSequence_proj N _ R hR hOverTail).mono hFoot
    rw [hNE] at hAdmTail
    rw [BlowupTower.proj_append, geoTransformAlong_append,
      geoTransformAlong_E_eq_of_E_eq (𝔍 := geoTransformAlong M L) (𝔪 := N) hNE.symm R]
    exact HironakaAdmissibleCalculus.IsAdmissibleBlowupSequence.comp
      (hAdmL.mono (show singularSet (n := n) W ⊆ F from subset_union_left)) hAdmTail
  exact dense_boundary_resolution_of_final_normalCrossings hW E hE hDense (L.append R)
    ((bm_stages_iff_markOne W E (L.append R)).mpr hStages) hAdm hClosed hSNC hNC

set_option maxHeartbeats 2000000 in
private theorem dense_finish_append_of_smooth_phase {m d : ℕ} {X Y Z : CMfd.{0} (m + 1)}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (m + 1) E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (L : BlowupTower X Y) (R : BlowupTower Y Z)
    (hL : IsGeoTestTower (actualSmoothBoundaryMarked W E) L)
    (hLStage : StageCentres (fun P C => C ⊆ singularSet (n := m + 1) (strictTransform (m + 1) P.proj W)) L)
    (hA : IsClosedSubmanifold (m + 1) (strictTransform (m + 1) L.proj W))
    (hPure : ∀ x ∈ strictTransform (m + 1) L.proj W,
      RegularAtDim (n := m + 1) (strictTransform (m + 1) L.proj W) x d)
    (hR : IsGeoTestTower (actualSmoothBoundaryMarked (strictTransform (m + 1) L.proj W)
      (geoTransformAlong (actualSmoothBoundaryMarked W E) L).E) R)
    (hROver : CentresOver (⋃ H ∈ (geoTransformAlong (actualSmoothBoundaryMarked W E) L).E, H) R)
    (hClosed : IsClosedSubmanifold (m + 1) (strictTransform (m + 1) (L.append R).proj W))
    (hSNC : IsSNCDivisor (m + 1) (geoTransformAlong (actualSmoothBoundaryMarked W E) (L.append R)).E)
    (hNC : HasNormalCrossings (m + 1) (strictTransform (m + 1) (L.append R).proj W)
      (geoTransformAlong (actualSmoothBoundaryMarked W E) (L.append R)).E) :
    DenseBoundaryResolution W E (L.append R) := by
  let n := m + 1
  let M := actualSmoothBoundaryMarked W E
  let A := strictTransform n L.proj W
  let F := singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H)
  let ET := (geoTransformAlong M L).E
  let N := actualSmoothBoundaryMarked A ET
  have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW, hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hET := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM L hL).isSNCDivisor
  have hADense := strict_transform_dense_off_accumulated_boundary hW E hE hDense L hL hLStage
  have hRAvoid : CentresAvoid (actualSmoothBoundaryOpen ET hET) R :=
    centresAvoid_of_centresOver _ disjoint_compl_left R hROver
  have hSteps := boundary_steps_of_test_avoid A ET hA d hPure hET R hR hRAvoid
  obtain ⟨hOverTail, hTailPos⟩ := smooth_positions_and_footprint A hA ET hET hADense R hR hRAvoid hSteps
  exact dense_finish_append_of_stage_geometry hW E hE hDense L R hL hLStage N rfl
    hR hOverTail hTailPos hClosed hSNC hNC

set_option maxHeartbeats 2500000 in
/-- On a neighbourhood of any compact task, the actual full-boundary local
smooth cleanup appends to a supplied pure singular smoothing. -/
theorem exists_local_pure_finish_of_singular_history {m d : ℕ} {X Y : CMfd.{0} (m + 1)}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (hPure : W ⊆ closure (regularLocus (n := m + 1) W d)) (hd : d < m + 1)
    (E : List (Set X)) (hE : IsSNCDivisor (m + 1) E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (actualSmoothBoundaryMarked W E) T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := m + 1) (strictTransform (m + 1) P.proj W)) T)
    (hSmooth : IsClosedSubmanifold (m + 1) (strictTransform (m + 1) T.proj W))
    (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{0} (m + 1)) (J : BlowupTower (CMfd.of (n := m + 1) O) Z),
      DenseBoundaryResolution ((Subtype.val : O → X) ⁻¹' W)
        (E.map ((Subtype.val : O → X) ⁻¹' ·)) J := by
  let n := m + 1
  let M := actualSmoothBoundaryMarked W E
  let A := strictTransform n T.proj W
  let ET := (geoTransformAlong M T).E
  let N := actualSmoothBoundaryMarked A ET
  have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW, hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hET := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT).isSNCDivisor
  have hA := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_proj hW T
  have hN : N.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence A hA, hET, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hET⟩
  have hADense := strict_transform_dense_off_accumulated_boundary hW E hE hDense T hT hStage
  have hAPure := pure_dim_of_smooth_singular_history hW hPure T hStage hSmooth
  obtain ⟨V, hKV, hEV, Z, S, hCleanup⟩ := exists_actual_local_smooth_boundary_cleanup A ET hSmooth d hd
    hAPure hET hADense ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK)
  obtain ⟨_, hS, hSAvoid, _, _, hSSmooth, _, hSStrict, _, hSNC, hSSNC, _⟩ := hCleanup
  rw [hSStrict] at hSSmooth hSNC
  obtain ⟨O, hKO, hOV, hGeo⟩ := exists_saturated_tower_append T K V hKV S
  let U := openPreimage T O
  let D := nestedOpens V U
  let e := (nestedOpensDiffeo (n := n) hOV).symm
  let R := transport e (restrict D S)
  let L := restrict O T
  let J := L.append R.tower
  let b : R.target → Z := fun z => (R.back z).val
  let W₀ := (Subtype.val : O → X) ⁻¹' W
  let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let M₀ := actualSmoothBoundaryMarked (X := CMfd.of (n := n) O) W₀ E₀
  let A₀ := strictTransform n L.proj W₀
  let E₁ := (geoTransformAlong M₀ L).E
  let N₀ := actualSmoothBoundaryMarked A₀ E₁
  let AV := (Subtype.val : V → Y) ⁻¹' A
  let EV := ET.map ((Subtype.val : V → Y) ⁻¹' ·)
  let NV := actualSmoothBoundaryMarked (X := CMfd.of (n := n) V) AV EV
  obtain ⟨hTIso, _, _, _, _, hStrict⟩ := hGeo
  have hNV : MarkedIdeal.pullback (Subtype.val : V → Y) N = NV := pullback_val_mk_vanishingIdeal V ET A
  have hMO : MarkedIdeal.pullback (Subtype.val : O → X) M = M₀ := pullback_val_mk_vanishingIdeal O E W
  obtain ⟨hLTest, hRTest, hE₁, hFinalE⟩ := saturated_marked_phase_restrict M hM T hT N hN rfl V S
    (hNV.symm ▸ hS) O hOV
  rw [hMO] at hLTest hE₁ hFinalE
  rw [hNV] at hFinalE
  have hA₀ : A₀ = (Subtype.val : U → Y) ⁻¹' A := strictTransform_restricted_tower O T W
  have hNU : MarkedIdeal.pullback (Subtype.val : U → Y) N = N₀ := by
    change MarkedIdeal.pullback (Subtype.val : U → Y) (actualSmoothBoundaryMarked A ET) = _
    rw [show MarkedIdeal.pullback (Subtype.val : U → Y) (actualSmoothBoundaryMarked A ET) =
      actualSmoothBoundaryMarked (X := CMfd.of (n := n) U) ((Subtype.val : U → Y) ⁻¹' A)
        (ET.map ((Subtype.val : U → Y) ⁻¹' ·)) from pullback_val_mk_vanishingIdeal U ET A, ← hA₀]
    change actualSmoothBoundaryMarked A₀ (ET.map ((Subtype.val : U → Y) ⁻¹' ·)) = N₀
    have hMap : E₁ = ET.map ((Subtype.val : U → Y) ⁻¹' ·) := hE₁
    rw [← hMap]
  rw [hNU] at hRTest
  have hMap : E₁ = ET.map ((Subtype.val : U → Y) ⁻¹' ·) := hE₁
  have hA₀Smooth : IsClosedSubmanifold n A₀ := hA₀.symm ▸ BlowupRestrictOpen.isClosedSubmanifold_preimage_val hSmooth U
  have hA₀Pure : ∀ x ∈ A₀, RegularAtDim (n := n) A₀ x d := by
    rw [hA₀]
    exact fun x hx => AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hAPure x hx)
  have hSOver : CentresOver (⋃ H ∈ EV, H) S := by
    have h := centresOver_compl_of_centresAvoid (actualSmoothBoundaryOpen EV hEV) S hSAvoid
    change CentresOver ((⋃ H ∈ EV, H)ᶜ)ᶜ S at h
    rwa [compl_compl] at h
  have hROver : CentresOver (⋃ H ∈ E₁, H) R.tower := by
    have h := centresOver_of_isTowerIso hTIso _ (centresOver_restrict D _ S hSOver)
    have hSet : e ⁻¹' ((Subtype.val : D → V) ⁻¹' (⋃ H ∈ EV, H)) = ⋃ H ∈ E₁, H := by
      rw [hMap, ← preimage_biUnion_list]
      dsimp only [EV]
      rw [← preimage_biUnion_list]
      rfl
    rwa [hSet] at h
  have hW₀ := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O
  have hE₀ := isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
  have hDense₀ := dense_complement_restrict W E hDense O
  have hLStage := singular_stages_restrict W O T hStage
  have hClosed : IsClosedSubmanifold n (strictTransform n J.proj W₀) := by
    rw [hStrict W]
    exact (isClosedSubmanifold_preimage_iff R.back).mpr
      (BlowupRestrictOpen.isClosedSubmanifold_preimage_val hSSmooth (openPreimage S D))
  have hb : IsOpenHoloEmbedding n b := ⟨openPreimage S D, R.back, fun _ => rfl⟩
  have hSNCF : IsSNCDivisor n (geoTransformAlong M₀ J).E := by
    rw [hFinalE]
    exact isSNCDivisor_map_preimage hb.pullsBackCoordinates hb.continuous hSSNC
  have hNCF : HasNormalCrossings n (strictTransform n J.proj W₀) (geoTransformAlong M₀ J).E := by
    rw [hStrict W, hFinalE]
    exact hasNormalCrossings_preimage hb.pullsBackCoordinates hSNC
  exact ⟨O, hKO, R.target, J, dense_finish_append_of_smooth_phase hW₀ E₀ hE₀ hDense₀ L R.tower
    hLTest hLStage hA₀Smooth hA₀Pure hRTest hROver hClosed hSNCF hNCF⟩

end
end Hironaka.HironakaG8LocalPureFinish
