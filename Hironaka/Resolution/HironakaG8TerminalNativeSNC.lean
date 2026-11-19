import Hironaka.Resolution.HironakaG8FiniteNativeTestServing
import Hironaka.Resolution.HironakaG8PrincipalCompactSNCFinish
import Hironaka.Resolution.HironakaCurrentStrictTransformIdeal

/-! Terminal full-boundary SNC cleanup after finite native TEST serving. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8TerminalNativeSNC

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaEmbeddedBoundary NormalCrossings NormalCrossingsInvariance
  HironakaG8UniverseDenseBoundary HironakaG8LocalPureFinish HironakaG8LocalPureEmbeddedResolution
  HironakaG8SeparatedSmoothPhases HironakaG8LocalMixedPhaseAssembly HironakaG8LocalMixedSmoothCleanup
  HironakaG8DenseBoundaryRestriction HironakaG8DenseBoundaryRestart HironakaG8FiniteSingularTowerMerge
  HironakaG8NativeRelativePhase HironakaActualSmoothBoundaryCleanup HironakaActualGeometricCleanupComposition
  HironakaSharpActualFiniteChronologicalHistory HironakaCoherentTransformExtension
  HironakaNormalCrossingsOpenRestrictionSeparation


open HironakaG8FiniteNativeTestServing HironakaG8PrincipalCompactSNCFinish
  HironakaG8UniverseBMTransport HironakaCurrentStrictTransformIdeal
  HironakaG8IntrinsicSingularBlockSchedule HironakaAdmissibleSequence HironakaAdmissibleCalculus
  HironakaG8OpenHoloEmbeddingComposition HironakaLocalPrincipalization HironakaBaseChange

private abbrev bad {n : ℕ} {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) :=
  singularSet (n := n) W ∪ (W ∩ ⋃ H ∈ E, H)

private theorem centresOver_mono {n : ℕ} {X Y : CMfd.{0} n} {A B : Set X}
    (hAB : A ⊆ B) (T : BlowupTower X Y) (hT : CentresOver A T) : CentresOver B T := by
  induction T with
  | refl => exact trivial
  | step T C π hπ ih => exact ⟨ih hT.1,hT.2.trans (preimage_mono hAB)⟩

/-- The original mark-one record tests a mixed-centre history with
the actual BM stage geometry and the original bad footprint. -/
theorem original_test_of_bm_stages_and_footprint {n : ℕ} {X Y : CMfd.{0} n}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := n) W) (E : List (Set X))
    (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y) (hStages : BMStages W E T) (hOver : CentresOver (bad W E) T) :
    IsGeoTestTower (actualSmoothBoundaryMarked W E) T := by
  let M := actualSmoothBoundaryMarked W E
  let G := geometricTemplate (univ : Set X) E
  let F := bad W E
  have hClosedE := isClosed_biUnion_of_forall_isClosed hE.1
  let O : Opens X := ⟨Fᶜ, ((isClosed_singularSet hW.isClosed).union
    (hW.isClosed.inter hClosedE)).isOpen_compl⟩
  have hDenseGood : W ⊆ closure (W ∩ (O : Set X)) := by
    have h := dense_off_original_boundary_and_singular hW hClosedE hDense
    change W ⊆ closure (W ∩ Fᶜ)
    rw [← sdiff_eq]
    exact h.trans (closure_mono (sdiff_subset_sdiff_right
      (fun x hx => hx.elim Or.inr (fun hb => Or.inl hb.2))))
  have hWF : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW,hE,
    SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  induction T with
  | refl => exact trivial
  | step P C π hπ ih =>
      have hP := ih hStages.1 hOver.1
      have hAvoid : CentresAvoid O P := centresAvoid_of_centresOver _ disjoint_compl_left P hOver.1
      have hCos := strictTransform_subset_cosupp_of_centresAvoid_wellFormed hW.isClosed
        hWF O hDenseGood P hP hAvoid
      have hPos := hStages.2
      have hCE : C ⊆ strictTransform n P.proj W := fun x hx =>
        hPos.1.elim (fun hs => singularSet_subset _ (hs hx)) (fun hs => (hs.2 hx).1)
      have hEq : (geoTransformAlong G P).E = (geoTransformAlong M P).E :=
        geoTransformAlong_E_eq_of_E_eq (𝔍 := G) (𝔪 := M) rfl P
      exact ⟨hP,hπ.1,hCE.trans hCos,hEq ▸ hPos.2⟩

private theorem finish_with_actual_smooth_tail {m : ℕ} {X Y Z : CMfd.{0} (m+1)}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (m+1) E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (L : BlowupTower X Y) (R : BlowupTower Y Z)
    (hLTest : IsGeoTestTower (actualSmoothBoundaryMarked W E) L)
    (hLSing : StageCentres (fun P C => C ⊆ singularSet (n := m+1) (strictTransform (m+1) P.proj W)) L)
    (hTail : SmoothBoundaryTower (strictTransform (m+1) L.proj W)
      (geoTransformAlong (actualSmoothBoundaryMarked W E) L).E R) :
    IsGeoTestTower (actualSmoothBoundaryMarked W E) (L.append R) ∧
      CentresOver (bad W E) (L.append R) ∧ DenseBoundaryResolution W E (L.append R) := by
  let n := m + 1
  let J := L.append R
  let M₀ := actualSmoothBoundaryMarked W E
  let A₀ := strictTransform n L.proj W
  let E₁ := (geoTransformAlong M₀ L).E
  let N := geometricTemplate (univ : Set Y) E₁
  have hEndA : strictTransform n J.proj W = strictTransform n R.proj A₀ := by
    rw [BlowupTower.proj_append, StrictTransformComposition.strictTransform_comp L.contMDiff_proj R.contMDiff_proj]
  have hEndE : (geoTransformAlong M₀ J).E = (geoTransformAlong N R).E := by
    rw [geoTransformAlong_append, geoTransformAlong_E_eq_of_E_eq
      (𝔍 := geoTransformAlong M₀ L) (𝔪 := N) rfl R]
  have hFinish : DenseBoundaryResolution W E J :=
    dense_finish_append_of_stage_geometry (X := X) (Y := Y) (Z := Z) (W := W)
      hW E hE hDense L R hLTest hLSing N rfl
      hTail.test hTail.footprint ((smooth_stages_iff_markOne A₀ E₁ R).mp hTail.stages)
      (hEndA.symm ▸ hTail.smooth) (hEndE.symm ▸ hTail.snc) (hEndA.symm ▸ hEndE.symm ▸ hTail.nc)
  let Osg : Opens X := ⟨(singularSet (n := n) W)ᶜ,(isClosed_singularSet hW.isClosed).isOpen_compl⟩
  have hLOver : CentresOver (singularSet (n := n) W) L := by
    have h := centresOver_compl_of_centresAvoid Osg L
      (intrinsic_singular_history_avoids_regular_open hW Osg disjoint_compl_right L hLSing)
    change CentresOver ((singularSet (n := n) W)ᶜ)ᶜ L at h
    rwa [compl_compl] at h
  have hAdmL := isAdmissibleBlowupSequence_proj M₀ _ L hLTest hLOver
  have hFoot : A₀ ∩ ⋃ H ∈ E₁, H ⊆ L.proj ⁻¹' bad W E := by
    rintro y ⟨hyA,hyE⟩
    have hyW := strictTransform_subset_preimage L.contMDiff_proj.continuous hW.isClosed hyA
    rcases IsAdmissibleBlowupSequence.biUnion_subset hAdmL hE.1 hyE with hyOld | hySing
    · exact Or.inr ⟨hyW,hyOld⟩
    · exact Or.inl hySing
  have hOver : CentresOver (bad W E) J := (centresOver_append_iff _ L R).mpr
    ⟨centresOver_mono subset_union_left L hLOver,centresOver_mono hFoot R hTail.footprint⟩
  exact ⟨original_test_of_bm_stages_and_footprint hW E hE hDense J hFinish.2.1 hOver,
    hOver,hFinish⟩

/-- Append the actual mixed-dimensional smooth cleanup to the saturated
restriction of the terminal physical singular trace. -/
theorem exists_smooth_mark_one_test_finish {m : ℕ} {X Y : CMfd.{0} (m + 1)}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (m + 1) E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (actualSmoothBoundaryMarked W E) T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := m + 1) (strictTransform (m + 1) P.proj W)) T)
    (hSmooth : IsClosedSubmanifold (m + 1) (strictTransform (m + 1) T.proj W))
    (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{0} (m + 1))
      (R : BlowupTower (CMfd.of (n := m + 1) (openPreimage T O)) Z),
      let W₀ := (Subtype.val : O → X) ⁻¹' W
      let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
      let L := restrict O T
      IsGeoTestTower (actualSmoothBoundaryMarked W₀ E₀) (L.append R) ∧
        CentresOver (bad W₀ E₀) (L.append R) ∧ DenseBoundaryResolution W₀ E₀ (L.append R) := by
  let n := m + 1
  let M := actualSmoothBoundaryMarked W E
  let G := geometricTemplate (univ : Set X) E
  let A := strictTransform n T.proj W
  let ET := (geoTransformAlong M T).E
  have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW, hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hET := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT).isSNCDivisor
  have hADense := strict_transform_dense_off_accumulated_boundary hW E hE hDense T hT hStage
  have hPhase : LocalSmoothTower (X := Y) A ET (T.proj ⁻¹' K) :=
    local_mixed_smooth_boundary_cleanup hSmooth ET hET hADense
      (T.proj ⁻¹' K) ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK)
  have hGeq : (geoTransformAlong G T).E = ET := geoTransformAlong_E_eq_of_E_eq (𝔍 := G) (𝔪 := M) rfl T
  have hPhaseG : LocalSmoothTower (X := Y) A (geoTransformAlong G T).E (T.proj ⁻¹' K) := by
    rw [hGeq]
    exact hPhase
  have hGT : IsGeoTestTower G T := geometric_test_of_test M E (List.Sublist.refl _) T hT
  obtain ⟨O, hKO, Z, R, hR⟩ := restrict_local_smooth_phase (W := W) E hE T hGT K hPhaseG
  let L := restrict O T
  let W₀ := (Subtype.val : O → X) ⁻¹' W
  let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let M₀ := actualSmoothBoundaryMarked (X := CMfd.of (n := n) O) W₀ E₀
  let G₀ := geometricTemplate (univ : Set (CMfd.of (n := n) O)) E₀
  let A₀ := strictTransform n L.proj W₀
  let E₁ := (geoTransformAlong M₀ L).E
  let XO := CMfd.of (n := n) O
  let YO := CMfd.of (n := n) (openPreimage T O)
  have hGE : (geoTransformAlong G₀ L).E = E₁ :=
    geoTransformAlong_E_eq_of_E_eq (𝔍 := G₀) (𝔪 := M₀) rfl L
  have hTail : SmoothBoundaryTower (X := YO) (Y := Z) A₀ E₁ R := by
    rw [← hGE]
    exact hR
  have hLTest : IsGeoTestTower M₀ L := by
    have h := MarkedIdealRestrictOpen.isGeoTestTower_restrict O hM.isClosedSubmanifold_N hM.isCoherent T hT
    have heq : MarkedIdeal.pullback (Subtype.val : O → X) M = M₀ :=
      pullback_val_mk_vanishingIdeal O E W
    rwa [heq] at h
  have hLSing := singular_stages_restrict W O T hStage
  have hW₀ := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW O
  have hE₀ := isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
  have hDense₀ := dense_complement_restrict W E hDense O
  exact ⟨O,hKO,Z,R,finish_with_actual_smooth_tail hW₀ E₀ hE₀ hDense₀ L R hLTest hLSing hTail⟩

open HironakaActualHilbertSamuelLexOrder

/-- The actual terminal native TEST prefix, restricted to a saturated
smooth neighbourhood of the compact task, has a proper SNC finish
on the same physical prefix. The full tower tests the literal original
mark-one record, through every cleanup step. -/
theorem NativeTestServingTrace.terminal_snc_finish {n : ℕ} {X Y : CMfd.{0} (n+1)}
    {W : Set X} {E : List (Set X)} {P : BlowupTower X Y} {K : Set X}
    {labels : List (ActualAnalyticLexHilbertSamuelProfile (n+1))}
    (h : NativeTestServingTrace W E P K labels) (hK : IsCompact K) :
    ∃ (A : CMfd.{0} (n+1)) (j : A → X), IsOpenHoloEmbedding (n+1) j ∧ K ⊆ range j ∧
      ∃ (B : CMfd.{0} (n+1)) (T : BlowupTower A B),
        NativeTestState (j ⁻¹' W) (E.map (j ⁻¹' ·)) T ∧
        Disjoint (T.proj ⁻¹' (j ⁻¹' K)) (singularSet (n := n+1) (strictTransform (n+1) T.proj (j ⁻¹' W))) ∧
        ∃ (V : Opens A), j ⁻¹' K ⊆ V ∧
          let P₀ := restrict V T
          let j₀ : V → X := j ∘ Subtype.val
          IsClosedSubmanifold (n+1) (strictTransform (n+1) P₀.proj (j₀ ⁻¹' W)) ∧
          ∃ (D : Opens (CMfd.of (n := n+1) V)) (C : CMfd.{0} (n+1))
            (R : BlowupTower (CMfd.of (n := n+1) (openPreimage P₀ D)) C),
            let i : D → X := j₀ ∘ Subtype.val
            let U := i ⁻¹' W
            let F := E.map (i ⁻¹' ·)
            let J := (restrict D P₀).append R
            IsOpenHoloEmbedding (n+1) i ∧ K ⊆ range i ∧
            IsGeoTestTower (actualSmoothBoundaryMarked U F) J ∧
            CentresOver (bad U F) J ∧ DenseBoundaryResolution U F J := by
  obtain ⟨A,j,hj,hCover,B,T,hState,hClear⟩ := h.endpoint
  let U := j ⁻¹' W
  let F := E.map (j ⁻¹' ·)
  let K' := j ⁻¹' K
  let M := actualSmoothBoundaryMarked (X := A) U F
  have hK' : IsCompact K' :=
    (hj.isOpenEmbedding.toIsInducing.isCompact_preimage_iff (fun x hx => hCover hx)).mpr hK
  obtain ⟨V,hKV,hSmooth⟩ :=
    exists_smooth_restriction_of_empty_singular_fibre hState.analytic T K' hClear
  let A₀ := CMfd.of (n := n+1) V
  let U₀ := (Subtype.val : V → A) ⁻¹' U
  let F₀ := F.map ((Subtype.val : V → A) ⁻¹' ·)
  let P₀ := restrict V T
  let K₀ := (Subtype.val : V → A) ⁻¹' K'
  have hM : M.IsWellFormed :=
    ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,CartanIrreducible.cartanCoherence U hState.analytic,
      hState.snc,SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hState.snc⟩
  have hTest₀ : IsGeoTestTower (actualSmoothBoundaryMarked U₀ F₀) P₀ := by
    have hh := MarkedIdealRestrictOpen.isGeoTestTower_restrict V hM.isClosedSubmanifold_N
      hM.isCoherent T hState.tested
    have heq : MarkedIdeal.pullback (Subtype.val : V → A) M =
        actualSmoothBoundaryMarked (X := A₀) U₀ F₀ :=
      pullback_val_mk_vanishingIdeal V F U
    rwa [heq] at hh
  have hK₀ : IsCompact K₀ := (Topology.IsInducing.subtypeVal.isCompact_preimage_iff
    (fun x hx => ⟨⟨x,hKV hx⟩,rfl⟩)).mpr hK'
  have hU₀ := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hState.analytic V
  have hF₀ := isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hState.snc
  have hDense₀ := dense_complement_restrict U F hState.dense V
  obtain ⟨D,hKD,C,R,hTest,hOver,hFinish⟩ := exists_smooth_mark_one_test_finish
    hU₀ F₀ hF₀ hDense₀ P₀ hTest₀ (singular_stages_restrict U V T hState.singular) hSmooth K₀ hK₀
  let i : D → X := (j ∘ (Subtype.val : V → A)) ∘ (Subtype.val : D → A₀)
  have hi : IsOpenHoloEmbedding (n+1) i :=
    isOpenHoloEmbedding_comp (A := X) (B := A₀) (C := CMfd.of (n := n+1) D)
      (isOpenHoloEmbedding_comp (A := X) (B := A) (C := A₀) hj (isOpenHoloEmbedding_val V))
      (isOpenHoloEmbedding_val D)
  have hiCover : K ⊆ range i := by
    intro x hx
    obtain ⟨a,ha⟩ := hCover hx
    have ha' : a ∈ K' := show j a ∈ K from ha.symm ▸ hx
    let v : V := ⟨a,hKV ha'⟩
    let d : D := ⟨v,hKD ha'⟩
    exact ⟨d,ha⟩
  have hBoundary : F₀.map ((Subtype.val : D → A₀) ⁻¹' ·) = E.map (i ⁻¹' ·) := by
    simp only [F₀,F,List.map_map]
    rfl
  rw [hBoundary] at hTest hOver hFinish
  exact ⟨A,j,hj,hCover,B,T,hState,hClear,V,hKV,hSmooth,D,C,R,hi,hiCover,hTest,hOver,hFinish⟩

/-- Finite actual TEST and proper embedded resolution near a compact task
in arbitrary positive ambient dimension. The finite native trace used for
singular serving and its same-prefix cleanup are retained by the producer. -/
theorem exists_local_native_test_snc_finish {n : ℕ} {X : CMfd.{0} (n+1)}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n+1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (n+1) E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (K : Set X) (hK : IsCompact K) :
    ∃ (A : CMfd.{0} (n+1)) (i : A → X), IsOpenHoloEmbedding (n+1) i ∧ K ⊆ range i ∧
      ∃ (Z : CMfd.{0} (n+1)) (J : BlowupTower A Z),
        let U := i ⁻¹' W
        let F := E.map (i ⁻¹' ·)
        IsGeoTestTower (actualSmoothBoundaryMarked U F) J ∧
          CentresOver (bad U F) J ∧ DenseBoundaryResolution U F J := by
  obtain ⟨_,hTrace⟩ := exists_finite_native_test_serving_from_refl W hW E hE hDense K hK
  obtain ⟨A,j,_,_,B,T,_,_,V,_,_,D,C,R,hi,hCover,hTest,hOver,hResolution⟩ :=
    NativeTestServingTrace.terminal_snc_finish hTrace hK
  exact ⟨CMfd.of (n := n+1) D,(j ∘ (Subtype.val : V → A)) ∘ Subtype.val,hi,hCover,
    C,(restrict D (restrict V T)).append R,hTest,hOver,hResolution⟩

#print axioms exists_local_native_test_snc_finish
#print axioms NativeTestServingTrace.terminal_snc_finish
#print axioms original_test_of_bm_stages_and_footprint
#print axioms exists_smooth_mark_one_test_finish

end
end Hironaka.HironakaG8TerminalNativeSNC
