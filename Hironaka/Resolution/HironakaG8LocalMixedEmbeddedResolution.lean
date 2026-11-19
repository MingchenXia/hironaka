import Hironaka.Resolution.HironakaG8LocalMixedSmoothCleanup
import Hironaka.Resolution.HironakaG8DenseBoundaryRestriction

/-! A finite actual embedded resolution with full BM centre conditions on
any prescribed compact-enclosed open, for a carrier of arbitrary dimension. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8LocalMixedEmbeddedResolution

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

/-- The smooth cleanup supplies its geometry and the retained data on the
very same actual finite tower over a neighbourhood of the compact task. -/
def ProducesLocalSmoothCertificates {n : ℕ} (C : SmoothTailCertificate n) : Prop :=
  ∀ {X : CMfd.{0} n} {W : Set X}, IsClosedSubmanifold n W →
    ∀ (E : List (Set X)), IsSNCDivisor n E → W ⊆ closure (W \ ⋃ B ∈ E, B) →
      ∀ (K : Set X), IsCompact K → LocalSmoothTowerWith C W E K

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- Finish an actual singular-centred prefix with the finite cleanup of its
smooth dimension parts, on the same tower after saturated restriction. -/
theorem exists_local_mixed_finish_with_certificate {m : ℕ} {X Y : CMfd.{0} (m + 1)}
    (C : SmoothTailCertificate (m + 1)) (produce : ProducesLocalSmoothCertificates C)
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
      C.holds (strictTransform (m + 1) L.proj W₀) (geoTransformAlong (actualSmoothBoundaryMarked W₀ E₀) L).E R ∧
        DenseBoundaryResolution W₀ E₀ (L.append R) := by
  let n := m + 1
  let M := actualSmoothBoundaryMarked W E
  let G := geometricTemplate (univ : Set X) E
  let A := strictTransform n T.proj W
  let ET := (geoTransformAlong M T).E
  have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW, hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hET := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT).isSNCDivisor
  have hADense := strict_transform_dense_off_accumulated_boundary hW E hE hDense T hT hStage
  have hPhase : LocalSmoothTowerWith (X := Y) C A ET (T.proj ⁻¹' K) :=
    produce hSmooth ET hET hADense
      (T.proj ⁻¹' K) ((HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK)
  have hGeq : (geoTransformAlong G T).E = ET := geoTransformAlong_E_eq_of_E_eq (𝔍 := G) (𝔪 := M) rfl T
  have hPhaseG : LocalSmoothTowerWith (X := Y) C A (geoTransformAlong G T).E (T.proj ⁻¹' K) := by
    rw [hGeq]
    exact hPhase
  have hGT : IsGeoTestTower G T := geometric_test_of_test M E (List.Sublist.refl _) T hT
  obtain ⟨O, hKO, Z, R, hR, hCert⟩ := restrict_local_smooth_phase_with_certificate (W := W) C E hE T hGT K hPhaseG
  let L := restrict O T
  let J := L.append R
  let W₀ := (Subtype.val : O → X) ⁻¹' W
  let E₀ := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let M₀ := actualSmoothBoundaryMarked (X := CMfd.of (n := n) O) W₀ E₀
  let G₀ := geometricTemplate (univ : Set (CMfd.of (n := n) O)) E₀
  let A₀ := strictTransform n L.proj W₀
  let E₁ := (geoTransformAlong M₀ L).E
  let XO := CMfd.of (n := n) O
  let YO := CMfd.of (n := n) (openPreimage T O)
  let N := geometricTemplate (univ : Set YO) E₁
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
  have hEndA : strictTransform n J.proj W₀ = strictTransform n R.proj A₀ := by
    rw [BlowupTower.proj_append, StrictTransformComposition.strictTransform_comp L.contMDiff_proj R.contMDiff_proj]
  have hEndE : (geoTransformAlong M₀ J).E = (geoTransformAlong N R).E := by
    rw [geoTransformAlong_append, geoTransformAlong_E_eq_of_E_eq
      (𝔍 := geoTransformAlong M₀ L) (𝔪 := N) rfl R]
  have hCert' : C.holds A₀ E₁ R := by rw [← hGE]; exact hCert
  refine ⟨O, hKO, Z, R, hCert', ?_⟩
  exact dense_finish_append_of_stage_geometry (X := XO) (Y := YO) (Z := Z) (W := W₀)
    hW₀ E₀ hE₀ hDense₀ L R hLTest hLSing N rfl
    hTail.test hTail.footprint ((smooth_stages_iff_markOne A₀ E₁ R).mp hTail.stages)
    (hEndA.symm ▸ hTail.smooth) (hEndE.symm ▸ hTail.snc) (hEndA.symm ▸ hEndE.symm ▸ hTail.nc)

/-- Finish an actual singular-centred prefix with the existing finite
cleanup on its literal saturated restriction. -/
theorem exists_local_mixed_finish_of_singular_history {m : ℕ} {X Y : CMfd.{0} (m + 1)}
    {W : Set X} (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (m + 1) E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (actualSmoothBoundaryMarked W E) T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := m + 1) (strictTransform (m + 1) P.proj W)) T)
    (hSmooth : IsClosedSubmanifold (m + 1) (strictTransform (m + 1) T.proj W))
    (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{0} (m + 1)) (J : BlowupTower (CMfd.of (n := m + 1) O) Z),
      DenseBoundaryResolution ((Subtype.val : O → X) ⁻¹' W)
        (E.map ((Subtype.val : O → X) ⁻¹' ·)) J := by
  have hProduce : ProducesLocalSmoothCertificates (SmoothTailCertificate.none (m + 1)) := by
    intro X W hW E hE hDense K hK
    exact (local_mixed_smooth_boundary_cleanup hW E hE hDense K hK).withoutExtra
  obtain ⟨O,hKO,Z,R,_,hR⟩ := exists_local_mixed_finish_with_certificate (SmoothTailCertificate.none (m + 1))
    hProduce hW E hE hDense T hT hStage hSmooth K hK
  exact ⟨O,hKO,Z,(restrict O T).append R,hR⟩

set_option maxHeartbeats 1500000 in
/-- Any analytic carrier with dense complement of the initial SNC list gets
one finite actual embedded resolution near each compact set. -/
theorem exists_local_embedded_resolution_of_dense_boundary_complement
    {m : ℕ} {X : CMfd.{0} (m + 1)} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (m + 1) E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{0} (m + 1)) (T : BlowupTower (CMfd.of (n := m + 1) O) Z),
      DenseBoundaryResolution ((Subtype.val : O → X) ⁻¹' W)
        (E.map ((Subtype.val : O → X) ⁻¹' ·)) T := by
  let n := m + 1
  obtain ⟨V, hKV, Y, T, hT, hSing, hSmooth⟩ :=
    exists_native_singular_resolution_near_compact (Nat.succ_pos m) hW E hE hDense K hK
  let WV := (Subtype.val : V → X) ⁻¹' W
  let EV := E.map ((Subtype.val : V → X) ⁻¹' ·)
  let KV := (Subtype.val : V → X) ⁻¹' K
  have hWV := AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hW V
  have hEV := isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hE
  have hKVC : IsCompact KV := by
    rw [Subtype.isCompact_iff, image_preimage_eq_inter_range, Subtype.range_coe, inter_eq_left.mpr hKV]
    exact hK
  obtain ⟨U, hKU, Z, J, hJ⟩ := exists_local_mixed_finish_of_singular_history (X := CMfd.of (n := n) V)
    hWV EV hEV (dense_complement_restrict W E hDense V) T hT hSing hSmooth KV hKVC
  exact flatten_local_dense_boundary_resolution hW E hE hDense V hKV U hKU J hJ

/-- The same conditions give a finite history on the prescribed original
open itself whenever a compact set contains that open. -/
theorem exists_embedded_resolution_on_compact_enclosed_open
    {m : ℕ} {X : CMfd.{0} (m + 1)} {W : Set X}
    (hW : IsComplexAnalyticSubset (n := m + 1) W)
    (E : List (Set X)) (hE : IsSNCDivisor (m + 1) E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (U : Opens X) (K : Set X) (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) :
    ∃ (Z : CMfd.{0} (m + 1)) (T : BlowupTower (CMfd.of (n := m + 1) U) Z),
      DenseBoundaryResolution ((Subtype.val : U → X) ⁻¹' W) (E.map ((Subtype.val : U → X) ⁻¹' ·)) T := by
  obtain ⟨O, hKO, Y, T, hT⟩ := exists_local_embedded_resolution_of_dense_boundary_complement hW E hE hDense K hK
  exact dense_boundary_resolution_on_smaller_open hW E hE hDense O U (hUK.trans hKO) T hT

end
end Hironaka.HironakaG8LocalMixedEmbeddedResolution
