import Hironaka.Resolution.HironakaG4CompactOpenBadService


/-! # Append a compact-open sharp-bad service block to an actual prefix -/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4CompactOpenServicePrefix

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  BlowupTowerIsomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport
  HironakaG4CompactOpenBadService HironakaG34NonPureLowDim HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaActualGlobalDefectProfileBlock
  HironakaSharpOriginalDynamicGoodPrefixes HironakaG34LowerTemplateBridge
  HironakaActualGeometricCleanupComposition HironakaCompactFootprintSharpExtension
  HironakaG4RecordedTowerResidualCompatibility RestrictEmptyTower

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- A compact-open service block can be appended to any actual sharp prefix, preserving the resolved region and recording the tail centre footprint. -/
private theorem centresOver_mono {A : CMfd.{u} n} {F G : Set A} (hFG : F ⊆ G) :
    ∀ {B : CMfd.{u} n} (T : BlowupTower A B), CentresOver F T → CentresOver G T
  | _, .refl, _ => trivial
  | _, .step T _ _ _, h => ⟨centresOver_mono hFG T h.1, fun _ hx => hFG (h.2 hx)⟩

theorem exists_compact_open_service_full_boundary_after_prefix {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (V₀ : Opens X) (hK : IsCompact (originalSharpBadLocus (n := n) W E ∩ V₀))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) (D : Set X)
    (hD : ∀ z ∈ strictAlong T W, T.proj z ∈ D →
      normalCrossingsAt (n := n) (strictAlong T W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z) :
    ∃ (Z : CMfd.{u} n) (S : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append S) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append S) ∧
      CurrentSharpCentres W E (T.append S) ∧
      CentresOver (T.proj ⁻¹' (originalSharpBadLocus (n := n) W E ∩ V₀)) S ∧
      ∀ z ∈ strictAlong (T.append S) W, (T.append S).proj z ∈ D ∪ V₀ →
        normalCrossingsAt (n := n) (strictAlong (T.append S) W)
          (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append S)).E z := by
  let N := strictAlong T W
  let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E
  have hWTemplate : (geometricTemplate W []).IsWellFormed :=
    ⟨hW, IdealWeightPowers.isCoherent_unitIdeal, isSNCDivisor_nil,
      isTransverse_nil_of_isClosedSubmanifold hW⟩
  have hETemplate : (geometricTemplate (univ : Set X) E).IsWellFormed :=
    ⟨isClosedSubmanifold_univ, IdealWeightPowers.isCoherent_unitIdeal, hE,
      SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hNdef : (geoTransformAlong (geometricTemplate W []) T).N = N := N_geoTransformAlong _ T
  have hN : IsClosedSubmanifold n N :=
    hNdef ▸ (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hWTemplate T hT).isClosedSubmanifold_N
  have hF : IsSNCDivisor n F :=
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hETemplate T hFull).isSNCDivisor
  have hFdef : E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E = F := by
    simpa only [List.append_nil] using (full_boundary_split W E [] T).symm
  let V : Opens Y := openPreimage T V₀
  let K := originalSharpBadLocus (n := n) W E ∩ V₀
  obtain ⟨hFoot, -⟩ :=
    HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint hW.1 hE.1 T hSharp
  have hBClosed : IsClosed (originalSharpBadLocus (n := n) N F) :=
    isClosed_originalSharpBadLocus hN.1 hF.1
  have hEq : originalSharpBadLocus (n := n) N F ∩ V =
      originalSharpBadLocus (n := n) N F ∩ T.proj ⁻¹' K := by
    ext z
    constructor
    · rintro ⟨hz,hzV⟩
      exact ⟨hz,hFoot hz,hzV⟩
    · rintro ⟨hz,_,hzV⟩
      exact ⟨hz,hzV⟩
  have hKT : IsCompact (originalSharpBadLocus (n := n) N F ∩ V) := by
    rw [hEq]
    have hc := (HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK
    exact hc.of_isClosed_subset (hBClosed.inter (hK.isClosed.preimage T.contMDiff_proj.continuous))
      (fun z hz => hz.2)
  obtain ⟨Z, S, hSM, hSFull, hSSharp, hOver, _hProper, _hIso, hSNC'⟩ :=
    exists_compact_open_bad_service_full_boundary hN hF V hKT
  refine ⟨Z, S, ?_, ?_, ?_, ?_, ?_⟩
  · rw [geometric_test_append_iff]
    refine ⟨hT, ?_⟩
    have hsub : (geoTransformAlong (geometricTemplate W []) T).E.Sublist F := by
      rw [← hFdef]
      exact List.sublist_append_right _ _
    exact geometric_test_of_test (geometricTemplate N F) _ hsub S hSM
  · refine (isGeoTestTower_append_iff _ T S).mpr ⟨hFull, ?_⟩
    rw [template_current (univ : Set X) E T, strict_univ T]
    exact hSFull
  · exact currentSharp_append W E T S hSharp hSSharp
  · apply centresOver_mono (T := S) _ hOver
    rw [hEq]
    exact inter_subset_right
  · intro z hz hzD
    rw [MemberInterLocusAlong.strictAlong_append T W S] at hz ⊢
    have hEq : (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append S)).E =
        (geoTransformAlong (geometricTemplate (univ : Set Y) F) S).E := by
      rw [geoTransformAlong_append, template_current (univ : Set X) E T, strict_univ T]
    rw [hEq]
    rw [BlowupTower.proj_append] at hzD
    rcases hzD with hzD | hzP
    · by_contra hnc
      obtain ⟨hFootS, -⟩ :=
        HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint hN.1 hF.1 S hSSharp
      have hbad : z ∈ originalSharpBadLocus (n := n) (strictAlong S N)
          (geoTransformAlong (geometricTemplate (univ : Set Y) F) S).E := ⟨hz, hnc⟩
      obtain ⟨hzN, hncN⟩ := hFootS hbad
      exact hncN (hD (S.proj z) hzN hzD)
    · exact hSNC' z hz (hzP)


set_option linter.unusedVariables false in
theorem exists_compact_open_service_after_prefix (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (V₀ : Opens X) (hK : IsCompact (originalSharpBadLocus (n := n) W E ∩ V₀))
    (T : BlowupTower X Y) (hT : IsGeoTestTower (geometricTemplate W []) T)
    (hFull : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hSharp : CurrentSharpCentres W E T) (D : Set X)
    (hD : ∀ z ∈ strictAlong T W, T.proj z ∈ D →
      normalCrossingsAt (n := n) (strictAlong T W)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z) :
    ∃ (Z : CMfd.{u} n) (S : BlowupTower Y Z),
      IsGeoTestTower (geometricTemplate W []) (T.append S) ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) (T.append S) ∧
      CurrentSharpCentres W E (T.append S) ∧
      CentresOver (T.proj ⁻¹' (originalSharpBadLocus (n := n) W E ∩ V₀)) S ∧
      ∀ z ∈ strictAlong (T.append S) W, (T.append S).proj z ∈ D ∪ V₀ →
        normalCrossingsAt (n := n) (strictAlong (T.append S) W)
          (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append S)).E z := by
  clear hn hdense
  exact exists_compact_open_service_full_boundary_after_prefix hW hE V₀ hK T hT hFull hSharp D hD


end
end Hironaka.HironakaG4CompactOpenServicePrefix
