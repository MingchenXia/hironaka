import Hironaka.Resolution.HironakaG4FullBoundaryUniverse
import Mathlib.Topology.DiscreteSubset


/-!
# A compact-open sharp-bad service block

An open subset meeting the original sharp-bad locus in a compact set admits
an actual finite global sharp tower supported over that set, resolving the
full boundary over the open. This does not produce a service block for an
arbitrary noncompact sharp-bad locus.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4CompactOpenBadService

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  BlowupTowerIsomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport
  HironakaG4FullBoundaryUniverse HironakaG34NonPureLowDim HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaActualGlobalDefectProfileBlock
  HironakaSharpOriginalDynamicGoodPrefixes HironakaG34LowerTemplateBridge
  HironakaActualGeometricCleanupComposition HironakaCompactFootprintSharpExtension
  HironakaG4RecordedTowerResidualCompatibility RestrictEmptyTower

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- Normal crossings on the actual local endpoint transfer to every
point of the original endpoint over the comparison window. -/
theorem normalCrossingsAt_of_supported_open_tower_iso {N : Set X} (F : List (Set X))
    (hN : IsClosedSubmanifold n N) (V : Opens X)
    (Q : BlowupTower X Y) (hMQ : IsGeoTestTower (geometricTemplate N F) Q)
    (TU : BlowupTower (CMfd.of (n := n) V) Z)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q V)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) V ∞) TU (restrict V Q) e)
    (hNCU : HasNormalCrossings n (strictAlong TU ((Subtype.val : V → X) ⁻¹' N))
      (geoTransformAlong (geometricTemplate (univ : Set V)
        (F.map ((Subtype.val : V → X) ⁻¹' ·))) TU).E) :
    ∀ z ∈ strictAlong Q N, Q.proj z ∈ V →
      normalCrossingsAt (n := n) (strictAlong Q N)
        (geoTransformAlong (geometricTemplate (univ : Set X) F) Q).E z := by
  let NU := (Subtype.val : V → X) ⁻¹' N
  let FU := F.map ((Subtype.val : V → X) ⁻¹' ·)
  intro z hz hzV
  obtain ⟨hTN, hTE, -⟩ := tuple_open_iso hN F V Q hMQ TU e he
  let w : openPreimage Q V := ⟨z, hzV⟩
  let z' : Z := e.symm w
  have hew : e z' = w := e.apply_symm_apply w
  have hNTU : (geoTransformAlong (geometricTemplate NU FU) TU).N = strictAlong TU NU :=
    N_geoTransformAlong _ TU
  change HasNormalCrossings n (strictAlong TU NU)
    (geoTransformAlong (geometricTemplate (univ : Set V) FU) TU).E at hNCU
  rw [← hNTU] at hNCU
  have hAN : (geoTransformAlong (geometricTemplate N F) Q).N = strictAlong Q N :=
    N_geoTransformAlong _ Q
  have hz'N : z' ∈ (geoTransformAlong (geometricTemplate NU FU) TU).N := by
    rw [hTN]
    change (e z').val ∈ (geoTransformAlong (geometricTemplate N F) Q).N
    rw [hew, hAN]
    exact hz
  have hNC0 := hNCU z' hz'N
  have hEsame : (geoTransformAlong (geometricTemplate (univ : Set (CMfd.of (n := n) V)) FU) TU).E =
      (geoTransformAlong (geometricTemplate NU FU) TU).E := template_E_eq _ _ FU TU
  have hNC1 : normalCrossingsAt (n := n) (geoTransformAlong (geometricTemplate NU FU) TU).N
      (geoTransformAlong (geometricTemplate NU FU) TU).E z' := by
    rw [← hEsame]
    exact hNC0
  rw [hTN, hTE] at hNC1
  let A := geoTransformAlong (geometricTemplate N F) Q
  have hList : A.E.map (((Subtype.val : openPreimage Q V → Y) ∘ e) ⁻¹' ·) =
      (A.E.map ((Subtype.val : openPreimage Q V → Y) ⁻¹' ·)).map (e ⁻¹' ·) := by
    rw [List.map_map]
    rfl
  rw [hList] at hNC1
  have hNC2 := normalCrossingsAt_of_preimage_diffeo (X := CMfd.of (n := n) (openPreimage Q V))
    (Y := Z) e
    (N := (Subtype.val : openPreimage Q V → Y) ⁻¹' A.N)
    (E := A.E.map ((Subtype.val : openPreimage Q V → Y) ⁻¹' ·)) hNC1
  rw [hew] at hNC2
  have hNC3 := HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mp hNC2
  have hAE : A.E = (geoTransformAlong (geometricTemplate (univ : Set X) F) Q).E :=
    template_E_eq _ _ F Q
  rw [hAN, hAE] at hNC3
  exact hNC3


/-- An open set meeting the bad locus compactly admits an actual global
sharp service tower supported over that compact part. -/
theorem exists_compact_open_bad_service_full_boundary {N : Set X} {F : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hF : IsSNCDivisor n F)
    (V : Opens X) (hK : IsCompact (originalSharpBadLocus (n := n) N F ∩ V)) :
    ∃ (Z : CMfd.{u} n) (S : BlowupTower X Z),
      IsGeoTestTower (geometricTemplate N F) S ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) F) S ∧
      CurrentSharpCentres N F S ∧
      CentresOver (originalSharpBadLocus (n := n) N F ∩ V) S ∧
      IsProperMap S.proj ∧
      IsIsomorphismOver n S.proj (originalSharpBadLocus (n := n) N F ∩ V)ᶜ ∧
      ∀ z ∈ strictAlong S N, S.proj z ∈ V →
        normalCrossingsAt (n := n) (strictAlong S N)
          (geoTransformAlong (geometricTemplate (univ : Set X) F) S).E z := by
  let NU := (Subtype.val : V → X) ⁻¹' N
  let FU := F.map ((Subtype.val : V → X) ⁻¹' ·)
  let K := originalSharpBadLocus (n := n) N F ∩ V
  have hNU : IsClosedSubmanifold n NU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN V
  have hFU : IsSNCDivisor n FU :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val (n := n) V) continuous_subtype_val hF
  have hBadU : originalSharpBadLocus (n := n) NU FU = (Subtype.val : V → X) ⁻¹' K := by
    ext y
    constructor
    · rintro ⟨hy, hnc⟩
      exact ⟨⟨hy, fun h => hnc
        (HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mpr h)⟩,
        y.property⟩
    · rintro ⟨⟨hy, hnc⟩, -⟩
      exact ⟨hy, fun h => hnc
        (HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mp h)⟩
  have hKV : K ⊆ V := fun x hx => hx.2
  have hKU : IsCompact (originalSharpBadLocus (n := n) NU FU) := by
    rw [hBadU]
    apply Subtype.isCompact_iff.mpr
    rw [Set.image_preimage_eq_of_subset (show K ⊆ Set.range (Subtype.val : V → X) from
      fun x hx => ⟨⟨x, hKV hx⟩, rfl⟩)]
    exact hK
  obtain ⟨Z, TU, hTU, hFullU, hSharpU, hOverU, -, -, hNCU, -, -⟩ :=
    exists_compact_full_boundary_sharp_cleanup (X := CMfd.of (n := n) V) hNU hFU hKU
  have hTUF : IsGeoTestTower (geometricTemplate NU FU) TU :=
    HironakaG34LowerTemplateBridge.lowerTemplate_test_of_two_tests NU FU TU hTU hFullU
  have hOverK : CentresOver ((Subtype.val : V → X) ⁻¹' K) TU := by
    rw [← hBadU]
    exact hOverU
  have hFullPull : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X)
      (geometricTemplate (univ : Set X) F)) TU := by
    rw [template_pullback (Y := CMfd.of (n := n) V) (Subtype.val : V → X) (univ : Set X) F]
    simpa only [Set.preimage_univ] using hFullU
  have hMPull : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X)
      (geometricTemplate N F)) TU := by
    rw [template_pullback (Y := CMfd.of (n := n) V) (Subtype.val : V → X) N F]
    exact hTUF
  obtain ⟨Y, Q, hFullQ, hMQ, hSharpQ, hOverQ, e, he, -, -⟩ :=
    HironakaCompactFootprintSharpExtension.exists_current_sharp_joint_test_extension
      N F (geometricTemplate N F) hN IdealWeightPowers.isCoherent_unitIdeal V K hK hKV TU hOverK
      hFullPull hMPull hSharpU
  refine ⟨Y, Q, hMQ, hFullQ, hSharpQ, hOverQ,
    HironakaLocalPrincipalization.isProperMap_proj Q,
    HironakaSharpOriginalDynamicGoodPrefixes.isIsomorphismOver_proj_of_centresOver _ Q hOverQ, ?_⟩
  rw [N_geoTransformAlong] at hNCU
  exact normalCrossingsAt_of_supported_open_tower_iso F hN V Q hMQ TU e he hNCU


set_option linter.unusedVariables false in
theorem exists_compact_open_bad_service (hn : 0 < n) {N : Set X} {F : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hF : IsSNCDivisor n F)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ F, H))
    (V : Opens X) (hK : IsCompact (originalSharpBadLocus (n := n) N F ∩ V)) :
    ∃ (Z : CMfd.{u} n) (S : BlowupTower X Z),
      IsGeoTestTower (geometricTemplate N F) S ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) F) S ∧
      CurrentSharpCentres N F S ∧
      CentresOver (originalSharpBadLocus (n := n) N F ∩ V) S ∧
      IsProperMap S.proj ∧
      IsIsomorphismOver n S.proj (originalSharpBadLocus (n := n) N F ∩ V)ᶜ ∧
      ∀ z ∈ strictAlong S N, S.proj z ∈ V →
        normalCrossingsAt (n := n) (strictAlong S N)
          (geoTransformAlong (geometricTemplate (univ : Set X) F) S).E z := by
  clear hn hdense
  exact exists_compact_open_bad_service_full_boundary hN hF V hK

/-- Every bad point of a discrete bad locus admits a global finite service
tower supported over that point, without a carrier-dimension hypothesis. -/
theorem exists_isolated_bad_service (hn : 0 < n) {N : Set X} {F : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hF : IsSNCDivisor n F)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ F, H))
    {x : X} (hx : x ∈ originalSharpBadLocus (n := n) N F)
    (hiso : IsDiscrete (originalSharpBadLocus (n := n) N F)) :
    ∃ (V : Opens X), x ∈ V ∧ ∃ (Z : CMfd.{u} n) (S : BlowupTower X Z),
      IsGeoTestTower (geometricTemplate N F) S ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) F) S ∧
      CurrentSharpCentres N F S ∧ CentresOver {x} S ∧ IsProperMap S.proj ∧
      IsIsomorphismOver n S.proj ({x} : Set X)ᶜ ∧
      ∀ z ∈ strictAlong S N, S.proj z ∈ V →
        normalCrossingsAt (n := n) (strictAlong S N)
          (geoTransformAlong (geometricTemplate (univ : Set X) F) S).E z := by
  obtain ⟨V,hV,hVB⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hiso x hx
  have hxV : x ∈ V := by
    have h : x ∈ V ∩ originalSharpBadLocus (n := n) N F := by rw [hVB]; simp
    exact h.1
  let U : Opens X := ⟨V,hV⟩
  have hBU : originalSharpBadLocus (n := n) N F ∩ U = {x} := by
    rw [inter_comm]
    exact hVB
  have hK : IsCompact (originalSharpBadLocus (n := n) N F ∩ U) := by
    rw [hBU]
    exact isCompact_singleton
  obtain ⟨Z,S,hS,hFull,hSharp,hOver,hProper,hIso,hNC⟩ :=
    exists_compact_open_bad_service hn hN hF hdense U hK
  refine ⟨U,hxV,Z,S,hS,hFull,hSharp,?_,hProper,?_,hNC⟩
  · simpa only [hBU] using hOver
  · simpa only [hBU] using hIso

end
end Hironaka.HironakaG4CompactOpenBadService
