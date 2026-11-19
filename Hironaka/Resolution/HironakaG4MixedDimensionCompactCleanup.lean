import Hironaka.Resolution.HironakaG34NonPureLowDim
import Hironaka.Resolution.HironakaG4OriginalMixedTailProtection

/-!
# Compact sharp cleanup with varying carrier dimension

The already proved dimension-piece topology and compact-footprint extension
let the all-dimensional pure cleanup run successively on the finitely many
local dimensions zero through the ambient dimension. The actual histories
are selected internally, preserve earlier good regions and retain both
original tests and the full chronological boundary. Only the original sharp
bad locus must be compact; the carrier and ambient manifold need not be.

Blueprint: `hironaka-g4-mixed-dimension-compact-cleanup.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG4MixedDimensionCompactCleanup

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupStrictSubmanifold HomogenizedGlueingTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealOperationsAlong MarkedIdealBiholomorphism
  NormalCrossings NormalCrossingsComparison NormalCrossingsInvariance
  RelativePrincipalizationSpan RestrictedIdealExtension InvertibleIdealQuotient
  HironakaSharpActualFiniteChronologicalHistory HironakaSharpNormalCrossingsOpenLocus
  BlowupTowerIsomorphism MarkedIdealRestrictOpen MarkedIdealTowerTransport
  HironakaG34NonPureLowDim HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaG4CompactWholeMonomialMaskPhase HironakaActualGlobalDefectProfileBlock
  HironakaSharpOriginalDynamicGoodPrefixes HironakaG34LowerTemplateBridge
  HironakaActualGeometricCleanupComposition HironakaCompactFootprintSharpExtension
  HironakaG4RecordedTowerResidualCompatibility RestrictEmptyTower

variable {n : ℕ} {X Y Z : CMfd.{u} n}

/-- **One phase on an open where the carrier is pure of dimension `m`** (general base). -/
theorem exists_piece_phase (hn : 0 < n) {N : Set X} {F : List (Set X)}
    (hN : IsClosedSubmanifold n N) (hF : IsSNCDivisor n F)
    (hdense : N ⊆ closure (N \ ⋃ H ∈ F, H))
    (V : Opens X) (G : Set X) (hGV : G ⊆ V) (hNVG : N ∩ V ⊆ G)
    (hK : IsCompact (originalSharpBadLocus (n := n) N F ∩ G))
    (m : ℕ) (hReg : ∀ y ∈ N, y ∈ V → RegularAtDim (n := n) N y m) :
    ∃ (Z : CMfd.{u} n) (S : BlowupTower X Z),
      IsGeoTestTower (geometricTemplate N F) S ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) F) S ∧
      CurrentSharpCentres N F S ∧
      ∀ z ∈ strictAlong S N, S.proj z ∈ V →
        normalCrossingsAt (n := n) (strictAlong S N)
          (geoTransformAlong (geometricTemplate (univ : Set X) F) S).E z := by
  let NU := (Subtype.val : V → X) ⁻¹' N
  let FU := F.map ((Subtype.val : V → X) ⁻¹' ·)
  let K := originalSharpBadLocus (n := n) N F ∩ G
  have hNU : IsClosedSubmanifold n NU := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hN V
  have hFU : IsSNCDivisor n FU :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val (n := n) V) continuous_subtype_val hF
  have hdenseU : NU ⊆ closure (NU \ ⋃ H ∈ FU, H) := open_full_density hdense V
  have hRegU : ∀ y ∈ NU, RegularAtDim (n := n) NU y m := fun y hy =>
    AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr (hReg y.val hy y.property)
  have hBadU : originalSharpBadLocus (n := n) NU FU = (Subtype.val : V → X) ⁻¹' K := by
    ext y
    constructor
    · rintro ⟨hy, hnc⟩
      exact ⟨⟨hy, fun h => hnc
        (HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mpr h)⟩,
        hNVG ⟨hy, y.property⟩⟩
    · rintro ⟨⟨hy, hnc⟩, -⟩
      exact ⟨hy, fun h => hnc
        (HironakaSharpOriginalAllBoundaryCentre.normalCrossingsAt_preimage_val_iff.mp h)⟩
  have hKV : K ⊆ V := fun x hx => hGV hx.2
  have hKU : IsCompact (originalSharpBadLocus (n := n) NU FU) := by
    rw [hBadU]
    apply Subtype.isCompact_iff.mpr
    rw [Set.image_preimage_eq_of_subset (show K ⊆ Set.range (Subtype.val : V → X) from
      fun x hx => ⟨⟨x, hKV hx⟩, rfl⟩)]
    exact hK
  obtain ⟨Z, TU, hTU, hFullU, hSharpU, hOverU, -, -, hNCU, -, -⟩ :=
    HironakaG4OriginalMixedTailProtection.exists_actual_compact_sharp_cleanup (X := CMfd.of (n := n) V)
      hn hNU hFU hdenseU m hRegU hKU
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
  obtain ⟨Y, Q, hFullQ, hMQ, hSharpQ, -, e, he, -, -⟩ :=
    HironakaCompactFootprintSharpExtension.exists_current_sharp_joint_test_extension
      N F (geometricTemplate N F) hN IdealWeightPowers.isCoherent_unitIdeal V K hK hKV TU hOverK
      hFullPull hMPull hSharpU
  refine ⟨Y, Q, hMQ, hFullQ, hSharpQ, ?_⟩
  intro z hz hzV
  obtain ⟨hTN, hTE, -⟩ := tuple_open_iso hN F V Q hMQ TU e he
  let w : openPreimage Q V := ⟨z, hzV⟩
  let z' : Z := e.symm w
  have hew : e z' = w := e.apply_symm_apply w
  have hNsame : (geoTransformAlong (geometricTemplate NU []) TU).N =
      (geoTransformAlong (geometricTemplate NU FU) TU).N := by
    have h0 : (geoTransformAlong (geometricTemplate NU []) TU).N = strictAlong TU NU :=
      N_geoTransformAlong _ TU
    have h1 : (geoTransformAlong (geometricTemplate NU FU) TU).N = strictAlong TU NU :=
      N_geoTransformAlong _ TU
    rw [h0, h1]
  have hAN : (geoTransformAlong (geometricTemplate N F) Q).N = strictAlong Q N :=
    N_geoTransformAlong _ Q
  have hz'N : z' ∈ (geoTransformAlong (geometricTemplate NU []) TU).N := by
    rw [hNsame, hTN]
    change (e z').val ∈ (geoTransformAlong (geometricTemplate N F) Q).N
    rw [hew, hAN]
    exact hz
  have hNC0 := hNCU z' hz'N
  have hEsame : (geoTransformAlong (geometricTemplate (univ : Set (CMfd.of (n := n) V)) FU) TU).E =
      (geoTransformAlong (geometricTemplate NU FU) TU).E := template_E_eq _ _ FU TU
  have hNC1 : normalCrossingsAt (n := n) (geoTransformAlong (geometricTemplate NU FU) TU).N
      (geoTransformAlong (geometricTemplate NU FU) TU).E z' := by
    rw [← hNsame, ← hEsame]
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

/-- **One piece appended to an actual prefix of the original problem.**  At an actual prefix `T` of
`(W, E)` (both tests, current sharp centres) at which the strict carrier has normal crossings with the
current boundary over a set `D`, the phase of the piece `dimPiece W m` (run for the current problem on
the open preimage of `pieceOpen`) gives an actual prefix `T·S` with normal crossings over
`D ∪ dimPiece W m`. -/
theorem exists_piece_step (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E))
    (m : ℕ)
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
      ∀ z ∈ strictAlong (T.append S) W, (T.append S).proj z ∈ D ∪ dimPiece W m →
        normalCrossingsAt (n := n) (strictAlong (T.append S) W)
          (geoTransformAlong (geometricTemplate (univ : Set X) E) (T.append S)).E z := by
  let N := strictAlong T W
  let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E
  obtain ⟨hNsm, hSNC, -, hDen, -⟩ :=
    actual_recorded_tower_residual_dictionary hn hW hE hdense T hT hFull
  have hNdef : (geoTransformAlong (geometricTemplate W []) T).N = N := N_geoTransformAlong _ T
  have hFdef : E.map (strictAlong T) ++ (geoTransformAlong (geometricTemplate W []) T).E = F := by
    have h := full_boundary_split W E [] T
    simp only [List.append_nil] at h
    exact h.symm
  have hN : IsClosedSubmanifold n N := by
    rw [← hNdef]
    exact hNsm
  have hF : IsSNCDivisor n F := by
    rw [← hFdef]
    exact hSNC
  have hdenseN : N ⊆ closure (N \ ⋃ H ∈ F, H) := by
    rw [← hNdef, ← hFdef]
    exact hDen
  let O := pieceOpen hW.1 m
  let V : Opens Y := openPreimage T O
  let G : Set Y := T.proj ⁻¹' dimPiece W m
  have hGV : G ⊆ V := fun z hz => dimPiece_subset_pieceOpen hW.1 m hz
  have hNVG : N ∩ V ⊆ G := fun z hz =>
    mem_dimPiece_of_mem_pieceOpen hW.1 m
      (MemberInterTowerAlong.strictAlong_subset_preimage T hW.1 hz.1) hz.2
  obtain ⟨hFoot, -⟩ :=
    HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint hW.1 hE.1 T hSharp
  have hKT : IsCompact (originalSharpBadLocus (n := n) N F ∩ G) := by
    have hc : IsCompact (T.proj ⁻¹' originalSharpBadLocus (n := n) W E) :=
      (HironakaLocalPrincipalization.isProperMap_proj T).isCompact_preimage hK
    refine hc.of_isClosed_subset ?_ (fun z hz => hFoot hz.1)
    exact (isClosed_originalSharpBadLocus hN.1 hF.1).inter
      ((isClosed_dimPiece hW m).preimage T.contMDiff_proj.continuous)
  have hReg : ∀ y ∈ N, y ∈ V → RegularAtDim (n := n) N y m := by
    intro y hy hyV
    have hTO := isGeoTestTower_restrict O hW IdealWeightPowers.isCoherent_unitIdeal T hT
    rw [template_pullback (Y := CMfd.of (n := n) O) (Subtype.val : O → X) W []] at hTO
    simp only [List.map_nil] at hTO
    have hpure : ∀ x ∈ (Subtype.val : O → X) ⁻¹' W,
        RegularAtDim (n := n) ((Subtype.val : O → X) ⁻¹' W) x m := by
      intro x hx
      exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr
        (mem_dimPiece_of_mem_pieceOpen hW.1 m hx x.property).2
    obtain ⟨-, hr⟩ := HironakaG34CarrierPureDimension.geoTransformAlong_N_regularAtDim
      (X := CMfd.of (n := n) O) (geometricTemplate ((Subtype.val : O → X) ⁻¹' W) [])
      (hW.1.preimage continuous_subtype_val) hpure (restrict O T) hTO
    let p : openPreimage T O := ⟨y, hyV⟩
    have hNr : (geoTransformAlong (geometricTemplate ((Subtype.val : O → X) ⁻¹' W) [])
        (restrict O T)).N = (Subtype.val : openPreimage T O → Y) ⁻¹' N := by
      rw [N_geoTransformAlong]
      exact strictAlong_restrict O T W
    have hp : p ∈ (geoTransformAlong (geometricTemplate ((Subtype.val : O → X) ⁻¹' W) [])
        (restrict O T)).N := by
      rw [hNr]
      exact hy
    have hrp := hr p hp
    rw [hNr] at hrp
    exact AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hrp
  obtain ⟨Z, S, hSM, hSFull, hSSharp, hSNC'⟩ :=
    exists_piece_phase hn hN hF hdenseN V G hGV hNVG hKT m hReg
  refine ⟨Z, S, ?_, ?_, ?_, ?_⟩
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
    · exact hSNC' z hz (dimPiece_subset_pieceOpen hW.1 m hzP)

/-- A finite actual sharp cleanup for a closed smooth carrier with compact
original sharp bad locus, allowing all local dimensions at once. -/
theorem exists_actual_compact_sharp_cleanup
    (hn : 0 < n) {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hdense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (U : BlowupTower X Y),
      let A := geoTransformAlong (geometricTemplate W []) U
      let F := (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
      IsGeoTestTower (geometricTemplate W []) U ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) U ∧
      CurrentSharpCentres W E U ∧
      CentresOver (originalSharpBadLocus (n := n) W E) U ∧
      IsClosedSubmanifold n A.N ∧ IsSNCDivisor n F ∧ HasNormalCrossings n A.N F ∧
      IsProperMap U.proj ∧ IsIsomorphismOver n U.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  have hDim : ∀ x ∈ W, ∃ m ≤ n, RegularAtDim (n := n) W x m := by
    intro x hx
    obtain ⟨m, hm⟩ := hW.2 x hx
    exact ⟨m, hm.1, hm⟩
  have key : ∀ k : ℕ, k ≤ n + 1 → ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate W []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres W E T ∧
      ∀ z ∈ strictAlong T W, T.proj z ∈ {x | ∃ m < k, x ∈ dimPiece W m} →
        normalCrossingsAt (n := n) (strictAlong T W)
          (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E z := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨X, .refl, trivial, trivial, trivial,
        fun z _ hz => absurd hz.choose_spec.1 (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨Y, T, hT, hFull, hSharp, hD⟩ := ih (by omega)
      obtain ⟨Z, S, hTS, hFullS, hSharpS, hNC⟩ :=
        exists_piece_step hn hW hE hdense hK k T hT hFull hSharp _ hD
      refine ⟨Z, T.append S, hTS, hFullS, hSharpS, fun z hz hzk => hNC z hz ?_⟩
      obtain ⟨m, hm, hmem⟩ := hzk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
      · exact Or.inl ⟨m, h, hmem⟩
      · subst h
        exact Or.inr hmem
  obtain ⟨Y, U, hU, hFullU, hSharpU, hNCU⟩ := key (n + 1) le_rfl
  obtain ⟨-, hOver⟩ :=
    HironakaG4SharpBadFootprint.currentSharpCentres_original_footprint hW.1 hE.1 U hSharpU
  obtain ⟨hNsm, hSNC, -, -, -⟩ :=
    actual_recorded_tower_residual_dictionary hn hW hE hdense U hU hFullU
  have hFdef : E.map (strictAlong U) ++ (geoTransformAlong (geometricTemplate W []) U).E =
      (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E := by
    have h := full_boundary_split W E [] U
    simp only [List.append_nil] at h
    exact h.symm
  have hAN : (geoTransformAlong (geometricTemplate W []) U).N = strictAlong U W :=
    N_geoTransformAlong _ U
  refine ⟨Y, U, hU, hFullU, hSharpU, hOver, hNsm, ?_, ?_,
    HironakaLocalPrincipalization.isProperMap_proj U,
    HironakaSharpOriginalDynamicGoodPrefixes.isIsomorphismOver_proj_of_centresOver _ U hOver⟩
  · rw [← hFdef]
    exact hSNC
  · show HasNormalCrossings n (geoTransformAlong (geometricTemplate W []) U).N
      (geoTransformAlong (geometricTemplate (univ : Set X) E) U).E
    rw [hAN]
    intro z hz
    have hzW : U.proj z ∈ W := MemberInterTowerAlong.strictAlong_subset_preimage U hW.1 hz
    obtain ⟨m, hm, hreg⟩ := hDim _ hzW
    exact hNCU z hz ⟨m, by omega, hzW, hreg⟩


end

end Hironaka.HironakaG4MixedDimensionCompactCleanup
