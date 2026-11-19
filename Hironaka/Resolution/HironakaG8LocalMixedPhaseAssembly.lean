import Hironaka.Resolution.HironakaG8SmoothBoundaryTowerTransport
import Hironaka.Resolution.HironakaG8LocalPureFinish

/-! Finite relative smooth-boundary phases and a literal saturated
concatenation of a partial phase with a terminal phase. -/

set_option autoImplicit false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8LocalMixedPhaseAssembly

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealTowerTransport MaxLocusLocal
  HironakaEmbeddedAnalytic HironakaStageCenters NormalCrossings NormalCrossingsInvariance
  HironakaActualSmoothBoundaryCleanup HironakaG8LocalPureFinish HironakaG8SeparatedSmoothPhases
  HironakaG8SmoothBoundaryTowerTransport HironakaSaturatedTowerAppend
  HironakaG8UniverseBMTransport HironakaG3BoundaryRestrictInitialList HironakaEmbeddedBoundary
  HironakaG3CentresOverGenericFactor HironakaCoherentTransformExtension HironakaActualGeometricCleanupComposition
  HironakaSharpActualFiniteChronologicalHistory HironakaNormalCrossingsOpenRestrictionSeparation

/-- A finite terminal smooth-boundary history on an actual original open. -/
abbrev LocalSmoothTower {n : ℕ} {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) (K : Set X) : Prop :=
  ∃ O : Opens X, K ⊆ O ∧ ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
    SmoothBoundaryTower ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) T

/-- Data retained on the actual smooth suffix, stable under the two
physical maps used to place it on literal saturated windows. -/
structure SmoothTailCertificate (n : ℕ) where
  holds : ∀ {X Y : CMfd.{0} n}, Set X → List (Set X) → BlowupTower X Y → Prop
  restrictOpen : ∀ {X Y : CMfd.{0} n} {W : Set X} {E : List (Set X)}
    {T : BlowupTower X Y}, holds W E T → ∀ O : Opens X,
      holds ((Subtype.val : O → X) ⁻¹' W) (E.map ((Subtype.val : O → X) ⁻¹' ·)) (restrict O T)
  ofTowerIso : ∀ {X X' Y Y' : CMfd.{0} n} {W : Set X} {E : List (Set X)}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'}
    {φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y},
    IsTowerIso φ T' T χ → holds W E T → holds (φ ⁻¹' W) (E.map (φ ⁻¹' ·)) T'

/-- Discarding additional data recovers the original geometric service. -/
def SmoothTailCertificate.none (n : ℕ) : SmoothTailCertificate n where
  holds _ _ _ := True
  restrictOpen _ _ := trivial
  ofTowerIso _ _ := trivial

abbrev LocalSmoothTowerWithCarriers {n : ℕ} {X : CMfd.{0} n} (C : SmoothTailCertificate n)
    (W WCert : Set X) (E : List (Set X)) (K : Set X) : Prop :=
  ∃ O : Opens X, K ⊆ O ∧ ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
    let WO := (Subtype.val : O → X) ⁻¹' W
    let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
    SmoothBoundaryTower WO EO T ∧ C.holds ((Subtype.val : O → X) ⁻¹' WCert) EO T

abbrev LocalSmoothTowerWith {n : ℕ} {X : CMfd.{0} n} (C : SmoothTailCertificate n)
    (W : Set X) (E : List (Set X)) (K : Set X) : Prop :=
  LocalSmoothTowerWithCarriers C W W E K

theorem LocalSmoothTower.withoutExtra {n : ℕ} {X : CMfd.{0} n} {W K : Set X} {E : List (Set X)}
    (h : LocalSmoothTower W E K) : LocalSmoothTowerWith (SmoothTailCertificate.none n) W E K := by
  obtain ⟨O,hKO,Y,T,hT⟩ := h
  exact ⟨O,hKO,Y,T,hT,trivial⟩

/-- The smooth positions depend on the literal full boundary only. A
unit geometric record and the mark-one carrier record give the same positions. -/
theorem smooth_stages_iff_markOne {n : ℕ} {X : CMfd.{0} n} (W : Set X) (E : List (Set X)) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      SmoothBoundaryStages W E T ↔ StageCentres (fun P C =>
        (IsClosedSubmanifold n (strictTransform n P.proj W) ∧
          C ⊆ strictTransform n P.proj W ∩ ⋃ H ∈ (geoTransformAlong (actualSmoothBoundaryMarked W E) P).E, H) ∧
        HasNormalCrossings n C (geoTransformAlong (actualSmoothBoundaryMarked W E) P).E) T
  | _, .refl => Iff.rfl
  | _, @BlowupTower.step _ _ Y Z T C π hπ => by
    let H := strictTransform n T.proj W
    let B := (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E
    let B' := (geoTransformAlong (actualSmoothBoundaryMarked W E) T).E
    change (SmoothBoundaryStages W E T ∧
      (IsClosedSubmanifold n H ∧ C ⊆ H ∩ ⋃ D ∈ B, D) ∧ HasNormalCrossings n C B) ↔
      (StageCentres _ T ∧ (IsClosedSubmanifold n H ∧ C ⊆ H ∩ ⋃ D ∈ B', D) ∧ HasNormalCrossings n C B')
    have hEq : B = B' := geoTransformAlong_E_eq_of_E_eq (𝔍 := geometricTemplate (univ : Set X) E)
      (𝔪 := actualSmoothBoundaryMarked W E) rfl T
    rw [hEq]
    exact and_congr_left' (smooth_stages_iff_markOne W E T)

/-- The held pure cleanup provides the literal smooth stage and footprint
certificate needed to serve one dimension part. -/
theorem pure_local_smooth_tower_with_cleanup {n d : ℕ} {X : CMfd.{0} n}
    {W : Set X} (hW : IsClosedSubmanifold n W) (hPure : ∀ x ∈ W, RegularAtDim (n := n) W x d)
    (hd : d < n) (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (K : Set X) (hK : IsCompact K) :
    ∃ O : Opens X, K ⊆ O ∧
      let A := CMfd.of (n := n) O
      let WO : Set A := (Subtype.val : O → X) ⁻¹' W
      let EO : List (Set A) := E.map ((Subtype.val : O → X) ⁻¹' ·)
      ∃ (Y : CMfd.{0} n) (T : BlowupTower A Y) (hEO : IsSNCDivisor n EO),
        ActualSmoothBoundaryCleanupResult WO EO d hEO T ∧ SmoothBoundaryTower WO EO T := by
  obtain ⟨O, hKO, hEO, Y, T, h⟩ := exists_actual_local_smooth_boundary_cleanup W E hW d hd hPure hE hDense hK
  have hCleanup := h
  obtain ⟨_, hTest, hAvoid, hSteps, _, hSmooth, _, hStrict, _, hNC, hSNC, _⟩ := h
  let WO := (Subtype.val : O → X) ⁻¹' W
  let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let M := actualSmoothBoundaryMarked (X := CMfd.of (n := n) O) WO EO
  let G := geometricTemplate (univ : Set (CMfd.of (n := n) O)) EO
  have hWOS : IsClosedSubmanifold n WO := BlowupRestrictOpen.isClosedSubmanifold_preimage_val hW O
  obtain ⟨hFoot, hStage⟩ := smooth_positions_and_footprint WO hWOS EO hEO
    (dense_complement_restrict W E hDense O) T hTest hAvoid hSteps
  have hEeq : (geoTransformAlong G T).E = (geoTransformAlong M T).E :=
    geoTransformAlong_E_eq_of_E_eq (𝔍 := G) (𝔪 := M) rfl T
  rw [hStrict] at hSmooth hNC
  exact ⟨O, hKO, Y, T, hEO, hCleanup, geometric_test_of_test M EO (List.Sublist.refl _) T hTest,
    hFoot, (smooth_stages_iff_markOne WO EO T).mpr hStage, hSmooth, hEeq.symm ▸ hSNC, hEeq.symm ▸ hNC⟩

/-- The held pure cleanup provides the literal smooth stage and footprint
certificate needed to serve one dimension part. -/
theorem pure_local_smooth_tower {n d : ℕ} {X : CMfd.{0} n}
    {W : Set X} (hW : IsClosedSubmanifold n W) (hPure : ∀ x ∈ W, RegularAtDim (n := n) W x d)
    (hd : d < n) (E : List (Set X)) (hE : IsSNCDivisor n E) (hDense : W ⊆ closure (W \ ⋃ H ∈ E, H))
    (K : Set X) (hK : IsCompact K) : LocalSmoothTower W E K := by
  obtain ⟨O, hKO, Y, T, _, _, hT⟩ :=
    pure_local_smooth_tower_with_cleanup hW hPure hd E hE hDense K hK
  exact ⟨O, hKO, Y, T, hT⟩

/-- Restrict a local terminal smooth phase over the saturated compact task.
The new suffix starts on the literal endpoint of the restricted prefix. -/
theorem restrict_local_smooth_phase_with_certified_carrier {n : ℕ} {X Y : CMfd.{0} n} {W WCert : Set X}
    (C : SmoothTailCertificate n) (E : List (Set X)) (hE : IsSNCDivisor n E) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (K : Set X) (phase : LocalSmoothTowerWithCarriers C (strictTransform n T.proj W) (strictTransform n T.proj WCert)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E (T.proj ⁻¹' K)) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{0} n)
      (R : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
      let WO := (Subtype.val : O → X) ⁻¹' W
      let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
      let A := strictTransform n (restrict O T).proj WO
      let B := (geoTransformAlong (geometricTemplate (univ : Set (CMfd.of (n := n) O)) EO) (restrict O T)).E
      let ACert := strictTransform n (restrict O T).proj ((Subtype.val : O → X) ⁻¹' WCert)
      SmoothBoundaryTower A B R ∧ C.holds ACert B R := by
  obtain ⟨V, hKV, Z, S, hS, hC⟩ := phase
  obtain ⟨O, hKO, hOV, _⟩ := exists_saturated_tower_append T K V hKV S
  let U := openPreimage T O
  let D := nestedOpens V U
  let e := (nestedOpensDiffeo (n := n) hOV).symm
  let L := restrict O T
  let R := transport e (restrict D S)
  let WO := (Subtype.val : O → X) ⁻¹' W
  let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
  let M := geometricTemplate (univ : Set X) E
  let MO := geometricTemplate (univ : Set (CMfd.of (n := n) O)) EO
  let ET := (geoTransformAlong M T).E
  let AV := (Subtype.val : V → Y) ⁻¹' strictTransform n T.proj W
  let EV := ET.map ((Subtype.val : V → Y) ⁻¹' ·)
  have hM : M.IsWellFormed := ⟨HomogenizedGlueingTower.isClosedSubmanifold_univ,
    IdealWeightPowers.isCoherent_unitIdeal, hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  have hET : IsSNCDivisor n ET := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hT).isSNCDivisor
  have hEV : IsSNCDivisor n EV := isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hET
  have hED := isSNCDivisor_map_preimage (pullsBackCoordinates_val D) continuous_subtype_val hEV
  have hAD : IsClosed ((Subtype.val : D → V) ⁻¹' AV) :=
    (show IsClosed (strictTransform n T.proj W) from isClosed_closure).preimage
      (continuous_subtype_val.comp continuous_subtype_val)
  have hS' := smoothTower_rebase e hAD hED (restrict D S) (smoothTower_restrict S hS D)
  have hStrict : strictTransform n L.proj WO = e ⁻¹' ((Subtype.val : D → V) ⁻¹' AV) :=
    strictTransform_restricted_tower O T W
  have hBoundary := boundary_restrict_of_initial_eq M O MO rfl T
  have hList : (geoTransformAlong MO L).E = (EV.map ((Subtype.val : D → V) ⁻¹' ·)).map (e ⁻¹' ·) := by
    rw [hBoundary]
    dsimp only [EV, ET]
    rw [List.map_map, List.map_map]
    rfl
  have hTail : SmoothBoundaryTower (strictTransform n L.proj WO) (geoTransformAlong MO L).E R.tower := by
    rw [hStrict, hList]
    exact hS'
  have hCert := C.ofTowerIso (transport_isTowerIso e (restrict D S)) (C.restrictOpen hC D)
  let CO := (Subtype.val : O → X) ⁻¹' WCert
  have hStrictCert : strictTransform n L.proj CO =
      e ⁻¹' ((Subtype.val : D → V) ⁻¹' ((Subtype.val : V → Y) ⁻¹' strictTransform n T.proj WCert)) :=
    strictTransform_restricted_tower O T WCert
  have hCert' : C.holds (strictTransform n L.proj CO) (geoTransformAlong MO L).E R.tower := by
    rw [hStrictCert,hList]
    exact hCert
  exact ⟨O, hKO, R.target, R.tower, hTail,hCert'⟩

/-- Restrict a local terminal smooth phase over the saturated compact task.
The new suffix starts on the literal endpoint of the restricted prefix. -/
theorem restrict_local_smooth_phase_with_certificate {n : ℕ} {X Y : CMfd.{0} n} {W : Set X}
    (C : SmoothTailCertificate n) (E : List (Set X)) (hE : IsSNCDivisor n E) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (K : Set X) (phase : LocalSmoothTowerWith C (strictTransform n T.proj W)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E (T.proj ⁻¹' K)) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{0} n)
      (R : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
      let WO := (Subtype.val : O → X) ⁻¹' W
      let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
      let A := strictTransform n (restrict O T).proj WO
      let B := (geoTransformAlong (geometricTemplate (univ : Set (CMfd.of (n := n) O)) EO) (restrict O T)).E
      SmoothBoundaryTower A B R ∧ C.holds A B R := by
  exact restrict_local_smooth_phase_with_certified_carrier (WCert := W) C E hE T hT K phase

/-- Restrict the original geometric smooth phase to its literal saturated task. -/
theorem restrict_local_smooth_phase {n : ℕ} {X Y : CMfd.{0} n} {W : Set X}
    (E : List (Set X)) (hE : IsSNCDivisor n E) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (K : Set X) (phase : LocalSmoothTower (strictTransform n T.proj W)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E (T.proj ⁻¹' K)) :
    ∃ O : Opens X, K ⊆ O ∧ ∃ (Z : CMfd.{0} n)
      (R : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z),
      let WO := (Subtype.val : O → X) ⁻¹' W
      let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
      SmoothBoundaryTower (strictTransform n (restrict O T).proj WO)
        (geoTransformAlong (geometricTemplate (univ : Set (CMfd.of (n := n) O)) EO) (restrict O T)).E R := by
  obtain ⟨O,hKO,Z,R,hR,_⟩ := restrict_local_smooth_phase_with_certificate
    (SmoothTailCertificate.none n) E hE T hT K phase.withoutExtra
  exact ⟨O,hKO,Z,R,hR⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
/-- Append the resulting suffix to the literal restricted smooth prefix. -/
theorem append_smooth_phase_on_open {n : ℕ} {X Y : CMfd.{0} n} {W : Set X} (hW : IsClosed W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (T : BlowupTower X Y)

    (hOver : CentresOver (W ∩ ⋃ H ∈ E, H) T) (hStage : SmoothBoundaryStages W E T)
    (O : Opens X) {Z : CMfd.{0} n}
    (R : BlowupTower (CMfd.of (n := n) (openPreimage T O)) Z) :
    let A := CMfd.of (n := n) O
    let WO := (Subtype.val : O → X) ⁻¹' W
    let EO := E.map ((Subtype.val : O → X) ⁻¹' ·)
    let L := restrict O T
    SmoothBoundaryTower (strictTransform n L.proj WO)
        (geoTransformAlong (geometricTemplate (univ : Set A) EO) L).E R →
      SmoothBoundaryTower WO EO (L.append R) := by
  intro A WO EO L hTail
  let XO := CMfd.of (n := n) O
  let YO := CMfd.of (n := n) (openPreimage T O)
  have hLStages : SmoothBoundaryStages WO EO L := smoothBoundaryStages_restrict W E O T hStage
  have hLOver : CentresOver (WO ∩ ⋃ H ∈ EO, H) L := by
    have h := centresOver_restrict O (W ∩ ⋃ H ∈ E, H) T hOver
    rw [preimage_inter, preimage_biUnion_list] at h
    exact h
  have hEO : IsSNCDivisor n EO :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
  have hWO : IsClosed WO := hW.preimage continuous_subtype_val
  have hLTest : IsGeoTestTower (geometricTemplate (univ : Set XO) EO) L :=
    bm_stage_test WO EO L (smoothBoundaryStages_bmStages hLStages)
  exact smoothTower_append_of_terminal (X := XO) (Y := YO) (Z := Z) (W := WO) (E := EO)
    hWO hEO L hLTest hLOver hLStages R hTail

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1500000 in
/-- Append the resulting suffix to the literal restricted smooth prefix. -/
theorem append_local_smooth_phase {n : ℕ} {X Y : CMfd.{0} n} {W : Set X} (hW : IsClosed W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (T : BlowupTower X Y)
    (hT : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    (hOver : CentresOver (W ∩ ⋃ H ∈ E, H) T) (hStage : SmoothBoundaryStages W E T)
    (K : Set X) (phase : LocalSmoothTower (strictTransform n T.proj W)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E (T.proj ⁻¹' K)) :
    LocalSmoothTower W E K := by
  obtain ⟨O, hKO, Z, R, hTail⟩ := restrict_local_smooth_phase E hE T hT K phase
  exact ⟨O, hKO, Z, (restrict O T).append R,
    append_smooth_phase_on_open hW E hE T hOver hStage O R hTail⟩

/-- Replace a nested source open by its literal ambient image open. -/
theorem flatten_local_smooth_tower_with_tower {n : ℕ} {X : CMfd.{0} n} {W K : Set X} (hW : IsClosed W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (V : Opens X) (hKV : K ⊆ V)
    (U : Opens (CMfd.of (n := n) V)) (hKU : (Subtype.val : V → X) ⁻¹' K ⊆ U)
    {Y : CMfd.{0} n} (T : BlowupTower (CMfd.of (n := n) U) Y)
    (hT : SmoothBoundaryTower ((Subtype.val : U → V) ⁻¹' ((Subtype.val : V → X) ⁻¹' W))
      ((E.map ((Subtype.val : V → X) ⁻¹' ·)).map ((Subtype.val : U → V) ⁻¹' ·)) T) :
    ∃ O : Opens X, K ⊆ O ∧
      ∃ e : (CMfd.of (n := n) O) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ (CMfd.of (n := n) U),
        (∀ x : O, (e x).val.val = x.val) ∧
        SmoothBoundaryTower ((Subtype.val : O → X) ⁻¹' W)
          (E.map ((Subtype.val : O → X) ⁻¹' ·)) (transport e T).tower := by
  let O : Opens X := ⟨(Subtype.val : V → X) '' (U : Set V), V.isOpen.isOpenMap_subtype_val _ U.isOpen⟩
  have hOV : O ≤ V := by rintro _ ⟨x, _, rfl⟩; exact x.property
  have hVU (x : V) : x ∈ U ↔ x.val ∈ O :=
    ⟨fun hx => ⟨x,hx,rfl⟩, fun ⟨p,hp,he⟩ => (Subtype.ext he : p = x) ▸ hp⟩
  let e := (nestedDiffeo (n := n) V U O hVU hOV).symm
  let R := transport e T
  let EU := (E.map ((Subtype.val : V → X) ⁻¹' ·)).map ((Subtype.val : U → V) ⁻¹' ·)
  have hEU : IsSNCDivisor n EU := isSNCDivisor_map_preimage (pullsBackCoordinates_val U)
    continuous_subtype_val (isSNCDivisor_map_preimage (pullsBackCoordinates_val V) continuous_subtype_val hE)
  have hWU := hW.preimage (continuous_subtype_val.comp continuous_subtype_val :
    Continuous (fun x : U => (x.val : V).val))
  have hRoot := smoothTower_rebase e hWU hEU T hT
  have hList : EU.map (e ⁻¹' ·) = E.map ((Subtype.val : O → X) ⁻¹' ·) := by
    dsimp only [EU]
    rw [List.map_map, List.map_map]
    rfl
  rw [hList] at hRoot
  exact ⟨O, fun x hx => ⟨⟨x,hKV hx⟩, hKU hx, rfl⟩, e, fun _ => rfl, hRoot⟩
/-- Replace a nested source open by its literal ambient image open. -/
theorem flatten_local_smooth_tower {n : ℕ} {X : CMfd.{0} n} {W K : Set X} (hW : IsClosed W)
    (E : List (Set X)) (hE : IsSNCDivisor n E) (V : Opens X) (hKV : K ⊆ V)
    (h : LocalSmoothTower (X := CMfd.of (n := n) V) ((Subtype.val : V → X) ⁻¹' W)
      (E.map ((Subtype.val : V → X) ⁻¹' ·)) ((Subtype.val : V → X) ⁻¹' K)) : LocalSmoothTower W E K := by
  obtain ⟨U, hKU, Y, T, hT⟩ := h
  obtain ⟨O, hKO, e, _, hR⟩ := flatten_local_smooth_tower_with_tower hW E hE V hKV U hKU T hT
  exact ⟨O, hKO, (transport e T).target, (transport e T).tower, hR⟩

end
end Hironaka.HironakaG8LocalMixedPhaseAssembly
