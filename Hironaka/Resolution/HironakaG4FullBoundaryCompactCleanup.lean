import Hironaka.Resolution.HironakaG4MixedDimensionCompactCleanup
import Hironaka.Resolution.HironakaActualFullBoundaryMixedPatterns
import Hironaka.Resolution.HironakaG3FiniteDisjointTowerMerge
import Hironaka.Resolution.HironakaG8EmptyAwareTestTransport
import Hironaka.Resolution.HironakaSharpActualCurveGlobalPrefixTests
import Hironaka.Resolution.HironakaG3EmptyAwareFullBoundary
import Hironaka.Resolution.HironakaOriginalStoppedBoundaryTransport

/-!
# Compact sharp cleanup with arbitrary full-boundary containment

The retained-boundary cleanup runs separately on the finite mixed-dimensional
containment pieces. Physical disjoint merging preserves the original tests,
current sharp centres, full endpoint geometry, and the original good locus.

Blueprint: `hironaka-g4-compact-full-boundary-cleanup.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG4FullBoundaryCompactCleanup

noncomputable section

attribute [local instance] Classical.propDecidable

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms HomogenizedGlueingTower RestrictEmptyTower
  MemberInterTowerAlong MarkedIdeals MarkedIdeals.MarkedIdeal NormalCrossings
  NormalCrossingsComparison HironakaEmbeddedAnalytic HironakaStageCenters
  CoefficientIdealRestriction HironakaSharpOriginalMultiBoundaryBadLocus
  HironakaSharpNormalCrossingsOpenLocus HironakaG4CompactWholeMonomialMaskPhase
  HironakaSharpOriginalAllBoundaryCentre
  HironakaActualFullBoundaryContainmentPatterns HironakaActualFullBoundaryMixedPatterns
  HironakaG3FiniteDisjointTowerMerge
  HironakaG3EmptyAwareHistory HironakaG34NonPureLowDim
  HironakaSharpActualFiniteChronologicalHistory HironakaG8EmptyAwareTestTransport
  MarkedIdealRestrictOpen HironakaSharpActualCurveGlobalPrefixTests
  MarkedIdealBiholomorphism
  HironakaNormalCrossingsOpenRestrictionSeparation MarkedIdealTowerTransport
  ResolutionInvariantExt SimultaneousNormalCrossings HironakaG3EmptyAwareOldSlots
  HironakaG3EmptyAwareFullBoundary

universe u

variable {n : ℕ} {X : CMfd.{u} n}

private theorem ambient_template_wellFormed {E : List (Set X)} (hE : IsSNCDivisor n E) :
    (geometricTemplate (univ : Set X) E).IsWellFormed :=
  ⟨isClosedSubmanifold_univ, IdealWeightPowers.isCoherent_unitIdeal, hE,
    isTransverse_univ_of_isSNCDivisor hE⟩

private theorem carrier_template_wellFormed {W : Set X} (hW : IsClosedSubmanifold n W) :
    (geometricTemplate W []).IsWellFormed :=
  ⟨hW, IdealWeightPowers.isCoherent_unitIdeal, isSNCDivisor_nil,
    isTransverse_nil_of_isClosedSubmanifold hW⟩

/-- Pointwise normal crossings depends only on the incident boundary members. -/
theorem normalCrossingsAt_of_incident_mem {C : Set X} {L L' : List (Set X)} {x : X}
    (hmem : ∀ H ∈ L, x ∈ H → H ∈ L') (h : normalCrossingsAt (n := n) C L' x) :
    normalCrossingsAt (n := n) C L x := by
  classical
  obtain ⟨S₀, S, hcoord, hcard⟩ := h
  have hj : ∀ (i : Fin L.length), x ∈ L.get i → ∃ j : Fin L'.length, L'.get j = L.get i := by
    intro i hi
    exact List.get_of_mem (hmem _ (List.get_mem _ _) hi)
  let idx (i : Fin L.length) (hi : x ∈ L.get i) : Fin L'.length := Classical.choose (hj i hi)
  have hidx (i : Fin L.length) (hi : x ∈ L.get i) : L'.get (idx i hi) = L.get i :=
    Classical.choose_spec (hj i hi)
  let S' (i : Fin L.length) := if hi : x ∈ L.get i then S (idx i hi) else ∅
  obtain ⟨Φ, hsrc, h0, hchart⟩ := hcoord
  refine ⟨S₀, S', ⟨Φ, hsrc, h0, ?_⟩, ?_⟩
  · rintro (_ | i) hi z hz hzΦ
    · exact hchart none hi hz hzΦ
    · change x ∈ L.get i at hi
      have hxi : x ∈ L'.get (idx i hi) := by rw [hidx i hi]; exact hi
      have hh := hchart (some (idx i hi)) hxi hz hzΦ
      change z ∈ L'.get (idx i hi) ↔ _ at hh
      rw [hidx i hi] at hh
      simpa only [Option.elim_some, S', dif_pos hi] using hh
  · intro i hi
    have hxi : x ∈ L'.get (idx i hi) := by rw [hidx i hi]; exact hi
    simpa only [S', dif_pos hi] using hcard (idx i hi) hxi

/-- Removing empty members preserves each point's normal crossings condition. -/
theorem normalCrossingsAt_filter_nonempty_iff (C : Set X) (L : List (Set X)) (x : X) :
    normalCrossingsAt (n := n) C (L.filter (fun H => decide H.Nonempty)) x ↔
      normalCrossingsAt (n := n) C L x := by
  classical
  constructor
  · exact normalCrossingsAt_of_incident_mem (fun H hH hx => by simp [hH, show H.Nonempty from ⟨x, hx⟩])
  · exact normalCrossingsAt_of_incident_mem (fun _ hH _ => (List.mem_filter.mp hH).1)

/-- Keeping omitted containing members in the tower preserves the current
sharp bad condition of every chosen centre. -/
theorem currentSharpCentres_of_retained_boundary {A : Set X} {E F : List (Set X)}
    (hE : IsSNCDivisor n E) (hFE : F.Sublist E)
    (hContains : ∀ H ∈ E, H ∉ F → A ⊆ H) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), CentresIn A T →
      CurrentSharpCentres A F T → CurrentSharpCentres A E T
  | _, .refl, _, _ => trivial
  | _, .step T C π hπ, hIn, hSharp => by
    refine ⟨currentSharpCentres_of_retained_boundary hE hFE hContains T hIn.1 hSharp.1, ?_⟩
    intro x hx
    have hBad := hSharp.2 hx
    have hDrop := DropMembers.isGeoTestTower_withE_iff_of_centresIn
      (geometricTemplate (univ : Set X) E) (ambient_template_wellFormed hE)
      (E' := F) (fun _ h => hFE.subset h) hContains T hIn.1
    exact ⟨hBad.1, fun hNC =>
      hBad.2 (normalCrossingsAt_of_incident_mem (fun H hH _ => hDrop.2.1 H hH) hNC)⟩

/-- Retain every containing member on the actual sharp tower for a
carrier piece. The whole ambient test and sharp centre law follow from
the retained-boundary test on that same tower. -/
theorem retain_full_boundary_on_sharp_piece {A : Set X} {E F : List (Set X)}
    (hE : IsSNCDivisor n E) (hFE : F.Sublist E)
    (hContains : ∀ H ∈ E, H ∉ F → A ⊆ H)
    {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hATest : IsGeoTestTower (geometricTemplate A []) T)
    (hFTest : IsGeoTestTower (geometricTemplate (univ : Set X) F) T)
    (hFSharp : CurrentSharpCentres A F T)
    (hFNC : HasNormalCrossings n (strictAlong T A)
      (geoTransformAlong (geometricTemplate (univ : Set X) F) T).E) :
    IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
    CurrentSharpCentres A E T ∧ HasNormalCrossings n (strictAlong T A)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E := by
  have hInside : CentresIn A T :=
    centresIn_of_isGeoTestTower_withN (geometricTemplate (univ : Set X) []) A T hATest
  let M := geometricTemplate (univ : Set X) E
  have hM := ambient_template_wellFormed hE
  have hDrop := DropMembers.isGeoTestTower_withE_iff_of_centresIn M hM
    (E' := F) (fun _ h => hFE.subset h) hContains T hInside
  have hTest : IsGeoTestTower M T := hDrop.1.mp hFTest
  have hSNC := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM T hTest).isSNCDivisor
  exact ⟨hTest, currentSharpCentres_of_retained_boundary hE hFE hContains T hInside hFSharp,
    (hasNormalCrossings_iff_of_forall_mem hSNC hDrop.2.1 hDrop.2.2).mp hFNC⟩

/-- Perform compact sharp cleanup on one carrier piece while retaining the
whole original boundary. The omitted slots contain the piece and are
restored on the same tower. -/
theorem exists_compact_sharp_cleanup_piece (hn : 0 < n)
    {W A : Set X} {E F : List (Set X)}
    (hW : IsClosed W) (hA : IsClosedSubmanifold n A) (hAW : A ⊆ W)
    (hGerm : ∀ x ∈ A, ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ W)
    (hE : IsSNCDivisor n E) (hFE : F.Sublist E)
    (hContains : ∀ H ∈ E, H ∉ F → A ⊆ H)
    (hDense : A ⊆ closure (A \ ⋃ H ∈ F, H))
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{u} n) (T : BlowupTower X Y),
      CentresOver (originalSharpBadLocus (n := n) W E ∩ A) T ∧
      IsGeoTestTower (geometricTemplate A []) T ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) T ∧
      CurrentSharpCentres A E T ∧
      HasNormalCrossings n (strictAlong T A)
        (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E := by
  have hF := isSNCDivisor_of_sublist hE hFE
  have hBad := sharpBad_subset_full_of_carrier_germs hW hE hFE hAW hGerm
  have hCompactF := hK.of_isClosed_subset (isClosed_originalSharpBadLocus hA.1 hF.1)
    (hBad.trans inter_subset_left)
  obtain ⟨Y, T, hATest, hFTest, hFSharp, hFoot, _, _, hFNC, _, _⟩ :=
    HironakaG4MixedDimensionCompactCleanup.exists_actual_compact_sharp_cleanup hn hA hF hDense
      hCompactF
  rw [N_geoTransformAlong] at hFNC
  obtain ⟨hTest, hSharp, hNC⟩ :=
    retain_full_boundary_on_sharp_piece hE hFE hContains T hATest hFTest hFSharp hFNC
  exact ⟨Y, T, HironakaActualProcessedAllMasksDrop.centresOver_mono_local hBad T hFoot,
    hATest, hTest, hSharp, hNC⟩

section Small

variable {X Y Z : CMfd.{0} n}

private theorem pullback_carrier_template_congr (V : Opens X) {W A : Set X}
    (hEq : (Subtype.val : V → X) ⁻¹' W = (Subtype.val : V → X) ⁻¹' A) :
    MarkedIdeal.pullback (Subtype.val : V → X) (geometricTemplate W []) =
      MarkedIdeal.pullback (Subtype.val : V → X) (geometricTemplate A []) := by
  unfold MarkedIdeal.pullback geometricTemplate
  rw [hEq]

/-- Transfer a literal full geometric test across a physical comparison of
the same source open. Empty positions in either source tower are allowed. -/
theorem pullback_test_of_physical_comparison (V : Opens X)
    (Q : BlowupTower X Y) (T : BlowupTower X Z)
    (φ : (CMfd.of (n := n) (openPreimage Q V)) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      (CMfd.of (n := n) (openPreimage T V)))
    (hφ : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) V) ∞)
      (restrict V Q) (restrict V T) φ)
    (M : MarkedIdeal n X) (hM : M.IsWellFormed)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V T)) :
    IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V → X) M) (restrict V Q) := by
  let A : MarkedIdeal n (CMfd.of (n := n) V) := MarkedIdeal.pullback (Subtype.val : V → X) M
  have hA : A.IsWellFormed := IsWellFormed.pullback_val hM V
  have heq := isGeoTestTower_iff_of_emptyAware (n := n)
    (X₁ := CMfd.of (n := n) V) (X₂ := CMfd.of (n := n) V)
    (Y₁ := CMfd.of (n := n) (openPreimage Q V))
    (Y₂ := CMfd.of (n := n) (openPreimage T V))
    (T₁ := restrict V Q) (T₂ := restrict V T) (ψ := φ) A hA
    (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) V) ∞) hφ
  simp only [Diffeomorph.coe_refl] at heq
  rw [ContactCanonicalAlong.pullback_id A hA.isCoherent] at heq
  exact heq.mpr hTest

/-- Pointwise sharp bad geometry uses the actual strict carrier and retained
nonempty ordered boundary under a physical comparison. -/
theorem sharp_bad_iff_of_emptyAware {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂}
    {Q : BlowupTower X₁ Y₁} {T : BlowupTower X₂ Y₂}
    {φ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂}
    (hφ : EmptyAwareTowerIso Φ Q T φ) {A : Set X₂} (hA : IsClosed A)
    (M : MarkedIdeal n X₂) (hE : ∀ H ∈ M.E, IsClosed H) (x : Y₁) :
    x ∈ originalSharpBadLocus (n := n) (strictAlong Q (Φ ⁻¹' A))
      (geoTransformAlong (MarkedIdeal.pullback Φ M) Q).E ↔
    φ x ∈ originalSharpBadLocus (n := n) (strictAlong T A) (geoTransformAlong M T).E := by
  classical
  have hStrict := emptyAware_strictAlong_eq hφ A hA
  have hBound := full_boundary_transport hφ (MarkedIdeal.pullback Φ M) M rfl hE
  let G := (geoTransformAlong (MarkedIdeal.pullback Φ M) Q).E
  let F := (geoTransformAlong M T).E
  change (x ∈ strictAlong Q (Φ ⁻¹' A) ∧
    ¬normalCrossingsAt (n := n) (strictAlong Q (Φ ⁻¹' A)) G x) ↔
    (φ x ∈ strictAlong T A ∧ ¬normalCrossingsAt (n := n) (strictAlong T A) F (φ x))
  rw [hStrict]
  refine and_congr Iff.rfl (not_congr ?_)
  rw [← normalCrossingsAt_filter_nonempty_iff _ G x,
    ← normalCrossingsAt_filter_nonempty_iff _ F (φ x)]
  change G.filter _ = (F.filter _).map _ at hBound
  rw [hBound]
  exact ⟨normalCrossingsAt_of_preimage_diffeo φ, normalCrossingsAt_preimage_diffeo φ⟩

/-- Each literal centre on the left comparison is sharp when its matched
centre on the right is sharp. Left-only empty positions satisfy it as well. -/
theorem currentSharpCentres_of_emptyAware {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}
    {Φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂}
    {Q : BlowupTower X₁ Y₁} {T : BlowupTower X₂ Y₂}
    {φ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂}
    (hφ : EmptyAwareTowerIso Φ Q T φ) {A : Set X₂} (hA : IsClosed A)
    {E : List (Set X₂)} (hE : ∀ H ∈ E, IsClosed H) :
    CurrentSharpCentres A E T →
      CurrentSharpCentres (Φ ⁻¹' A) (E.map (Φ ⁻¹' ·)) Q := by
  induction hφ with
  | refl => exact fun _ => trivial
  | @step Y₁ Y₂ Z₁ Z₂ Q T χ hχ C₁ π hπ C₂ ρ hρ χ' hComm hC ih =>
    intro hSharp
    refine ⟨ih hSharp.1, ?_⟩
    intro x hx
    have hx₂ : χ x ∈ C₂ := by
      change x ∈ χ ⁻¹' C₂
      rwa [hC]
    have hBad := hSharp.2 hx₂
    let M := geometricTemplate (univ : Set X₂) E
    have h := (sharp_bad_iff_of_emptyAware hχ hA M hE x).mpr hBad
    have hBoundary := HironakaCoherentTransformExtension.geoTransformAlong_E_eq_of_E_eq
      (𝔍 := geometricTemplate (univ : Set X₁) (E.map (Φ ⁻¹' ·)))
      (𝔪 := MarkedIdeal.pullback Φ M) rfl Q
    change x ∈ originalSharpBadLocus (n := n) (strictAlong Q (Φ ⁻¹' A)) _
    rwa [hBoundary]
  | leftEmpty _ _ _ _ ih => exact fun hs => ⟨ih hs, empty_subset _⟩
  | rightEmpty _ _ _ _ ih => exact fun hs => ih hs.1

private theorem sharp_bad_restrict_iff (V : Opens X) (W : Set X) (E : List (Set X))
    (Q : BlowupTower X Y) (hTest : IsGeoTestTower (geometricTemplate (univ : Set X) E) Q)
    (x : openPreimage Q V) :
    x ∈ originalSharpBadLocus (n := n) (strictAlong (restrict V Q) ((Subtype.val : V → X) ⁻¹' W))
      (geoTransformAlong (geometricTemplate (univ : Set V) (E.map ((Subtype.val : V → X) ⁻¹' ·)))
        (restrict V Q)).E ↔
    x.val ∈ originalSharpBadLocus (n := n) (strictAlong Q W)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) Q).E := by
  let M := geometricTemplate (univ : Set X) E
  have hBoundary := congrArg MarkedIdeal.E
    (geoTransformAlong_restrict V isClosedSubmanifold_univ IdealWeightPowers.isCoherent_unitIdeal Q hTest)
  rw [template_pullback (Y := CMfd.of (n := n) V) (Subtype.val : V → X)
    (univ : Set X) E, preimage_univ] at hBoundary
  change (geoTransformAlong (geometricTemplate (univ : Set V) (E.map ((Subtype.val : V → X) ⁻¹' ·)))
      (restrict V Q)).E = (geoTransformAlong M Q).E.map
      ((Subtype.val : openPreimage Q V → Y) ⁻¹' ·) at hBoundary
  rw [strictAlong_restrict, hBoundary]
  exact and_congr Iff.rfl (not_congr normalCrossingsAt_preimage_val_iff)

private theorem currentSharpCentres_restrict (V : Opens X) (W : Set X) (E : List (Set X)) :
    ∀ {Y : CMfd.{0} n} (Q : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate (univ : Set X) E) Q → CurrentSharpCentres W E Q →
      CurrentSharpCentres ((Subtype.val : V → X) ⁻¹' W) (E.map ((Subtype.val : V → X) ⁻¹' ·))
        (restrict V Q)
  | _, .refl, _, _ => trivial
  | _, .step Q C π hπ, hTest, hSharp => by
    refine ⟨currentSharpCentres_restrict V W E Q hTest.1 hSharp.1, ?_⟩
    intro x hx
    exact (sharp_bad_restrict_iff V W E Q hTest.1 x).mpr (hSharp.2 hx)

private theorem currentSharpCentres_of_open_cover {ι : Type} (V : ι → Opens X)
    (hcover : ∀ x : X, ∃ i, x ∈ V i) (W : Set X) (E : List (Set X)) :
    ∀ {Y : CMfd.{0} n} (Q : BlowupTower X Y),
      IsGeoTestTower (geometricTemplate (univ : Set X) E) Q →
      (∀ i, CurrentSharpCentres ((Subtype.val : V i → X) ⁻¹' W)
        (E.map ((Subtype.val : V i → X) ⁻¹' ·)) (restrict (V i) Q)) →
      CurrentSharpCentres W E Q
  | _, .refl, _, _ => trivial
  | _, .step Q C π hπ, hTest, hLocal => by
    refine ⟨currentSharpCentres_of_open_cover V hcover W E Q hTest.1 fun i => (hLocal i).1, ?_⟩
    intro x hx
    obtain ⟨i, hi⟩ := hcover (Q.proj x)
    let xU : openPreimage Q (V i) := ⟨x, hi⟩
    exact (sharp_bad_restrict_iff (V i) W E Q hTest.1 xU).mp ((hLocal i).2
      (show xU ∈ (Subtype.val : openPreimage Q (V i) → _) ⁻¹' C from hx))

private theorem currentSharpCentres_of_empty {W : Set X} {E : List (Set X)} :
    ∀ {Y : CMfd.{0} n} (Q : BlowupTower X Y), IsEmptyTower Q → CurrentSharpCentres W E Q
  | _, .refl, _ => trivial
  | _, .step Q C π hπ, hEmpty => by
    refine ⟨currentSharpCentres_of_empty Q hEmpty.1, ?_⟩
    rw [hEmpty.2]
    exact empty_subset _

/-- On a shared source open, a physical comparison identifies the actual sharp
bad locus for carriers agreeing on that open and the same initial boundary. -/
theorem sharp_bad_on_open_iff_of_physical_comparison (V : Opens X)
    (Q : BlowupTower X Y) (T : BlowupTower X Z)
    (φ : (CMfd.of (n := n) (openPreimage Q V)) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      (CMfd.of (n := n) (openPreimage T V)))
    (hφ : EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (CMfd.of (n := n) V) ∞)
      (restrict V Q) (restrict V T) φ)
    {E : List (Set X)} (hE : IsSNCDivisor n E)
    (hQ : IsGeoTestTower (geometricTemplate (univ : Set X) E) Q)
    (hT : IsGeoTestTower (geometricTemplate (univ : Set X) E) T)
    {W A : Set X} (hA : IsClosed A)
    (hEq : (Subtype.val : V → X) ⁻¹' W = (Subtype.val : V → X) ⁻¹' A)
    (z : openPreimage Q V) :
    z.val ∈ originalSharpBadLocus (n := n) (strictAlong Q W)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) Q).E ↔
    (φ z).val ∈ originalSharpBadLocus (n := n) (strictAlong T A)
      (geoTransformAlong (geometricTemplate (univ : Set X) E) T).E := by
  let E₀ := E.map ((Subtype.val : V → X) ⁻¹' ·)
  let M₀ := geometricTemplate (univ : Set (CMfd.of (n := n) V)) E₀
  have hClosed : ∀ H ∈ E₀, IsClosed H := by
    rintro H hH
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hH
    exact (hE.1 J hJ).preimage continuous_subtype_val
  have heq := sharp_bad_iff_of_emptyAware hφ (hA.preimage continuous_subtype_val) M₀ hClosed z
  simp only [Diffeomorph.coe_refl, preimage_id] at heq
  rw [ContactCanonicalAlong.pullback_id M₀ IdealWeightPowers.isCoherent_unitIdeal] at heq
  refine (sharp_bad_restrict_iff V W E Q hQ z).symm.trans ?_
  rw [hEq]
  exact heq.trans (sharp_bad_restrict_iff V A E T hT (φ z))

/-- Read the full sharp endpoint from a supplied actual merger and its
physical comparisons with the disjoint piece towers. -/
theorem full_sharp_cleanup_of_piece_comparisons {ι : Type} [Fintype ι]
    {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (A : ι → Set X) (V : ι → Opens X) (hA : ∀ P, IsClosedSubmanifold n (A P))
    (hCover : (⋃ P, A P) = W) (hAV : ∀ P, A P ⊆ V P)
    (hSep : ∀ P R, P ≠ R → Disjoint (V P : Set X) (A R))
    (Y : ι → CMfd.{0} n) (T : ∀ P, BlowupTower X (Y P))
    (hATest : ∀ P, IsGeoTestTower (geometricTemplate (A P) []) (T P))
    (hETest : ∀ P, IsGeoTestTower (geometricTemplate (univ : Set X) E) (T P))
    (hSharp : ∀ P, CurrentSharpCentres (A P) E (T P))
    (hNC : ∀ P, HasNormalCrossings n (strictAlong (T P) (A P))
      (geoTransformAlong (geometricTemplate (univ : Set X) E) (T P)).E)
    {Z : CMfd.{0} n} (Q : BlowupTower X Z)
    (hSupport : CentresOver (finiteSupport (fun P => originalSharpBadLocus (n := n) W E ∩ A P)
      (Finset.univ : Finset ι)) Q)
    (hCompare : ∀ P, ∃ φ : (CMfd.of (n := n) (openPreimage Q (V P)))
        ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ (CMfd.of (n := n) (openPreimage (T P) (V P))),
        EmptyAwareTowerIso (Diffeomorph.refl 𝓘(ℂ, ComplexModel n) (V P) ∞)
          (restrict (V P) Q) (restrict (V P) (T P)) φ) :
      let WQ := geoTransformAlong (geometricTemplate W []) Q
      let FQ := (geoTransformAlong (geometricTemplate (univ : Set X) E) Q).E
      IsGeoTestTower (geometricTemplate W []) Q ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) Q ∧
      CurrentSharpCentres W E Q ∧
      CentresOver (originalSharpBadLocus (n := n) W E) Q ∧
      IsClosedSubmanifold n WQ.N ∧ IsSNCDivisor n FQ ∧ HasNormalCrossings n WQ.N FQ ∧
      IsProperMap Q.proj ∧ IsIsomorphismOver n Q.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  classical
  let K := originalSharpBadLocus (n := n) W E
  let B : ι → Set X := fun P => K ∩ A P
  have hAW (P : ι) : A P ⊆ W := hCover ▸ subset_iUnion A P
  have hB (P : ι) : IsClosed (B P) := (isClosed_originalSharpBadLocus hW.1 hE.1).inter (hA P).1
  have hLocalEq (P : ι) : (Subtype.val : V P → X) ⁻¹' W = (Subtype.val : V P → X) ⁻¹' A P := by
    ext x
    exact ⟨fun hx => by
      obtain ⟨R, hR⟩ := mem_iUnion.mp (hCover.symm ▸ (show x.val ∈ W from hx))
      by_cases hPR : P = R
      · subst R
        exact hR
      · exact False.elim (disjoint_left.mp (hSep P R hPR) x.property hR),
      fun hx => hAW P hx⟩
  have hKOver : CentresOver K Q :=
    HironakaActualProcessedAllMasksDrop.centresOver_mono_local
      (iUnion₂_subset fun P _ => (inter_subset_left : B P ⊆ K)) Q hSupport
  let L := finiteSupport B (Finset.univ : Finset ι)
  have hL : IsClosed L := Finset.univ.finite_toSet.isClosed_biUnion (fun P _ => hB P)
  let U : Opens X := ⟨Lᶜ, hL.isOpen_compl⟩
  let cover : Option ι → Opens X := fun i => match i with
    | none => U
    | some P => V P
  have hOpenCover (x : X) : ∃ i, x ∈ cover i := by
    by_cases hx : x ∈ L
    · obtain ⟨P, _, hxP⟩ := mem_iUnion₂.mp hx
      exact ⟨some P, hAV P hxP.2⟩
    · exact ⟨none, hx⟩
  have hEmpty : IsEmptyTower (restrict U Q) :=
    isEmptyTower_restrict_of_centresOver U (disjoint_compl_left : Disjoint (Lᶜ) L) Q hSupport
  have hGlobalTest (M : MarkedIdeal n X) (hM : M.IsWellFormed)
      (hLocal : ∀ P, IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V P → X) M)
        (restrict (V P) (T P))) : IsGeoTestTower M Q := by
    apply isGeoTestTower_of_open_cover M hM.isClosedSubmanifold_N hM.isCoherent cover hOpenCover Q
    intro i
    cases i with
    | none => exact isGeoTestTower_of_isEmptyTower _ _ hEmpty
    | some P =>
      obtain ⟨φ, hφ⟩ := hCompare P
      exact pullback_test_of_physical_comparison (V P) Q (T P) φ hφ M hM (hLocal P)
  let M := geometricTemplate (univ : Set X) E
  let C := geometricTemplate W []
  have hM := ambient_template_wellFormed hE
  have hC := carrier_template_wellFormed hW
  have hCQ : IsGeoTestTower C Q := by
    apply hGlobalTest C hC
    intro P
    change IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : V P → X) (geometricTemplate W []))
      (restrict (V P) (T P))
    rw [pullback_carrier_template_congr (V P) (hLocalEq P)]
    have hAP := carrier_template_wellFormed (hA P)
    exact isGeoTestTower_restrict (V P) hAP.isClosedSubmanifold_N hAP.isCoherent (T P) (hATest P)
  have hMQ : IsGeoTestTower M Q := hGlobalTest M hM fun P =>
    isGeoTestTower_restrict (V P) hM.isClosedSubmanifold_N hM.isCoherent (T P) (hETest P)
  have hQSharp : CurrentSharpCentres W E Q := by
    apply currentSharpCentres_of_open_cover cover hOpenCover W E Q hMQ
    intro i
    cases i with
    | none => exact currentSharpCentres_of_empty _ hEmpty
    | some P =>
      obtain ⟨φ, hφ⟩ := hCompare P
      have hLocal := currentSharpCentres_restrict (V P) (A P) E (T P) (hETest P) (hSharp P)
      have hClosed : IsClosed ((Subtype.val : V P → X) ⁻¹' A P) :=
        (hA P).1.preimage continuous_subtype_val
      have hEClosed : ∀ H ∈ E.map ((Subtype.val : V P → X) ⁻¹' ·), IsClosed H := by
        rintro H hH
        obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp hH
        exact (hE.1 J hJ).preimage continuous_subtype_val
      have hTransport := currentSharpCentres_of_emptyAware hφ hClosed hEClosed hLocal
      simp only [Diffeomorph.coe_refl, preimage_id, List.map_id'] at hTransport
      change CurrentSharpCentres (X := CMfd.of (n := n) (V P))
        ((Subtype.val : V P → X) ⁻¹' W) _ _
      rwa [hLocalEq P]
  refine ⟨hCQ, hMQ, hQSharp, hKOver,
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hC Q hCQ).isClosedSubmanifold_N,
    (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong hM Q hMQ).isSNCDivisor,
    ?_, HironakaLocalPrincipalization.isProperMap_proj Q,
    HironakaSharpOriginalDynamicGoodPrefixes.isIsomorphismOver_proj_of_centresOver K Q hKOver⟩
  rw [N_geoTransformAlong]
  intro z hz
  have hx : Q.proj z ∈ W := strictAlong_subset_preimage Q hW.1 hz
  obtain ⟨P, hP⟩ := mem_iUnion.mp (hCover.symm ▸ hx)
  obtain ⟨φ, hφ⟩ := hCompare P
  by_contra hzNC
  let zV : openPreimage Q (V P) := ⟨z, hAV P hP⟩
  have hBad := (sharp_bad_on_open_iff_of_physical_comparison (V P) Q (T P) φ hφ hE hMQ
    (hETest P) (hA P).1 (hLocalEq P) zV).mp ⟨hz, hzNC⟩
  exact hBad.2 (hNC P (φ zV).val hBad.1)

/-- Assemble actual sharp histories on disjoint closed carrier pieces.
Each piece retains the full ambient boundary. -/
theorem exists_full_sharp_cleanup_of_disjoint_pieces {ι : Type} [Fintype ι]
    {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (A : ι → Set X) (V : ι → Opens X) (hA : ∀ P, IsClosedSubmanifold n (A P))
    (hCover : (⋃ P, A P) = W) (hAV : ∀ P, A P ⊆ V P)
    (hSep : ∀ P R, P ≠ R → Disjoint (V P : Set X) (A R))
    (Y : ι → CMfd.{0} n) (T : ∀ P, BlowupTower X (Y P))
    (hOver : ∀ P, CentresOver (originalSharpBadLocus (n := n) W E ∩ A P) (T P))
    (hATest : ∀ P, IsGeoTestTower (geometricTemplate (A P) []) (T P))
    (hETest : ∀ P, IsGeoTestTower (geometricTemplate (univ : Set X) E) (T P))
    (hSharp : ∀ P, CurrentSharpCentres (A P) E (T P))
    (hNC : ∀ P, HasNormalCrossings n (strictAlong (T P) (A P))
      (geoTransformAlong (geometricTemplate (univ : Set X) E) (T P)).E) :
    ∃ (Y : CMfd.{0} n) (Q : BlowupTower X Y),
      let WQ := geoTransformAlong (geometricTemplate W []) Q
      let FQ := (geoTransformAlong (geometricTemplate (univ : Set X) E) Q).E
      IsGeoTestTower (geometricTemplate W []) Q ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) Q ∧
      CurrentSharpCentres W E Q ∧
      CentresOver (originalSharpBadLocus (n := n) W E) Q ∧
      IsClosedSubmanifold n WQ.N ∧ IsSNCDivisor n FQ ∧ HasNormalCrossings n WQ.N FQ ∧
      IsProperMap Q.proj ∧ IsIsomorphismOver n Q.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  classical
  let K := originalSharpBadLocus (n := n) W E
  let B : ι → Set X := fun P => K ∩ A P
  have hB (P : ι) : IsClosed (B P) := (isClosed_originalSharpBadLocus hW.1 hE.1).inter (hA P).1
  obtain ⟨Z, Q, hSupport, hCompare⟩ :=
    finite_disjoint_towers_physical_comparisons B hB V (fun P => inter_subset_right.trans (hAV P))
      (fun P R hPR => (hSep P R hPR).mono_right inter_subset_right) Y T hOver Finset.univ
  exact ⟨Z, Q, full_sharp_cleanup_of_piece_comparisons hW hE A V hA hCover hAV hSep
    Y T hATest hETest hSharp hNC Q hSupport (fun P => hCompare P (Finset.mem_univ P))⟩


/-- A finite compact sharp cleanup on a smooth carrier, with arbitrary
containment patterns in the original ordered boundary. -/
theorem exists_actual_compact_sharp_cleanup_full_boundary (hn : 0 < n)
    {W : Set X} {E : List (Set X)}
    (hW : IsClosedSubmanifold n W) (hE : IsSNCDivisor n E)
    (hK : IsCompact (originalSharpBadLocus (n := n) W E)) :
    ∃ (Y : CMfd.{0} n) (Q : BlowupTower X Y),
      let WQ := geoTransformAlong (geometricTemplate W []) Q
      let FQ := (geoTransformAlong (geometricTemplate (univ : Set X) E) Q).E
      IsGeoTestTower (geometricTemplate W []) Q ∧
      IsGeoTestTower (geometricTemplate (univ : Set X) E) Q ∧
      CurrentSharpCentres W E Q ∧
      CentresOver (originalSharpBadLocus (n := n) W E) Q ∧
      IsClosedSubmanifold n WQ.N ∧ IsSNCDivisor n FQ ∧ HasNormalCrossings n WQ.N FQ ∧
      IsProperMap Q.proj ∧ IsIsomorphismOver n Q.proj (originalSharpBadLocus (n := n) W E)ᶜ := by
  classical
  let ι := Fin (n + 1) × Finset (Fin E.length)
  let D : Fin (n + 1) → Set X := fun d => dimPiece W d.val
  let A : ι → Set X := fun P => patternPiece (D P.1) E P.2
  let F : ι → List (Set X) := fun P => remainingBoundary E P.2
  obtain ⟨hDgerm, hDreg, hD, hA, hCover, V, hAV, hSep⟩ :=
    mixed_dimension_containment_patterns hW hE
  have hAW (P : ι) : A P ⊆ W :=
    (patternPiece_subset (D P.1) E P.2).trans (dimPiece_subset W P.1.val)
  have hPattern (P : ι) := (actual_full_boundary_containment_patterns (hD P.1) hE (hDreg P.1)).2.2 P.2
  have hPiece (P : ι) := by
    obtain ⟨hAD, _, _, hGerm, _, hFE, _, hContains, hDense⟩ := hPattern P
    have hGermW (x : X) (hx : x ∈ A P) : ∀ᶠ y in 𝓝 x, y ∈ A P ↔ y ∈ W := by
      filter_upwards [hGerm x hx, hDgerm P.1 x (hAD hx)] with y hy hz
      exact hy.trans hz
    exact exists_compact_sharp_cleanup_piece hn hW.1 (hA P) (hAW P) hGermW hE hFE hContains hDense hK
  choose Y T hOver hATest hETest hSharp hNC using hPiece
  exact exists_full_sharp_cleanup_of_disjoint_pieces hW hE A V hA hCover hAV hSep
    Y T hOver hATest hETest hSharp hNC

end Small

end
end Hironaka.HironakaG4FullBoundaryCompactCleanup
