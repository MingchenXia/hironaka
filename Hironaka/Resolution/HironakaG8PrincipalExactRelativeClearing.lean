import Hironaka.Resolution.HironakaG8PrincipalNativeAtlasSuccessor

/-! Finite relative clearing retaining exact ambient principal records. -/

set_option autoImplicit false
set_option maxHeartbeats 3200000

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8PrincipalExactRelativeClearing

noncomputable section

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  ResolutionInvariantSpec NormalCrossings HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  HironakaStageCenters MaxLocusLocal HironakaOriginalTerminalOverlapComparison
  HironakaG11PresLineState HironakaG11PresTowerState HironakaG11InvBMClass HironakaG8LocalHistory
  HironakaG11InvCommonMark HironakaActualVanishingIntrinsicHSTransport
  HomogenizedGlueingTower HironakaG8NativePrefixReplay HironakaG8NativeRelativeSuccessor
  HironakaActualPowerBoundaryExponents HironakaActualWholeAmbientHSSuperlevel
  HironakaOriginalSelectedContactCosupport StepOneLowerDomain HironakaG8NativeNumericalOverlap
  HironakaG8SurfaceLimitEndpoint HironakaBaseChange HironakaG8OpenHoloEmbeddingComposition
  NormalCrossingsInvariance HironakaG8FiniteSingularTowerMerge HironakaEmbeddedBoundary
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaG8SingularFootprintExtension
  HironakaNormalCrossingsSeparationChoiceComparison MarkedIdealTowerTransport BlowupTowerIsomorphism
  StrictTransformComposition StepOneTangentChange HironakaG8NativePrefixWindowRestriction
  HironakaG1OriginalUnequalMarkCanonical HironakaSmoothSubmersionOriginalAmbientCanonical
  CanonicalCentres HironakaActualOriginalPowerTransform RestrictEmptyTower HironakaG3CentresOverGenericFactor

open HironakaG8NativeRelativeClearing HironakaG8PrincipalNativeAtlasSuccessor
  HironakaG8NativeSimultaneousCentre

variable {n : ℕ} {X Y : CMfd.{0} n} {I Λ : Type} [LinearOrder Λ]
local notation "HS[" A "]" => hilbertSamuelAt (vanishingIdeal (n := n) A)
local notation "original[" W "; " E "]" => MarkedIdeal.mk (n := n) univ E (vanishingIdeal (n := n) W) 1

/-- Native endpoints retaining simultaneous stages and the original exact chart records. -/
def ExactTerminalWindows (I : Type) (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ)
    (q : ℕ) : TerminalCondition n :=
  fun T W D E H =>
    ∃ A : NativeWindows _ I W E H D,
      ExactWholeAt A q ∧
      (∀ i, IsCanonical (A.powered i) (R.inv (A.powered i)) (restrict (A.openSet i) T) ∧
        IsGeoResolution (A.powered i) (restrict (A.openSet i) T)) ∧
      NativeSimultaneousStages R A.openSet A.powered T

abbrev ExactClearedOver (I : Type) (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ)
    (q : ℕ) (X : CMfd.{0} n) (W D K : Set X) (E : List (Set X)) (H : ℕ → ℕ) : Prop :=
  ClearedOverWith (ExactTerminalWindows I R q) X W D K E H

private theorem clearedOverWith_of_restrict {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {term : TerminalCondition n} (O : Opens X) (hKO : K ⊆ O)
    (h : ClearedOverWith term (CMfd.of (n := n) O) ((Subtype.val : O → X) ⁻¹' W)
      ((Subtype.val : O → X) ⁻¹' D) ((Subtype.val : O → X) ⁻¹' K)
      (E.map ((Subtype.val : O → X) ⁻¹' ·)) H) :
    ClearedOverWith term X W D K E H := by
  obtain ⟨B, j, hj, hK, Y, T, hT, hStage, hBound, hDrop, hOver, hEnd⟩ := h
  refine ⟨B, (Subtype.val : O → X) ∘ j, isOpenHoloEmbedding_comp (isOpenHoloEmbedding_val O) hj,
    ?_, Y, T, ?_, hStage, hBound, hDrop, hOver, ?_⟩
  · intro x hx
    obtain ⟨b, hb⟩ := hK (show (⟨x,hKO hx⟩ : O) ∈ (Subtype.val : O → X) ⁻¹' K from hx)
    exact ⟨b, congrArg Subtype.val hb⟩
  · rw [List.map_map] at hT
    exact hT
  · rw [List.map_map] at hEnd
    exact hEnd

private theorem hs_nonincrease_restrict {W : Set X} {Y : CMfd.{0} n}
    (T : BlowupTower X Y) (O : Opens X)
    (hBound : ∀ y ℓ, HS[strictTransform n T.proj W] y ℓ ≤ HS[W] (T.proj y) ℓ) :
    ∀ y ℓ, HS[strictTransform n (restrict O T).proj ((Subtype.val : O → X) ⁻¹' W)] y ℓ ≤
      HS[(Subtype.val : O → X) ⁻¹' W] ((restrict O T).proj y) ℓ := by
  intro y ℓ
  rw [strictTransform_restricted_tower O T W]
  rw [hilbertSamuelAt_vanishing_actual_open_any (openPreimage T O) _ y ℓ,
    hilbertSamuelAt_vanishing_actual_open_any O W ((restrict O T).proj y) ℓ, proj_restrict]
  exact hBound y.val ℓ

private theorem exactClearedOver_of_no_active {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    (q : ℕ) (R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ) {Y : CMfd.{0} n} (T : BlowupTower X Y)
    (hW : IsComplexAnalyticSubset (n := n) W) (hE : IsSNCDivisor n E)
    (hT : IsGeoTestTower original[W;E] T)
    (hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T)
    (hOver : CentresOver D T)
    (hBound : ∀ y ℓ, HS[strictTransform n T.proj W] y ℓ ≤ HS[W] (T.proj y) ℓ)
    (A : NativeWindows X I W E H D)
    (hR : ActiveWindows A T R)
    (hCan : ∀ i, IsCanonical (A.powered i) (R.inv (A.powered i)) (restrict (A.openSet i) T))
    (hSync : NativeSimultaneousStages R A.openSet A.powered T)
    (hExact : ExactWholeAt A q)
    (hF : IsClosed (activeSupport T W D H)) (hNe : ¬ (activeSupport T W D H ∩ T.proj ⁻¹' K).Nonempty) :
    ExactClearedOver I R q X W D K E H := by
  let O : Opens X := ⟨(T.proj '' activeSupport T W D H)ᶜ,
    ((HironakaLocalPrincipalization.isProperMap_proj T).isClosedMap _ hF).isOpen_compl⟩
  have hK : K ⊆ range (Subtype.val : O → X) := by
    intro x hx
    have hO : x ∈ O := by
      rintro ⟨y, hy, rfl⟩
      exact hNe ⟨y,hy,hx⟩
    exact ⟨⟨x,hO⟩,rfl⟩
  have hM : original[W;E].IsWellFormed := ⟨isClosedSubmanifold_univ,
    CartanIrreducible.cartanCoherence W hW, hE, SimultaneousNormalCrossings.isTransverse_univ_of_isSNCDivisor hE⟩
  refine ⟨CMfd.of (n := n) O, Subtype.val, isOpenHoloEmbedding_val O, hK, _, restrict O T, ?_,
    singular_stages_restrict W O T hStage, hs_nonincrease_restrict T O hBound, ?_, centresOver_restrict O D T hOver, ?_⟩
  · rw [← pullback_val_mk_vanishingIdeal O E W]
    exact MarkedIdealRestrictOpen.isGeoTestTower_restrict O
      hM.isClosedSubmanifold_N hM.isCoherent T hT
  · intro z hz
    change ((restrict O T).proj z).val ∈ D at hz
    rw [proj_restrict] at hz
    obtain ⟨i,hi⟩ := A.covers (T.proj z.val) hz
    have hLe : ∀ ℓ, HS[strictTransform n T.proj W] z.val ℓ ≤ H ℓ :=
      hR.upper i ⟨z.val,hi⟩
    rw [strictTransform_restricted_tower O T W]
    have hHS : HS[(Subtype.val : openPreimage T O → Y) ⁻¹' strictTransform n T.proj W] z =
        HS[strictTransform n T.proj W] z.val :=
      funext (hilbertSamuelAt_vanishing_actual_open_any (openPreimage T O) _ z)
    rw [hHS]
    apply lt_of_le_of_ne (Pi.toLex_monotone hLe)
    intro hEq
    exact z.property ⟨z.val, ⟨hz, fun ℓ => (congrFun (congrArg ofLex hEq) ℓ).ge⟩, rfl⟩
  · have hOff : Disjoint (O : Set X) (T.proj '' activeSupport T W D H) :=
      Set.disjoint_left.mpr fun _ hAvoid hHit => hAvoid hHit
    exact ⟨A.restrictAmbient O, exactWholeAt_restrictAmbient A q hExact O, fun i => A.terminal_on_open_of_disjoint R T hR hCan O hOff i,
      A.simultaneous_restrictAmbient R T hCan hSync O⟩

/-- The relative clearing induction with its exact whole-record witness retained
through each ambient shrink and the terminal cut. -/
theorem exists_finite_exact_native_clearing_along [WellFoundedLT Λ] (hn : 0 < n) (q : ℕ)
    (R : BMInvariant.{0,0} n (fun {A} P Q => LocWPEquiv (X := A) P Q) n Λ)
    (H : ℕ → ℕ) (μ : WithTop Λ) :
    ∀ {X : CMfd.{0} n} {W D K : Set X} {E : List (Set X)}
      (_hW : IsComplexAnalyticSubset (n := n) W) (_hE : IsSNCDivisor n E)
      (_hD : IsClosed D) (_hExact : D = {x | ∀ ℓ, HS[W] x ℓ = H ℓ})
      (_hK : IsCompact K)
      (_hNot : ∀ B ∈ E, ∀ x ∈ D, x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W)
      (A : NativeWindows X I W E H D) {Y : CMfd.{0} n} (T : BlowupTower X Y)
      (_hT : IsGeoTestTower original[W;E] T)
      (_hStage : StageCentres (fun S C => C ⊆ singularSet (n := n) (strictTransform n S.proj W)) T)
      (_hOver : CentresOver D T)
      (_hBound : ∀ y ℓ, HS[strictTransform n T.proj W] y ℓ ≤ HS[W] (T.proj y) ℓ)
      (_hCan : ∀ i, IsCanonical (A.powered i) (R.toResolutionInvariant.inv (A.powered i))
        (restrict (A.openSet i) T)),
      NativeSimultaneousStages R.toResolutionInvariant A.openSet A.powered T →
      ExactWholeAt A q →
      (∀ i (y : openPreimage T (A.openSet i)),
        y ∈ (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp →
        T.proj y.val ∈ K →
        (R.toResolutionInvariant.inv (A.powered i) (restrict (A.openSet i) T) y : WithTop Λ) < μ) →
      ExactClearedOver I R.toResolutionInvariant q X W D K E H := by
  classical
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
    intro X W D K E hW hE hD hExact hK hNot A Y T hT hStage hOver hBound hCan hSync hChart hRank
    let F := activeSupport T W D H
    have hF : IsClosed F := isClosed_activeSupport T hW hD
    have hR := nativeWindows_active_replay hn R hW hE hExact hNot A T hT hStage hCan
    by_cases hNe : (F ∩ T.proj ⁻¹' K).Nonempty
    · have hCover : ∀ y ∈ F, ∃ (i : I) (hy : y ∈ openPreimage T (A.openSet i)),
          (⟨y, hy⟩ : openPreimage T (A.openSet i)) ∈ (geoTransformAlong (A.powered i) (restrict (A.openSet i) T)).cosupp := by
        intro y hy
        obtain ⟨i,hi⟩ := A.covers (T.proj y) hy.1
        exact ⟨i,hi,(hR.support i ⟨y,hi⟩).mpr hy⟩
      obtain ⟨m,O,hKO,⟨i,y,hy,hyK,hym⟩,hNext⟩ := exists_relative_native_successor_with_cut
        R.toResolutionInvariant hW E hE T hT hStage A.openSet F hF hK hNe A.powered A.powered_domain
        hCan hR.boundary H hR.currentCut hCover (fun i y => (hR.support i y).mp) hR.overlap
      have hm : (m : WithTop Λ) < μ := by
        rw [← hym]
        exact hRank i y hy hyK
      dsimp only at hNext
      obtain ⟨C,Z,π,hπ,_,hWhere,_,hS,hStageS,hLocal,hStepBound,hCut⟩ := hNext
      let A' := A.restrictAmbient O
      let W' := (Subtype.val : O → X) ⁻¹' W
      let E' := E.map ((Subtype.val : O → X) ⁻¹' ·)
      let D' := (Subtype.val : O → X) ⁻¹' D
      let K' := (Subtype.val : O → X) ⁻¹' K
      let S := BlowupTower.step (restrict O T) C π hπ
      have hW' : IsComplexAnalyticSubset (n := n) W' :=
        AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage contMDiff_subtype_val hW
      have hE' : IsSNCDivisor n E' :=
        isSNCDivisor_map_preimage (pullsBackCoordinates_val O) continuous_subtype_val hE
      have hD' : IsClosed D' := hD.preimage continuous_subtype_val
      have hExact' : D' = {x | ∀ ℓ, HS[W'] x ℓ = H ℓ} := by
        change (Subtype.val : O → X) ⁻¹' D = _
        rw [hExact]
        ext x
        have hHS := funext (hilbertSamuelAt_vanishing_actual_open_any (n := n) O W x)
        change (∀ ℓ, HS[W] x.val ℓ = H ℓ) ↔ (∀ ℓ, HS[(Subtype.val : O → X) ⁻¹' W] x ℓ = H ℓ)
        rw [hHS]
      have hK' : IsCompact K' :=
        (Topology.IsInducing.subtypeVal.isCompact_preimage_iff (fun x hx => ⟨⟨x,hKO hx⟩,rfl⟩)).mpr hK
      have hNot' : ∀ B ∈ E', ∀ x ∈ D', x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W' := by
        intro B hB x hx hxB hBnear
        obtain ⟨B₀,hB₀,rfl⟩ := List.mem_map.mp hB
        apply hNot B₀ hB₀ x.val hx hxB
        rw [← O.isOpen.isOpenEmbedding_subtypeVal.map_nhds_eq x, Filter.eventually_map]
        exact hBnear
      have hCan' (i : I) : IsCanonical (A'.powered i) (R.toResolutionInvariant.inv (A'.powered i))
          (restrict (A'.openSet i) S) := by
        change IsCanonical ((A.restrictAmbient O).powered i)
          (R.toResolutionInvariant.inv ((A.restrictAmbient O).powered i)) (restrict (A'.openSet i) S)
        rw [A.restrictAmbient_powered O i]
        exact (hLocal i).2.1
      have hBound' : ∀ y ℓ, HS[strictTransform n S.proj W'] y ℓ ≤ HS[W'] (S.proj y) ℓ := by
        intro z ℓ
        dsimp only [S]
        rw [BlowupTower.proj_step, strictTransform_comp (restrict O T).contMDiff_proj hπ.contMDiff W']
        exact (hStepBound z ℓ).trans (hs_nonincrease_restrict T O hBound (π z) ℓ)
      have hOver' : CentresOver D' S := by
        refine ⟨centresOver_restrict O D T hOver, ?_⟩
        intro z hz
        change ((restrict O T).proj z).val ∈ D
        rw [proj_restrict]
        exact (hWhere hz).1
      have hSync' : NativeSimultaneousStages
          R.toResolutionInvariant A'.openSet A'.powered S := by
        refine ⟨A.simultaneous_restrictAmbient R.toResolutionInvariant T hCan hSync O,
          Or.inr ⟨m,?_⟩⟩
        open HironakaG8NativeSimultaneousTransport in
        have hRecords : A'.powered =
            (fun i => shrunkRecord (n := n) O (A.openSet i) (A.powered i)) :=
          funext (A.restrictAmbient_powered O)
        rw [hRecords]
        exact hCut
      apply clearedOverWith_of_restrict O hKO
      refine IH (m : WithTop Λ) hm hW' hE' hD' hExact' hK' hNot' A' S hS hStageS hOver' hBound' hCan' hSync' (exactWholeAt_restrictAmbient A q hChart O) ?_
      intro i z hz _
      change z ∈ (geoTransformAlong ((A.restrictAmbient O).powered i) (restrict (A'.openSet i) S)).cosupp at hz
      change (R.toResolutionInvariant.inv ((A.restrictAmbient O).powered i) (restrict (A'.openSet i) S) z :
        WithTop Λ) < (m : WithTop Λ)
      rw [A.restrictAmbient_powered O i] at hz ⊢
      exact WithTop.coe_lt_coe.mpr ((hLocal i).2.2 z hz)
    · exact exactClearedOver_of_no_active q R.toResolutionInvariant T hW hE hT hStage hOver hBound A hR hCan hSync hChart hF hNe


private theorem clearedOverWith_exists_literal_open {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {term : TerminalCondition n} (hTransport : ∀ {A B Y Y' : CMfd.{0} n}
      (φ : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ A)
      {T : BlowupTower A Y} {T' : BlowupTower B Y'}
      {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y},
      IsTowerIso φ T' T χ →
      ∀ {W D : Set A} {E : List (Set A)} {H : ℕ → ℕ}, term T W D E H →
        term T' (φ ⁻¹' W) (φ ⁻¹' D) (E.map (φ ⁻¹' ·)) H)
    (h : ClearedOverWith term X W D K E H) (hW : IsComplexAnalyticSubset (n := n) W) :
    ∃ O : Opens X, K ⊆ O ∧
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
        IsGeoTestTower original[(Subtype.val : O → X) ⁻¹' W; E.map ((Subtype.val : O → X) ⁻¹' ·)] T ∧
        StageCentres (fun S C => C ⊆ singularSet (n := n)
          (strictTransform n S.proj ((Subtype.val : O → X) ⁻¹' W))) T ∧
        (∀ z ℓ, HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z ℓ ≤
          HS[(Subtype.val : O → X) ⁻¹' W] (T.proj z) ℓ) ∧
        (∀ z ∈ T.proj ⁻¹' ((Subtype.val : O → X) ⁻¹' D),
          toLex (HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z) < toLex H) ∧
        CentresOver ((Subtype.val : O → X) ⁻¹' D) T ∧
        term T ((Subtype.val : O → X) ⁻¹' W) ((Subtype.val : O → X) ⁻¹' D)
          (E.map ((Subtype.val : O → X) ⁻¹' ·)) H := by
  obtain ⟨B,j,hj,hK,Y,T,hT,hStage,hBound,hDrop,hOver,hEnd⟩ := h
  let Wb := j ⁻¹' W
  have hWb : IsComplexAnalyticSubset (n := n) Wb :=
    AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage hj.contMDiff hW
  obtain ⟨O,φ,hφ⟩ := hj
  let Wo := (Subtype.val : O → X) ⁻¹' W
  let β := φ.symm
  let tr := transport (X' := CMfd.of (n := n) O) β T
  have hβ (x : O) : j (β x) = x.val := by
    rw [hφ, φ.apply_symm_apply]
  have hWs : (β ⁻¹' Wb) = Wo := by
    ext x
    change j (β x) ∈ W ↔ x.val ∈ W
    rw [hβ]
  have hWt : φ ⁻¹' Wo = Wb := by
    ext x
    change (φ x).val ∈ W ↔ j x ∈ W
    rw [hφ]
  have hEtrace : (E.map (j ⁻¹' ·)).map (β ⁻¹' ·) = E.map ((Subtype.val : O → X) ⁻¹' ·) := by
    rw [List.map_map]
    apply congrArg E.map
    funext D
    ext x
    change j (β x) ∈ D ↔ x.val ∈ D
    rw [hβ]
  have hVan : GermIdeal.pullback (m := n) β (vanishingIdeal (n := n) Wb) = vanishingIdeal (n := n) Wo := by
    have hId := MarkedIdealBiholomorphism.pullback_vanishingIdeal_preimage
      β.contMDiff β.symm.contMDiff β.apply_symm_apply β.symm_apply_apply
      (g := (id : O → O)) contMDiff_id Wb
    rw [hWs, Function.comp_id] at hId
    exact hId.symm.trans (GermIdeal.ext (funext fun _ => funext fun _ =>
      propext BlowupExistenceCodimOne.pullback_id_vanishingIdeal_mem_iff))
  have hRecord : MarkedIdeal.pullback β original[Wb; E.map (j ⁻¹' ·)] =
      original[Wo; E.map ((Subtype.val : O → X) ⁻¹' ·)] := by
    change (MarkedIdeal.mk (β ⁻¹' univ) ((E.map (j ⁻¹' ·)).map (β ⁻¹' ·))
      (GermIdeal.pullback (m := n) β (vanishingIdeal (n := n) Wb)) 1 : MarkedIdeal n O) = _
    rw [preimage_univ, hEtrace, hVan]
  have hTest := (isGeoTestTower_transport_iff (X' := CMfd.of (n := n) O) β (CartanIrreducible.cartanCoherence Wb hWb) T).mpr hT
  rw [hRecord] at hTest
  have hIso := transport_isTowerIso (X' := CMfd.of (n := n) O) β T
  have hTrace := strictTransform_preimage_of_square (A' := CMfd.of (n := n) O) β tr.back
    tr.tower.contMDiff_proj T.contMDiff_proj Wb hWb.isClosed
    (fun x => (proj_transport (X' := CMfd.of (n := n) O) β T x).symm)
  have hDs : β ⁻¹' (j ⁻¹' D) = (Subtype.val : O → X) ⁻¹' D := by
    ext x
    change j (β x) ∈ D ↔ x.val ∈ D
    rw [hβ]
  refine ⟨O, ?_, tr.target, tr.tower, hTest, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y,rfl⟩ := hK hx
    rw [hφ]
    exact (φ y).property
  · have hSing := singular_stages_of_tower_iso (X' := B) (X := CMfd.of (n := n) O)
      (T' := T) (T := tr.tower) Wo (hW.isClosed.preimage continuous_subtype_val) β.symm hIso.symm
    apply hSing
    change StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj (φ ⁻¹' Wo))) T
    rw [hWt]
    exact hStage
  · intro z ℓ
    change HS[strictTransform n tr.tower.proj Wo] z ℓ ≤ HS[Wo] (tr.tower.proj z) ℓ
    rw [← hWs, hTrace, hilbertSamuelAt_vanishing_actual_biholomorphic_any tr.back,
      hilbertSamuelAt_vanishing_actual_biholomorphic_any β,
      proj_transport (X' := CMfd.of (n := n) O) β T z]
    exact hBound _ _
  · intro z hz
    have hz' : T.proj (tr.back z) ∈ j ⁻¹' D := by
      change j (T.proj (tr.back z)) ∈ D
      rw [← proj_transport (X' := CMfd.of (n := n) O) β T z, hβ]
      exact hz
    change toLex (HS[strictTransform n tr.tower.proj Wo] z) < toLex H
    rw [← hWs, hTrace]
    have hHS := funext (hilbertSamuelAt_vanishing_actual_biholomorphic_any tr.back
      (strictTransform n T.proj Wb) z)
    rw [hHS]
    exact hDrop _ hz'
  · have hOver' := centresOver_of_isTowerIso hIso (j ⁻¹' D) hOver
    rw [hDs] at hOver'
    exact hOver'
  · have hNew : term tr.tower (β ⁻¹' Wb) (β ⁻¹' (j ⁻¹' D))
        ((E.map (j ⁻¹' ·)).map (β ⁻¹' ·)) H :=
      hTransport (B := CMfd.of (n := n) O) β hIso hEnd
    rw [hWs,hDs,hEtrace] at hNew
    exact hNew

theorem ExactClearedOver.exists_literal_open {W D K : Set X} {E : List (Set X)} {H : ℕ → ℕ}
    {q : ℕ} {R : ResolutionInvariantSeq.ResolutionInvariant.{0,0} n n Λ}
    (h : ExactClearedOver I R q X W D K E H) (hW : IsComplexAnalyticSubset (n := n) W) :
    ∃ O : Opens X, K ⊆ O ∧
      ∃ (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) O) Y),
        IsGeoTestTower original[(Subtype.val : O → X) ⁻¹' W; E.map ((Subtype.val : O → X) ⁻¹' ·)] T ∧
        StageCentres (fun S C => C ⊆ singularSet (n := n)
          (strictTransform n S.proj ((Subtype.val : O → X) ⁻¹' W))) T ∧
        (∀ z ℓ, HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z ℓ ≤
          HS[(Subtype.val : O → X) ⁻¹' W] (T.proj z) ℓ) ∧
        (∀ z ∈ T.proj ⁻¹' ((Subtype.val : O → X) ⁻¹' D),
          toLex (HS[strictTransform n T.proj ((Subtype.val : O → X) ⁻¹' W)] z) < toLex H) ∧
        CentresOver ((Subtype.val : O → X) ⁻¹' D) T ∧
        ExactTerminalWindows I R q T ((Subtype.val : O → X) ⁻¹' W) ((Subtype.val : O → X) ⁻¹' D)
          (E.map ((Subtype.val : O → X) ⁻¹' ·)) H :=
  clearedOverWith_exists_literal_open (fun {A B Y Y'} φ {T T' χ} hIso {W D E H} hEnd => by
    obtain ⟨S,hExact,hS,hSync⟩ := hEnd
    exact ⟨S.transportBase (B := B) φ, exactWholeAt_transportBase S q hExact φ, fun i => S.terminal_transportBase (B := B) (T := T) (T' := T') φ _ hIso hS i,
      S.simultaneous_transportBase (B := B) (T := T) (T' := T') φ _ hIso (fun i => (hS i).1) hSync⟩) h hW



open HironakaG8NativePhaseCertificate HironakaG8PrincipalNativeAtlas
  HironakaG8PrincipalEpochLabels HironakaG8OccupiedAtlasRestart
  HironakaG1OriginalInvariantClassFunctorial HironakaActualHistoricalOriginalSingularReference
  GermIdealOrder

/-- A compact task at an attained highest principal profile has an actual
clearing phase with the exact whole-record native atlas still attached. -/
theorem exists_principal_exact_native_phase_near_compact
    {m : ℕ} {X : CMfd.{0} (m+1)} (W : Set X)
    (hW : IsComplexAnalyticSubset (n := m+1) W) (E : List (Set X)) (hE : IsSNCDivisor (m+1) E)
    (hI : (vanishingIdeal (n := m+1) W).IsInvertible)
    (K : Set X) (hK : IsCompact K) (a : X) (ha : a ∈ singularSet (n := m+1) W) (q : ℕ)
    (hOrd : order (m+1) univ (vanishingIdeal (n := m+1) W) a = q)
    (hHighest : ∀ x, toLex (hilbertSamuelAt (vanishingIdeal (n := m+1) W) x) ≤
      toLex (hilbertSamuelAt (vanishingIdeal (n := m+1) W) a))
    (hNot : ∀ B ∈ E, ∀ x ∈ phaseLevel W (hilbertSamuelAt (vanishingIdeal (n := m+1) W) a),
        x ∈ B → ¬ ∀ᶠ z in 𝓝 x, z ∈ B → z ∈ W) :
    ∃ O : Opens X, K ⊆ O ∧
      ∃ (Y : CMfd.{0} (m+1)) (T : BlowupTower (CMfd.of (n := m+1) O) Y),
      let U := (Subtype.val : O → X) ⁻¹' W
      let B := E.map ((Subtype.val : O → X) ⁻¹' ·)
      let H := hilbertSamuelAt (vanishingIdeal (n := m+1) W) a
      ActualNativePhase (X := CMfd.of (n := m+1) O) U B H T ∧
      HasExactCoveredNativeAtlas U B H T ⟨univ,B,vanishingIdeal (n := m+1) U,q⟩ := by
  let H := hilbertSamuelAt (vanishingIdeal (n := m+1) W) a
  let D := phaseLevel W H
  let F : MarkedIdeal (m+1) X := ⟨univ,E,vanishingIdeal (n := m+1) W,q⟩
  have hCut (x : X) : x ∈ F.cosupp ↔ (q : ℕ∞) ≤ order (m+1) univ F.ideal x := by
    rw [le_order_iff (𝔞 := vanishingIdeal (n := m+1) W) (fun _ hg => hg.1)]
    exact ⟨And.right,fun h => ⟨mem_univ x,h⟩⟩
  have hDF : D = F.cosupp := by
    ext x
    change hilbertSamuelAt (vanishingIdeal (n := m+1) W) x = H ↔ x ∈ F.cosupp
    rw [hCut x]
    constructor
    · intro h
      rw [← hOrd]
      apply le_of_not_gt
      intro hLt
      have hh := (principal_profile_lt_iff_order_lt _ _ hI hI x a).2 hLt
      exact (lt_irrefl _) (h ▸ hh)
    · intro hx
      apply congrArg ofLex
      apply le_antisymm (hHighest x)
      apply le_of_not_gt
      intro hLt
      have hh := (principal_profile_lt_iff_order_lt _ _ hI hI x a).1 hLt
      exact (not_lt_of_ge hx) (hh.trans_le (le_of_eq hOrd))
  have hD : IsClosed D := hDF ▸ OrderTaylor.isClosed_cosupport (CartanIrreducible.cartanCoherence W hW) q
  have hLevel : D = {x | ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := m+1) W) x ℓ = H ℓ} := by
    ext x
    exact ⟨fun h => congrFun h,funext⟩
  have hSing : D ⊆ singularSet (n := m+1) W := by
    rw [hLevel]
    exact actual_original_singular_profile_locus_subset_current_singular W hW a ha W hW
  obtain ⟨A,hExact,_⟩ := exists_exact_principal_native_windows W hW E hE hI a q H rfl hOrd hSing
  let R : BMInvariant.{0,0} (m+1) (fun {M} P Q => LocWPEquiv (X := M) P Q) (m+1) (ValTy (m+1)) :=
    ⟨canonicalInvariant (m+1), classFunctorialFor_canonicalInvariant (m+1)⟩
  have hCleared : ExactClearedOver D R.toResolutionInvariant q X W D K E H := by
    apply exists_finite_exact_native_clearing_along (Nat.succ_pos m) q R H ⊤
      hW hE hD hLevel hK hNot A (.refl : BlowupTower X X) trivial trivial trivial
    · intro z ℓ
      simpa only [BlowupTower.proj_refl, strictTransform_id hW.isClosed, id_eq] using
        (le_rfl : hilbertSamuelAt (vanishingIdeal (n := m+1) W) z ℓ ≤ _)
    · exact fun _ => trivial
    · trivial
    · exact hExact
    · exact fun _ _ _ _ => WithTop.coe_lt_top _
  obtain ⟨O,hKO,Y,T,hTest,hSingT,hBound,hDrop,hOver,hEnd⟩ := hCleared.exists_literal_open hW
  let U := (Subtype.val : O → X) ⁻¹' W
  let B := E.map ((Subtype.val : O → X) ⁻¹' ·)
  have hDO : (Subtype.val : O → X) ⁻¹' D = phaseLevel (X := CMfd.of (n := m+1) O) U H := by
    ext x
    change hilbertSamuelAt (vanishingIdeal (n := m+1) W) x.val = H ↔
      hilbertSamuelAt (vanishingIdeal (n := m+1) U) x = H
    rw [funext (hilbertSamuelAt_vanishing_actual_open_any O W x)]
  rw [hDO] at hOver hDrop hEnd
  obtain ⟨S,hRaw,hCan,hSync⟩ := hEnd
  refine ⟨O,hKO,Y,T,⟨hTest,hSingT,hOver,⟨D,S,hCan,fun _ => hSync⟩,hBound,hDrop⟩,?_⟩
  apply hasExactCoveredNativeAtlas_of_retained S q hRaw T hSync
  intro x hx
  rw [← hDO,hDF]
  have hFpull : MarkedIdeal.pullback (Subtype.val : O → X) F =
      (⟨univ,B,vanishingIdeal (n := m+1) U,q⟩ : MarkedIdeal (m+1) O) :=
    MarkedIdealOperationsTransform.MarkedIdeal.ext_of preimage_univ rfl
      (HironakaActualOpenEmbeddingVanishingIdeal.pullback_vanishingIdeal_of_isOpenHoloEmbedding
        _ (isOpenHoloEmbedding_val O) W) rfl
  rw [← MarkedIdealRestrictOpen.cosupp_pullback_val F (fun _ _ hg => hg.1) O,hFpull]
  exact hx

end
end Hironaka.HironakaG8PrincipalExactRelativeClearing
