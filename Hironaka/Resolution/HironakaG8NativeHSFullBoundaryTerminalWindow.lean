import Hironaka.Resolution.HironakaG8CompactNativeFirstStep
import Hironaka.Resolution.HironakaG8NativeHSStageCentres
import Hironaka.Resolution.HironakaG3EmptyAwareFullBoundary

/-!
# Native Hilbert--Samuel terminal windows with a full initial boundary

The ambient native state receives the original ordered SNC boundary before
the actual canonical local resolver is applied. Transport back to a literal
ambient open keeps the entire ordered list and its chronological births.

Blueprint: `hironaka-g8-native-hs-full-boundary-terminal-window.tex`.
-/

set_option autoImplicit false

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8NativeHSFullBoundaryTerminalWindow

noncomputable section

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism MarkedIdealTowerTransport
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance HironakaBaseChange
  NormalCrossings NormalCrossingsInvariance ResolutionInvariantSpec CanonicalCentres
  HironakaG11PresLineState HironakaG11PresNativePhase HironakaEmbeddedResolutionLocal
  HironakaG8CompactNativeFirstStep HironakaG8NativeBoundaryComparison
  HironakaG8OpenHoloEmbeddingComposition HironakaG8NativeHSStageCentres HironakaStageCenters
  HironakaG3EmptyAwareBornSlots HironakaG3EmptyAwareFullBoundary HomogenizedGlueingTower
  HironakaActualVanishingIntrinsicHSTransport

/-- Every singular point carries an actual canonical native terminal tower
on a literal ambient open inside the prescribed neighborhood, with the
entire supplied initial SNC boundary and its ordered transform. -/
theorem exists_native_hs_ambient_full_boundary_terminal_window
    {n : ℕ} (hn : 0 < n) {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (E : List (Set X)) (hE : IsSNCDivisor n E)
    (a : X) (ha : a ∈ singularSet (n := n) W)
    (U₀ : Opens X) (haU : a ∈ U₀) :
    ∃ (U : Opens X) (ha' : a ∈ U), U ≤ U₀ ∧
      ∃ (R : MarkedIdeal n (CMfd.of (n := n) U)) (Y : CMfd.{0} n)
        (T : BlowupTower (CMfd.of (n := n) U) Y),
        IsInvDomain n R ∧ R.E = E.map ((Subtype.val : U → X) ⁻¹' ·) ∧
        NativeHSState R ((Subtype.val : U → X) ⁻¹' W)
          (hilbertSamuelAt (vanishingIdeal (n := n) W) a) ∧
        IsCanonical R ((invFamily hn n).inv R) T ∧ IsGeoResolution R T ∧
        StageCentres (fun P C => C ⊆ singularSet (n := n)
          (strictTransform n P.proj ((Subtype.val : U → X) ⁻¹' W))) T ∧
        (geoTransformAlong R T).E =
          E.map (fun H => strictAlong T ((Subtype.val : U → X) ⁻¹' H)) ++ bornAlong T ∧
        IsSNCDivisor n (geoTransformAlong R T).E ∧ (⟨a, ha'⟩ : U) ∈ R.cosupp := by
  obtain ⟨D, haD, hDU₀, Q, hQ, _, hState⟩ :=
    exists_native_state_on_ambient_open W hW a ha U₀ haU
  let F := E.map ((Subtype.val : D → X) ⁻¹' ·)
  have hF : IsSNCDivisor n F :=
    isSNCDivisor_map_preimage (pullsBackCoordinates_val D) continuous_subtype_val hE
  let M : MarkedIdeal n (CMfd.of (n := n) D) := { Q with E := F }
  obtain ⟨hM, hMS, _⟩ := native_state_with_snc_boundary Q hQ hState F hF
  let aD : D := ⟨a, haD⟩
  obtain ⟨K, hK, Y, T, hCan, hRes⟩ :=
    exists_local_resolution_isCanonical (invFamily hn n) hM
      (K := ({aD} : Set D)) isCompact_singleton
  let aK : K := ⟨aD, hK (mem_singleton aD)⟩
  let f : K → X := (Subtype.val : D → X) ∘ (Subtype.val : K → D)
  have hf : IsOpenHoloEmbedding n f :=
    isOpenHoloEmbedding_comp (A := X) (B := CMfd.of (n := n) D) (C := CMfd.of (n := n) K)
      (isOpenHoloEmbedding_val D) (isOpenHoloEmbedding_val K)
  obtain ⟨U, e, he⟩ := hf
  have ha' : a ∈ U := by
    have hfa : f aK = a := rfl
    rw [← hfa, he]
    exact (e aK).property
  have hComp : f ∘ e.symm = (Subtype.val : U → X) := by
    funext x
    change f (e.symm x) = x.val
    rw [he, e.apply_symm_apply]
  have hU : U ≤ D := by
    intro x hx
    let xU : U := ⟨x, hx⟩
    have hfx : f (e.symm xU) = x := congrFun hComp xU
    have hD : f (e.symm xU) ∈ D := (e.symm xU).val.property
    exact hfx ▸ hD
  let M₀ := MarkedIdeal.pullback (Subtype.val : K → D) M
  have hM₀ : IsInvDomain n M₀ := InvDomainTowerAlong.isInvDomain_pullback_val K hM
  let R := MarkedIdeal.pullback e.symm M₀
  have hR : IsInvDomain n R := InvDomainTowerAlong.isInvDomain_pullback e.symm hM₀
  have hRE : R.E = E.map ((Subtype.val : U → X) ⁻¹' ·) := by
    change ((E.map ((Subtype.val : D → X) ⁻¹' ·)).map ((Subtype.val : K → D) ⁻¹' ·)).map
      (e.symm ⁻¹' ·) = E.map ((Subtype.val : U → X) ⁻¹' ·)
    simp only [List.map_map]
    apply List.map_congr_left
    intro H _
    change (f ∘ e.symm) ⁻¹' H = (Subtype.val : U → X) ⁻¹' H
    rw [hComp]
  have hStateR : NativeHSState (X := CMfd.of (n := n) U) R ((Subtype.val : U → X) ⁻¹' W)
      (hilbertSamuelAt (vanishingIdeal (n := n) W) a) := by
    have hs := NativeHSState.pullback (X := CMfd.of (n := n) K)
      (X' := CMfd.of (n := n) U) e.symm (hMS.restrict K)
    change NativeHSState (X := CMfd.of (n := n) U) R ((f ∘ e.symm) ⁻¹' W) _ at hs
    rwa [hComp] at hs
  let A := transport (X' := CMfd.of (n := n) U) e.symm T
  have hCan' : IsCanonical R ((invFamily hn n).inv R) A.tower :=
    Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso (X' := CMfd.of (n := n) U)
      (invFamily hn n) hM₀ e.symm (transport_isTowerIso (X' := CMfd.of (n := n) U) e.symm T) hCan
  have hRes' : IsGeoResolution R A.tower :=
    (isGeoResolution_transport_iff (X' := CMfd.of (n := n) U) e.symm hM₀.isWellFormed.isCoherent T).mpr hRes
  have hStage := hs_tower_stage_centres_singular R hStateR.2.1.isClosed hStateR.hsTowerState
    A.tower hRes'.1
  refine ⟨U, ha', hU.trans hDU₀, R, A.target, A.tower, hR, hRE, hStateR, hCan', hRes', hStage, ?_, ?_, ?_⟩
  · rw [boundary_decomp, hRE, List.map_map]
    rfl
  · exact (InvDomainTowerAlong.isInvDomain_geoTransformAlong hR A.tower hRes'.1).isWellFormed.isSNCDivisor
  · rw [hStateR.cosupp_eq]
    exact fun ℓ => hilbertSamuelAt_vanishing_actual_open_any U W ⟨a, ha'⟩ ℓ

end
end Hironaka.HironakaG8NativeHSFullBoundaryTerminalWindow
