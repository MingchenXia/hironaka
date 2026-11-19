import Hironaka.Resolution.HironakaG8NativeHSStageCentres
import Hironaka.Resolution.HironakaOriginalSelectedContactCosupport
import Hironaka.Resolution.HironakaCoherentTransformExtension
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8NativeHSOriginalTestBridge
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal HironakaG11PresLineState HironakaG11PresTowerState
  HironakaG8NativeHSStageCentres HironakaOriginalSelectedContactCosupport
  HironakaCoherentTransformExtension HomogenizedGlueingTower HironakaStageCenters
  HironakaG8NativeHSAmbientTerminalWindow ResolutionInvariantSpec CanonicalCentres
variable {n : ℕ} {X : CMfd.{0} n}

/-- Every native HS-state test tower is a genuine test tower for the original
mark-one vanishing ideal with the same initial boundary. -/
theorem hs_state_test_is_original_test (Q : MarkedIdeal n X) {W : Set X}
    (hW : IsComplexAnalyticSubset (n := n) W) {H : ℕ → ℕ} (hs : HSTowerState Q W H) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower Q T →
      IsGeoTestTower (⟨univ,Q.E,vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
    let P : MarkedIdeal n X := ⟨univ,Q.E,vanishingIdeal (n := n) W,1⟩
    have hPT : IsGeoTestTower P T := hs_state_test_is_original_test Q hW hs T hT.1
    have hCos : W ⊆ P.cosupp := by
      rw [HironakaEmbeddedBoundary.cosupp_mk_vanishingIdeal hW.isClosed Q.E]
    have hPersist := strictAlong_subset_cosupp_of_subset P
      HomogenizedGlueingTower.isClosedSubmanifold_univ (CartanIrreducible.cartanCoherence W hW)
      hCos T hPT
    have hQ := (hs T hT.1).2.1
    have hE : (geoTransformAlong P T).E = (geoTransformAlong Q T).E :=
      geoTransformAlong_E_eq_of_E_eq (𝔍 := P) (𝔪 := Q) rfl T
    refine ⟨hPT,hT.2.1, hT.2.2.1.trans (hQ.trans hPersist),?_⟩
    rw [hE]
    exact hT.2.2.2
/-- The native terminal history is also an original marked-ideal test history,
with every recorded centre on the current strict singular locus. -/
theorem exists_native_terminal_original_test_singular_centres (hn : 0<n)
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (a₀ : X) (ha₀ : a₀ ∈ singularSet (n := n) W)
    (U₀ : Set X) (hU₀ : IsOpen U₀) (haU₀ : a₀ ∈ U₀) :
    ∃ (D : Opens X), a₀ ∈ D ∧ (D : Set X) ⊆ U₀ ∧
      ∃ (Q : MarkedIdeal n (CMfd.of (n := n) D)) (Y : CMfd.{0} n)
        (T : BlowupTower (CMfd.of (n := n) D) Y),
        IsInvDomain n Q ∧ Q.E = [] ∧
        NativeHSState Q ((Subtype.val : D → X) ⁻¹' W)
          (hilbertSamuelAt (vanishingIdeal (n := n) W) a₀) ∧
        IsCanonical Q ((invFamily hn n).inv Q) T ∧ IsGeoResolution Q T ∧
        IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) ((Subtype.val : D → X) ⁻¹' W),1⟩ :
          MarkedIdeal n (CMfd.of (n := n) D)) T ∧
        StageCentres (fun P C => C ⊆ singularSet (n := n)
          (strictTransform n P.proj ((Subtype.val : D → X) ⁻¹' W))) T := by
  obtain ⟨D,haD,hDU,Q,Y,T,hQ,hE,hState,hCan,hRes,hCent⟩ :=
    exists_native_hs_ambient_terminal_window_singular_centres hn W hW a₀ ha₀ U₀ hU₀ haU₀
  have htest := hs_state_test_is_original_test Q hState.2.1 hState.hsTowerState T hRes.1
  rw [hE] at htest
  exact ⟨D,haD,hDU,Q,Y,T,hQ,hE,hState,hCan,hRes,htest,hCent⟩
end
end Hironaka.HironakaG8NativeHSOriginalTestBridge
