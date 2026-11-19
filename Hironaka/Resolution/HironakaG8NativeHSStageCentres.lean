import Hironaka.Resolution.HironakaG8NativeHSAmbientTerminalWindow
import Hironaka.Resolution.HironakaG8HSTowerStateStrictTransform
import Hironaka.Resolution.HironakaStageCenters
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8NativeHSStageCentres
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance BlowupTowers BlowupTowerTransforms
  MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  HironakaG11PresLineState HironakaG11PresTowerState HironakaG8HSTowerStateStrictTransform
  HironakaG8NativeHSAmbientTerminalWindow HironakaStageCenters

/-- Every center of a genuine HS-state test tower lies in the singular locus of
its actual geometric strict transform at the corresponding literal prefix. -/
theorem hs_tower_stage_centres_singular {n : ℕ} {X : CMfd.{0} n}
    (Q : MarkedIdeal n X) {W : Set X} (hW : IsClosed W) {H : ℕ → ℕ}
    (hs : HSTowerState Q W H) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower Q T →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hT => by
    refine ⟨hs_tower_stage_centres_singular Q hW hs T hT.1, ?_⟩
    have hSing := (hs T hT.1).2.2.2.2
    rw [hsTowerState_strictAlong_eq_strictTransform Q hW hs T hT.1] at hSing
    exact hT.2.2.1.trans hSing

/-- Inside any prescribed neighborhood of a singular point, the actual native
terminal tower has all its recorded centers in the current strict singular locus. -/
theorem exists_native_hs_ambient_terminal_window_singular_centres {n : ℕ} (hn : 0<n) {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (a₀ : X) (ha₀ : a₀ ∈ singularSet (n := n) W)
    (U₀ : Set X) (hU₀ : IsOpen U₀) (haU₀ : a₀ ∈ U₀) :
    ∃ (D : Opens X), a₀ ∈ D ∧ (D : Set X) ⊆ U₀ ∧
      ∃ (R : MarkedIdeal n (CMfd.of (n := n) D)) (Y : CMfd.{0} n)
        (T : BlowupTower (CMfd.of (n := n) D) Y),
        IsInvDomain n R ∧ R.E = [] ∧
        NativeHSState R ((Subtype.val : D → X) ⁻¹' W)
          (hilbertSamuelAt (vanishingIdeal (n := n) W) a₀) ∧
        IsCanonical R ((invFamily hn n).inv R) T ∧ IsGeoResolution R T ∧
        StageCentres (fun P C => C ⊆ singularSet (n := n)
          (strictTransform n P.proj ((Subtype.val : D → X) ⁻¹' W))) T := by
  obtain ⟨D,haD,hDU,R,Y,T,hR,hE,hState,hCan,hRes⟩ :=
    exists_native_hs_ambient_terminal_window hn W hW a₀ ha₀ U₀ hU₀ haU₀
  exact ⟨D,haD,hDU,R,Y,T,hR,hE,hState,hCan,hRes,
    hs_tower_stage_centres_singular R hState.2.1.isClosed hState.hsTowerState T hRes.1⟩
end
end Hironaka.HironakaG8NativeHSStageCentres
