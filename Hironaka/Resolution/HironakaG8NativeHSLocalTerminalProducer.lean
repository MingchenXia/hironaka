import Hironaka.Resolution.HironakaG11PresNativeStateWindow
import Hironaka.Resolution.HironakaEmbeddedResolutionLocal
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8NativeHSLocalTerminalProducer
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance BlowupTowers MarkedIdeals
  MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres
  HironakaG11PresLineState HironakaG11PresNativeStateWindow HironakaG11PresNativePhase HironakaEmbeddedResolutionLocal

/-- A singular point admits an actual native HS window inside any prescribed
neighborhood, with a smaller actual canonical resolving native window. -/
theorem exists_native_hs_local_terminal_window {n : ℕ} (hn : 0<n) {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (a₀ : X) (ha₀ : a₀ ∈ singularSet (n := n) W)
    (U₀ : Set X) (hU₀ : IsOpen U₀) (haU₀ : a₀ ∈ U₀) :
    ∃ (U : Opens (ComplexModel n)) (V : Opens X)
      (η : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ V)
      (O : Opens (ComplexModel n)) (hOU : O ≤ U) (z₀ : O)
      (Q : MarkedIdeal n (CMfd.of (n := n) (opensIn U O)))
      (K : Opens (CMfd.of (n := n) (opensIn U O)))
      (z : K) (Y : CMfd.{0} n) (T : BlowupTower (CMfd.of (n := n) K) Y),
      (η (Opens.inclusion hOU z₀) : X) = a₀ ∧
      (∀ v : O, (η (Opens.inclusion hOU v) : X) ∈ U₀) ∧
      (Subtype.val : K → opensIn U O) z = ⟨Opens.inclusion hOU z₀,z₀.property⟩ ∧
      let R := MarkedIdeal.pullback (Subtype.val : K → opensIn U O) Q
      IsInvDomain n R ∧ R.E = [] ∧
      NativeHSState (X := CMfd.of (n := n) K) R ((Subtype.val : K → opensIn U O) ⁻¹'
        ((Subtype.val : opensIn U O → U) ⁻¹' ((fun v : U => (η v : X)) ⁻¹' W)))
        (hilbertSamuelAt (vanishingIdeal (n := n) W) a₀) ∧
      IsCanonical R ((invFamily hn n).inv R) T ∧ IsGeoResolution R T := by
  obtain ⟨U,V,η,O,hOU,z₀,Q,hz,hinside,hQ,hE,hState⟩ :=
    exists_native_state_phase_window W hW a₀ ha₀ U₀ hU₀ haU₀
  let z₁ : opensIn U O := ⟨Opens.inclusion hOU z₀,z₀.property⟩
  obtain ⟨K,hK,Y,T,hCan,hRes⟩ := exists_local_resolution_isCanonical (invFamily hn n) hQ
    (K := ({z₁} : Set (opensIn U O))) isCompact_singleton
  have hzK : z₁ ∈ K := hK (Set.mem_singleton z₁)
  let z : K := ⟨z₁,hzK⟩
  let R := MarkedIdeal.pullback (Subtype.val : K → opensIn U O) Q
  have hR : IsInvDomain n R := InvDomainTowerAlong.isInvDomain_pullback_val K hQ
  have hRE : R.E = [] := by change Q.E.map ((Subtype.val : K → opensIn U O) ⁻¹' ·) = []; rw [hE]; rfl
  exact ⟨U,V,η,O,hOU,z₀,Q,K,z,Y,T,hz,hinside,rfl,hR,hRE,hState.restrict K,hCan,hRes⟩
end
end Hironaka.HironakaG8NativeHSLocalTerminalProducer
