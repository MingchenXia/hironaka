import Hironaka.Resolution.HironakaG8NativeHSLocalTerminalProducer
import Hironaka.Resolution.HironakaG8OpenHoloEmbeddingComposition
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8NativeHSAmbientTerminalWindow
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance BlowupTowers BlowupTowerTransforms
  BlowupTowerIsomorphism MarkedIdealTowerTransport MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionInvariantSpec CanonicalCentres HironakaBaseChange
  HironakaG11PresLineState HironakaG11PresNativePhase HironakaG8NativeHSLocalTerminalProducer
  HironakaG8OpenHoloEmbeddingComposition

/-- Every singular point has an actual ambient-open native HS record and
canonical resolving tower within a prescribed neighborhood. -/
theorem exists_native_hs_ambient_terminal_window {n : ℕ} (hn : 0<n) {X : CMfd.{0} n}
    (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (a₀ : X) (ha₀ : a₀ ∈ singularSet (n := n) W)
    (U₀ : Set X) (hU₀ : IsOpen U₀) (haU₀ : a₀ ∈ U₀) :
    ∃ (D : Opens X), a₀ ∈ D ∧ (D : Set X) ⊆ U₀ ∧
      ∃ (R : MarkedIdeal n (CMfd.of (n := n) D)) (Y : CMfd.{0} n)
        (T : BlowupTower (CMfd.of (n := n) D) Y),
        IsInvDomain n R ∧ R.E = [] ∧
        NativeHSState R ((Subtype.val : D → X) ⁻¹' W)
          (hilbertSamuelAt (vanishingIdeal (n := n) W) a₀) ∧
        IsCanonical R ((invFamily hn n).inv R) T ∧ IsGeoResolution R T := by
  obtain ⟨U,V,η,O,hOU,z₀,Q,K,z,Y,T,hz,hinside,hzK,hR,hRE,hS,hCan,hRes⟩ :=
    exists_native_hs_local_terminal_window hn W hW a₀ ha₀ U₀ hU₀ haU₀
  let R₀ := MarkedIdeal.pullback (Subtype.val : K → opensIn U O) Q
  let f : K → X := fun t => (η ((t.val : opensIn U O).val) : X)
  have hf₁ : IsOpenHoloEmbedding n (Subtype.val : K → opensIn U O) := isOpenHoloEmbedding_val K
  have hf₂ : IsOpenHoloEmbedding n (Subtype.val : opensIn U O → U) := isOpenHoloEmbedding_val (opensIn U O)
  have hf₃ : IsOpenHoloEmbedding n (fun u : U => (η u : X)) := ⟨V,η,fun _ => rfl⟩
  have hf : IsOpenHoloEmbedding n f := by
    change IsOpenHoloEmbedding n ((fun u : U => (η u : X)) ∘
      ((Subtype.val : opensIn U O → U) ∘ (Subtype.val : K → opensIn U O)))
    exact isOpenHoloEmbedding_comp (A := X) (B := CMfd.of (n := n) U) (C := CMfd.of (n := n) K)
      hf₃ (isOpenHoloEmbedding_comp (A := CMfd.of (n := n) U)
        (B := CMfd.of (n := n) (opensIn U O)) (C := CMfd.of (n := n) K) hf₂ hf₁)
  obtain ⟨D,e,he⟩ := hf
  have hfa : f z = a₀ := by
    change (η ((z.val : opensIn U O).val) : X) = a₀
    rw [hzK]
    exact hz
  have haD : a₀ ∈ D := by rw [← hfa, he]; exact (e z).property
  have hDU : (D : Set X) ⊆ U₀ := by
    intro x hx
    let t := e.symm ⟨x,hx⟩
    have ht : f t = x := by rw [he,e.apply_symm_apply]
    rw [← ht]
    let v : O := ⟨((t.val : opensIn U O).val : U).val,(t.val : opensIn U O).property⟩
    exact hinside v
  let R := MarkedIdeal.pullback e.symm R₀
  have hR' : IsInvDomain n R := InvDomainTowerAlong.isInvDomain_pullback e.symm hR
  have hE : R.E = [] := by change R₀.E.map (e.symm ⁻¹' ·) = []; rw [hRE]; rfl
  have hSet : e.symm ⁻¹' (f ⁻¹' W) = (Subtype.val : D → X) ⁻¹' W := by
    ext x
    change f (e.symm x) ∈ W ↔ x.val ∈ W
    rw [he,e.apply_symm_apply]
  have hS' : NativeHSState (X := CMfd.of (n := n) D) R ((Subtype.val : D → X) ⁻¹' W)
      (hilbertSamuelAt (vanishingIdeal (n := n) W) a₀) := by
    rw [← hSet]
    exact NativeHSState.pullback (X := CMfd.of (n := n) K) (X' := CMfd.of (n := n) D) e.symm hS
  have hCan' := Seq.ResolutionInvariantExt.isCanonical_of_isTowerIso (X' := CMfd.of (n := n) D)
    (invFamily hn n) hR e.symm (transport_isTowerIso (X' := CMfd.of (n := n) D) e.symm T) hCan
  have hRes' := (isGeoResolution_transport_iff (X' := CMfd.of (n := n) D) e.symm hR.isWellFormed.isCoherent T).mpr hRes
  exact ⟨D,haD,hDU,R,_,_,hR',hE,hS',hCan',hRes'⟩
end
end Hironaka.HironakaG8NativeHSAmbientTerminalWindow
