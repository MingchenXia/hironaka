import Hironaka.Resolution.HironakaG8SingularFootprintExtension
import Hironaka.Resolution.HironakaG8NativeHSAmbientTerminalWindow
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8IsolatedProfileGlobalPhase
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance
  HironakaG11PresLineState HironakaG8NativeHSAmbientTerminalWindow
  HironakaActualVanishingIntrinsicHSTransport HironakaG8SingularFootprintExtension
  HironakaStageCenters RestrictEmptyTower BlowupTowerIsomorphism

/-- A point isolated in its actual Hilbert--Samuel level has an actual
native window whose whole cosupport is that single point. -/
theorem exists_isolated_profile_native_window {n : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (a : X) (ha : a ∈ singularSet (n := n) W) (O : Opens X) (haO : a ∈ O)
    (hisol : ∀ x ∈ O, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ) → x = a) :
    ∃ (D : Opens X) (haD : a ∈ D), D ≤ O ∧
      ∃ R : MarkedIdeal n (CMfd.of (n := n) D),
        ResolutionInvariantSpec.IsInvDomain n R ∧ R.E = [] ∧
        NativeHSState R ((Subtype.val : D → X) ⁻¹' W)
          (hilbertSamuelAt (vanishingIdeal (n := n) W) a) ∧
        R.cosupp = {⟨a,haD⟩} := by
  obtain ⟨D,haD,hDO,R,Y,T,hR,hE,hS,hCan,hRes⟩ :=
    exists_native_hs_ambient_terminal_window hn W hW a ha O O.isOpen haO
  refine ⟨D,haD,hDO,R,hR,hE,hS,?_⟩
  rw [hS.cosupp_eq]
  ext x
  constructor
  · intro hx
    have hlocal : ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) (x : X) ℓ =
        hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ := by
      intro ℓ
      exact (hilbertSamuelAt_vanishing_actual_open_any D W x ℓ).symm.trans (hx ℓ)
    exact Subtype.ext (hisol x (hDO x.property) hlocal)
  · intro hx
    have heq : x = ⟨a,haD⟩ := hx
    subst x
    intro ℓ
    exact hilbertSamuelAt_vanishing_actual_open_any D W ⟨a,haD⟩ ℓ

/-- An isolated singular Hilbert--Samuel level produces a genuine finite
ambient singular-centred original-test phase over the single original point. -/
theorem exists_isolated_profile_global_phase {n : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (a : X) (ha : a ∈ singularSet (n := n) W) (O : Opens X) (haO : a ∈ O)
    (hisol : ∀ x ∈ O, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ) → x = a) :
    ∃ (D : Opens X) (haD : a ∈ D) (R : MarkedIdeal n (CMfd.of (n := n) D))
      (Y Z : CMfd.{0} n) (Q : BlowupTower X Y) (T : BlowupTower (CMfd.of (n := n) D) Z),
      D ≤ O ∧ R.cosupp = {⟨a,haD⟩} ∧
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
      CentresOver {a} Q ∧ IsGeoResolution R T ∧
      (∀ z : Z, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
          (strictTransform n T.proj ((Subtype.val : D → X) ⁻¹' W))) z ℓ ≤
            hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ) ∧
        ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
          (strictTransform n T.proj ((Subtype.val : D → X) ⁻¹' W))) z ℓ <
            hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ) ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q D,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) D ∞) T (restrict D Q) e ∧
        T.length = Q.length ∧ (∀ z, Q.proj (e z).val = (T.proj z).val) ∧
        ∀ y : openPreimage Q D, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
          (strictTransform n Q.proj W)) y.val ℓ ≤ hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ) ∧
          ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ <
            hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ := by
  obtain ⟨D,haD,hDO,R,hR,hE,hS,hcos⟩ :=
    exists_isolated_profile_native_window hn W hW a ha O haO hisol
  have hK : IsCompact R.cosupp := by rw [hcos]; exact isCompact_singleton
  obtain ⟨Y,Z,Q,T,hTest,hStage,hFoot,hCan,hRes,hDrop,e,he,hLength,hProj⟩ :=
    exists_compact_native_local_phase_global_extension hn W hW D R hR hE hS hK
  have hFoot' : CentresOver {a} Q := by simpa only [hcos, image_singleton] using hFoot
  exact ⟨D,haD,R,Y,Z,Q,T,hDO,hcos,hTest,hStage,hFoot',hRes,hDrop,e,he,hLength,hProj,
    profile_drop_of_open_tower_iso W hW.isClosed D (hilbertSamuelAt (vanishingIdeal (n := n) W) a)
      Q T e he hDrop⟩
end
end Hironaka.HironakaG8IsolatedProfileGlobalPhase
