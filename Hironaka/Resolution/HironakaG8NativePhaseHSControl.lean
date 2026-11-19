import Hironaka.Resolution.HironakaG3EmptyAwareHistory
import Hironaka.Resolution.HironakaG8IsolatedProfileGlobalPhase
import Hironaka.Resolution.HironakaG8SingularFootprintExtension
import Hironaka.Resolution.HironakaUniformHistoricalSuccessorCompactFootprint
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8NativePhaseHSControl
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaEmbeddedAnalytic HironakaHolomorphicJetChartInvariance HironakaStageCenters
  HironakaG11PresLineState HironakaG8HSTowerStateStrictTransform
  HironakaG8SingularFootprintExtension HironakaResolutionSpaceLocal
  HironakaNormalCrossingsOpenRestrictionSeparation HironakaNormalCrossingsSeparationChoiceComparison
  HironakaOriginalCanonicalDimensionList HironakaSmoothSubmersionOriginalGlobalFinite
  HironakaActualVanishingIntrinsicHSTransport HironakaUniformHistoricalSuccessorCompactFootprint
  HironakaG8IsolatedProfileGlobalPhase HironakaG3EmptyAwareHistory

/-- Every centre of a native test history has the actual current HS profile H. -/
theorem native_test_stages_HS_profile {n : ℕ} {X : CMfd.{0} n}
    (Q : MarkedIdeal n X) {W : Set X} (hW : IsClosed W) {H : ℕ → ℕ}
    (hs : HironakaG11PresTowerState.HSTowerState Q W H) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), IsGeoTestTower Q T →
      StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ,
        hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) c ℓ = H ℓ) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, ht => by
      refine ⟨native_test_stages_HS_profile Q hW hs T ht.1,?_⟩
      intro c hc ℓ
      have hstate := hs T ht.1
      have he := (hstate.2.2.2.1 c).mp (ht.2.2.1 hc)
      rw [hsTowerState_strictAlong_eq_strictTransform Q hW hs T ht.1] at he
      exact he ℓ

/-- Empty-aware comparison preserves the actual prescribed HS profile on centres. -/
theorem stages_HS_profile_of_emptyAware {n : ℕ} {X' X Y' Y : CMfd.{0} n}
    (W : Set X) (hW : IsClosed W) (H : ℕ → ℕ)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : EmptyAwareTowerIso Φ T' T χ) :
    StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
      (strictTransform n P.proj (Φ ⁻¹' W))) c ℓ = H ℓ) T' →
    StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
      (strictTransform n P.proj W)) c ℓ = H ℓ) T := by
  induction hiso with
  | refl => exact fun _ => trivial
  | @step Y' Y Z' Z T' T χ hiso C' π' hπ' C π hπ χ₁ hcomm hC ih =>
      intro hs
      refine ⟨ih hs.1,?_⟩
      intro c hc ℓ
      let c' : Y' := χ.symm c
      have hc' : c' ∈ C' := by
        rw [← hC]
        change χ (χ.symm c) ∈ C
        simpa using hc
      have hcH := hs.2 c' hc' ℓ
      have hst := strictTransform_preimage_of_square Φ χ T'.contMDiff_proj T.contMDiff_proj W hW
        (emptyAware_proj_comm hiso)
      rw [hst,hilbertSamuelAt_vanishing_actual_biholomorphic_any] at hcH
      simpa [c'] using hcH
  | leftEmpty _ _ _ _ ih => exact fun hs => ih hs.1
  | rightEmpty _ _ _ _ ih =>
      intro hs
      refine ⟨ih hs,?_⟩
      intro c hc
      exact False.elim hc

/-- Constant native profile positions transfer through the same physical
tower isomorphism. -/
theorem stages_HS_profile_of_tower_iso {n : ℕ} {X' X Y' Y : CMfd.{0} n}
    (W : Set X) (hW : IsClosed W) (H : ℕ → ℕ)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) :
    StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
      (strictTransform n P.proj (Φ ⁻¹' W))) c ℓ = H ℓ) T' →
    StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
      (strictTransform n P.proj W)) c ℓ = H ℓ) T := by
  exact stages_HS_profile_of_emptyAware W hW H Φ (emptyAware_of_isTowerIso hiso)

/-- A supported ambient tower inherits the exact profile from its restriction. -/
theorem stages_HS_profile_of_restrict {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (H : ℕ → ℕ) (U : Opens X) (K : Set X) (hKU : K ⊆ U) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), CentresOver K T →
      StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n P.proj ((Subtype.val : U → X) ⁻¹' W))) c ℓ = H ℓ) (restrict U T) →
      StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n P.proj W)) c ℓ = H ℓ) T
  | _, .refl, _, _ => trivial
  | _, .step P C π hπ, ho, hs => by
      refine ⟨stages_HS_profile_of_restrict W H U K hKU P ho.1 hs.1,?_⟩
      intro c hc ℓ
      let v : openPreimage P U := ⟨c,hKU (ho.2 hc)⟩
      have hv := hs.2 v (show v ∈ (Subtype.val : openPreimage P U → _) ⁻¹' C from hc) ℓ
      rw [strictTransform_restricted_tower U P W,hilbertSamuelAt_vanishing_actual_open_any] at hv
      exact hv

/-- A stagewise prescribed profile is in particular constant on each actual centre. -/
theorem stages_HS_profile_constant {n : ℕ} {X : CMfd.{0} n} (W : Set X) (H : ℕ → ℕ) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y),
      StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n P.proj W)) c ℓ = H ℓ) T →
      StageCentres (fun P C => ∀ x ∈ C, ∀ y ∈ C, ∀ ℓ,
        hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) x ℓ =
          hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n P.proj W)) y ℓ) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hs => by
      refine ⟨stages_HS_profile_constant W H T hs.1,?_⟩
      intro x hx y hy ℓ
      exact (hs.2 x hx ℓ).trans (hs.2 y hy ℓ).symm

/-- A compact local native phase extends to an actual global singular-centred
original test history with no HS increase anywhere and strict drop over its
window. -/
theorem exists_compact_native_local_phase_global_HS_control {n k : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (U : Opens X) {H : ℕ → ℕ} (R : MarkedIdeal n (CMfd.of (n := n) U))
    (hR : ResolutionInvariantSpec.IsInvDomain k R) (hE : R.E = [])
    (hS : NativeHSState R ((Subtype.val : U → X) ⁻¹' W) H) (hK : IsCompact R.cosupp) :
    ∃ (Y : CMfd.{0} n) (Q : BlowupTower X Y),
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
      CentresOver ((Subtype.val : U → X) '' R.cosupp) Q ∧
      StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n P.proj W)) c ℓ = H ℓ) Q ∧
      (∀ y ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (Q.proj y) ℓ) ∧
      ∀ y : openPreimage Q U, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n Q.proj W)) y.val ℓ ≤ H ℓ) ∧
        ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ < H ℓ := by
  obtain ⟨Y,Z,Q,T,hTest,hSing,hFoot,hCan,hRes,hDrop,e,he,hLength,hProj⟩ :=
    exists_compact_native_local_phase_global_extension hn W hW U R hR hE hS hK
  let K : Set X := (Subtype.val : U → X) '' R.cosupp
  have hKU : K ⊆ U := fun _ hx => by obtain ⟨x,_,rfl⟩ := hx; exact x.property
  have hLocal := native_test_stages_HS_profile R (hW.isClosed.preimage continuous_subtype_val)
    hS.hsTowerState T hRes.1
  have hRestricted : StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ,
      hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n P.proj ((Subtype.val : U → X) ⁻¹' W))) c ℓ = H ℓ) (restrict U Q) := by
    have h := stages_HS_profile_of_tower_iso (n := n)
      (X' := CMfd.of (n := n) U) (X := CMfd.of (n := n) U)
      (T' := T) (T := restrict U Q) (χ := e)
      ((Subtype.val : U → X) ⁻¹' W) (hW.isClosed.preimage continuous_subtype_val) H
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) he
    simp only [Diffeomorph.coe_refl, preimage_id] at h
    exact h hLocal
  have hProfile := stages_HS_profile_of_restrict W H U K hKU Q hFoot hRestricted
  have hConst := stages_HS_profile_constant W H Q hProfile
  exact ⟨Y,Q,hTest,hSing,hFoot,hProfile,
    actual_hs_constant_history_pointwise_bound W hW Q hConst,
    profile_drop_of_open_tower_iso W hW.isClosed U H Q T e he hDrop⟩

/-- An isolated singular profile gives an actual global singular-centred
phase with no HS increase anywhere and strict drop above its local window. -/
theorem exists_isolated_profile_global_HS_control {n : ℕ} (hn : 0<n)
    {X : CMfd.{0} n} (W : Set X) (hW : IsComplexAnalyticSubset (n := n) W)
    (a : X) (ha : a ∈ singularSet (n := n) W) (O : Opens X) (haO : a ∈ O)
    (hisol : ∀ x ∈ O, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) W) x ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ) → x = a) :
    ∃ (D : Opens X), a ∈ D ∧ D ≤ O ∧ ∃ (Y : CMfd.{0} n) (Q : BlowupTower X Y),
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
      CentresOver {a} Q ∧
      StageCentres (fun P C => ∀ c ∈ C, ∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n P.proj W)) c ℓ = hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ) Q ∧
      (∀ y ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y ℓ ≤
        hilbertSamuelAt (vanishingIdeal (n := n) W) (Q.proj y) ℓ) ∧
      ∀ y : openPreimage Q D, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n Q.proj W)) y.val ℓ ≤ hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ) ∧
        ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ <
          hilbertSamuelAt (vanishingIdeal (n := n) W) a ℓ := by
  obtain ⟨D,haD,hDO,R,hR,hE,hS,hcos⟩ :=
    exists_isolated_profile_native_window hn W hW a ha O haO hisol
  have hK : IsCompact R.cosupp := by rw [hcos]; exact isCompact_singleton
  obtain ⟨Y,Q,hTest,hSing,hFoot,hProfile,hBound,hDrop⟩ :=
    exists_compact_native_local_phase_global_HS_control hn W hW D R hR hE hS hK
  have hFoot' : CentresOver {a} Q := by simpa only [hcos,image_singleton] using hFoot
  exact ⟨D,haD,hDO,Y,Q,hTest,hSing,hFoot',hProfile,hBound,hDrop⟩
end
end Hironaka.HironakaG8NativePhaseHSControl
