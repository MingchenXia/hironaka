import Hironaka.Resolution.HironakaG3EmptyAwareHistory
import Hironaka.Resolution.HironakaG8CompactNativeSingularPhase
import Hironaka.Resolution.HironakaOriginalCanonicalDimensionList
import Hironaka.Resolution.HironakaCompactFootprintJointTests
import Hironaka.Resolution.HironakaNormalCrossingsSeparationChoiceComparison
import Hironaka.Resolution.HironakaNormalCrossingsOpenRestrictionSeparation
import Hironaka.Resolution.HironakaResolutionSpaceLocal
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalGlobalFinite
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG8SingularFootprintExtension
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism RestrictEmptyTower
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  HironakaEmbeddedAnalytic HironakaStageCenters HironakaOriginalCanonicalDimensionList
  HironakaNormalCrossingsSeparationChoiceComparison HironakaNormalCrossingsOpenRestrictionSeparation
  HironakaResolutionSpaceLocal HironakaSmoothSubmersionOriginalGlobalFinite
  HironakaCompactFootprintOpenTowerExtension HironakaCompactFootprintJointTests
  HironakaG8CompactNativeSingularPhase HironakaAdmissibleSequence HironakaEmbeddedBoundary
  HironakaHolomorphicJetChartInvariance HomogenizedGlueingTower
  HironakaActualVanishingIntrinsicHSTransport HironakaG3EmptyAwareHistory

/-- Literal singular positions survive actual stage comparisons which may
insert or delete recorded empty blowups. -/
theorem singular_stages_of_emptyAware {n : ℕ} {X' X Y' Y : CMfd.{0} n}
    (W : Set X) (hW : IsClosed W)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : EmptyAwareTowerIso Φ T' T χ) :
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj (Φ ⁻¹' W))) T' →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T := by
  induction hiso with
  | refl => exact fun _ => trivial
  | @step Y' Y Z' Z T' T χ hiso C' π' hπ' C π hπ χ₁ hcomm hC ih =>
      intro hs
      refine ⟨ih hs.1,?_⟩
      intro c hc
      let c' : Y' := χ.symm c
      have hc' : c' ∈ C' := by
        rw [← hC]
        change χ (χ.symm c) ∈ C
        simpa using hc
      have hcSing := hs.2 hc'
      have hst := strictTransform_preimage_of_square Φ χ T'.contMDiff_proj T.contMDiff_proj W hW
        (fun z => emptyAware_proj_comm hiso z)
      rw [hst, singularSet_preimage_eq (isSubmersion_biholomorphism χ)] at hcSing
      simpa [c'] using hcSing
  | leftEmpty _ _ _ _ ih => exact fun hs => ih hs.1
  | rightEmpty _ _ _ _ ih => exact fun hs => ⟨ih hs, empty_subset _⟩

/-- Literal singular positions descend through an isomorphism of whole towers. -/
theorem singular_stages_of_tower_iso {n : ℕ} {X' X Y' Y : CMfd.{0} n}
    (W : Set X) (hW : IsClosed W)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) :
    StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj (Φ ⁻¹' W))) T' →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T := by
  exact singular_stages_of_emptyAware W hW Φ (emptyAware_of_isTowerIso hiso)

/-- Centres supported over an open are singular globally when the same
literal restricted tower has singular centres. -/
theorem singular_stages_of_restrict {n : ℕ} {X : CMfd.{0} n}
    (W : Set X) (U : Opens X) (K : Set X) (hKU : K ⊆ U) :
    ∀ {Y : CMfd.{0} n} (T : BlowupTower X Y), CentresOver K T →
      StageCentres (fun P C => C ⊆ singularSet (n := n)
        (strictTransform n P.proj ((Subtype.val : U → X) ⁻¹' W))) (restrict U T) →
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) T
  | _, .refl, _, _ => trivial
  | _, .step P C π hπ, ho, hs => by
      refine ⟨singular_stages_of_restrict W U K hKU P ho.1 hs.1,?_⟩
      intro c hc
      let v : openPreimage P U := ⟨c,hKU (ho.2 hc)⟩
      have hv := hs.2 (show v ∈ (Subtype.val : openPreimage P U → _) ⁻¹' C from hc)
      rw [strictTransform_restricted_tower U P W, singularSet_preimage_val] at hv
      exact hv

/-- A compact-footprint local test history with literal singular centres
extends to one actual ambient test history with the same singular positions. -/
theorem exists_compact_footprint_singular_test_extension
    {n : ℕ} {X Z : CMfd.{0} n} (M : MarkedIdeal n X)
    (hN : IsClosedSubmanifold n M.N) (hI : M.ideal.IsCoherent)
    (W : Set X) (hW : IsClosed W) (U : Opens X) (K : Set X)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (T : BlowupTower (CMfd.of (n := n) U) Z)
    (hOver : CentresOver ((Subtype.val : U → X) ⁻¹' K) T)
    (hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) T)
    (hStage : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U → X) ⁻¹' W))) T) :
    ∃ (Y : CMfd.{0} n) (Q : BlowupTower X Y),
      IsGeoTestTower M Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
      CentresOver K Q ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e ∧
        T.length = Q.length ∧ ∀ z, Q.proj (e z).val = (T.proj z).val := by
  obtain ⟨Y,Q,hQ,e,he,hLength,hProj⟩ :=
    exists_compact_footprint_extension U K hK hKU T hOver
  have hTQ := isGeoTestTower_of_supported_open_iso M hN hI U K hK.isClosed hKU Q hQ T e he hTest
  have hStageU : StageCentres (fun P C => C ⊆ singularSet (n := n)
      (strictTransform n P.proj ((Subtype.val : U → X) ⁻¹' W))) (restrict U Q) := by
    have hs := singular_stages_of_tower_iso (n := n) (X' := CMfd.of (n := n) U)
      (X := CMfd.of (n := n) U) (T' := T) (T := restrict U Q) (χ := e)
      ((Subtype.val : U → X) ⁻¹' W) (hW.preimage continuous_subtype_val)
      (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) he
    simp only [Diffeomorph.coe_refl, preimage_id] at hs
    exact hs hStage
  exact ⟨Y,Q,hTQ,singular_stages_of_restrict W U K hKU Q hQ hStageU,hQ,e,he,hLength,hProj⟩

/-- A compact local native record produces a global original-test singular
phase on exactly its compact cosupport footprint. -/
theorem exists_compact_native_local_phase_global_extension
    {n k : ℕ} (hn : 0<n) {X : CMfd.{0} n} (W : Set X)
    (hW : IsComplexAnalyticSubset (n := n) W) (U : Opens X) {H : ℕ → ℕ}
    (R : MarkedIdeal n (CMfd.of (n := n) U))
    (hR : ResolutionInvariantSpec.IsInvDomain k R) (hE : R.E = [])
    (hS : HironakaG11PresLineState.NativeHSState R ((Subtype.val : U → X) ⁻¹' W) H)
    (hK : IsCompact R.cosupp) :
    ∃ (Y Z : CMfd.{0} n) (Q : BlowupTower X Y)
      (T : BlowupTower (CMfd.of (n := n) U) Z),
      IsGeoTestTower (⟨univ,[],vanishingIdeal (n := n) W,1⟩ : MarkedIdeal n X) Q ∧
      StageCentres (fun P C => C ⊆ singularSet (n := n) (strictTransform n P.proj W)) Q ∧
      CentresOver ((Subtype.val : U → X) '' R.cosupp) Q ∧
      ResolutionInvariantSpec.IsCanonical R ((CanonicalCentres.invFamily hn k).inv R) T ∧
      IsGeoResolution R T ∧
      (∀ z : Z, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
          (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' W))) z ℓ ≤ H ℓ) ∧
        ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
          (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' W))) z ℓ < H ℓ) ∧
      ∃ e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U,
        IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e ∧
        T.length = Q.length ∧ ∀ z, Q.proj (e z).val = (T.proj z).val := by
  obtain ⟨Z,T,hCan,hRes,hOriginal,hStage,hDrop⟩ :=
    compact_native_record_global_singular_phase hn R hR hE hS hK
  let K : Set X := (Subtype.val : U → X) '' R.cosupp
  have hKC : IsCompact K := hK.image continuous_subtype_val
  have hKU : K ⊆ U := fun _ hx => by obtain ⟨x,_,rfl⟩ := hx; exact x.property
  have hOver : CentresOver ((Subtype.val : U → X) ⁻¹' K) T := by
    dsimp only [K]
    rw [Subtype.val_injective.preimage_image]
    exact centresOver_cosupp R hR.isWellFormed.isClosedSubmanifold_N hR.isWellFormed.isCoherent T hRes.1
  let M : MarkedIdeal n X := ⟨univ,[],vanishingIdeal (n := n) W,1⟩
  have hTest : IsGeoTestTower (MarkedIdeal.pullback (Subtype.val : U → X) M) T := by
    rw [pullback_val_mk_vanishingIdeal U [] W]
    exact hOriginal
  obtain ⟨Y,Q,hQ,hSing,hFoot,e,he,hLength,hProj⟩ :=
    exists_compact_footprint_singular_test_extension M isClosedSubmanifold_univ
      (CartanIrreducible.cartanCoherence W hW) W hW.isClosed U K hKC hKU T hOver hTest hStage
  exact ⟨Y,Z,Q,T,hQ,hSing,hFoot,hCan,hRes,hDrop,e,he,hLength,hProj⟩

/-- A profile drop on a local tower transfers to the actual global strict
transform over the same source open, through the provided tower isomorphism. -/
theorem profile_drop_of_open_tower_iso {n : ℕ} {X Y Z : CMfd.{0} n}
    (W : Set X) (hW : IsClosed W) (U : Opens X) (H : ℕ → ℕ)
    (Q : BlowupTower X Y) (T : BlowupTower (CMfd.of (n := n) U) Z)
    (e : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ openPreimage Q U)
    (he : IsTowerIso (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) T (restrict U Q) e)
    (hDrop : ∀ z : Z, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' W))) z ℓ ≤ H ℓ) ∧
      ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' W))) z ℓ < H ℓ) :
    ∀ y : openPreimage Q U, (∀ ℓ, hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n Q.proj W)) y.val ℓ ≤ H ℓ) ∧
      ∃ ℓ, hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ < H ℓ := by
  have hst := strictTransform_preimage_of_square
    (Diffeomorph.refl 𝓘(ℂ,ComplexModel n) U ∞) e T.contMDiff_proj (restrict U Q).contMDiff_proj
    ((Subtype.val : U → X) ⁻¹' W) (hW.preimage continuous_subtype_val)
    (fun z => (he.proj_comm z).symm)
  simp only [Diffeomorph.coe_refl, preimage_id] at hst
  rw [strictTransform_restricted_tower U Q W] at hst
  intro y
  let z := e.symm y
  have hHS (ℓ : ℕ) : hilbertSamuelAt (vanishingIdeal (n := n)
      (strictTransform n T.proj ((Subtype.val : U → X) ⁻¹' W))) z ℓ =
      hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n Q.proj W)) y.val ℓ := by
    rw [hst, hilbertSamuelAt_vanishing_actual_biholomorphic_any,
      hilbertSamuelAt_vanishing_actual_open_any]
    simp [z]
  obtain ⟨hle,ℓ,hlt⟩ := hDrop z
  exact ⟨fun ℓ => (hHS ℓ).symm ▸ hle ℓ, ⟨ℓ,(hHS ℓ).symm ▸ hlt⟩⟩
end
end Hironaka.HironakaG8SingularFootprintExtension
