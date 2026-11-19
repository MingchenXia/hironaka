import Hironaka.Resolution.HironakaG8OriginalOverlapPrefixTransport
import Hironaka.Resolution.HironakaG8NativePhaseCertificate

/-! Original phase maxima on the literal active Hilbert–Samuel level. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Hironaka.HironakaG8ActiveProfileCentreTransport

open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism ResolutionDriver ResolutionInvariantSpec CanonicalCentres
  HironakaG3EmptyAwareHistory HironakaG8NativePhaseCertificate
  HironakaG8OriginalOverlapPrefixTransport HironakaActualVanishingIntrinsicHSTransport
  HironakaHolomorphicJetChartInvariance HironakaEmbeddedAnalytic
  HironakaNormalCrossingsSeparationChoiceComparison HironakaStageCenters RestrictEmptyTower

variable {n : ℕ} {X₁ X₂ Y₁ Y₂ : CMfd.{0} n}

/-- The pullback of the phase's base Hilbert–Samuel level agrees on the
two physical prefix stages. -/
theorem phase_level_over_prefix_preimage
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (ψ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂)
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) (W : Set X₂) (H : ℕ → ℕ) :
    T₁.proj ⁻¹' phaseLevel (Φ ⁻¹' W) H = ψ ⁻¹' (T₂.proj ⁻¹' phaseLevel W H) := by
  ext y
  change hilbertSamuelAt (vanishingIdeal (n := n) (Φ ⁻¹' W)) (T₁.proj y) = H ↔
    hilbertSamuelAt (vanishingIdeal (n := n) W) (T₂.proj (ψ y)) = H
  rw [funext (hilbertSamuelAt_vanishing_actual_biholomorphic_any Φ W (T₁.proj y))]
  rw [emptyAware_proj_comm h y]

/-- Original canonicality and the maxima over the active epoch transport
across an actual overlap of canonical prefixes. -/
theorem original_active_profile_max_transport
    (hn : 0 < n) (M : MarkedIdeal n X₂) (hM : IsInvDomain n M)
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (ψ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂)
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) (W : Set X₂) (H : ℕ → ℕ) :
    let M₁ := MarkedIdeal.pullback Φ M
    let R := invFamily hn n
    IsCanonical M (R.inv M) T₂ →
      IsCanonical M₁ (R.inv M₁) T₁ ∧
      maxLocus (R.inv M₁ T₁)
        ((geoTransformAlong M₁ T₁).cosupp ∩ T₁.proj ⁻¹' phaseLevel (Φ ⁻¹' W) H) =
      ψ ⁻¹' maxLocus (R.inv M T₂)
        ((geoTransformAlong M T₂).cosupp ∩ T₂.proj ⁻¹' phaseLevel W H) := by
  intro M₁ R hCan
  have hRead := original_prefix_transport_of_emptyAware hn M hM Φ T₁ T₂ ψ h
  obtain ⟨hCos, hOrder, _⟩ := hRead.2 hCan
  refine ⟨hRead.1.mpr hCan, ?_⟩
  have hMask := phase_level_over_prefix_preimage Φ T₁ T₂ ψ h W H
  have hCosAt (a : Y₁) : a ∈ (geoTransformAlong M₁ T₁).cosupp ↔
      ψ a ∈ (geoTransformAlong M T₂).cosupp := by
    change a ∈ (geoTransformAlong M₁ T₁).cosupp ↔ a ∈ ψ ⁻¹' (geoTransformAlong M T₂).cosupp
    rw [show (geoTransformAlong M₁ T₁).cosupp = _ from hCos]
  have hMaskAt (a : Y₁) : a ∈ T₁.proj ⁻¹' phaseLevel (Φ ⁻¹' W) H ↔
      ψ a ∈ T₂.proj ⁻¹' phaseLevel W H := by
    change a ∈ T₁.proj ⁻¹' phaseLevel (Φ ⁻¹' W) H ↔ a ∈ ψ ⁻¹' (T₂.proj ⁻¹' phaseLevel W H)
    rw [hMask]
  ext a
  constructor
  · rintro ⟨ha, hm⟩
    refine ⟨⟨(hCosAt a).mp ha.1, (hMaskAt a).mp ha.2⟩, ?_⟩
    intro z hz
    obtain ⟨b, rfl⟩ := ψ.surjective z
    have hb : b ∈ (geoTransformAlong M₁ T₁).cosupp ∩
        T₁.proj ⁻¹' phaseLevel (Φ ⁻¹' W) H :=
      ⟨(hCosAt b).mpr hz.1, (hMaskAt b).mpr hz.2⟩
    exact (hOrder b hb.1 a ha.1).mp (hm b hb)
  · rintro ⟨ha, hm⟩
    have ha₁ : a ∈ (geoTransformAlong M₁ T₁).cosupp ∩
        T₁.proj ⁻¹' phaseLevel (Φ ⁻¹' W) H :=
      ⟨(hCosAt a).mpr ha.1, (hMaskAt a).mpr ha.2⟩
    refine ⟨ha₁, fun b hb => (hOrder b hb.1 a ha₁.1).mpr ?_⟩
    exact hm (ψ b) ⟨(hCosAt b).mp hb.1, (hMaskAt b).mp hb.2⟩

/-- The rebased strict-transform profile has the same maximum and exactly
the same maximizing slice on two physically identified views of an epoch
endpoint. The task slice (K) may itself be the covered physical open or
the compact-enclosed footprint used for the next restart. -/
theorem rebase_profile_max_transport
    (Φ : X₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X₂)
    (T₁ : BlowupTower X₁ Y₁) (T₂ : BlowupTower X₂ Y₂)
    (ψ : Y₁ ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y₂)
    (h : EmptyAwareTowerIso Φ T₁ T₂ ψ) (W : Set X₂) (hW : IsClosed W)
    (K : Set Y₂) :
    let A₁ := strictTransform n T₁.proj (Φ ⁻¹' W)
    let A₂ := strictTransform n T₂.proj W
    let HS₁ : Y₁ → ℕ → ℕ := hilbertSamuelAt (vanishingIdeal (n := n) A₁)
    let HS₂ : Y₂ → ℕ → ℕ := hilbertSamuelAt (vanishingIdeal (n := n) A₂)
    (∀ z, HS₁ z = HS₂ (ψ z)) ∧
    maxLocus (toLex ∘ HS₁) (ψ ⁻¹' K) = ψ ⁻¹' maxLocus (toLex ∘ HS₂) K := by
  intro A₁ A₂ HS₁ HS₂
  have hStrict : A₁ = ψ ⁻¹' A₂ :=
    strictTransform_preimage_of_square Φ ψ T₁.contMDiff_proj T₂.contMDiff_proj
      W hW (emptyAware_proj_comm h)
  have hValues (z : Y₁) : HS₁ z = HS₂ (ψ z) := by
    change hilbertSamuelAt (vanishingIdeal (n := n) A₁) z = _
    rw [hStrict]
    exact funext (hilbertSamuelAt_vanishing_actual_biholomorphic_any ψ A₂ z)
  refine ⟨hValues,?_⟩
  have hFun : (toLex ∘ HS₁) = (toLex ∘ HS₂) ∘ ψ := by
    funext a
    exact congrArg toLex (hValues a)
  rw [hFun]
  ext z
  constructor
  · rintro ⟨hz, hm⟩
    refine ⟨hz, ?_⟩
    intro y hy
    obtain ⟨a, rfl⟩ := ψ.surjective y
    exact hm a hy
  · rintro ⟨hz, hm⟩
    exact ⟨hz, fun a ha => hm (ψ a) ha⟩

/-- A certified canonical chart history uses exactly the original
maximum on the active profile at every occupied step of its actual phase. -/
theorem stage_centres_eq_active_profile_max
    {Λ : Type} [LinearOrder Λ] (M : MarkedIdeal n X₂)
    (inv : ∀ {Y : CMfd.{0} n}, BlowupTower X₂ Y → Y → Λ)
    (W : Set X₂) (H : ℕ → ℕ) (T : BlowupTower X₂ Y₂)
    (hOver : CentresOver (phaseLevel W H) T) (hCan : IsCanonical M inv T) :
    StageCentres (fun P C => C = ∅ ∨
      C = maxLocus (inv P) ((geoTransformAlong M P).cosupp ∩ P.proj ⁻¹' phaseLevel W H)) T := by
  induction T with
  | refl => trivial
  | @step A B P C π hπ ih =>
    refine ⟨ih hOver.1 hCan.1,?_⟩
    rcases hCan.2 with he | hC
    · exact Or.inl he
    by_cases hne : C.Nonempty
    · right
      obtain ⟨a, ha⟩ := hne
      ext z
      constructor
      · intro hz
        have hzMax := hC ▸ hz
        exact ⟨⟨hzMax.1,hOver.2 hz⟩, fun b hb => hzMax.2 b hb.1⟩
      · intro hz
        have haMax := hC ▸ ha
        have haz := hz.2 a ⟨haMax.1,hOver.2 ha⟩
        rw [hC]
        exact ⟨hz.1.1, fun b hb => (haMax.2 b hb).trans haz⟩
    · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

end Hironaka.HironakaG8ActiveProfileCentreTransport
