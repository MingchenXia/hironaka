/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalTerminalChoiceNaturality
import Hironaka.Resolution.CanonicalResolution
/-! Original compact canonical terminal objects and intrinsic smooth arrows.
Complete four-node mathematics preceded proofs. All actual terminal histories
are outputs of the genuine per-sequence canonical driver, never caller inputs. -/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalCompactTerminal
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionOrderedChoiceBaseChange
  HironakaSmoothSubmersionOrderedChoiceImageTrace HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionOriginalTerminalFunctor HironakaOriginalTerminalProjectionUniqueness
  HironakaSmoothSubmersionOriginalTerminalChoiceNaturality HironakaSmoothSubmersionComposition
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m ℓ : ℕ} {X : CMfd.{u} n} {Y : CMfd.{u} m} {Z : CMfd.{u} ℓ}

/-- An actual original finite terminal object is constructed internally. -/
def compactCanonicalTower [CompactSpace X] (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    Σ D : CMfd.{u} n, {T : BlowupTower X D //
      ResolutionDriver.IsCanonicalSegment M ((canonicalInvariant n).inv M) T ∧ IsGeoResolution M T} :=
  let h := ResolutionInvariantSeq.exists_isGeoResolution_isCanonicalSegment (canonicalInvariant n) hM
  ⟨h.choose,h.choose_spec.choose,h.choose_spec.choose_spec⟩

theorem compactCanonicalTower_isCanonical [CompactSpace X]
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    IsCanonical M ((canonicalInvariant n).inv M) (compactCanonicalTower M hM).2.val :=
  ResolutionInvariantDriver.isCanonical_of_isCanonicalSegment _ _
    (compactCanonicalTower M hM).2.property.1

def compactTerminalMap [CompactSpace X] [CompactSpace Y] {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    (compactCanonicalTower (markedPullback (m := m) f M) (original_ambient_domain_pullback hf M hM)).1 →
      (compactCanonicalTower M hM).1 :=
  let hN := original_ambient_domain_pullback hf M hM
  let S := compactCanonicalTower (markedPullback (m := m) f M) hN
  let T := compactCanonicalTower M hM
  terminalSmoothMap hf M hM S.2.val T.2.val
    (compactCanonicalTower_isCanonical _ hN) (compactCanonicalTower_isCanonical M hM)
    S.2.property.2 T.2.property.2

theorem compactTerminalMap_properties [CompactSpace X] [CompactSpace Y] {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    let hN := original_ambient_domain_pullback hf M hM
    let S := compactCanonicalTower (markedPullback (m := m) f M) hN
    let T := compactCanonicalTower M hM
    let g := compactTerminalMap hf M hM
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      (∀ z, T.2.val.proj (g z)=f (S.2.val.proj z)) ∧
      HolomorphicSquarePullback f g S.2.val.proj T.2.val.proj :=
  terminalSmoothMap_properties hf M hM _ _
    (compactCanonicalTower_isCanonical _ _) (compactCanonicalTower_isCanonical M hM)
    (compactCanonicalTower (markedPullback (m := m) f M)
      (original_ambient_domain_pullback hf M hM)).2.property.2 (compactCanonicalTower M hM).2.property.2

theorem compactTerminalMap_unique [CompactSpace X] [CompactSpace Y] {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (g : (compactCanonicalTower (markedPullback (m := m) f M)
      (original_ambient_domain_pullback hf M hM)).1 → (compactCanonicalTower M hM).1)
    (hg : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g)
    (hp : ∀ z, (compactCanonicalTower M hM).2.val.proj (g z)=
      f ((compactCanonicalTower (markedPullback (m := m) f M)
        (original_ambient_domain_pullback hf M hM)).2.val.proj z))
    (hU : HolomorphicSquarePullback f g
      (compactCanonicalTower (markedPullback (m := m) f M)
        (original_ambient_domain_pullback hf M hM)).2.val.proj
      (compactCanonicalTower M hM).2.val.proj) : g=compactTerminalMap hf M hM :=
  terminalSmoothMap_unique hf M hM _ _
    (compactCanonicalTower_isCanonical _ _) (compactCanonicalTower_isCanonical M hM)
    (compactCanonicalTower (markedPullback (m := m) f M)
      (original_ambient_domain_pullback hf M hM)).2.property.2 (compactCanonicalTower M hM).2.property.2 g hg hp hU

theorem existsUnique_original_compact_terminal_submersion_cartesian
    [CompactSpace X] [CompactSpace Y] {f : Y → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    let hN := original_ambient_domain_pullback hf M hM
    let S := compactCanonicalTower (markedPullback (m := m) f M) hN
    let T := compactCanonicalTower M hM
    ∃! g : S.1 → T.1, Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ g ∧
      (∀ z, T.2.val.proj (g z)=f (S.2.val.proj z)) ∧
      HolomorphicSquarePullback f g S.2.val.proj T.2.val.proj := by
  dsimp only
  refine ⟨compactTerminalMap hf M hM,compactTerminalMap_properties hf M hM,?_⟩
  intro g hg
  exact compactTerminalMap_unique hf M hM g hg.1.contMDiff hg.2.1 hg.2.2

theorem compactTerminalMap_identity_biholomorphism [CompactSpace X]
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    let hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (id : X → X) :=
      Manifold.IsSubmersion.id
    let S := compactCanonicalTower (markedPullback (m := n) (id : X → X) M)
      (original_ambient_domain_pullback hf M hM)
    let T := compactCanonicalTower M hM
    ∃ η : S.1 ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ T.1,
      compactTerminalMap hf M hM=η ∧ ∀ z, T.2.val.proj (η z)=S.2.val.proj z := by
  dsimp only
  let hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ (id : X → X) :=
      Manifold.IsSubmersion.id
  let hN := original_ambient_domain_pullback hf M hM
  let S := compactCanonicalTower (markedPullback (m := n) (id : X → X) M) hN
  let T := compactCanonicalTower M hM
  have hid := whole_markedPullback_id M hM.isWellFormed.isCoherent
  have hcS : IsCanonical M ((canonicalInvariant n).inv M) S.2.val :=
    Eq.mp (congrArg (fun N : MarkedIdeal n X =>
      IsCanonical N ((canonicalInvariant n).inv N) S.2.val) hid) (compactCanonicalTower_isCanonical _ hN)
  have hrS : IsGeoResolution M S.2.val :=
    Eq.mp (congrArg (fun N : MarkedIdeal n X => IsGeoResolution N S.2.val) hid) S.2.property.2
  let η := ambientTerminalComparison M hM S.2.val T.2.val hcS
    (compactCanonicalTower_isCanonical M hM) hrS T.2.property.2
  refine ⟨η,?_,ambientTerminalComparison_proj M hM S.2.val T.2.val hcS
    (compactCanonicalTower_isCanonical M hM) hrS T.2.property.2⟩
  exact terminalSmoothMap_identity_independent_histories M hM S.2.val T.2.val hcS
    (compactCanonicalTower_isCanonical M hM) hrS T.2.property.2

theorem compactTerminalMap_composition_after_whole_record_transport
    [CompactSpace X] [CompactSpace Y] [CompactSpace Z] {f : Y → X} {h : Z → Y}
    (hf : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    (hh : Manifold.IsSubmersion 𝓘(ℂ,ComplexModel ℓ) 𝓘(ℂ,ComplexModel m) ∞ h)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) :
    let hN := original_ambient_domain_pullback hf M hM
    let hP := original_ambient_domain_pullback (isSubmersion_composition hf hh) M hM
    let R := compactCanonicalTower (markedPullback (m := ℓ) (f ∘ h) M) hP
    let S := compactCanonicalTower (markedPullback (m := m) f M) hN
    let hrec := whole_markedPullback_comp hf.contMDiff hh.contMDiff M hM.isWellFormed.isCoherent
    compactTerminalMap hf M hM ∘
      terminalSmoothMap hh (markedPullback (m := m) f M) hN R.2.val S.2.val
        (hrec ▸ compactCanonicalTower_isCanonical _ hP) (compactCanonicalTower_isCanonical _ hN)
        (hrec ▸ R.2.property.2) S.2.property.2=
      compactTerminalMap (isSubmersion_composition hf hh) M hM := by
  dsimp only
  exact terminalSmoothMap_composition hf hh M hM _ _ _
    (compactCanonicalTower_isCanonical _ _) (compactCanonicalTower_isCanonical _ _)
    (compactCanonicalTower_isCanonical M hM)
    (compactCanonicalTower (markedPullback (m := ℓ) (f ∘ h) M)
      (original_ambient_domain_pullback (isSubmersion_composition hf hh) M hM)).2.property.2
    (compactCanonicalTower (markedPullback (m := m) f M)
      (original_ambient_domain_pullback hf M hM)).2.property.2 (compactCanonicalTower M hM).2.property.2

end
end Hironaka.HironakaSmoothSubmersionOriginalCompactTerminal
