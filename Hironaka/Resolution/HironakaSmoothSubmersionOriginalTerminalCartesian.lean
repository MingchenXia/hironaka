/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalAmbientCanonical
import Hironaka.Resolution.HironakaSmoothSubmersionCartesianTowerChoiceComparison
import Hironaka.Resolution.HironakaOriginalAmbientTerminalChoice
/-! Genuine holomorphic Cartesian comparisons between given terminal histories.
Complete two-node mathematics preceded proofs. Original source and target histories
may have different actual empty-step counts; their final spaces are compared.
-/
set_option autoImplicit false
open Set
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaSmoothSubmersionOriginalTerminalCartesian
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionCartesianTower
  HironakaSmoothSubmersionRelativeControlledTower HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionOriginalAmbientCanonical
  HironakaSmoothSubmersionCartesianTowerChoiceComparison
  HironakaSmoothSubmersionOrderedChoiceBaseChange HironakaOriginalAmbientTerminalChoice
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n m : ℕ} {X D : CMfd.{u} n} {Y E : CMfd.{u} m} {f : Y → X}

theorem original_terminal_source_actual_cartesian_comparison
    (β : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower Y E) (T : BlowupTower X D)
    (hscan : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S)
    (htcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hsres : IsGeoResolution (markedPullback (m := m) f M) S)
    (htres : IsGeoResolution M T) :
    let P := chosenActualTower β hf T
    IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) P.2.1 ∧
    IsGeoResolution (markedPullback (m := m) f M) P.2.1 ∧
    ∃ η : E ≃ₘ⟮𝓘(ℂ, ComplexModel m),𝓘(ℂ, ComplexModel m)⟯ P.1,
      ∀ y, P.2.1.proj (η y) = S.proj y := by
  dsimp only
  let P := chosenActualTower β hf T
  have h := P.2.2.property
  have hd := original_ambient_domain_pullback hf M hM
  have hc := IsActualTowerPullback.original_ambient_canonical h M hM htcan
  have htest := (IsActualTowerPullback.relative_marked_dictionary h M hM.isWellFormed htres.1).1
  have hcos := IsActualTowerPullback.relative_cosupport_dictionary h M hM.isWellFormed htres.1
  have hr : IsGeoResolution (markedPullback (m := m) f M) P.2.1 := by
    refine ⟨htest,?_⟩
    rw [hcos,htres.2,preimage_empty]
  exact ⟨hc,hr,original_ambient_terminal_choice_comparison _ hd S P.2.1 hscan hc hsres hr⟩

theorem original_terminal_final_holomorphic_cartesian
    (β : SmoothBlowupChoices.{u} m)
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower Y E) (T : BlowupTower X D)
    (hscan : IsCanonical (markedPullback (m := m) f M)
      ((canonicalInvariant m).inv (markedPullback (m := m) f M)) S)
    (htcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hsres : IsGeoResolution (markedPullback (m := m) f M) S)
    (htres : IsGeoResolution M T) :
    ∃ g : E → D, ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ g ∧
      (∀ y, T.proj (g y) = f (S.proj y)) ∧
      HolomorphicSquarePullback f g S.proj T.proj := by
  let P := chosenActualTower β hf T
  obtain ⟨_hc,_hr,η,hη⟩ :=
    original_terminal_source_actual_cartesian_comparison β hf M hM S T hscan htcan hsres htres
  have h := P.2.2.property
  refine ⟨P.2.2.val ∘ η,h.isSubmersion.contMDiff.comp η.contMDiff,?_,?_⟩
  · intro y
    exact (h.proj_comm (η y)).trans (congrArg f (hη y))
  · intro ℓ W a b ha hb hcone
    obtain ⟨w,hw,huniq⟩ := h.universal ℓ W a b ha hb hcone
    refine ⟨η.symm ∘ w,⟨η.symm.contMDiff.comp hw.1,?_,?_⟩,?_⟩
    · intro y
      exact (hη (η.symm (w y))).symm.trans (by
        rw [η.apply_symm_apply]
        exact hw.2.1 y)
    · intro y
      change P.2.2.val (η (η.symm (w y))) = b y
      rw [η.apply_symm_apply]
      exact hw.2.2 y
    · intro v hv
      have he : η ∘ v = w := huniq (η ∘ v)
        ⟨η.contMDiff.comp hv.1,fun y => (hη (v y)).trans (hv.2.1 y),hv.2.2⟩
      funext y
      apply η.injective
      change η (v y) = η (η.symm (w y))
      rw [η.apply_symm_apply]
      exact congrFun he y

end
end Hironaka.HironakaSmoothSubmersionOriginalTerminalCartesian
