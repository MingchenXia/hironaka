/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalFiniteEmptyCompression
import Hironaka.Resolution.CanonicalResolution
/-! Actual original terminal choice comparison allowing arbitrary empty steps.
Complete three-node mathematics preceded code. True nonempty compressed CAN is
constructed internally before the existing genuine per-sequence terminal Iso. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalTerminalChoiceComparison
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  MarkedIdealBiholomorphism BlowupTowers BlowupTowerTransforms BlowupTowerIsomorphism
  HironakaStageCenters CanonicalCentres HironakaOriginalFiniteEmptyCompression
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

theorem isCanonicalSegment_of_actual_nonempty_centres {Λ : Type v} [LinearOrder Λ]
    (M : MarkedIdeal n X) (inv : ∀ {Z : CMfd.{u} n}, BlowupTower X Z → Z → Λ)
    (T : BlowupTower X Y) (hcan : IsCanonical M inv T)
    (hne : StageCentres (fun _ C => C.Nonempty) T) :
    ResolutionDriver.IsCanonicalSegment M inv T := by
  induction T with
  | refl => trivial
  | step T C π hπ ih =>
    refine ⟨ih hcan.1 hne.1,hne.2,?_⟩
    rcases hcan.2 with he | hm
    · exact False.elim (hne.2.ne_empty he)
    · exact hm

/-- ONLY original domain and TWO actual canonical terminal histories (allowing
all real empty steps) internally supply the final comparison over the base. -/
theorem original_terminal_histories_biholomorphic_base_comparison (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (hcan' : IsCanonical (MarkedIdeal.pullback Φ M)
      ((invFamily hn k).inv (MarkedIdeal.pullback Φ M)) T')
    (hcan : IsCanonical M ((invFamily hn k).inv M) T)
    (hres' : IsGeoResolution (MarkedIdeal.pullback Φ M) T')
    (hres : IsGeoResolution M T) :
    ∃ η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      ∀ y, T.proj (η y)=Φ (T'.proj y) := by
  have hM' := InvDomainTowerAlong.isInvDomain_pullback Φ hM
  obtain ⟨Z',Q',χ',F',hne',hlen',hc',hp',hcos',hv',hr'⟩ :=
    original_recursive_family_empty_free_compression hn k (MarkedIdeal.pullback Φ M) hM' T' hcan'
  obtain ⟨Z,Q,χ,F,hne,hlen,hc,hp,hcos,hv,hr⟩ :=
    original_recursive_family_empty_free_compression hn k M hM T hcan
  have hs' := isCanonicalSegment_of_actual_nonempty_centres (MarkedIdeal.pullback Φ M)
    ((invFamily hn k).inv (MarkedIdeal.pullback Φ M)) Q' hc' hne'
  have hs := isCanonicalSegment_of_actual_nonempty_centres M ((invFamily hn k).inv M) Q hc hne
  obtain ⟨ψ,hi⟩ := CanonicalResolution.exists_isTowerIso_of_isGeoResolution
    (invFamily hn k) hM Φ Q' Q hs' hs (hr'.mp hres') (hr.mp hres)
  refine ⟨(χ'.symm.trans ψ).trans χ,?_⟩
  intro y
  change T.proj (χ (ψ (χ'.symm y)))=Φ (T'.proj y)
  rw [hp]
  have hpi := hi.proj_comm (χ'.symm y)
  have hps := hp' (χ'.symm y)
  rw [χ'.apply_symm_apply] at hps
  exact hpi.symm.trans (congrArg Φ hps.symm)

/-- Same original base and marked record, different actual empty-step counts
and blowup choices; no nonempty/compressed/final comparison input certificate. -/
theorem original_terminal_histories_actual_choice_comparison (hn : 0<n) (k : ℕ)
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (hcan' : IsCanonical M ((invFamily hn k).inv M) T')
    (hcan : IsCanonical M ((invFamily hn k).inv M) T)
    (hres' : IsGeoResolution M T') (hres : IsGeoResolution M T) :
    ∃ η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      ∀ y, T.proj (η y)=T'.proj y := by
  let Φ := Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞
  have hpull : MarkedIdeal.pullback Φ M=M := ContactCanonicalAlong.pullback_id M hM.isWellFormed.isCoherent
  exact original_terminal_histories_biholomorphic_base_comparison hn k M hM Φ T' T
    (by rw [hpull];exact hcan') hcan (by rw [hpull];exact hres') hres

end
end Hironaka.HironakaOriginalTerminalChoiceComparison
