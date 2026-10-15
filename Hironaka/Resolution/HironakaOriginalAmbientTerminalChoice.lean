/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalTerminalChoiceComparison
/-! Actual ambient terminal choice geometry including dimension zero.
Complete two-node mathematics preceded code. Original bound-zero canonicality
internally derives every empty centre before constructing whole projection geometry. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaOriginalAmbientTerminalChoice
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres
  HironakaOriginalTerminalChoiceComparison
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Y' : CMfd.{u} n}

theorem original_bound_zero_canonical_projection_biholomorphism {Λ : Type v} [LinearOrder Λ]
    (M : MarkedIdeal n X) (hM : IsInvDomain 0 M)
    (inv : ∀ {Z : CMfd.{u} n}, BlowupTower X Z → Z → Λ)
    (T : BlowupTower X Y) (hcan : IsCanonical M inv T) :
    ∃ χ : Y ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X, ∀ y, χ y=T.proj y := by
  induction T with
  | refl => exact ⟨Diffeomorph.refl 𝓘(ℂ,ComplexModel n) X ∞,fun _ => rfl⟩
  | step T C π hπ ih =>
    obtain ⟨χ,hχ⟩ := ih hcan.1
    have ht := (ResolutionInvariantSpec.countCentresMeeting_eq_zero_of_dimLE_zero hM inv ∅ T hcan.1).1
    have hc := ResolutionInvariantSpec.cosupp_geoTransformAlong_eq_empty_of_dimLE_zero hM T ht
    have he : C=∅ := by
      rcases hcan.2 with he | hm
      · exact he
      · rw [hm,hc]
        exact eq_empty_iff_forall_notMem.mpr fun _ hy => hy.1
    subst C
    obtain ⟨φ,hφ⟩ := HironakaNormalCrossingsOpenRestrictionSeparation.exists_empty_blowup_biholomorphism hπ
    refine ⟨φ.trans χ,fun y => ?_⟩
    change χ (φ y)=T.proj (π y)
    rw [hχ,hφ]

theorem original_ambient_terminal_choice_comparison (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (hcan' : IsCanonical M ((canonicalInvariant n).inv M) T')
    (hcan : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hres' : IsGeoResolution M T') (hres : IsGeoResolution M T) :
    ∃ η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      ∀ y, T.proj (η y)=T'.proj y := by
  cases n with
  | zero =>
    obtain ⟨χ',hχ'⟩ := original_bound_zero_canonical_projection_biholomorphism M hM
      ((canonicalInvariant 0).inv M) T' hcan'
    obtain ⟨χ,hχ⟩ := original_bound_zero_canonical_projection_biholomorphism M hM
      ((canonicalInvariant 0).inv M) T hcan
    refine ⟨χ'.trans χ.symm,fun y => ?_⟩
    change T.proj (χ.symm (χ' y))=T'.proj y
    rw [← hχ,χ.apply_symm_apply,hχ']
  | succ n =>
    exact original_terminal_histories_actual_choice_comparison (Nat.succ_pos n) (n+1)
      M hM T' T hcan' hcan hres' hres

end
end Hironaka.HironakaOriginalAmbientTerminalChoice
