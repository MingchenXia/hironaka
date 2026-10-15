/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalAmbientTerminalChoice
import Hironaka.Resolution.HironakaNormalCrossingsTotalIdeal
/-! Intrinsic actual final projection uniqueness and canonical terminal cocycles.
Complete four-node mathematics preceded code. True first-centre pullback
invertibility is internally supplied from actual original blowups and whole tails. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalTerminalProjectionUniqueness
noncomputable section
open Hironaka.BlowupSequences Hironaka.HolomorphicIdealSheaves
  MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers BlowupTowerTransforms
  CanonicalCentres HironakaOriginalAmbientTerminalChoice
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Z : CMfd.{u} n}

theorem exists_actual_first_step_split (T : BlowupTower X Y) (hpos : 0<T.length) :
    ∃ (A : CMfd.{u} n) (C : Set X) (π : A → X) (hπ : IsBlowupAlong n C π)
      (S : BlowupTower A Y), T=(BlowupTower.refl.step C π hπ).append S := by
  induction T with
  | refl => exact False.elim (Nat.not_lt_zero _ hpos)
  | @step Y Z T C π hπ ih =>
    cases T with
    | refl => exact ⟨Z,C,π,hπ,.refl,rfl⟩
    | step T₀ C₀ π₀ hπ₀ =>
      obtain ⟨A,D,ρ,hρ,S,heq⟩ := ih (Nat.succ_pos _)
      refine ⟨A,D,ρ,hρ,S.step C π hπ,?_⟩
      rw [BlowupTower.append_step,← heq]

/-- ALL needed first-centre pullback invertibility is supplied from the actual
blowup/tail/biholomorphism, before its genuine universal uniqueness is used. -/
theorem biholomorphisms_eq_of_actual_proj_eq (T : BlowupTower X Y)
    (f g : Z ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y)
    (hproj : ∀ z, T.proj (f z)=T.proj (g z)) : f=g := by
  generalize hlen : T.length=ℓ
  induction ℓ using Nat.strong_induction_on generalizing X Y Z with
  | h ℓ ih =>
    by_cases hpos : 0<T.length
    · obtain ⟨A,C,π,hπ,S,heq⟩ := exists_actual_first_step_split T hpos
      have hlt : S.length<ℓ := by
        rw [heq,BlowupTower.length_append] at hlen
        change 1+S.length=ℓ at hlen
        omega
      have hproj' : ∀ z, π (S.proj (f z))=π (S.proj (g z)) := by
        intro z
        have hz := hproj z
        rw [heq,BlowupTower.proj_append] at hz
        exact hz
      have hJ : (GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)).IsInvertible := hπ.2.2.2.1
      have hJcoh := DivisorMetric.isCoherent_of_isInvertible hJ
      have hSI := HironakaNormalCrossingsTotalIdeal.isInvertible_original_pullback_tower S hJ
      have hfExc : interior (exceptionalLocus n f)=∅ := by
        have he : exceptionalLocus n f=∅ := eq_empty_iff_forall_notMem.mpr
          (MarkedIdealTowerTransport.notMem_exceptionalLocus f)
        rw [he,interior_empty]
      have hFI := GermIdealTotalTransform.isInvertible_pullback f.contMDiff hfExc hSI
      rw [← GermIdealTotalTransform.pullback_comp S.contMDiff_proj f.contMDiff hJcoh] at hFI
      have hCcoh := BlowupExceptionalDivisor.isCoherent_vanishingIdeal_centre hπ
      rw [← GermIdealTotalTransform.pullback_comp hπ.contMDiff
        (S.contMDiff_proj.comp f.contMDiff) hCcoh] at hFI
      obtain ⟨w,hw,huniq⟩ := hπ.2.2.2.2 n Z (π ∘ (S.proj ∘ f))
        (hπ.contMDiff.comp (S.contMDiff_proj.comp f.contMDiff)) hFI
      have hfg : S.proj ∘ f=S.proj ∘ g :=
        (huniq (S.proj ∘ f) ⟨S.contMDiff_proj.comp f.contMDiff,rfl⟩).trans
          (huniq (S.proj ∘ g) ⟨S.contMDiff_proj.comp g.contMDiff,
            funext fun z => (hproj' z).symm⟩).symm
      exact ih _ hlt S f g (fun z => congrFun hfg z) rfl
    · cases T with
      | refl => exact Diffeomorph.ext hproj
      | step T C π hπ => exact False.elim (hpos (Nat.succ_pos _))

variable {Y' Y'' : CMfd.{u} n}

theorem original_ambient_terminal_choice_existsUnique
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (hc' : IsCanonical M ((canonicalInvariant n).inv M) T')
    (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hr' : IsGeoResolution M T') (hr : IsGeoResolution M T) :
    ∃! η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      ∀ y, T.proj (η y)=T'.proj y := by
  obtain ⟨η,hη⟩ := original_ambient_terminal_choice_comparison M hM T' T hc' hc hr' hr
  refine ⟨η,hη,?_⟩
  intro η' hη'
  exact biholomorphisms_eq_of_actual_proj_eq T η' η
    (fun y => (hη' y).trans (hη y).symm)

noncomputable def ambientTerminalComparison
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (hc' : IsCanonical M ((canonicalInvariant n).inv M) T')
    (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hr' : IsGeoResolution M T') (hr : IsGeoResolution M T) :
    Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y :=
  (original_ambient_terminal_choice_existsUnique M hM T' T hc' hc hr' hr).choose

theorem ambientTerminalComparison_proj
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (hc' : IsCanonical M ((canonicalInvariant n).inv M) T')
    (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hr' : IsGeoResolution M T') (hr : IsGeoResolution M T) (y : Y') :
    T.proj (ambientTerminalComparison M hM T' T hc' hc hr' hr y)=T'.proj y :=
  (original_ambient_terminal_choice_existsUnique M hM T' T hc' hc hr' hr).choose_spec.1 y

theorem ambientTerminalComparison_self
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T : BlowupTower X Y)
    (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hr : IsGeoResolution M T) :
    ambientTerminalComparison M hM T T hc hc hr hr=
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) Y ∞ := by
  exact biholomorphisms_eq_of_actual_proj_eq T _ _
    (ambientTerminalComparison_proj M hM T T hc hc hr hr)

theorem ambientTerminalComparison_symm
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T' : BlowupTower X Y') (T : BlowupTower X Y)
    (hc' : IsCanonical M ((canonicalInvariant n).inv M) T')
    (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hr' : IsGeoResolution M T') (hr : IsGeoResolution M T) :
    (ambientTerminalComparison M hM T' T hc' hc hr' hr).symm=
      ambientTerminalComparison M hM T T' hc hc' hr hr' := by
  apply biholomorphisms_eq_of_actual_proj_eq T'
  intro y
  have h := ambientTerminalComparison_proj M hM T' T hc' hc hr' hr
    ((ambientTerminalComparison M hM T' T hc' hc hr' hr).symm y)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm.trans (ambientTerminalComparison_proj M hM T T' hc hc' hr hr' y).symm

theorem ambientTerminalComparison_trans
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T₁ : BlowupTower X Y') (T₂ : BlowupTower X Y) (T₃ : BlowupTower X Y'')
    (hc₁ : IsCanonical M ((canonicalInvariant n).inv M) T₁)
    (hc₂ : IsCanonical M ((canonicalInvariant n).inv M) T₂)
    (hc₃ : IsCanonical M ((canonicalInvariant n).inv M) T₃)
    (hr₁ : IsGeoResolution M T₁) (hr₂ : IsGeoResolution M T₂)
    (hr₃ : IsGeoResolution M T₃) :
    (ambientTerminalComparison M hM T₁ T₂ hc₁ hc₂ hr₁ hr₂).trans
      (ambientTerminalComparison M hM T₂ T₃ hc₂ hc₃ hr₂ hr₃)=
      ambientTerminalComparison M hM T₁ T₃ hc₁ hc₃ hr₁ hr₃ := by
  apply biholomorphisms_eq_of_actual_proj_eq T₃
  intro y
  change T₃.proj (ambientTerminalComparison M hM T₂ T₃ hc₂ hc₃ hr₂ hr₃
    (ambientTerminalComparison M hM T₁ T₂ hc₁ hc₂ hr₁ hr₂ y))=_
  rw [ambientTerminalComparison_proj,ambientTerminalComparison_proj,
    ambientTerminalComparison_proj]

end
end Hironaka.HironakaOriginalTerminalProjectionUniqueness
