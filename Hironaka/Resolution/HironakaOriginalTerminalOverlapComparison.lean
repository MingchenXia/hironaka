/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaOriginalTerminalOpenComparison
import Hironaka.Invariant.ContactMarkedCanonical
/-! True overlap comparisons of independent original local terminal histories.
Complete four-node mathematics preceded code. Actual nested-base equivalences,
whole marked dictionaries and both restricted canonical terminal histories
are supplied internally from original inputs, before comparison is invoked. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalTerminalOverlapComparison
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres
  HironakaOriginalAmbientTerminalChoice HironakaOriginalTerminalChoiceComparison
  HironakaOriginalTerminalProjectionUniqueness HironakaOriginalTerminalOpenComparison MaxLocusLocal
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X X' Y Y' : CMfd.{u} n}

theorem original_ambient_terminal_base_existsUnique (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (Φ : X' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ X)
    (S : BlowupTower X' Y') (T : BlowupTower X Y)
    (hs : IsCanonical (pullback Φ M) ((canonicalInvariant n).inv (pullback Φ M)) S)
    (ht : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hrs : IsGeoResolution (pullback Φ M) S) (hrt : IsGeoResolution M T) :
    ∃! η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      ∀ y, T.proj (η y)=Φ (S.proj y) := by
  have hex : ∃ η : Y' ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ Y,
      ∀ y, T.proj (η y)=Φ (S.proj y) := by
    cases n with
    | zero =>
      have hM' := InvDomainTowerAlong.isInvDomain_pullback Φ hM
      obtain ⟨χS,hχS⟩ := original_bound_zero_canonical_projection_biholomorphism
        (pullback Φ M) hM' ((canonicalInvariant 0).inv (pullback Φ M)) S hs
      obtain ⟨χT,hχT⟩ := original_bound_zero_canonical_projection_biholomorphism
        M hM ((canonicalInvariant 0).inv M) T ht
      refine ⟨(χS.trans Φ).trans χT.symm,fun y => ?_⟩
      change T.proj (χT.symm (Φ (χS y)))=Φ (S.proj y)
      rw [← hχT,χT.apply_symm_apply,hχS]
    | succ n =>
      exact original_terminal_histories_biholomorphic_base_comparison (Nat.succ_pos n) (n+1)
        M hM Φ S T hs ht hrs hrt
  obtain ⟨η,hη⟩ := hex
  refine ⟨η,hη,?_⟩
  intro η' hη'
  exact biholomorphisms_eq_of_actual_proj_eq T η' η
    (fun y => (hη' y).trans (hη y).symm)

/-- Real nested-open identifications construct THIS actual common-base map. -/
def overlapBaseEquiv {U V W : Opens X} (hWU : W ≤ U) (hWV : W ≤ V) :
    CMfd.of (n := n) (nestedOpens U W) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (nestedOpens V W) :=
  (nestedOpensDiffeo hWU).trans (nestedOpensDiffeo hWV).symm

theorem overlapBaseEquiv_point {U V W : Opens X} (hWU : W ≤ U) (hWV : W ≤ V)
    (y : nestedOpens U W) : ((overlapBaseEquiv hWU hWV y).val).val=y.val.val := rfl

theorem original_overlap_whole_marked_dictionary (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {U V W : Opens X} (hWU : W ≤ U) (hWV : W ≤ V) :
    pullback (overlapBaseEquiv hWU hWV)
      (pullback (Subtype.val : nestedOpens V W → V) (pullback (Subtype.val : V → X) M))=
      pullback (Subtype.val : nestedOpens U W → U) (pullback (Subtype.val : U → X) M) := by
  have hMW := InvDomainTowerAlong.isInvDomain_pullback_val W hM
  rw [pullback_val_pullback_val hM.isWellFormed.isCoherent hWV,
    pullback_val_pullback_val hM.isWellFormed.isCoherent hWU]
  have he := ContactMarkedCanonical.pullback_pullback_of_comp_eq hMW.isWellFormed.isCoherent
    (nestedOpensDiffeo (n := n) hWV).contMDiff (overlapBaseEquiv hWU hWV).contMDiff
    (nestedOpensDiffeo (n := n) hWU).contMDiff contMDiff_id
    (fun y => (nestedOpensDiffeo (n := n) hWV).apply_symm_apply
      ((nestedOpensDiffeo (n := n) hWU) y))
  rw [ContactCanonicalAlong.pullback_id _ hMW.isWellFormed.isCoherent] at he
  exact he

variable {Z P : CMfd.{u} n}

theorem biholomorphisms_eq_of_common_open_original_proj_eq
    {V W : Opens X} (T : BlowupTower (CMfd.of (n := n) V) Z)
    (f g : P ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T (nestedOpens V W)))
    (hp : ∀ y, (T.proj (f y).val).val=(T.proj (g y).val).val) : f=g := by
  apply biholomorphisms_eq_of_actual_proj_eq (restrict (nestedOpens V W) T)
  intro y
  apply Subtype.ext
  apply Subtype.ext
  rw [proj_restrict,proj_restrict]
  exact hp y

theorem original_common_open_terminal_existsUnique
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    {U V W : Opens X} (hWU : W ≤ U) (hWV : W ≤ V)
    (S : BlowupTower (CMfd.of (n := n) U) Y)
    (T : BlowupTower (CMfd.of (n := n) V) Z)
    (hs : IsCanonical (pullback (Subtype.val : U → X) M)
      ((canonicalInvariant n).inv (pullback (Subtype.val : U → X) M)) S)
    (ht : IsCanonical (pullback (Subtype.val : V → X) M)
      ((canonicalInvariant n).inv (pullback (Subtype.val : V → X) M)) T)
    (hrs : IsGeoResolution (pullback (Subtype.val : U → X) M) S)
    (hrt : IsGeoResolution (pullback (Subtype.val : V → X) M) T) :
    ∃! η : CMfd.of (n := n) (openPreimage S (nestedOpens U W))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage T (nestedOpens V W)),
      ∀ y, (T.proj (η y).val).val=(S.proj y.val).val := by
  have hU := InvDomainTowerAlong.isInvDomain_pullback_val U hM
  have hV := InvDomainTowerAlong.isInvDomain_pullback_val V hM
  have hS := original_terminal_open_history_data _ hU S hs hrs (nestedOpens U W)
  have hT := original_terminal_open_history_data _ hV T ht hrt (nestedOpens V W)
  have he := original_overlap_whole_marked_dictionary M hM hWU hWV
  obtain ⟨η,hη,_⟩ := original_ambient_terminal_base_existsUnique _ hT.1
    (overlapBaseEquiv hWU hWV) (restrict (nestedOpens U W) S) (restrict (nestedOpens V W) T)
    (he.symm ▸ hS.2.1) hT.2.1 (he.symm ▸ hS.2.2) hT.2.2
  have hp : ∀ y, (T.proj (η y).val).val=(S.proj y.val).val := by
    intro y
    have hz := congrArg (fun q : nestedOpens V W => q.val.val) (hη y)
    rw [overlapBaseEquiv_point] at hz
    have htproj := congrArg (fun q : V => q.val) (proj_restrict (nestedOpens V W) T (η y))
    have hsproj := congrArg (fun q : U => q.val) (proj_restrict (nestedOpens U W) S y)
    exact htproj.symm.trans (hz.trans hsproj)
  refine ⟨η,hp,?_⟩
  intro η' hη'
  exact biholomorphisms_eq_of_common_open_original_proj_eq T η' η
    (fun y => (hη' y).trans (hp y).symm)

section ActualCommonChoice
variable (M : MarkedIdeal n X) (hM : IsInvDomain n M)
  {U V W : Opens X} (hWU : W ≤ U) (hWV : W ≤ V)
  (S : BlowupTower (CMfd.of (n := n) U) Y)
  (T : BlowupTower (CMfd.of (n := n) V) Z)
  (hs : IsCanonical (pullback (Subtype.val : U → X) M)
    ((canonicalInvariant n).inv (pullback (Subtype.val : U → X) M)) S)
  (ht : IsCanonical (pullback (Subtype.val : V → X) M)
    ((canonicalInvariant n).inv (pullback (Subtype.val : V → X) M)) T)
  (hrs : IsGeoResolution (pullback (Subtype.val : U → X) M) S)
  (hrt : IsGeoResolution (pullback (Subtype.val : V → X) M) T)

/-- The actual UNIQUE overlap map is constructed from original independent
local histories, not a restriction of a given global comparison/tower. -/
def commonOpenTerminalComparison :
    CMfd.of (n := n) (openPreimage S (nestedOpens U W))
      ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
        CMfd.of (n := n) (openPreimage T (nestedOpens V W)) :=
  (original_common_open_terminal_existsUnique M hM hWU hWV S T hs ht hrs hrt).choose

theorem commonOpenTerminalComparison_proj (y : openPreimage S (nestedOpens U W)) :
    (T.proj (commonOpenTerminalComparison M hM hWU hWV S T hs ht hrs hrt y).val).val=
      (S.proj y.val).val :=
  (original_common_open_terminal_existsUnique M hM hWU hWV S T hs ht hrs hrt).choose_spec.1 y

theorem commonOpenTerminalComparison_self :
    commonOpenTerminalComparison M hM hWU hWU S S hs hs hrs hrs=
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n)
        (CMfd.of (n := n) (openPreimage S (nestedOpens U W))) ∞ := by
  exact biholomorphisms_eq_of_common_open_original_proj_eq S _ _
    (commonOpenTerminalComparison_proj M hM hWU hWU S S hs hs hrs hrs)

theorem commonOpenTerminalComparison_symm :
    (commonOpenTerminalComparison M hM hWU hWV S T hs ht hrs hrt).symm=
      commonOpenTerminalComparison M hM hWV hWU T S ht hs hrt hrs := by
  apply biholomorphisms_eq_of_common_open_original_proj_eq S
  intro y
  have h := commonOpenTerminalComparison_proj M hM hWU hWV S T hs ht hrs hrt
    ((commonOpenTerminalComparison M hM hWU hWV S T hs ht hrs hrt).symm y)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm.trans (commonOpenTerminalComparison_proj M hM hWV hWU T S ht hs hrt hrs y).symm

variable {O : Opens X} (hWO : W ≤ O)
  (R : BlowupTower (CMfd.of (n := n) O) P)
  (hr : IsCanonical (pullback (Subtype.val : O → X) M)
    ((canonicalInvariant n).inv (pullback (Subtype.val : O → X) M)) R)
  (hrr : IsGeoResolution (pullback (Subtype.val : O → X) M) R)

theorem commonOpenTerminalComparison_trans :
    (commonOpenTerminalComparison M hM hWU hWV S T hs ht hrs hrt).trans
      (commonOpenTerminalComparison M hM hWV hWO T R ht hr hrt hrr)=
      commonOpenTerminalComparison M hM hWU hWO S R hs hr hrs hrr := by
  apply biholomorphisms_eq_of_common_open_original_proj_eq R
  intro y
  change (R.proj (commonOpenTerminalComparison M hM hWV hWO T R ht hr hrt hrr
    (commonOpenTerminalComparison M hM hWU hWV S T hs ht hrs hrt y)).val).val=_
  rw [commonOpenTerminalComparison_proj,commonOpenTerminalComparison_proj,
    commonOpenTerminalComparison_proj]
end ActualCommonChoice

/-- Actual pair intersection internally supplies BOTH original-open containments. -/
theorem original_terminal_intersection_existsUnique
    (M : MarkedIdeal n X) (hM : IsInvDomain n M) (U V : Opens X)
    (S : BlowupTower (CMfd.of (n := n) U) Y)
    (T : BlowupTower (CMfd.of (n := n) V) Z)
    (hs : IsCanonical (pullback (Subtype.val : U → X) M)
      ((canonicalInvariant n).inv (pullback (Subtype.val : U → X) M)) S)
    (ht : IsCanonical (pullback (Subtype.val : V → X) M)
      ((canonicalInvariant n).inv (pullback (Subtype.val : V → X) M)) T)
    (hrs : IsGeoResolution (pullback (Subtype.val : U → X) M) S)
    (hrt : IsGeoResolution (pullback (Subtype.val : V → X) M) T) :
    ∃! η : CMfd.of (n := n) (openPreimage S (nestedOpens U (U ⊓ V)))
        ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
          CMfd.of (n := n) (openPreimage T (nestedOpens V (U ⊓ V))),
      ∀ y, (T.proj (η y).val).val=(S.proj y.val).val :=
  original_common_open_terminal_existsUnique M hM inf_le_left inf_le_right S T hs ht hrs hrt

end
end Hironaka.HironakaOriginalTerminalOverlapComparison
