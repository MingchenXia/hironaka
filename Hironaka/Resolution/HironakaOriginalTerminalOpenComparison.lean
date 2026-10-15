/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.GeoResolutionRestrictExact
import Hironaka.Resolution.HironakaOriginalTerminalProjectionUniqueness
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
/-! Literal original terminal comparison restrictions and true open naturality.
Complete four-node mathematics preceded proof code. Actual restricted histories,
both subtype domains and whole projections are supplied from original inputs. -/
set_option autoImplicit false
open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaOriginalTerminalOpenComparison
noncomputable section
open Hironaka.BlowupSequences MarkedIdeals MarkedIdeals.MarkedIdeal
  BlowupTowers BlowupTowerTransforms CanonicalCentres
  HironakaOriginalTerminalProjectionUniqueness
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)
variable {n : ℕ} {X Y Z W : CMfd.{u} n}

theorem original_terminal_open_history_data (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hr : IsGeoResolution M T) (U : Opens X) :
    IsInvDomain n (pullback (Subtype.val : U → X) M) ∧
    IsCanonical (pullback (Subtype.val : U → X) M)
      ((canonicalInvariant n).inv (pullback (Subtype.val : U → X) M)) (restrict U T) ∧
    IsGeoResolution (pullback (Subtype.val : U → X) M) (restrict U T) :=
  ⟨InvDomainTowerAlong.isInvDomain_pullback_val U hM,
    Seq.ResolutionInvariantExt.isCanonical_restrict (canonicalInvariant n) hM U T hc,
    MarkedIdealRestrictOpen.isGeoResolution_restrict U
      hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent hr⟩

theorem original_terminal_open_whole_record (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T : BlowupTower X Y) (hr : IsGeoResolution M T) (U : Opens X) :
    geoTransformAlong (pullback (Subtype.val : U → X) M) (restrict U T)=
      pullback (Subtype.val : openPreimage T U → Y) (geoTransformAlong M T) :=
  MarkedIdealRestrictOpen.geoTransformAlong_restrict U
    hM.isWellFormed.isClosedSubmanifold_N hM.isWellFormed.isCoherent T hr.1

/-- BOTH true open-subtype domains are consequences of the internally constructed
original whole projection comparison, rather than caller comparison certificates. -/
def actualTerminalComparisonOnOpen (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower X Y) (T : BlowupTower X Z)
    (hs : IsCanonical M ((canonicalInvariant n).inv M) S)
    (ht : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hrs : IsGeoResolution M S) (hrt : IsGeoResolution M T) (U : Opens X) :
    CMfd.of (n := n) (openPreimage S U) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U) := by
  let η := ambientTerminalComparison M hM S T hs ht hrs hrt
  have hη : ∀ y, T.proj (η y)=S.proj y := ambientTerminalComparison_proj M hM S T hs ht hrs hrt
  have hηinv : ∀ z, S.proj (η.symm z)=T.proj z := by
    intro z
    have h := hη (η.symm z)
    rw [η.apply_symm_apply] at h
    exact h.symm
  have hforward : ∀ y : openPreimage S U, η y.val ∈ openPreimage T U := by
    intro y
    change T.proj (η y.val) ∈ U
    rw [hη]
    exact y.property
  have hinverse : ∀ z : openPreimage T U, η.symm z.val ∈ openPreimage S U := by
    intro z
    change S.proj (η.symm z.val) ∈ U
    rw [hηinv]
    exact z.property
  exact {
    toFun y := ⟨η y.val,hforward y⟩
    invFun z := ⟨η.symm z.val,hinverse z⟩
    left_inv y := Subtype.ext (η.symm_apply_apply y.val)
    right_inv z := Subtype.ext (η.apply_symm_apply z.val)
    contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk
      (η.contMDiff.comp contMDiff_subtype_val) hforward
    contMDiff_invFun := BlowupRestrictOpen.contMDiff_opens_mk
      (η.symm.contMDiff.comp contMDiff_subtype_val) hinverse }

theorem actualTerminalComparisonOnOpen_apply (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower X Y) (T : BlowupTower X Z)
    (hs : IsCanonical M ((canonicalInvariant n).inv M) S)
    (ht : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hrs : IsGeoResolution M S) (hrt : IsGeoResolution M T) (U : Opens X)
    (y : openPreimage S U) :
    (actualTerminalComparisonOnOpen M hM S T hs ht hrs hrt U y).val=
      ambientTerminalComparison M hM S T hs ht hrs hrt y.val := rfl

theorem actualTerminalComparisonOnOpen_symm_apply (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower X Y) (T : BlowupTower X Z)
    (hs : IsCanonical M ((canonicalInvariant n).inv M) S)
    (ht : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hrs : IsGeoResolution M S) (hrt : IsGeoResolution M T) (U : Opens X)
    (z : openPreimage T U) :
    ((actualTerminalComparisonOnOpen M hM S T hs ht hrs hrt U).symm z).val=
      (ambientTerminalComparison M hM S T hs ht hrs hrt).symm z.val := rfl

theorem actualTerminalComparisonOnOpen_proj (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower X Y) (T : BlowupTower X Z)
    (hs : IsCanonical M ((canonicalInvariant n).inv M) S)
    (ht : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hrs : IsGeoResolution M S) (hrt : IsGeoResolution M T) (U : Opens X)
    (y : openPreimage S U) :
    (restrict U T).proj (actualTerminalComparisonOnOpen M hM S T hs ht hrs hrt U y)=
      (restrict U S).proj y := by
  apply Subtype.ext
  rw [proj_restrict,proj_restrict,actualTerminalComparisonOnOpen_apply,
    ambientTerminalComparison_proj]

/-- ONLY original inputs INTERNALLY supply all restricted domain/CAN/terminal
inputs before the genuine unique terminal factory on U is consumed. -/
def openCanonicalTerminalComparison (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower X Y) (T : BlowupTower X Z)
    (hs : IsCanonical M ((canonicalInvariant n).inv M) S)
    (ht : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hrs : IsGeoResolution M S) (hrt : IsGeoResolution M T) (U : Opens X) :
    CMfd.of (n := n) (openPreimage S U) ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage T U) := by
  have hS := original_terminal_open_history_data M hM S hs hrs U
  have hT := original_terminal_open_history_data M hM T ht hrt U
  exact ambientTerminalComparison (pullback (Subtype.val : U → X) M) hS.1
    (restrict U S) (restrict U T) hS.2.1 hT.2.1 hS.2.2 hT.2.2

theorem openCanonicalTerminalComparison_proj (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower X Y) (T : BlowupTower X Z)
    (hs : IsCanonical M ((canonicalInvariant n).inv M) S)
    (ht : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hrs : IsGeoResolution M S) (hrt : IsGeoResolution M T) (U : Opens X)
    (y : openPreimage S U) :
    (restrict U T).proj (openCanonicalTerminalComparison M hM S T hs ht hrs hrt U y)=
      (restrict U S).proj y := by
  have hS := original_terminal_open_history_data M hM S hs hrs U
  have hT := original_terminal_open_history_data M hM T ht hrt U
  exact ambientTerminalComparison_proj (X := CMfd.of (n := n) U)
    (Y' := CMfd.of (n := n) (openPreimage S U))
    (Y := CMfd.of (n := n) (openPreimage T U))
    (pullback (Subtype.val : U → X) M) hS.1 (restrict U S) (restrict U T)
    hS.2.1 hT.2.1 hS.2.2 hT.2.2 y

theorem actualTerminalComparisonOnOpen_eq_canonical
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower X Y) (T : BlowupTower X Z)
    (hs : IsCanonical M ((canonicalInvariant n).inv M) S)
    (ht : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hrs : IsGeoResolution M S) (hrt : IsGeoResolution M T) (U : Opens X) :
    actualTerminalComparisonOnOpen M hM S T hs ht hrs hrt U=
      openCanonicalTerminalComparison M hM S T hs ht hrs hrt U := by
  apply biholomorphisms_eq_of_actual_proj_eq (restrict U T)
  intro y
  exact (actualTerminalComparisonOnOpen_proj M hM S T hs ht hrs hrt U y).trans
    (openCanonicalTerminalComparison_proj M hM S T hs ht hrs hrt U y).symm

theorem actualTerminalComparisonOnOpen_self
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (T : BlowupTower X Y) (hc : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hr : IsGeoResolution M T) (U : Opens X) :
    actualTerminalComparisonOnOpen M hM T T hc hc hr hr U=
      Diffeomorph.refl 𝓘(ℂ,ComplexModel n) (CMfd.of (n := n) (openPreimage T U)) ∞ := by
  exact biholomorphisms_eq_of_actual_proj_eq (restrict U T) _ _
    (actualTerminalComparisonOnOpen_proj M hM T T hc hc hr hr U)

theorem actualTerminalComparisonOnOpen_symm
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower X Y) (T : BlowupTower X Z)
    (hs : IsCanonical M ((canonicalInvariant n).inv M) S)
    (ht : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hrs : IsGeoResolution M S) (hrt : IsGeoResolution M T) (U : Opens X) :
    (actualTerminalComparisonOnOpen M hM S T hs ht hrs hrt U).symm=
      actualTerminalComparisonOnOpen M hM T S ht hs hrt hrs U := by
  apply biholomorphisms_eq_of_actual_proj_eq (restrict U S)
  intro z
  have h := actualTerminalComparisonOnOpen_proj M hM S T hs ht hrs hrt U
    ((actualTerminalComparisonOnOpen M hM S T hs ht hrs hrt U).symm z)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm.trans (actualTerminalComparisonOnOpen_proj M hM T S ht hs hrt hrs U z).symm

theorem actualTerminalComparisonOnOpen_trans
    (M : MarkedIdeal n X) (hM : IsInvDomain n M)
    (S : BlowupTower X Y) (T : BlowupTower X Z) (R : BlowupTower X W)
    (hs : IsCanonical M ((canonicalInvariant n).inv M) S)
    (ht : IsCanonical M ((canonicalInvariant n).inv M) T)
    (hr : IsCanonical M ((canonicalInvariant n).inv M) R)
    (hrs : IsGeoResolution M S) (hrt : IsGeoResolution M T)
    (hrr : IsGeoResolution M R) (U : Opens X) :
    (actualTerminalComparisonOnOpen M hM S T hs ht hrs hrt U).trans
      (actualTerminalComparisonOnOpen M hM T R ht hr hrt hrr U)=
      actualTerminalComparisonOnOpen M hM S R hs hr hrs hrr U := by
  apply biholomorphisms_eq_of_actual_proj_eq (restrict U R)
  intro y
  change (restrict U R).proj (actualTerminalComparisonOnOpen M hM T R ht hr hrt hrr U
    (actualTerminalComparisonOnOpen M hM S T hs ht hrs hrt U y))=_
  rw [actualTerminalComparisonOnOpen_proj,actualTerminalComparisonOnOpen_proj,
    actualTerminalComparisonOnOpen_proj]

end
end Hironaka.HironakaOriginalTerminalOpenComparison
