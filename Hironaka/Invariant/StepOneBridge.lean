/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneTowerIso
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.HomogenizedIdealAlongTower
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneAdmissible
import Hironaka.Invariant.StepOneEmptyPrefix
import Hironaka.Invariant.StepOneLowerDomain
import Hironaka.Invariant.StepOneRepresentative
import Hironaka.Invariant.StepOneRestrictOpen
import Hironaka.Invariant.StepOneValue
import Hironaka.Invariant.StepOneValueMasked
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Step 1: the properties of the value stated for the marked ideal itself

The properties of the masked Step 1 value function `stepOneInvM R 𝔍` were proved along the canonical segments of `J̄ =
𝓒_N(𝓗_N(𝔍))` (maximum loci on `cosupp J̄_T`).  The fields of a resolution invariant (`ResolutionInvariantExt.ResolutionInvariant`)
are stated for the marked ideal `𝔍` itself: canonical segments with maximum loci on `cosupp 𝔍_T`, and the cosupport and admissible
centres of `𝔍_T`.  For `𝔍` in the domain, `J̄` and `𝔍` are equivalent (`HomogenizedIdealAlongTower.coeff_homAlong_wEquiv`: the same
divisor, the same multiple test blow-ups and, along them, the same cosupports), so the two notions of canonical segment agree
(`isCanonical_iff`), and every property transfers.  This module states properties (1)--(7) and (4') of the masked Step 1 value
in exactly the shape of the fields of `ResolutionInvariantExt.ResolutionInvariant`, for the marked ideals of the domain in dimension
`≤ k` which are of maximal order along `N` (`0 < n`), given a resolution invariant `R` in dimension `≤ k - 1`.

## Main results

* `isAdmissibleCentre_pullback_val_iff_of_eq`: admissible centres on an open set depend only on the divisor and the cosupport;
* `isCanonical_iff`, `isGeoTestTower_of_isCanonical`, `cosupp_eq_of_isCanonical`: canonical segments of `𝔍` and of `J̄` agree;
* `admissible_field`, `usc_field`, `decrease_field`, `emptyStep_field`, `emptyPrefix_field`, `restrictOpen_field`,
  `towerIso_field`, `representative_field`: the fields (1)--(7) and (4').
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.StepOneBridge

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.StepOneValue Hironaka.StepOneValueMasked Hironaka.HomogenizedIdealAlong Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerIsomorphism Hironaka.MarkedIdealOperationsAlong.MarkedIdeal Hironaka.ResolutionInvariantOrder
open Hironaka.MarkedIdealEquivalence.MarkedIdeal (WEquiv E_geoTransformAlong_eq)
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical DimLE)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant IsEmptyTower)

noncomputable section

variable {n : ℕ}

/-- **Admissible centres on an open set depend only on the divisor and the cosupport** (coherent ideals). -/
theorem isAdmissibleCentre_pullback_val_iff_of_eq {Y : CMfd.{u} n} {𝔪 𝔫 : MarkedIdeal n Y} (h𝔪 : 𝔪.ideal.IsCoherent)
    (h𝔫 : 𝔫.ideal.IsCoherent) (hE : 𝔪.E = 𝔫.E) (hc : 𝔪.cosupp = 𝔫.cosupp) (W : Opens Y) (C : Set W) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔪).IsAdmissibleCentre C ↔
      (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).IsAdmissibleCentre C := by
  unfold IsAdmissibleCentre
  rw [cosupp_pullback_val 𝔪 (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔪 hg) W,
    cosupp_pullback_val 𝔫 (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h𝔫 hg) W, hc]
  have hE' : (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔪).E = (MarkedIdeal.pullback (Subtype.val : W → Y) 𝔫).E := by
    show 𝔪.E.map _ = 𝔫.E.map _
    rw [hE]
  rw [hE']

variable {X : CMfd.{u} n} {k : ℕ} {Λ : Type v} [LinearOrder Λ] (R : ResolutionInvariant.{u, v} n (k - 1) Λ)
  (𝔍 : MarkedIdeal n X)

/-- `J̄ ≃ 𝔍` for `𝔍` in the domain. -/
theorem barMarked_wEquiv (h : IsInvDomain k 𝔍) : WEquiv (barMarked 𝔍) 𝔍 :=
  HomogenizedIdealAlongTower.coeff_homAlong_wEquiv 𝔍 h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent
    h.one_le_d

/-- **The canonical segments of the masked Step 1 value for `𝔍` and for `J̄` agree** (`𝔍` in the domain, of maximal order):
along a canonical segment of `J̄`, a multiple test blow-up of `J̄` and of `𝔍`, the cosupports agree, hence the maximum loci. -/
theorem isCanonical_iff (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y),
      IsCanonical 𝔍 (stepOneInvM R 𝔍) T ↔ IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T
  | _, .refl => Iff.rfl
  | _, .step T C π hπ => by
      have ih := isCanonical_iff h hmax hn T
      have hW := barMarked_wEquiv 𝔍 h
      have hcos : IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T →
          (geoTransformAlong (barMarked 𝔍) T).cosupp = (geoTransformAlong 𝔍 T).cosupp := fun hc =>
        (hW.2 T).2 (StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h.isWellFormed h.one_le_d hn hmax
          h.dimLE T hc)
      show (IsCanonical 𝔍 (stepOneInvM R 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp)) ↔
        (IsCanonical (barMarked 𝔍) (stepOneInvM R 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong (barMarked 𝔍) T).cosupp))
      constructor
      · rintro ⟨hc, hC⟩
        have hc' := ih.mp hc
        exact ⟨hc', by rw [hcos hc']; exact hC⟩
      · rintro ⟨hc', hC⟩
        exact ⟨ih.mpr hc', by rw [← hcos hc']; exact hC⟩

/-- Canonical segments of the masked Step 1 value for `𝔍` are multiple test blow-ups of `𝔍` and of `J̄`, and along them the
cosupports of `J̄_T` and `𝔍_T` agree. -/
theorem isGeoTestTower_of_isCanonical (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T) :
    IsGeoTestTower (barMarked 𝔍) T ∧ IsGeoTestTower 𝔍 T ∧
      (geoTransformAlong (barMarked 𝔍) T).cosupp = (geoTransformAlong 𝔍 T).cosupp := by
  have hW := barMarked_wEquiv 𝔍 h
  have hJ := StepOneAdmissible.isGeoTestTower_of_isCanonical_stepOneInvM 𝔍 R h.isWellFormed h.one_le_d hn hmax h.dimLE T
    ((isCanonical_iff R 𝔍 h hmax hn T).mp hcan)
  exact ⟨hJ, (hW.2 T).1.mp hJ, (hW.2 T).2 hJ⟩

/-- **Property (1), the field `admissible`.** -/
theorem admissible_field (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T) (W : Opens Y)
    (l : ℕ ×ₗ WithTop Λ) (hle : ∀ y ∈ (geoTransformAlong 𝔍 T).cosupp, y ∈ W → stepOneInvM R 𝔍 T y ≤ l) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong 𝔍 T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔍 T).cosupp ∧ stepOneInvM R 𝔍 T y = l}) := by
  have hcanJ := (isCanonical_iff R 𝔍 h hmax hn T).mp hcan
  obtain ⟨hJT, hT, hcos⟩ := isGeoTestTower_of_isCanonical R 𝔍 h hmax hn T hcan
  rw [← hcos] at hle ⊢
  have hadm := StepOneAdmissible.stepOneInvM_admissible_of_isCanonical 𝔍 R h.isWellFormed h.one_le_d hn hmax h.dimLE T
    hcanJ W l hle
  have hJ := StepOneLowerDomain.isWellFormed_barMarked 𝔍 h.isWellFormed
  obtain ⟨-, hcJ⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong hJ.isClosedSubmanifold_N hJ.isCoherent T hJT
  obtain ⟨-, hc𝔍⟩ := isClosedSubmanifold_N_and_isCoherent_geoTransformAlong h.isWellFormed.isClosedSubmanifold_N
    h.isWellFormed.isCoherent T hT
  exact (isAdmissibleCentre_pullback_val_iff_of_eq hcJ hc𝔍 (E_geoTransformAlong_eq (barMarked_wEquiv 𝔍 h).1 T) hcos W
    _).mp hadm

/-- **Property (2), the field `usc`.** -/
theorem usc_field (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T) :
    IsInvUSCOn (stepOneInvM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp := by
  rw [← (isGeoTestTower_of_isCanonical R 𝔍 h hmax hn T hcan).2.2]
  exact StepOneAdmissible.stepOneInvM_usc_of_isCanonical 𝔍 R h.isWellFormed h.one_le_d hn hmax h.dimLE T
    ((isCanonical_iff R 𝔍 h hmax hn T).mp hcan)

/-- **Property (3), the field `decrease`** (`C ≠ ∅` not needed). -/
theorem decrease_field (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T)
    (hC : C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) :
    ∀ z ∈ (geoTransformAlong 𝔍 (.step T C π hπ)).cosupp,
      (π z ∈ C → stepOneInvM R 𝔍 (.step T C π hπ) z < stepOneInvM R 𝔍 T (π z)) ∧
      (π z ∉ C → stepOneInvM R 𝔍 (.step T C π hπ) z = stepOneInvM R 𝔍 T (π z)) := by
  have hcanS : IsCanonical 𝔍 (stepOneInvM R 𝔍) (.step T C π hπ) :=
    (⟨hcan, Or.inr hC⟩ : IsCanonical 𝔍 (stepOneInvM R 𝔍) T ∧
      (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp))
  rw [← (isGeoTestTower_of_isCanonical R 𝔍 h hmax hn _ hcanS).2.2]
  rw [← (isGeoTestTower_of_isCanonical R 𝔍 h hmax hn T hcan).2.2] at hC
  exact StepOneAdmissible.stepOneInvM_decrease_of_isCanonical 𝔍 R h.isWellFormed h.one_le_d hn hmax h.dimLE T C π hπ
    ((isCanonical_iff R 𝔍 h hmax hn T).mp hcan) hC

/-- **Property (4), the field `emptyStep`.** -/
theorem emptyStep_field (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π) (hC : C = ∅)
    (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T) :
    ∀ z ∈ (geoTransformAlong 𝔍 (.step T C π hπ)).cosupp,
      stepOneInvM R 𝔍 (.step T C π hπ) z = stepOneInvM R 𝔍 T (π z) := by
  have hcanS : IsCanonical 𝔍 (stepOneInvM R 𝔍) (.step T C π hπ) :=
    (⟨hcan, Or.inl hC⟩ : IsCanonical 𝔍 (stepOneInvM R 𝔍) T ∧
      (C = ∅ ∨ C = maxLocus (stepOneInvM R 𝔍 T) (geoTransformAlong 𝔍 T).cosupp))
  rw [← (isGeoTestTower_of_isCanonical R 𝔍 h hmax hn _ hcanS).2.2]
  exact StepOneAdmissible.stepOneInvM_emptyStep_of_isCanonical 𝔍 R h.isWellFormed h.one_le_d hn hmax h.dimLE T C π hπ hC
    ((isCanonical_iff R 𝔍 h hmax hn T).mp hcan)

/-- **Property (4'), the field `emptyPrefix`.** -/
theorem emptyPrefix_field (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (h₀ : IsEmptyTower T₀)
    (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) (T₀.append T₁)) :
    ∀ z ∈ (geoTransformAlong 𝔍 (T₀.append T₁)).cosupp,
      stepOneInvM R 𝔍 (T₀.append T₁) z = stepOneInvM R (geoTransformAlong 𝔍 T₀) T₁ z := by
  intro z hz
  rw [← (isGeoTestTower_of_isCanonical R 𝔍 h hmax hn _ hcan).2.2] at hz
  exact (StepOneEmptyPrefix.stepOneInvM_emptyPrefix 𝔍 R h.isWellFormed h.one_le_d hn hmax h.dimLE T₀ h₀ T₁
    ((isCanonical_iff R 𝔍 h hmax hn _).mp hcan)).2 z hz

/-- **Property (5), the field `restrictOpen`.** -/
theorem restrictOpen_field (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n)
    (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T)
    (p : openPreimage T U) (hp : (p : Y) ∈ (geoTransformAlong 𝔍 T).cosupp) :
    stepOneInvM (X := CMfd.of (n := n) U) R (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p =
      stepOneInvM R 𝔍 T p := by
  rw [← (isGeoTestTower_of_isCanonical R 𝔍 h hmax hn T hcan).2.2] at hp
  exact (StepOneRestrictOpen.stepOneInvM_restrict 𝔍 U R h.isWellFormed h.one_le_d hn hmax h.dimLE T
    ((isCanonical_iff R 𝔍 h hmax hn T).mp hcan)).2 p hp

/-- **Property (6), the field `towerIso`.** -/
theorem towerIso_field {X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (hn : 0 < n) {Y' Y : CMfd.{u} n}
    (T' : BlowupTower X' Y') (T : BlowupTower X Y) (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y)
    (hiso : IsTowerIso Φ T' T χ) (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T) (p : Y')
    (hp : χ p ∈ (geoTransformAlong 𝔍 T).cosupp) :
    stepOneInvM R (MarkedIdeal.pullback Φ 𝔍) T' p = stepOneInvM R 𝔍 T (χ p) := by
  rw [← (isGeoTestTower_of_isCanonical R 𝔍 h hmax hn T hcan).2.2] at hp
  exact (StepOneTowerIso.stepOneInvM_isTowerIso Φ 𝔍 R h.isWellFormed h.one_le_d hn hmax h.dimLE hiso
    ((isCanonical_iff R 𝔍 h hmax hn T).mp hcan)).2 p hp

/-- **Property (7), the field `representative`** (both marked ideals of maximal order). -/
theorem representative_field {𝔫 : MarkedIdeal n X} (h : IsInvDomain k 𝔍) (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d)
    (h𝔫 : IsInvDomain k 𝔫) (hmax𝔫 : IsMaximalOrderAlong 𝔫.N 𝔫.ideal 𝔫.d) (hn : 0 < n) (hEq : RestrictEquiv 𝔍 𝔫)
    {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔍 (stepOneInvM R 𝔍) T)
    (y : Y) (hy : y ∈ (geoTransformAlong 𝔍 T).cosupp) :
    stepOneInvM R 𝔍 T y = stepOneInvM R 𝔫 T y := by
  rw [← (isGeoTestTower_of_isCanonical R 𝔍 h hmax hn T hcan).2.2] at hy
  exact (StepOneRepresentative.stepOneInvM_representative R h.isWellFormed h.one_le_d hn hmax h.dimLE h𝔫.isWellFormed
    h𝔫.one_le_d hmax𝔫 h𝔫.dimLE hEq T ((isCanonical_iff R 𝔍 h hmax hn T).mp hcan)).2 y hy

end

end Hironaka.StepOneBridge
