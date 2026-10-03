/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.StepOneWellFounded
import Hironaka.Invariant.InvDomainRebase
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneBridge
import Hironaka.Invariant.StepOneValueMasked
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Value functions for the marked ideals of maximal order: the properties without (8)

Sources: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 2a ("By Step 1 we can resolve
the marked ideal of maximal order `O(𝓘, μ)`"); Bierstone--Milman 2008, Step II.B.

The general step (`hir:general-step`) computes its value at a point of positive order `o` of the nonmonomial part
from the maximal-order invariant of a companion ideal, formed at a point-dependent stage on an open set. What it
uses of that invariant are its properties (1)--(7) and (4') of `hir:centre-function`, for the marked ideals of the
domain **of maximal order**, in the shape of the fields of `ResolutionInvariantExt.ResolutionInvariant`; for
well-ordered values it is automatic. This module packages those properties as a predicate `IsMaxOrderValue n k M` on
a value function `M` (no data, no field (8)), proves it for the masked Step 1 value (`isMaxOrderValue_stepOneInvM`,
from `StepOneBridge`, for a lower invariant of `ResolutionInvariantExt`; the route uses
`StepOneSeq.isMaxOrderValue_stepOneInvM`, its form for `ResolutionInvariantSeq` obtained by the kernel-checked
transport of `ExtSeqTransport`), and derives the canonical-segment API the general step needs, as
`ResolutionInvariantExt` and `InvDomainRebase` do for resolution invariants:

* `IsMaxOrderValue.step_of_notMem`, `.step_lt_of_mem`;
* `.isAdmissibleCentre_maxLocus`, `.isGeoTestTower_of_isCanonical` (canonical segments are multiple test blow-ups);
* `.isCanonical_restrict` (open sets), `.isCanonical_of_isTowerIso` (isomorphisms of towers), `.isCanonical_append_iff`
  (re-basing after an empty prefix), `.isCanonical_of_restrictEquiv` (representatives), and `.value_rebase` (re-basing the
  values: empty prefix and representative together, the form in which the general step compares nearby points).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.MaxOrderValue

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MarkedIdealOperationsAlong.MarkedIdeal Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerIsomorphism Hironaka.ResolutionInvariantOrder Hironaka.HomogenizedIdealAlong Hironaka.StepOneValueMasked Hironaka.StepOneWellFounded
open Hironaka.ResolutionDriver (maxLocus)
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (ResolutionInvariant IsEmptyTower isCanonical_of_isEmptyTower maxLocus_congr)
open Hironaka.ResolutionInvariantDriver (isAdmissibleCentre_of_pullback_val_top maxLocus_eq_level)
open Hironaka.ResolutionInvariantSegments (maxLocus_preimage maxLocus_preimage_of_surjective cosupp_geoTransformAlong_restrict)

noncomputable section

variable {n : ℕ}

/-! ### The predicate -/

variable (n) in
/-- **A value function for the marked ideals of maximal order** in dimension `≤ k` (`hir:max-order-value`): for every marked
ideal `𝔍` of `IsInvDomain k` of maximal order along its submanifold (`IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d`), the properties
(1)--(7) and (4') of `hir:centre-function` along the canonical segments of `M 𝔍`, in the shape of the fields of
`ResolutionInvariantExt.ResolutionInvariant` (the representatives in (7) both of maximal order).  Property (8) is not part
of it. -/
structure IsMaxOrderValue (k : ℕ) {Λ : Type v} [LinearOrder Λ]
    (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) : Prop where
  /-- (1) Admissibility of the level sets of the maximum, on open sets. -/
  admissible : ∀ {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔍 (M 𝔍) T →
    ∀ (W : Opens Y) (l : Λ), (∀ y ∈ (geoTransformAlong 𝔍 T).cosupp, y ∈ W → M 𝔍 T y ≤ l) →
      (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong 𝔍 T)).IsAdmissibleCentre
        ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔍 T).cosupp ∧ M 𝔍 T y = l})
  /-- (2) Upper semicontinuity on the cosupport. -/
  usc : ∀ {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔍 (M 𝔍) T →
      IsInvUSCOn (M 𝔍 T) (geoTransformAlong 𝔍 T).cosupp
  /-- (3) Decrease under the blowup of the maximum locus. -/
  decrease : ∀ {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
    ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsCanonical 𝔍 (M 𝔍) T → C = maxLocus (M 𝔍 T) (geoTransformAlong 𝔍 T).cosupp →
      ∀ z ∈ (geoTransformAlong 𝔍 (.step T C π hπ)).cosupp,
        (π z ∈ C → M 𝔍 (.step T C π hπ) z < M 𝔍 T (π z)) ∧ (π z ∉ C → M 𝔍 (.step T C π hπ) z = M 𝔍 T (π z))
  /-- (4) Empty steps. -/
  emptyStep : ∀ {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
    ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π), C = ∅ →
      IsCanonical 𝔍 (M 𝔍) T → ∀ z ∈ (geoTransformAlong 𝔍 (.step T C π hπ)).cosupp,
        M 𝔍 (.step T C π hπ) z = M 𝔍 T (π z)
  /-- (4') Empty prefixes. -/
  emptyPrefix : ∀ {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
    ∀ {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y), IsEmptyTower T₀ →
      IsCanonical 𝔍 (M 𝔍) (T₀.append T₁) → ∀ z ∈ (geoTransformAlong 𝔍 (T₀.append T₁)).cosupp,
        M 𝔍 (T₀.append T₁) z = M (geoTransformAlong 𝔍 T₀) T₁ z
  /-- (5) Restriction to open sets. -/
  restrictOpen : ∀ {X : CMfd.{u} n} (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
    ∀ (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔍 (M 𝔍) T →
    ∀ p : openPreimage T U, (p : Y) ∈ (geoTransformAlong 𝔍 T).cosupp →
      M (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T) p = M 𝔍 T p
  /-- (6) Isomorphisms of towers over biholomorphisms. -/
  towerIso : ∀ {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (𝔍 : MarkedIdeal n X), IsInvDomain k 𝔍 → IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d →
    ∀ {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y') (T : BlowupTower X Y)
      (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y),
      IsTowerIso Φ T' T χ → IsCanonical 𝔍 (M 𝔍) T → ∀ p : Y', χ p ∈ (geoTransformAlong 𝔍 T).cosupp →
        M (MarkedIdeal.pullback Φ 𝔍) T' p = M 𝔍 T (χ p)
  /-- (7) Independence of the representative (both of maximal order). -/
  representative : ∀ {X : CMfd.{u} n} (𝔍 𝔫 : MarkedIdeal n X), IsInvDomain k 𝔍 →
    IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d → IsInvDomain k 𝔫 → IsMaximalOrderAlong 𝔫.N 𝔫.ideal 𝔫.d →
    RestrictEquiv 𝔍 𝔫 → ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔍 (M 𝔍) T →
      ∀ y ∈ (geoTransformAlong 𝔍 T).cosupp, M 𝔍 T y = M 𝔫 T y

/-! ### The masked Step 1 value -/

section StepOne

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]

/-- **The masked Step 1 value is a value function for the marked ideals of maximal order** (`0 < n`;
`StepOneBridge`). -/
theorem isMaxOrderValue_stepOneInvM (R : ResolutionInvariant.{u, v} n (k - 1) Λ) (hn : 0 < n) :
    IsMaxOrderValue n k (fun {X} 𝔍 {Y} T y => stepOneInvM (X := X) R 𝔍 (Y := Y) T y) where
  admissible := by
    intro X 𝔍 h hmax Y T hcan W l hle
    exact StepOneBridge.admissible_field R 𝔍 h hmax hn T hcan W l hle
  usc := by
    intro X 𝔍 h hmax Y T hcan
    exact StepOneBridge.usc_field R 𝔍 h hmax hn T hcan
  decrease := by
    intro X 𝔍 h hmax Y Z T C π hπ hcan hC
    exact StepOneBridge.decrease_field R 𝔍 h hmax hn T C π hπ hcan hC
  emptyStep := by
    intro X 𝔍 h hmax Y Z T C π hπ hC hcan
    exact StepOneBridge.emptyStep_field R 𝔍 h hmax hn T C π hπ hC hcan
  emptyPrefix := by
    intro X 𝔍 h hmax Y₀ Y T₀ T₁ h₀ hcan
    exact StepOneBridge.emptyPrefix_field R 𝔍 h hmax hn T₀ T₁ h₀ hcan
  restrictOpen := by
    intro X 𝔍 h hmax U Y T hcan p hp
    exact StepOneBridge.restrictOpen_field R 𝔍 h hmax hn U T hcan p hp
  towerIso := by
    intro X X' Φ 𝔍 h hmax Y' Y T' T χ hiso hcan p hp
    exact StepOneBridge.towerIso_field R 𝔍 Φ h hmax hn T' T χ hiso hcan p hp
  representative := by
    intro X 𝔍 𝔫 h hmax h𝔫 hmax𝔫 hEq Y T hcan y hy
    exact StepOneBridge.representative_field R 𝔍 h hmax h𝔫 hmax𝔫 hn hEq T hcan y hy

end StepOne

/-! ### One step -/

namespace IsMaxOrderValue

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

section Step

variable {X : CMfd.{u} n}

/-- **Off the centre of the last blowup of a canonical segment the value does not change** ((3) and (4)). -/
theorem step_of_notMem (hM : IsMaxOrderValue n k M) {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hcan : IsCanonical 𝔍 (M 𝔍) (.step T C π hπ)) {z : Z}
    (hz : z ∈ (geoTransformAlong 𝔍 (.step T C π hπ)).cosupp) (hzC : π z ∉ C) :
    M 𝔍 (.step T C π hπ) z = M 𝔍 T (π z) := by
  obtain ⟨hT, hC⟩ : IsCanonical 𝔍 (M 𝔍) T ∧ (C = ∅ ∨ C = maxLocus (M 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) := hcan
  rcases hC with hC | hC
  · exact hM.emptyStep 𝔍 h hmax T C π hπ hC hT z hz
  · exact (hM.decrease 𝔍 h hmax T C π hπ hT hC z hz).2 hzC

/-- **Over the centre of the last blowup of a canonical segment the value drops** (property (3)). -/
theorem step_lt_of_mem (hM : IsMaxOrderValue n k M) {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hcan : IsCanonical 𝔍 (M 𝔍) (.step T C π hπ)) {z : Z}
    (hz : z ∈ (geoTransformAlong 𝔍 (.step T C π hπ)).cosupp) (hzC : π z ∈ C) :
    M 𝔍 (.step T C π hπ) z < M 𝔍 T (π z) := by
  obtain ⟨hT, hC⟩ : IsCanonical 𝔍 (M 𝔍) T ∧ (C = ∅ ∨ C = maxLocus (M 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) := hcan
  rcases hC with hC | hC
  · rw [hC] at hzC
    exact absurd hzC (notMem_empty _)
  · exact (hM.decrease 𝔍 h hmax T C π hπ hT hC z hz).1 hzC

/-- **The maximum locus is an admissible centre** along a canonical segment which is a multiple test blow-up (property (1)
on the whole last stage). -/
theorem isAdmissibleCentre_maxLocus (hM : IsMaxOrderValue n k M) {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical 𝔍 (M 𝔍) T) (hT : IsGeoTestTower 𝔍 T) :
    (geoTransformAlong 𝔍 T).IsAdmissibleCentre (maxLocus (M 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) := by
  by_cases hne : (maxLocus (M 𝔍 T) (geoTransformAlong 𝔍 T).cosupp).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hadm := hM.admissible 𝔍 h hmax T hcan ⊤ (M 𝔍 T y₀) (fun y hy _ => hy₀.2 y hy)
    rw [← maxLocus_eq_level hy₀] at hadm
    have hcoh := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT).isCoherent
    exact isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg) hadm
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Canonical segments are multiple test blow-ups.** -/
theorem isGeoTestTower_of_isCanonical (hM : IsMaxOrderValue n k M) {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔍 (M 𝔍) T → IsGeoTestTower 𝔍 T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔍 (M 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (M 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) := hcan
      have hTt := isGeoTestTower_of_isCanonical hM h hmax T hT
      refine (isGeoTestTower_step_iff 𝔍 T C π hπ).mpr ⟨hTt, ?_⟩
      rcases hC with rfl | rfl
      · exact MarkedIdeal.isAdmissibleCentre_empty _
      · exact isAdmissibleCentre_maxLocus hM h hmax T hT hTt

end Step

/-! ### Canonical segments on open sets, along isomorphisms of towers, after empty prefixes, for representatives -/

section Segments

variable {X X' : CMfd.{u} n}

/-- **The restriction of a canonical segment to an open set is a canonical segment** of the restricted marked ideal. -/
theorem isCanonical_restrict (hM : IsMaxOrderValue n k M) {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (U : Opens X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔍 (M 𝔍) T →
      IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
        (M (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T)
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔍 (M 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (M 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) := hcan
      have ih := isCanonical_restrict hM h hmax U T hT
      have hTt := isGeoTestTower_of_isCanonical hM h hmax T hT
      show IsCanonical (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)
          (M (X := CMfd.of (n := n) U) (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍)) (restrict U T) ∧
        (((Subtype.val : openPreimage T U → _) ⁻¹' C) = ∅ ∨
          ((Subtype.val : openPreimage T U → _) ⁻¹' C) = maxLocus (M (X := CMfd.of (n := n) U)
            (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T))
            (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔍) (restrict U T)).cosupp)
      refine ⟨ih, ?_⟩
      rcases hC with rfl | rfl
      · exact Or.inl preimage_empty
      · by_cases hne : ((Subtype.val : openPreimage T U → _) ⁻¹'
            maxLocus (M 𝔍 T) (geoTransformAlong 𝔍 T).cosupp).Nonempty
        · right
          rw [cosupp_geoTransformAlong_restrict h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent U T hTt]
          exact (maxLocus_preimage _ (fun p hp => hM.restrictOpen 𝔍 h hmax U T hT p hp) hne).symm
        · exact Or.inl (not_nonempty_iff_eq_empty.mp hne)

/-- **Canonical segments correspond along isomorphisms of towers.** -/
theorem isCanonical_of_isTowerIso (hM : IsMaxOrderValue n k M) {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    {Y' Y : CMfd.{u} n} {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hiso : IsTowerIso Φ T' T χ) :
    IsCanonical 𝔍 (M 𝔍) T → IsCanonical (MarkedIdeal.pullback Φ 𝔍) (M (MarkedIdeal.pullback Φ 𝔍)) T' := by
  induction hiso with
  | refl => exact fun _ => trivial
  | @step Y' Y Z' Z T' T χ hiso C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro hcan
    obtain ⟨hT, hCc⟩ : IsCanonical 𝔍 (M 𝔍) T ∧
        (C = ∅ ∨ C = maxLocus (M 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) := hcan
    have hTt := isGeoTestTower_of_isCanonical hM h hmax T hT
    show IsCanonical (MarkedIdeal.pullback Φ 𝔍) (M (MarkedIdeal.pullback Φ 𝔍)) T' ∧
      (C' = ∅ ∨ C' = maxLocus (M (MarkedIdeal.pullback Φ 𝔍) T')
        (geoTransformAlong (MarkedIdeal.pullback Φ 𝔍) T').cosupp)
    refine ⟨ih hT, ?_⟩
    subst hC
    rcases hCc with rfl | rfl
    · exact Or.inl preimage_empty
    · right
      rw [IsTowerIso.cosupp_geoTransformAlong Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent
        hiso hTt]
      exact (maxLocus_preimage_of_surjective χ.toEquiv.surjective
        (fun p hp => hM.towerIso Φ 𝔍 h hmax T' T χ hiso hT p hp)).symm

/-- **Re-basing canonical segments**: after a prefix `T₀` with only empty centres, `T₀ T₁` is a canonical segment of `𝔍` iff
`T₁` is a canonical segment of `𝔍_{T₀}`. -/
theorem isCanonical_append_iff (hM : IsMaxOrderValue n k M) {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (h₀ : IsEmptyTower T₀) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y),
      IsCanonical 𝔍 (M 𝔍) (T₀.append T₁) ↔ IsCanonical (geoTransformAlong 𝔍 T₀) (M (geoTransformAlong 𝔍 T₀)) T₁
  | _, .refl => ⟨fun _ => trivial, fun _ => isCanonical_of_isEmptyTower 𝔍 (M 𝔍) T₀ h₀⟩
  | _, .step T₁ C π hπ => by
      have ih := isCanonical_append_iff hM h hmax T₀ h₀ T₁
      have hloc : IsCanonical 𝔍 (M 𝔍) (T₀.append T₁) →
          maxLocus (M 𝔍 (T₀.append T₁)) (geoTransformAlong 𝔍 (T₀.append T₁)).cosupp =
            maxLocus (M (geoTransformAlong 𝔍 T₀) T₁) (geoTransformAlong (geoTransformAlong 𝔍 T₀) T₁).cosupp := by
        intro hc
        rw [← geoTransformAlong_append 𝔍 T₀ T₁]
        exact maxLocus_congr fun z hz => hM.emptyPrefix 𝔍 h hmax T₀ T₁ h₀ hc z hz
      show (IsCanonical 𝔍 (M 𝔍) (T₀.append T₁) ∧
          (C = ∅ ∨ C = maxLocus (M 𝔍 (T₀.append T₁)) (geoTransformAlong 𝔍 (T₀.append T₁)).cosupp)) ↔
        (IsCanonical (geoTransformAlong 𝔍 T₀) (M (geoTransformAlong 𝔍 T₀)) T₁ ∧
          (C = ∅ ∨ C = maxLocus (M (geoTransformAlong 𝔍 T₀) T₁)
            (geoTransformAlong (geoTransformAlong 𝔍 T₀) T₁).cosupp))
      constructor
      · rintro ⟨hc, hC⟩
        exact ⟨ih.mp hc, hC.imp id fun h => h.trans (hloc hc)⟩
      · rintro ⟨hc', hC⟩
        have hc := ih.mpr hc'
        exact ⟨hc, hC.imp id fun h => h.trans (hloc hc).symm⟩

/-- **Canonical segments correspond along restricted equivalence** (both marked ideals in the domain, of maximal order). -/
theorem isCanonical_of_restrictEquiv (hM : IsMaxOrderValue n k M) {𝔍 𝔫 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) (h𝔫 : IsInvDomain k 𝔫) (hmax𝔫 : IsMaximalOrderAlong 𝔫.N 𝔫.ideal 𝔫.d)
    (hEq : RestrictEquiv 𝔍 𝔫) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔍 (M 𝔍) T → IsCanonical 𝔫 (M 𝔫) T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔍 (M 𝔍) T ∧
          (C = ∅ ∨ C = maxLocus (M 𝔍 T) (geoTransformAlong 𝔍 T).cosupp) := hcan
      have hcos := (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.cosupp_admissible_geoTransformAlong hEq
        h.isWellFormed.isClosedSubmanifold_N.1 h.isWellFormed.isCoherent h𝔫.isWellFormed.isCoherent T).1
      show IsCanonical 𝔫 (M 𝔫) T ∧ (C = ∅ ∨ C = maxLocus (M 𝔫 T) (geoTransformAlong 𝔫 T).cosupp)
      refine ⟨isCanonical_of_restrictEquiv hM h hmax h𝔫 hmax𝔫 hEq T hT, hC.imp id fun hC => ?_⟩
      rw [hC, ← hcos]
      exact maxLocus_congr fun y hy => hM.representative 𝔍 𝔫 h hmax h𝔫 hmax𝔫 hEq T hT y hy

/-- **Re-basing the values** (empty prefix and representative together): let `𝔍` lie in the domain, of maximal order, `T₀` a
tower with only empty centres, and `𝔫` (coherent ideal, of maximal order) restricted-equivalent to `𝔍_{T₀}`.  If `T₀ T₁` is a
canonical segment of `𝔍`, then `𝔫` lies in the domain, `T₁` is a canonical segment of `𝔫`, and the values of `𝔍` along
`T₀ T₁` are those of `𝔫` along `T₁` on the cosupport. -/
theorem value_rebase (hM : IsMaxOrderValue n k M) {𝔍 : MarkedIdeal n X} (h : IsInvDomain k 𝔍)
    (hmax : IsMaximalOrderAlong 𝔍.N 𝔍.ideal 𝔍.d) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (h₀ : IsEmptyTower T₀)
    {𝔫 : MarkedIdeal n Y₀} (hEq : RestrictEquiv 𝔫 (geoTransformAlong 𝔍 T₀)) (h𝔫 : 𝔫.ideal.IsCoherent)
    (hmax𝔫 : IsMaximalOrderAlong 𝔫.N 𝔫.ideal 𝔫.d) (hmax₀ : IsMaximalOrderAlong (geoTransformAlong 𝔍 T₀).N
      (geoTransformAlong 𝔍 T₀).ideal (geoTransformAlong 𝔍 T₀).d) (T₁ : BlowupTower Y₀ Y)
    (hcan : IsCanonical 𝔍 (M 𝔍) (T₀.append T₁)) :
    IsInvDomain k 𝔫 ∧ IsCanonical 𝔫 (M 𝔫) T₁ ∧
      ∀ z ∈ (geoTransformAlong 𝔍 (T₀.append T₁)).cosupp, M 𝔍 (T₀.append T₁) z = M 𝔫 T₁ z := by
  have hdom₀ := InvDomainRebase.isInvDomain_geoTransformAlong_of_isEmptyTower h T₀ h₀
  have hEq' := InvDomainRebase.restrictEquiv_symm hEq
  have h𝔫d : IsInvDomain k 𝔫 := InvDomainRebase.isInvDomain_of_restrictEquiv hdom₀ hEq' h𝔫
  have hcan₁ := (isCanonical_append_iff hM h hmax T₀ h₀ T₁).mp hcan
  refine ⟨h𝔫d, isCanonical_of_restrictEquiv hM hdom₀ hmax₀ h𝔫d hmax𝔫 hEq' T₁ hcan₁, fun z hz => ?_⟩
  rw [hM.emptyPrefix 𝔍 h hmax T₀ T₁ h₀ hcan z hz]
  rw [geoTransformAlong_append] at hz
  exact hM.representative _ 𝔫 hdom₀ hmax₀ h𝔫d hmax𝔫 hEq' T₁ hcan₁ z hz

end Segments

end IsMaxOrderValue

end

end Hironaka.MaxOrderValue
