/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.ResolutionInvariantSegments
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantDriver
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Resolution invariants along canonical segments, invariant under empty prefixes

* the properties (2) and (4)--(7) are required along **canonical segments** only, as in the sources (Włodarczyk
  2005, Proposition `pr:resol` (1) and (4): the invariants live on the supports of the canonical resolution, and an
  étale pullback of the canonical resolution is an *extension* of the canonical resolution), instead of along every
  multiple test blow-up;
* invariance under an empty step is stated for a centre `C` with `C = ∅` (restricted towers have centres `(↑) ⁻¹'
  C`, empty only propositionally);
* **re-basing along an empty prefix** (new field `emptyPrefix`): if the first part `T₀` of a canonical segment `T₀
  T₁` has only empty centres, the invariant of `𝔪` along `T₀ T₁` is that of `𝔪_{T₀}` along `T₁`. Włodarczyk's
  extensions insert isomorphisms anywhere in a resolution (`hiron.tex`, the definition of extensions and the étale
  lemma in the proof of `pr:resol`); the inductive step compares points whose lower-dimensional invariants are
  computed from different stages, across steps which are empty near them.

This structure enters the constant cone of the main theorem only through the base case
`ResolutionInvariantSeq.ResolutionInvariant.ofDimZero` (`ofExt` of `ResolutionInvariant.ofDimZero` here). Results
stated for it that never use `locallyFinite` reach the route through the kernel-checked transport of
`ExtSeqTransport` (`StepOneSeq`).

The domain `ResolutionInvariantSpec.IsInvDomain`, canonical segments `ResolutionInvariantSpec.IsCanonical` and the count
`ResolutionInvariantSpec.countCentresMeeting` are unchanged.

## Main results

* `IsEmptyTower`: every centre is empty; such towers are canonical segments and multiple test blow-ups;
* `ResolutionInvariant n k Λ`: the structure (fields `admissible`, `usc`, `decrease`, `emptyStep`, `emptyPrefix`,
  `restrictOpen`, `towerIso`, `representative`, `locallyFinite`);
* `ResolutionInvariant.ofDimZero`: the base case -- every constant function is one in dimension `≤ 0`;
* `isAdmissibleCentre_maxLocus`, `isGeoTestTower_of_isCanonical`, `isInvDomain_of_isCanonical`,
  `exists_isGeoResolution_isCanonicalSegment`: the driver (`hir:invariant-driver`) for the new structure -- over a
  compact base every marked ideal of the domain is resolved by a canonical segment;
* `isCanonical_restrict`, `isCanonical_of_isTowerIso`: canonical segments restrict to open sets and correspond along
  isomorphisms of towers (`hir:canonical-segments`);
* `maxLocus_congr`, `isCanonical_append_iff`: **re-basing canonical segments** -- after an empty prefix `T₀`, `T₀ T₁` is a
  canonical segment of `𝔪` iff `T₁` is one of `𝔪_{T₀}`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ResolutionInvariantExt

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealBiholomorphism.MarkedIdeal Hironaka.MarkedIdealOperationsAlong.MarkedIdeal Hironaka.MarkedIdealRestrictOpen Hironaka.BlowupTowerIsomorphism Hironaka.ResolutionInvariantOrder Hironaka.ResolutionDriver
open Hironaka.ResolutionInvariantSpec (DimLE IsInvDomain IsCanonical countCentresMeeting cosupp_geoTransformAlong_eq_empty_of_dimLE_zero countCentresMeeting_eq_zero_of_dimLE_zero)
open Hironaka.ResolutionInvariantDriver (isAdmissibleCentre_of_pullback_val_top maxLocus_eq_level interior_maxLocus_eq_empty isCanonical_of_isCanonicalSegment)
open Hironaka.ResolutionInvariantSegments (maxLocus_preimage maxLocus_preimage_of_surjective cosupp_geoTransformAlong_restrict)

noncomputable section

variable {n : ℕ}

/-! ### Empty towers -/

section Empty

variable {X : CMfd.{u} n}

/-- **A tower all of whose centres are empty** (a sequence of isomorphisms, in Włodarczyk's terms). -/
def IsEmptyTower : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ => IsEmptyTower T ∧ C = ∅

/-- An empty tower is a canonical segment (for every function). -/
theorem isCanonical_of_isEmptyTower {Λ : Type v} [LinearOrder Λ] (𝔪 : MarkedIdeal n X)
    (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower T → IsCanonical 𝔪 inv T
  | _, .refl, _ => trivial
  | _, .step T C _ _, h => by
      obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := h
      exact (⟨isCanonical_of_isEmptyTower 𝔪 inv T hT, Or.inl hC⟩ :
        IsCanonical 𝔪 inv T ∧ (C = ∅ ∨ C = maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp))

/-- An empty tower is a multiple test blow-up (of every marked ideal). -/
theorem isGeoTestTower_of_isEmptyTower (𝔪 : MarkedIdeal n X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsEmptyTower T → IsGeoTestTower 𝔪 T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, h => by
      obtain ⟨hT, hC⟩ : IsEmptyTower T ∧ C = ∅ := h
      subst hC
      exact (isGeoTestTower_step_iff 𝔪 T ∅ π hπ).mpr
        ⟨isGeoTestTower_of_isEmptyTower 𝔪 T hT, MarkedIdeal.isAdmissibleCentre_empty _⟩

end Empty

/-! ### The structure -/

variable (n) in
/-- **A resolution invariant in dimension `≤ k`** (`hir:centre-function`) with values in the linearly ordered `Λ`: a value
`inv 𝔪 T y ∈ Λ` for every marked ideal `𝔪` on every `X : CMfd n`, every tower `T` over `X` and every point `y` of its last
stage, such that for the marked ideals of `IsInvDomain k` and along their canonical segments `T` (`IsCanonical 𝔪 (inv 𝔪) T`:
every centre is empty or the maximum locus of the invariant of the preceding part on the cosupport):
1. (admissibility) on an open `W` of the last stage on which `inv ≤ λ` on the cosupport, the points of `W` in the cosupport
   with value `λ` form an admissible centre of `𝔪_T|_W`;
2. (semicontinuity) `inv 𝔪 T` is upper semicontinuous on the cosupport;
3. (decrease) blowing up the maximum locus `C ≠ ∅`, the value drops over `C` and is unchanged off it;
4. (empty steps) a blowup along an empty centre does not change the values;
4'. (empty prefixes) if all centres of `T₀` are empty, the invariant of `𝔪` along `T₀ T₁` is that of `𝔪_{T₀}` along `T₁`;
5. (open sets) restriction to an open `U ⊆ X` does not change the values;
6. (biholomorphisms) the values correspond along isomorphisms of towers over biholomorphisms (`IsTowerIso`);
7. (representatives) restricted-equivalent marked ideals have the same values;
8. (local finiteness) over a compact set, canonical segments have boundedly many nonempty centres meeting it.

Superseded on the route by `ResolutionInvariantSeq.ResolutionInvariant`, kept: see the module docstring. -/
structure ResolutionInvariant (k : ℕ) (Λ : Type v) [LinearOrder Λ] where
  /-- The invariant. -/
  inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ
  /-- (1) Admissibility of the level sets of the maximum, on open sets. -/
  admissible : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
    ∀ (W : Opens Y) (l : Λ), (∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, y ∈ W → inv 𝔪 T y ≤ l) →
      (pullback (Subtype.val : W → Y) (geoTransformAlong 𝔪 T)).IsAdmissibleCentre
        ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ inv 𝔪 T y = l})
  /-- (2) Upper semicontinuity on the cosupport, along canonical segments. -/
  usc : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
      IsInvUSCOn (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp
  /-- (3) Decrease under the blowup of the maximum locus. -/
  decrease : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsCanonical 𝔪 (inv 𝔪) T → C.Nonempty →
      C = maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp →
      ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
        (π z ∈ C → inv 𝔪 (.step T C π hπ) z < inv 𝔪 T (π z)) ∧
        (π z ∉ C → inv 𝔪 (.step T C π hπ) z = inv 𝔪 T (π z))
  /-- (4) Empty steps, after a canonical segment. -/
  emptyStep : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π), C = ∅ →
      IsCanonical 𝔪 (inv 𝔪) T → ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
        inv 𝔪 (.step T C π hπ) z = inv 𝔪 T (π z)
  /-- (4') Empty prefixes: re-basing a canonical segment after a part with only empty centres. -/
  emptyPrefix : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y), IsEmptyTower T₀ →
      IsCanonical 𝔪 (inv 𝔪) (T₀.append T₁) → ∀ z ∈ (geoTransformAlong 𝔪 (T₀.append T₁)).cosupp,
        inv 𝔪 (T₀.append T₁) z = inv (geoTransformAlong 𝔪 T₀) T₁ z
  /-- (5) Restriction to open sets, along canonical segments. -/
  restrictOpen : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ (U : Opens X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
    ∀ p : openPreimage T U, (p : Y) ∈ (geoTransformAlong 𝔪 T).cosupp →
      inv (pullback (Subtype.val : U → X) 𝔪) (restrict U T) p = inv 𝔪 T p
  /-- (6) Isomorphisms of towers over biholomorphisms, along canonical segments. -/
  towerIso : ∀ {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y')
    (T : BlowupTower X Y) (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y),
      IsTowerIso Φ T' T χ → IsCanonical 𝔪 (inv 𝔪) T → ∀ p : Y', χ p ∈ (geoTransformAlong 𝔪 T).cosupp →
        inv (pullback Φ 𝔪) T' p = inv 𝔪 T (χ p)
  /-- (7) Independence of the representative, along canonical segments. -/
  representative : ∀ {X : CMfd.{u} n} (𝔪 𝔫 : MarkedIdeal n X), IsInvDomain k 𝔪 → IsInvDomain k 𝔫 →
    RestrictEquiv 𝔪 𝔫 → ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
      ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, inv 𝔪 T y = inv 𝔫 T y
  /-- (8) Local finiteness of canonical segments. -/
  locallyFinite : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ K : Set X, IsCompact K →
    ∃ m : ℕ, ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T → countCentresMeeting K T ≤ m

/-! ### Dimension `0` -/

section DimZero

/-- **The base case of `hir:canonical-centres`**: in dimension `≤ 0` every constant function is a resolution invariant --
along every canonical segment (which has only empty centres and is a multiple test blow-up) the cosupport is empty, so
(2)--(7) hold (vacuously or by `rfl`), the level sets of (1) are empty, and (8) holds with the bound `0`. -/
def ResolutionInvariant.ofDimZero (Λ : Type v) [LinearOrder Λ] (l₀ : Λ) : ResolutionInvariant.{u, v} n 0 Λ where
  inv := fun {_} _ {_} _ _ => l₀
  admissible := by
    intro X 𝔪 h Y T hT W l _
    have hempty := cosupp_geoTransformAlong_eq_empty_of_dimLE_zero h T
      (countCentresMeeting_eq_zero_of_dimLE_zero h (fun {_} _ _ => l₀) ∅ T hT).1
    have hset : ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ l₀ = l}) = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun y hy => ?_
      have := hy.1
      rw [hempty] at this
      exact this
    rw [hset]
    exact MarkedIdeal.isAdmissibleCentre_empty _
  usc := by
    intro X 𝔪 h Y T hT
    rw [cosupp_geoTransformAlong_eq_empty_of_dimLE_zero h T
      (countCentresMeeting_eq_zero_of_dimLE_zero h (fun {_} _ _ => l₀) ∅ T hT).1]
    exact fun x hx => absurd hx (notMem_empty x)
  decrease := by
    intro X 𝔪 h Y Z T C π hπ hT hne hC
    exfalso
    have hempty := cosupp_geoTransformAlong_eq_empty_of_dimLE_zero h T
      (countCentresMeeting_eq_zero_of_dimLE_zero h (fun {_} _ _ => l₀) ∅ T hT).1
    obtain ⟨y, hy⟩ := hne
    rw [hC, hempty] at hy
    exact hy.1
  emptyStep := by
    intro X 𝔪 h Y Z T C π hπ _ hT z _
    rfl
  emptyPrefix := by
    intro X 𝔪 h Y₀ Y T₀ T₁ _ _ z _
    rfl
  restrictOpen := by
    intro X 𝔪 h U Y T hT p _
    rfl
  towerIso := by
    intro X X' Φ 𝔪 h Y' Y T' T χ hiso hT p _
    rfl
  representative := by
    intro X 𝔪 𝔫 h𝔪 h𝔫 hEq Y T hT y _
    rfl
  locallyFinite := by
    intro X 𝔪 h K _
    exact ⟨0, fun T hT => (countCentresMeeting_eq_zero_of_dimLE_zero h (fun {_} _ _ => l₀) K T hT).2.le⟩

end DimZero

/-! ### The driver -/

section Driver

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **The maximum locus is an admissible centre** along a canonical segment which is a multiple test blow-up
(property (1) on the whole last stage). -/
theorem isAdmissibleCentre_maxLocus (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔪 (R.inv 𝔪) T)
    (hT : IsGeoTestTower 𝔪 T) :
    (geoTransformAlong 𝔪 T).IsAdmissibleCentre (maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := by
  by_cases hne : (maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hadm := R.admissible 𝔪 h T hcan ⊤ (R.inv 𝔪 T y₀) (fun y hy _ => hy₀.2 y hy)
    rw [← maxLocus_eq_level hy₀] at hadm
    have hcoh := (MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT).isCoherent
    exact isAdmissibleCentre_of_pullback_val_top
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hcoh hg) hadm
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact MarkedIdeal.isAdmissibleCentre_empty _

/-- **Canonical segments are multiple test blow-ups.** -/
theorem isGeoTestTower_of_isCanonical (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (R.inv 𝔪) T →
      IsGeoTestTower 𝔪 T
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (R.inv 𝔪) T ∧
          (C = ∅ ∨ C = maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
      have hTt := isGeoTestTower_of_isCanonical R h T hT
      refine (isGeoTestTower_step_iff 𝔪 T C π hπ).mpr ⟨hTt, ?_⟩
      rcases hC with rfl | rfl
      · exact MarkedIdeal.isAdmissibleCentre_empty _
      · exact isAdmissibleCentre_maxLocus R h T hT hTt

/-- Along a canonical segment the transform stays in the domain. -/
theorem isInvDomain_of_isCanonical (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain k 𝔪) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hcan : IsCanonical 𝔪 (R.inv 𝔪) T) :
    IsInvDomain k (geoTransformAlong 𝔪 T) :=
  InvDomainTowerAlong.isInvDomain_geoTransformAlong h T (isGeoTestTower_of_isCanonical R h T hcan)

end Driver

/-! ### Canonical segments on open sets and along isomorphisms of towers -/

section Segments

variable {X X' : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- **The restriction of a canonical segment to an open set is a canonical segment** of the restricted marked ideal. -/
theorem isCanonical_restrict (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪)
    (U : Opens X) : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (R.inv 𝔪) T →
      IsCanonical (pullback (Subtype.val : U → X) 𝔪) (R.inv (pullback (Subtype.val : U → X) 𝔪)) (restrict U T)
  | _, .refl, _ => trivial
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔪 (R.inv 𝔪) T ∧
          (C = ∅ ∨ C = maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
      have ih := isCanonical_restrict R hdom U T hT
      have hTt := isGeoTestTower_of_isCanonical R hdom T hT
      show IsCanonical (pullback (Subtype.val : U → X) 𝔪) (R.inv (pullback (Subtype.val : U → X) 𝔪)) (restrict U T) ∧
        (((Subtype.val : openPreimage T U → _) ⁻¹' C) = ∅ ∨
          ((Subtype.val : openPreimage T U → _) ⁻¹' C) = maxLocus (R.inv (pullback (Subtype.val : U → X) 𝔪)
            (restrict U T)) (geoTransformAlong (pullback (Subtype.val : U → X) 𝔪) (restrict U T)).cosupp)
      refine ⟨ih, ?_⟩
      rcases hC with rfl | rfl
      · exact Or.inl (preimage_empty)
      · by_cases hne : ((Subtype.val : openPreimage T U → _) ⁻¹'
            maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp).Nonempty
        · right
          rw [cosupp_geoTransformAlong_restrict hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent
            U T hTt]
          exact (maxLocus_preimage _ (fun p hp => R.restrictOpen 𝔪 hdom U T hT p hp) hne).symm
        · exact Or.inl (not_nonempty_iff_eq_empty.mp hne)

/-- **Canonical segments correspond along isomorphisms of towers.** -/
theorem isCanonical_of_isTowerIso (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X}
    (hdom : IsInvDomain k 𝔪) (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y}
    {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y} (hiso : IsTowerIso Φ T' T χ) :
    IsCanonical 𝔪 (R.inv 𝔪) T → IsCanonical (pullback Φ 𝔪) (R.inv (pullback Φ 𝔪)) T' := by
  induction hiso with
  | refl => exact fun _ => trivial
  | @step Y' Y Z' Z T' T χ hiso C' π' hπ' C π hπ χ₁ hcomm hC ih =>
    intro hcan
    obtain ⟨hT, hCc⟩ : IsCanonical 𝔪 (R.inv 𝔪) T ∧
        (C = ∅ ∨ C = maxLocus (R.inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp) := hcan
    have hTt := isGeoTestTower_of_isCanonical R hdom T hT
    show IsCanonical (pullback Φ 𝔪) (R.inv (pullback Φ 𝔪)) T' ∧
      (C' = ∅ ∨ C' = maxLocus (R.inv (pullback Φ 𝔪) T') (geoTransformAlong (pullback Φ 𝔪) T').cosupp)
    refine ⟨ih hT, ?_⟩
    subst hC
    rcases hCc with rfl | rfl
    · exact Or.inl preimage_empty
    · right
      rw [IsTowerIso.cosupp_geoTransformAlong Φ hdom.isWellFormed.isClosedSubmanifold_N hdom.isWellFormed.isCoherent
        hiso hTt]
      exact (maxLocus_preimage_of_surjective χ.toEquiv.surjective
        (fun p hp => R.towerIso Φ 𝔪 hdom T' T χ hiso hT p hp)).symm

end Segments

/-! ### Re-basing along an empty prefix -/

section Rebase

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}

/-- Maximum loci of functions agreeing on the set agree. -/
theorem maxLocus_congr {Y : Type*} {f g : Y → Λ} {s : Set Y} (hfg : ∀ y ∈ s, f y = g y) :
    maxLocus f s = maxLocus g s := by
  ext y
  constructor
  · rintro ⟨hys, hy⟩
    exact ⟨hys, fun y' hy' => by rw [← hfg y' hy', ← hfg y hys]; exact hy y' hy'⟩
  · rintro ⟨hys, hy⟩
    exact ⟨hys, fun y' hy' => by rw [hfg y' hy', hfg y hys]; exact hy y' hy'⟩

/-- **Re-basing canonical segments**: after a prefix `T₀` with only empty centres, `T₀ T₁` is a canonical segment of `𝔪`
iff `T₁` is a canonical segment of `𝔪_{T₀}` (by (4'), the two invariants agree on the cosupports, so their maximum loci
agree). -/
theorem isCanonical_append_iff (R : ResolutionInvariant.{u, v} n k Λ) {𝔪 : MarkedIdeal n X} (hdom : IsInvDomain k 𝔪)
    {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (h₀ : IsEmptyTower T₀) :
    ∀ {Y : CMfd.{u} n} (T₁ : BlowupTower Y₀ Y),
      IsCanonical 𝔪 (R.inv 𝔪) (T₀.append T₁) ↔
        IsCanonical (geoTransformAlong 𝔪 T₀) (R.inv (geoTransformAlong 𝔪 T₀)) T₁
  | _, .refl => ⟨fun _ => trivial, fun _ => isCanonical_of_isEmptyTower 𝔪 (R.inv 𝔪) T₀ h₀⟩
  | _, .step T₁ C π hπ => by
      have ih := isCanonical_append_iff R hdom T₀ h₀ T₁
      have hloc : IsCanonical 𝔪 (R.inv 𝔪) (T₀.append T₁) →
          maxLocus (R.inv 𝔪 (T₀.append T₁)) (geoTransformAlong 𝔪 (T₀.append T₁)).cosupp =
            maxLocus (R.inv (geoTransformAlong 𝔪 T₀) T₁) (geoTransformAlong (geoTransformAlong 𝔪 T₀) T₁).cosupp := by
        intro hc
        rw [← geoTransformAlong_append 𝔪 T₀ T₁]
        exact maxLocus_congr fun z hz => R.emptyPrefix 𝔪 hdom T₀ T₁ h₀ hc z hz
      show (IsCanonical 𝔪 (R.inv 𝔪) (T₀.append T₁) ∧
          (C = ∅ ∨ C = maxLocus (R.inv 𝔪 (T₀.append T₁)) (geoTransformAlong 𝔪 (T₀.append T₁)).cosupp)) ↔
        (IsCanonical (geoTransformAlong 𝔪 T₀) (R.inv (geoTransformAlong 𝔪 T₀)) T₁ ∧
          (C = ∅ ∨ C = maxLocus (R.inv (geoTransformAlong 𝔪 T₀) T₁)
            (geoTransformAlong (geoTransformAlong 𝔪 T₀) T₁).cosupp))
      constructor
      · rintro ⟨hc, hC⟩
        exact ⟨ih.mp hc, hC.imp id fun h => h.trans (hloc hc)⟩
      · rintro ⟨hc', hC⟩
        have hc := ih.mpr hc'
        exact ⟨hc, hC.imp id fun h => h.trans (hloc hc).symm⟩

end Rebase

end

end Hironaka.ResolutionInvariantExt
