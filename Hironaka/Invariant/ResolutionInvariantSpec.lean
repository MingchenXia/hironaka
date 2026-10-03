/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Invariant.ResolutionInvariantOrder
import Hironaka.Invariant.ResolutionDriver
import Hironaka.MarkedIdeal.TransformOffCentre
import Hironaka.MarkedIdeal.MarkedIdealOpenBiholomorphism
import Hironaka.Analytic.PositiveDimensionalComponent
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowers
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Resolution invariants and canonical segments

Sources: Bierstone--Milman 2008 §§4--6 (the invariant `inv` with values in a totally ordered set, its
semicontinuity, its decrease and its functoriality); Włodarczyk 2005, Proposition `pr:resol` and §2.4 (resolutions
commuting with étale morphisms, i.e. with open restriction and biholomorphisms, and *extensions* by isomorphisms --
here blowups along the empty set).

The structure and `ofDimZero` lie outside the constant cone of the main theorem; the definitions `DimLE`,
`IsInvDomain`, `IsCanonical`, `countCentresMeeting` and the dimension-zero lemmas of this module lie inside it.

## Definitions

* `DimLE n N k`: `N` is regular of dimension `≤ k` at each of its points.
* `IsInvDomain k 𝔪`: the marked ideals an invariant in dimension `≤ k` is defined on -- well formed, `dim N ≤ k`,
  `d ≥ 1`, `𝔞|_N` vanishing identically near no point of `N`.
* `IsCanonical 𝔪 inv T`: every centre of `T` is empty or the maximum locus of `inv` of the preceding part on the cosupport
  of the transform (a *canonical segment*; empty centres are Włodarczyk's extensions by isomorphisms).
* `countCentresMeeting K T`: the number of nonempty centres of `T` meeting the preimage of `K`.
* `ResolutionInvariant n k Λ`: a function `inv 𝔪 T: X_T → Λ` (`Λ` linearly ordered) with the eight properties of
  `hir:centre-function`, required for the marked ideals of `IsInvDomain k` along their multiple test blow-ups: (1)
  admissibility of the level sets of the maximum on open sets, (2) upper semicontinuity on the cosupport, (3)
  decrease under the blowup of the maximum locus, (4) invariance under empty steps, (5) under restriction to open
  sets, (6) under isomorphisms of towers over biholomorphisms (`BlowupTowerIsomorphism.IsTowerIso`), (7)
  independence of the representative (`MarkedIdealOperationsAlong.MarkedIdeal.RestrictEquiv`), (8) local finiteness
  of canonical segments.

## Main results

* `cosupp_eq_empty_of_dimLE_zero`, `cosupp_geoTransformAlong_eq_empty_of_dimLE_zero`: in dimension `0` the cosupport is
  empty, and stays empty along every multiple test blow-up;
* `ResolutionInvariant.ofDimZero`: **the base case of `hir:canonical-centres`** -- every constant function is a
  resolution invariant in dimension `≤ 0`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.ResolutionInvariantSpec

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.DivisorExponentAlong Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.MarkedIdealBiholomorphism.MarkedIdeal Hironaka.MarkedIdealOperationsAlong.MarkedIdeal Hironaka.BlowupTowerIsomorphism Hironaka.ResolutionInvariantOrder

noncomputable section

variable {n : ℕ}

/-! ### The domain of an invariant in dimension `≤ k` -/

section Domain

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

variable (n) in
/-- **`N` has dimension at most `k`**: it is regular of some dimension `≤ k` at each of its points. -/
def DimLE (N : Set M) (k : ℕ) : Prop :=
  ∀ x ∈ N, ∃ j ≤ k, RegularAtDim (n := n) N x j

/-- **The marked ideals of the domain of a resolution invariant in dimension `≤ k`** (`hir:centre-function`): well
formed, `dim N ≤ k`, `d ≥ 1`, and `𝔞|_N` vanishing identically near no point of `N` (equivalently, on no nonempty open
subset of `N`). -/
structure IsInvDomain (k : ℕ) (𝔪 : MarkedIdeal n M) : Prop where
  isWellFormed : 𝔪.IsWellFormed
  dimLE : DimLE n 𝔪.N k
  one_le_d : 1 ≤ 𝔪.d
  isNonzeroAlongAt : ∀ y ∈ 𝔪.N, IsNonzeroAlongAt 𝔪.N 𝔪.ideal y

/-- **In dimension `0` the cosupport is empty**: a point of `N` is isolated in `N`, so a germ of `𝔞` not vanishing
identically on `N` near it does not vanish at it, and its order along `N` is `0 < d`. -/
theorem cosupp_eq_empty_of_dimLE_zero {𝔪 : MarkedIdeal n M} (h : IsInvDomain 0 𝔪) : 𝔪.cosupp = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  have hxN : x ∈ 𝔪.N := hx.1
  obtain ⟨j, hj, hreg⟩ := h.dimLE x hxN
  obtain rfl : j = 0 := Nat.le_zero.mp hj
  obtain ⟨O, hO, hxO, hsub⟩ :=
    PositiveDimensionalComponent.exists_isOpen_inter_subset_singleton_of_regularAtDim_zero hreg
  obtain ⟨g, hg, hfreq⟩ := h.isNonzeroAlongAt x hxN
  have hgx : g x ≠ 0 := by
    obtain ⟨y, ⟨hyN, hyg⟩, hyO⟩ := (hfreq.and_eventually (hO.mem_nhds hxO)).exists
    have hyx : y = x := hsub ⟨hyN, hyO⟩
    rw [hyx] at hyg
    exact hyg
  have hghol : HolomorphicAt n g x :=
    RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem h.isWellFormed.isCoherent hg
  have h1 : VanishesToOrderOn n 𝔪.N x 1 g := (hx.2 g hg).mono h.one_le_d
  exact hgx ((vanishesToOrderOn_one_iff hxN hghol).mp h1)

end Domain

/-! ### Canonical segments and the count of centres -/

section Segments

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- **Canonical segments** (`hir:centre-function`): every centre is empty or the maximum locus of `inv` of the preceding
part of the tower on the cosupport of the transform. -/
def IsCanonical (𝔪 : MarkedIdeal n X) (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) :
    ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Prop
  | _, .refl => True
  | _, .step T C _ _ =>
    IsCanonical 𝔪 inv T ∧ (C = ∅ ∨ C = ResolutionDriver.maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp)

open Classical in
/-- **The number of nonempty centres of a tower meeting the preimage of `K`.** -/
def countCentresMeeting (K : Set X) : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → ℕ
  | _, .refl => 0
  | _, .step T C _ _ => countCentresMeeting K T + if (C ∩ T.proj ⁻¹' K).Nonempty then 1 else 0

end Segments

/-! ### Resolution invariants -/

variable (n) in
/-- **A resolution invariant in dimension `≤ k`** (`hir:centre-function`) with values in the linearly ordered `Λ`: a value
`inv 𝔪 T y ∈ Λ` for every marked ideal `𝔪` on every `X : CMfd n`, every tower `T` over `X` and every point `y` of its last
stage, such that for the marked ideals of `IsInvDomain k`:
1. (admissibility) along a canonical segment `T`, on an open `W` of the last stage on which `inv ≤ λ` on the cosupport,
   the points of `W` in the cosupport with value `λ` form an admissible centre of `𝔪_T|_W`;
2. (semicontinuity) `inv 𝔪 T` is upper semicontinuous on the cosupport along every multiple test blow-up;
3. (decrease) blowing up the maximum locus `C ≠ ∅` after a canonical segment, the value drops over `C` and is unchanged
   off it;
4. (empty steps) a blowup along `∅` does not change the values;
5. (open sets) restriction to an open `U ⊆ X` does not change the values;
6. (biholomorphisms) the values correspond along isomorphisms of towers over biholomorphisms (`IsTowerIso`; the transport
   of `hir:tower-transport` is one);
7. (representatives) restricted-equivalent marked ideals have the same values;
8. (local finiteness) over a compact set, canonical segments have boundedly many nonempty centres meeting it.

Superseded, kept: see the module docstring (the route uses `ResolutionInvariantSeq.ResolutionInvariant`). -/
structure ResolutionInvariant (k : ℕ) (Λ : Type v) [LinearOrder Λ] where
  /-- The invariant. -/
  inv : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ
  /-- (1) Admissibility of the level sets of the maximum, on open sets. -/
  admissible : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T →
    ∀ (W : Opens Y) (l : Λ), (∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, y ∈ W → inv 𝔪 T y ≤ l) →
      (pullback (Subtype.val : W → Y) (geoTransformAlong 𝔪 T)).IsAdmissibleCentre
        ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ inv 𝔪 T y = l})
  /-- (2) Upper semicontinuity on the cosupport. -/
  usc : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
      IsInvUSCOn (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp
  /-- (3) Decrease under the blowup of the maximum locus. -/
  decrease : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π),
      IsCanonical 𝔪 (inv 𝔪) T → C.Nonempty →
      C = ResolutionDriver.maxLocus (inv 𝔪 T) (geoTransformAlong 𝔪 T).cosupp →
      ∀ z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp,
        (π z ∈ C → inv 𝔪 (.step T C π hπ) z < inv 𝔪 T (π z)) ∧
        (π z ∉ C → inv 𝔪 (.step T C π hπ) z = inv 𝔪 T (π z))
  /-- (4) Empty steps. -/
  emptyStep : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 →
    ∀ {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (π : Z → Y) (hπ : IsBlowupAlong n (∅ : Set Y) π),
      IsGeoTestTower 𝔪 T → ∀ z ∈ (geoTransformAlong 𝔪 (.step T ∅ π hπ)).cosupp,
        inv 𝔪 (.step T ∅ π hπ) z = inv 𝔪 T (π z)
  /-- (5) Restriction to open sets. -/
  restrictOpen : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ (U : Opens X)
    {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
    ∀ p : openPreimage T U, (p : Y) ∈ (geoTransformAlong 𝔪 T).cosupp →
      inv (pullback (Subtype.val : U → X) 𝔪) (restrict U T) p = inv 𝔪 T p
  /-- (6) Isomorphisms of towers over biholomorphisms. -/
  towerIso : ∀ {X X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X)
    (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y')
    (T : BlowupTower X Y) (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y),
      IsTowerIso Φ T' T χ → IsGeoTestTower 𝔪 T → ∀ p : Y', χ p ∈ (geoTransformAlong 𝔪 T).cosupp →
        inv (pullback Φ 𝔪) T' p = inv 𝔪 T (χ p)
  /-- (7) Independence of the representative. -/
  representative : ∀ {X : CMfd.{u} n} (𝔪 𝔫 : MarkedIdeal n X), IsInvDomain k 𝔪 → IsInvDomain k 𝔫 →
    RestrictEquiv 𝔪 𝔫 → ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
      ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, inv 𝔪 T y = inv 𝔫 T y
  /-- (8) Local finiteness of canonical segments. -/
  locallyFinite : ∀ {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X), IsInvDomain k 𝔪 → ∀ K : Set X, IsCompact K →
    ∃ m : ℕ, ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 (inv 𝔪) T → countCentresMeeting K T ≤ m

/-! ### Dimension `0` -/

section DimZero

variable {X : CMfd.{u} n}

/-- **In dimension `0` the cosupport stays empty along every multiple test blow-up**: the centres lie in the (empty)
cosupport, and a blowup along `∅` does not create cosupport (`TransformOffCentre.mem_cosupp_geoTransform_iff`). -/
theorem cosupp_geoTransformAlong_eq_empty_of_dimLE_zero {𝔪 : MarkedIdeal n X} (h : IsInvDomain 0 𝔪) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → (geoTransformAlong 𝔪 T).cosupp = ∅
  | _, .refl, _ => cosupp_eq_empty_of_dimLE_zero h
  | _, .step T C π hπ, hT => by
      obtain ⟨hT', hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
      have hempty := cosupp_geoTransformAlong_eq_empty_of_dimLE_zero h T hT'
      have hwf := MarkedIdealOpenBiholomorphism.isWellFormed_geoTransformAlong h.isWellFormed T hT'
      have hC0 : C = ∅ := eq_empty_iff_forall_notMem.mpr fun x hx => by
        have := hC.2.1 hx
        rw [hempty] at this
        exact this
      refine eq_empty_iff_forall_notMem.mpr fun z hz => ?_
      rw [geoTransformAlong_step] at hz
      have hzC : π z ∉ C := by rw [hC0]; exact notMem_empty _
      have h1 := (TransformOffCentre.mem_cosupp_geoTransform_iff _ hwf.isClosedSubmanifold_N.1
        (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem hwf.isCoherent hg)
        hπ hzC).mp hz
      rw [hempty] at h1
      exact h1

/-- **The empty set is an admissible centre** (of every marked ideal). -/
theorem isAdmissibleCentre_empty {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
    (𝔪 : MarkedIdeal n M) : 𝔪.IsAdmissibleCentre ∅ :=
  ⟨⟨isClosed_empty, fun _ hx => absurd hx (notMem_empty _)⟩, empty_subset _, fun _ hx => absurd hx (notMem_empty _)⟩

/-- Canonical segments of a marked ideal of dimension `0` have only empty centres. -/
theorem countCentresMeeting_eq_zero_of_dimLE_zero {Λ : Type v} [LinearOrder Λ] {𝔪 : MarkedIdeal n X}
    (h : IsInvDomain 0 𝔪) (inv : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) (K : Set X) :
    ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsCanonical 𝔪 inv T →
      IsGeoTestTower 𝔪 T ∧ countCentresMeeting K T = 0
  | _, .refl, _ => ⟨trivial, rfl⟩
  | _, .step T C π hπ, hcan => by
      obtain ⟨hT, hC⟩ : IsCanonical 𝔪 inv T ∧
          (C = ∅ ∨ C = ResolutionDriver.maxLocus (inv T) (geoTransformAlong 𝔪 T).cosupp) := hcan
      obtain ⟨hTt, hcount⟩ := countCentresMeeting_eq_zero_of_dimLE_zero h inv K T hT
      have hempty := cosupp_geoTransformAlong_eq_empty_of_dimLE_zero h T hTt
      have hC0 : C = ∅ := by
        rcases hC with hC | hC
        · exact hC
        · rw [hC, hempty]
          exact eq_empty_iff_forall_notMem.mpr fun y hy => hy.1
      subst hC0
      refine ⟨(isGeoTestTower_step_iff 𝔪 T ∅ π hπ).mpr ⟨hTt, isAdmissibleCentre_empty _⟩, ?_⟩
      simp [countCentresMeeting, hcount]

end DimZero

end

end Hironaka.ResolutionInvariantSpec
