/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.GeneralAdmissible
import Hironaka.Invariant.NonmonomialOrderMonomialTransport
import Hironaka.Invariant.NonmonomialOrderTransport
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerIsomorphism
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.GeneralValue
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdealRestrictOpen
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxOrderValue
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.MonomialInvariantFunctorialAlong
import Hironaka.Invariant.MonomialStepAlong
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The general value at the points of order zero: re-basing, open sets, isomorphisms, representatives

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2 of Proposition `pr:resol` (Step 2b, the monomial case);
Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Step II.A.

General value `GeneralValue.genInv M 𝔪` (generic in the maximal-order value function `M`) is, at a point `y` of the
last stage of a tower `T` where the nonmonomial part of the transform has order `ν_T(y) = 0`, the pair `(0, inl
γ_T(y))` with `γ_T = MonomialStepAlong.towerInvAlong 𝔪 T` the monomial invariant of the transform
(`genInv_eq_towerInvAlong`). This module states, for `genInv M 𝔪` itself, the order-`0` halves of the properties
(4'), (5), (6), (7) of `hir:centre-function` (the remaining ones: (1)--(4) hold at every value, `GeneralAdmissible`,
`GeneralUSC`, `GeneralCanonicalTail`). Each is the conjunction of the same property for the order `ν`
(`NonmonomialOrderLocal`, `NonmonomialOrderTransport`) and for `γ` (`NonmonomialOrderMonomialTransport`,
`MonomialInvariantFunctorialAlong.towerInvAlong_restrict`); `M` plays no role at order `0`:

* **`genInv_append_of_nmOrd_eq_zero`** ((4'), for every prefix `P`, empty or not): `genInv M 𝔪 (P T₁) z = genInv M 𝔪_P T₁ z`;
* **`genInv_restrict_of_nmOrd_eq_zero`** ((5)): restriction to an open set `U ⊆ X`, along multiple test blow-ups;
* **`genInv_isTowerIso_of_nmOrd_eq_zero`** ((6)): isomorphisms of towers over biholomorphisms, along multiple test blow-ups;
* **`genInv_congr_of_nmOrd_eq_zero`** ((7)): restricted-equivalent marked ideals, along every tower;
* `emptyPrefix_field_of_nmOrd_eq_zero`, `restrictOpen_field_of_nmOrd_eq_zero`, `towerIso_field_of_nmOrd_eq_zero`:
  the same in the shapes of the fields of `ResolutionInvariantExt.ResolutionInvariant`, along canonical segments of
  `genInv M 𝔪` (multiple test blow-ups by `GeneralAdmissible.isGeoTestTower_of_isCanonical_genInv`), with the extra
  hypothesis `ν = 0` at the point, so that each field splits into the order-`0` half (here) and the positive-order
  half.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralValueOrderZero

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialInvariant Hironaka.MonomialStepAlong Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerIsomorphism Hironaka.MarkedIdealRestrictOpen Hironaka.MarkedIdealOperationsAlong.MarkedIdeal Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderTransport Hironaka.NonmonomialOrderMonomialTransport Hironaka.MaxOrderValue Hironaka.GeneralValue Hironaka.GeneralAdmissible
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionInvariantExt (IsEmptyTower)

noncomputable section

variable {n : ℕ}

/-! ### The value at the points of order zero -/

section Basic

variable {Λ : Type v} [LinearOrder Λ]
  (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)

/-- **At a point of order `0` the general value is `(0, inl γ_T)`**, `γ_T = towerInvAlong 𝔪 T` the monomial invariant of the
transform. -/
theorem genInv_eq_towerInvAlong {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y}
    (h0 : nmOrd (geoTransformAlong 𝔪 T) y = 0) :
    genInv M 𝔪 T y =
      toLex ((0 : ℕ), (toLex (Sum.inl (towerInvAlong 𝔪 T y)) : WithBot Val ⊕ₗ WithTop Λ)) :=
  genInv_of_nmOrd_eq_zero M 𝔪 T h0

/-- **Two points of order `0` with the same invariant `γ` have the same general value** (for any two marked ideals and
towers). -/
theorem genInv_eq_of_nmOrd_eq_zero {X X' Y Y' : CMfd.{u} n} {𝔪 : MarkedIdeal n X} {𝔫 : MarkedIdeal n X'}
    {T : BlowupTower X Y} {T' : BlowupTower X' Y'} {y : Y} {y' : Y'} (h0 : nmOrd (geoTransformAlong 𝔪 T) y = 0)
    (h0' : nmOrd (geoTransformAlong 𝔫 T') y' = 0) (hγ : towerInvAlong 𝔪 T y = towerInvAlong 𝔫 T' y') :
    genInv M 𝔪 T y = genInv M 𝔫 T' y' := by
  rw [genInv_eq_towerInvAlong M 𝔪 T h0, genInv_eq_towerInvAlong M 𝔫 T' h0', hγ]

end Basic

/-! ### (4') Re-basing, for every prefix -/

section Rebase

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]
  (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)

/-- **(4') at order `0`, for every prefix**: at a point `z` of order `0` of the last stage of `P T₁`, the general value of `𝔪`
along `P T₁` is that of `𝔪_P` along `T₁` -- both are `(0, inl γ)` of the same transform
(`BlowupTowerTransforms.geoTransformAlong_append`).  No emptiness of `P` and no canonicity are needed. -/
theorem genInv_append_of_nmOrd_eq_zero (𝔪 : MarkedIdeal n X) {Y₀ Y : CMfd.{u} n} (P : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) {z : Y} (h0 : nmOrd (geoTransformAlong 𝔪 (P.append T₁)) z = 0) :
    genInv M 𝔪 (P.append T₁) z = genInv M (geoTransformAlong 𝔪 P) T₁ z := by
  have h0' : nmOrd (geoTransformAlong (geoTransformAlong 𝔪 P) T₁) z = 0 := by
    rwa [← geoTransformAlong_append]
  refine genInv_eq_of_nmOrd_eq_zero M h0 h0' ?_
  rw [towerInvAlong_append]

/-- **(4') at order `0`, in the shape of the field `emptyPrefix`**. -/
theorem emptyPrefix_field_of_nmOrd_eq_zero (𝔪 : MarkedIdeal n X) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) (_h₀ : IsEmptyTower T₀) (_hcan : IsCanonical 𝔪 (genInv M 𝔪) (T₀.append T₁))
    (z : Y) (_hz : z ∈ (geoTransformAlong 𝔪 (T₀.append T₁)).cosupp)
    (h0 : nmOrd (geoTransformAlong 𝔪 (T₀.append T₁)) z = 0) :
    genInv M 𝔪 (T₀.append T₁) z = genInv M (geoTransformAlong 𝔪 T₀) T₁ z :=
  genInv_append_of_nmOrd_eq_zero M 𝔪 T₀ T₁ h0

end Rebase

/-! ### (5) Open sets, (6) isomorphisms of towers, (7) representatives -/

section Operations

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]
  (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)

/-- **(5) at order `0`**: for `𝔪` in the domain (`n > 0`), `U ⊆ X` open and `T` a multiple test blow-up of `𝔪`, at a point `p`
over `U` where the order is `0`, the general value of `𝔪|_U` along `T|_U` is that of `𝔪` along `T` -- the transform of `𝔪|_U`
along `T|_U` is the restriction of `𝔪_T` (`MarkedIdealRestrictOpen.geoTransformAlong_restrict`), which has the same order
(`NonmonomialOrderLocal.nmOrd_pullback_val`) and the same `γ` (`MonomialInvariantFunctorialAlong.towerInvAlong_restrict`). -/
theorem genInv_restrict_of_nmOrd_eq_zero (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (hT : IsGeoTestTower 𝔪 T) (p : openPreimage T U)
    (h0 : nmOrd (geoTransformAlong 𝔪 T) p = 0) :
    genInv M (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T) p = genInv M 𝔪 T p := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hν : nmOrd (geoTransformAlong (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T)) p =
      nmOrd (geoTransformAlong 𝔪 T) p := by
    rw [geoTransformAlong_restrict U h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent T hT]
    exact nmOrd_pullback_val hn hdomT.isWellFormed hdomT.isNonzeroAlongAt (openPreimage T U) p
  exact genInv_eq_of_nmOrd_eq_zero M (hν.trans h0) h0
    (MonomialInvariantFunctorialAlong.towerInvAlong_restrict 𝔪 h.isWellFormed.isClosedSubmanifold_N
      h.isWellFormed.isCoherent U T hT p)

/-- **(6) at order `0`**: for `𝔪` in the domain (`n > 0`), `T` a multiple test blow-up of `𝔪` and `χ : T' → T` an isomorphism
of towers over a biholomorphism `Φ : X' ≅ X`, at a point `p` with `ν(χ p) = 0` the general value of `Φ^*𝔪` along `T'` at `p` is
that of `𝔪` along `T` at `χ p` (`NonmonomialOrderLocal.nmOrd_geoTransformAlong_isTowerIso`,
`NonmonomialOrderMonomialTransport.towerInvAlong_isTowerIso`). -/
theorem genInv_isTowerIso_of_nmOrd_eq_zero (hn : 0 < n) {k : ℕ} {𝔪 : MarkedIdeal n X} (h : IsInvDomain k 𝔪)
    {X' : CMfd.{u} n} (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) {Y' Y : CMfd.{u} n}
    {T' : BlowupTower X' Y'} {T : BlowupTower X Y} {χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y}
    (hiso : IsTowerIso Φ T' T χ) (hT : IsGeoTestTower 𝔪 T) (p : Y') (h0 : nmOrd (geoTransformAlong 𝔪 T) (χ p) = 0) :
    genInv M (MarkedIdeal.pullback Φ 𝔪) T' p = genInv M 𝔪 T (χ p) :=
  genInv_eq_of_nmOrd_eq_zero M ((nmOrd_geoTransformAlong_isTowerIso hn Φ h hiso hT p).trans h0) h0
    (towerInvAlong_isTowerIso Φ h.isWellFormed.isClosedSubmanifold_N h.isWellFormed.isCoherent hiso hT p)

/-- **(7) at order `0`**: restricted-equivalent marked ideals (closed `N`, coherent ideals) have the same general value at the
points of order `0`, along every tower (`NonmonomialOrderTransport.nmOrd_geoTransformAlong_congr`,
`NonmonomialOrderMonomialTransport.towerInvAlong_congr`). -/
theorem genInv_congr_of_nmOrd_eq_zero {𝔪 𝔫 : MarkedIdeal n X} (hEq : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N)
    (h𝔪 : 𝔪.ideal.IsCoherent) (h𝔫 : 𝔫.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y}
    (h0 : nmOrd (geoTransformAlong 𝔪 T) y = 0) : genInv M 𝔪 T y = genInv M 𝔫 T y :=
  genInv_eq_of_nmOrd_eq_zero M h0 ((nmOrd_geoTransformAlong_congr hEq hN h𝔪 h𝔫 T y).symm.trans h0)
    (congrFun (towerInvAlong_congr hEq hN h𝔪 h𝔫 T) y)

end Operations

/-! ### The field shapes along canonical segments -/

section Fields

variable {k : ℕ} {Λ : Type v} [LinearOrder Λ]
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}

/-- **(5) at order `0`, in the shape of the field `restrictOpen`**: along canonical segments of the general value (`M` a value
function for the marked ideals of maximal order, `n > 0`). -/
theorem restrictOpen_field_of_nmOrd_eq_zero (hM : IsMaxOrderValue n k M) (hn : 0 < n) {X : CMfd.{u} n}
    (𝔪 : MarkedIdeal n X) (h : IsInvDomain k 𝔪) (U : Opens X) {Y : CMfd.{u} n} (T : BlowupTower X Y)
    (hcan : IsCanonical 𝔪 (genInv M 𝔪) T) (p : openPreimage T U)
    (_hp : (p : Y) ∈ (geoTransformAlong 𝔪 T).cosupp) (h0 : nmOrd (geoTransformAlong 𝔪 T) p = 0) :
    genInv M (MarkedIdeal.pullback (Subtype.val : U → X) 𝔪) (restrict U T) p = genInv M 𝔪 T p :=
  genInv_restrict_of_nmOrd_eq_zero M hn h U T (isGeoTestTower_of_isCanonical_genInv hM hn h T hcan) p h0

/-- **(6) at order `0`, in the shape of the field `towerIso`**: along canonical segments of the general value. -/
theorem towerIso_field_of_nmOrd_eq_zero (hM : IsMaxOrderValue n k M) (hn : 0 < n) {X X' : CMfd.{u} n}
    (Φ : X' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ X) (𝔪 : MarkedIdeal n X) (h : IsInvDomain k 𝔪)
    {Y' Y : CMfd.{u} n} (T' : BlowupTower X' Y') (T : BlowupTower X Y)
    (χ : Y' ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ Y) (hiso : IsTowerIso Φ T' T χ)
    (hcan : IsCanonical 𝔪 (genInv M 𝔪) T) (p : Y') (_hp : χ p ∈ (geoTransformAlong 𝔪 T).cosupp)
    (h0 : nmOrd (geoTransformAlong 𝔪 T) (χ p) = 0) :
    genInv M (MarkedIdeal.pullback Φ 𝔪) T' p = genInv M 𝔪 T (χ p) :=
  genInv_isTowerIso_of_nmOrd_eq_zero M hn h Φ hiso (isGeoTestTower_of_isCanonical_genInv hM hn h T hcan) p h0

end Fields

end

end Hironaka.GeneralValueOrderZero
