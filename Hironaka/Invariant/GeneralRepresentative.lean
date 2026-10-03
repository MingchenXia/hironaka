/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.GeneralValueOrderZero
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionRebase
import Hironaka.Invariant.ContactRepresentative
import Hironaka.Invariant.GeneralValue
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealEquivalence
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Invariant.NonmonomialOrderTransport
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneRegime
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The general value does not depend on the representative: property (7)

Source: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 2 (the invariant is assigned to
the marked ideal "up to equivalence"; the companion ideal only depends on the restriction of the ideal to `N`);
Bierstone--Milman 2008, Step II.

Let `𝔪 ≃ 𝔫` be restricted-equivalent marked ideals (closed `N`, coherent ideals). The general value
`GeneralValue.genInv M 𝔪` is built from three pieces of data along a tower `T`: the order `ν` of the nonmonomial
part, the run of a point in its regime `OrdRegime 𝔪 o`, and -- at positive order -- the companion ideal of the
transform at the start of the run, restricted to its mask `{ν ≤ o}`. All three agree for `𝔪` and `𝔫`
(`NonmonomialOrderTransport`: `ν`, the regime and its run, the mask; `CompanionRebase.companionOf_congr`:
restricted-equivalent marked ideals have EQUAL companion ideals, and from the first blowup on the transforms are
equal, `RestrictEquiv.geoTransformAlong_step_eq`). Hence the companion values, and the general values, are equal --
along every tower, at every point, for every value function `M` (at order `0` this is
`GeneralValueOrderZero.genInv_congr_of_nmOrd_eq_zero`).

## Main results

* `genLowerValue_eq_refl`, `genLowerValue_congr_of_eq`: the companion value at a split only depends on the transform at the
  head;
* `genLowerValue_refl_congr`, **`genLowerValue_congr`**: restricted-equivalent marked ideals have the same companion values;
* **`genInv_congr_of_pos`** (property (7) at positive order), **`genInv_congr`** (at every point, along every tower);
* **`representative_field`**: property (7) in the shape of the field `representative` of
  `ResolutionInvariantExt.ResolutionInvariant`.
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralRepresentative

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.CompanionRebase Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdealRestrictOpen Hironaka.MarkedIdealOperationsAlong.MarkedIdeal Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderTail Hironaka.NonmonomialOrderTransport Hironaka.MaxOrderValue Hironaka.GeneralValue
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)

noncomputable section

variable {n : ℕ} {Λ : Type v} [LinearOrder Λ]
  (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)

/-! ### The companion value only depends on the transform at the head -/

section Head

/-- **The companion value at the split `T₀ T₁` is that of the transform `𝔪_{T₀}` at the split `refl T₁`** (by definition). -/
theorem genLowerValue_eq_refl {X : CMfd.{u} n} (𝔪 : MarkedIdeal n X) (o : ℕ) {Y₀ Y : CMfd.{u} n}
    (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y : Y) :
    genLowerValue M 𝔪 o T₀ T₁ y = genLowerValue M (geoTransformAlong 𝔪 T₀) o .refl T₁ y :=
  rfl

/-- **Two splits with equal transforms at their heads give the same companion value.** -/
theorem genLowerValue_congr_of_eq {X X' : CMfd.{u} n} {𝔪 : MarkedIdeal n X} {𝔫 : MarkedIdeal n X'} (o : ℕ)
    {Y₀ Y : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {S₀ : BlowupTower X' Y₀}
    (h : geoTransformAlong 𝔪 T₀ = geoTransformAlong 𝔫 S₀) (T₁ : BlowupTower Y₀ Y) (y : Y) :
    genLowerValue M 𝔪 o T₀ T₁ y = genLowerValue M 𝔫 o S₀ T₁ y := by
  rw [genLowerValue_eq_refl M 𝔪, genLowerValue_eq_refl M 𝔫, h]

end Head

/-! ### Restricted-equivalent marked ideals -/

section Congr

variable {X : CMfd.{u} n} {𝔪 𝔫 : MarkedIdeal n X}

/-- **At the split `refl T₁`, restricted-equivalent marked ideals with the same mask have the same companion value**: their
restrictions to the (common) mask are restricted-equivalent, so their companion ideals are equal
(`CompanionRebase.companionOf_congr`). -/
theorem genLowerValue_refl_congr (hEq : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N) (h𝔪 : 𝔪.ideal.IsCoherent)
    (h𝔫 : 𝔫.ideal.IsCoherent) (o : ℕ) (hW : ordMask 𝔪 o = ordMask 𝔫 o) {Y : CMfd.{u} n} (T₁ : BlowupTower X Y)
    (y : Y) : genLowerValue M 𝔪 o .refl T₁ y = genLowerValue M 𝔫 o .refl T₁ y := by
  classical
  let F : Opens X → MarkedIdeal n X → WithTop Λ := fun W 𝔠 =>
    if h : T₁.proj y ∈ W then
      ((M (companionOf n (M := CMfd.of (n := n) W) (MarkedIdeal.pullback (Subtype.val : W → X) 𝔠) o)
        (restrict W T₁) (⟨y, h⟩ : openPreimage T₁ W) : Λ) : WithTop Λ)
    else ⊤
  show F (ordMask 𝔪 o) 𝔪 = F (ordMask 𝔫 o) 𝔫
  rw [← hW]
  have hNA : IsClosed (MarkedIdeal.pullback (Subtype.val : ordMask 𝔪 o → X) 𝔪).N :=
    hN.preimage continuous_subtype_val
  simp only [F]
  rw [companionOf_congr (ContactRepresentative.restrictEquiv_pullback_val (ordMask 𝔪 o) hEq h𝔪 h𝔫) hNA o]

/-- **Restricted-equivalent marked ideals have the same companion values at every split** (closed `N`, coherent ideals): at
the split `refl T₁` by `genLowerValue_refl_congr` (the masks agree, `NonmonomialOrderTransport.ordMask_geoTransformAlong_congr`);
after at least one blowup the transforms at the head are equal (`RestrictEquiv.geoTransformAlong_step_eq`). -/
theorem genLowerValue_congr (hEq : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N) (h𝔪 : 𝔪.ideal.IsCoherent)
    (h𝔫 : 𝔫.ideal.IsCoherent) (o : ℕ) :
    ∀ {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y) (y : Y),
      genLowerValue M 𝔪 o T₀ T₁ y = genLowerValue M 𝔫 o T₀ T₁ y
  | _, _, .refl, T₁, y =>
      genLowerValue_refl_congr M hEq hN h𝔪 h𝔫 o (ordMask_geoTransformAlong_congr hEq hN h𝔪 h𝔫 .refl o) T₁ y
  | _, _, .step T C π hπ, T₁, y =>
      genLowerValue_congr_of_eq M o
        (MarkedIdealEquivalence.MarkedIdeal.RestrictEquiv.geoTransformAlong_step_eq hEq hN h𝔪 h𝔫 T C π hπ) T₁ y

/-- **Property (7) of the general value at positive order**: restricted-equivalent marked ideals (closed `N`, coherent ideals)
have the same general value at every point of positive order, along every tower -- the order, the run in the regime and the
companion value agree. -/
theorem genInv_congr_of_pos (hEq : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N) (h𝔪 : 𝔪.ideal.IsCoherent)
    (h𝔫 : 𝔫.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y}
    (hpos : 0 < nmOrd (geoTransformAlong 𝔪 T) y) : genInv M 𝔪 T y = genInv M 𝔫 T y := by
  obtain ⟨o, ho⟩ : ∃ o, nmOrd (geoTransformAlong 𝔪 T) y = o := ⟨_, rfl⟩
  have hν := nmOrd_geoTransformAlong_congr hEq hN h𝔪 h𝔫 T y
  have ho0 : o ≠ 0 := by omega
  rw [genInv_of_nmOrd_ne_zero M 𝔪 T ho ho0, genInv_of_nmOrd_ne_zero M 𝔫 T (hν ▸ ho) ho0,
    regimeRun_ordRegime_congr hEq hN h𝔪 h𝔫 o T y, genLowerValue_congr M hEq hN h𝔪 h𝔫 o]

/-- **Property (7) of the general value**: restricted-equivalent marked ideals (closed `N`, coherent ideals) have the
same general value, at every point, along every tower (order `0`:
`GeneralValueOrderZero.genInv_congr_of_nmOrd_eq_zero`). -/
theorem genInv_congr (hEq : RestrictEquiv 𝔪 𝔫) (hN : IsClosed 𝔪.N) (h𝔪 : 𝔪.ideal.IsCoherent)
    (h𝔫 : 𝔫.ideal.IsCoherent) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    genInv M 𝔪 T y = genInv M 𝔫 T y := by
  rcases Nat.eq_zero_or_pos (nmOrd (geoTransformAlong 𝔪 T) y) with h0 | hpos
  · exact GeneralValueOrderZero.genInv_congr_of_nmOrd_eq_zero M hEq hN h𝔪 h𝔫 T h0
  · exact genInv_congr_of_pos M hEq hN h𝔪 h𝔫 T hpos

end Congr

/-! ### The field shape -/

section Field

variable {M} {k : ℕ}

/-- **Property (7) of the general value in the shape of the field `representative`** of
`ResolutionInvariantExt.ResolutionInvariant` (both marked ideals in the domain; the canonicity and the cosupport are not
needed). -/
theorem representative_field {X : CMfd.{u} n} (𝔪 𝔫 : MarkedIdeal n X) (h𝔪 : IsInvDomain k 𝔪) (h𝔫 : IsInvDomain k 𝔫)
    (hEq : RestrictEquiv 𝔪 𝔫) {Y : CMfd.{u} n} (T : BlowupTower X Y) (_hcan : IsCanonical 𝔪 (genInv M 𝔪) T) (y : Y)
    (_hy : y ∈ (geoTransformAlong 𝔪 T).cosupp) : genInv M 𝔪 T y = genInv M 𝔫 T y :=
  genInv_congr M hEq h𝔪.isWellFormed.isClosedSubmanifold_N.1 h𝔪.isWellFormed.isCoherent h𝔫.isWellFormed.isCoherent T y

end Field

end

end Hironaka.GeneralRepresentative
