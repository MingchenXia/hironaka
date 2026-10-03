/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.MaxOrderValue
import Hironaka.Invariant.NonmonomialOrderPhase
import Hironaka.Invariant.MonomialCaseAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupTowerSplit
import Hironaka.Blowup.BlowupTowerTransforms
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.CompanionRebase
import Hironaka.MarkedIdeal.HomogenizedIdealAlong
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.NonmonomialOrderCanonical
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.NonmonomialOrderRegime
import Hironaka.Invariant.NonmonomialOrderTail
import Hironaka.Invariant.ResolutionInvariantSpec
import Hironaka.Invariant.StepOneRegime
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The value function of the general step

Sources: Włodarczyk 2005 (arXiv `hiron.tex`), proof of Proposition `pr:resol`, Step 2 (Step 2a: the companion ideal
`O(𝓘, μ)` of maximal order, resolved by Step 1, "then we repeat the procedure"; Step 2b: the monomial case);
Bierstone--Milman 2008, Step II.

Let `𝔪` be a marked ideal and `T` a tower over its base. At a point `y` of the last stage write `ν(y) = o` for the
order of the nonmonomial part of the transform `𝔪_T` (`NonmonomialOrderLocal.nmOrd`). The value of the general step
is the lexicographic pair `(o, ·)` with

* for `o ≥ 1`: the value of a maximal-order value function `M` (`MaxOrderValue.IsMaxOrderValue`; in the induction,
  the masked Step 1 value) of the **companion ideal** `𝓞 = 𝓞(𝔪_{T₀}|_W, o)` formed at the stage `T₀` at which the
  images of `y` reached the order `o` -- the start of the run of `y` in the regime `OrdRegime 𝔪 o`, `T = T₀ T₁` --
  restricted to the open set `W = {ν ≤ o}` (`NonmonomialOrderTail.ordMask`), along the restricted tail `T₁|_W`, at
  `y` (`genLowerValue`; `∞` if the image of `y` is off `W`);
* for `o = 0`: the invariant `γ` of the monomial case (`MonomialCaseAlong.gammaAlong`) of `𝔪_T` at `y` -- near a
  point of order `0` the marked ideal is monomial (`NonmonomialOrderZero`).

The value is generic in `M`, so that it serves whichever form the maximal-order invariant takes once property (8) is
settled; it is ordered lexicographically, the second entry in `WithBot Val ⊕ₗ WithTop Λ` (the two cases never meet,
the first entry deciding). The data `T₀`, `W`, `𝓞` are those of
`NonmonomialOrderTail.isGeoTestTower_companion_tail_of_canonical` (the restricted tail is a multiple test blow-up of
the companion ideal along every canonical segment of a value function whose order dominates `ν`, which this one
does: `ordMonotone_genInv`).

## Main results

* `compAt`, `genLowerValue`, `genSecond`, `genInv`, `GenLowerData`: the definitions;
* `ordMonotone_genInv`, `genInv_lt_of_nmOrd_lt`, `genInv_of_nmOrd_eq_zero`, `genInv_of_nmOrd_ne_zero`,
  `genLowerValue_eq_of_mem`: basic facts;
* **the value under one blowup**, at a point whose image has positive order and keeps it: `genLowerValue_step_of_notMem`,
  `genLowerValue_step_lt_of_mem` (given lower data, from (3), (4) of `M` along the restricted tail), `genInv_step_eq_of_regime`,
  **`genInv_step_of_notMem`** (equal off the centre), **`genInv_step_lt_of_mem`** (smaller over the centre).
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.GeneralValue

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialPartAlong Hironaka.CompanionReductionAlong Hironaka.CompanionRebase Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.BlowupTowerSplit Hironaka.MarkedIdealRestrictOpen Hironaka.StepOneRegime Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderRegime Hironaka.NonmonomialOrderCanonical Hironaka.NonmonomialOrderTail Hironaka.HomogenizedIdealAlong Hironaka.MaxOrderValue Hironaka.MonomialCaseAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### The definitions -/

section Defs

variable {X : CMfd.{u} n}

/-- **The companion ideal formed at the last stage of `T₀`, on the mask `{ν ≤ o}`**:
`𝓞((𝔪_{T₀})|_{ordMask 𝔪_{T₀} o}, o)`. -/
abbrev compAt (𝔪 : MarkedIdeal n X) (o : ℕ) {Y₀ : CMfd.{u} n} (T₀ : BlowupTower X Y₀) :
    MarkedIdeal n (CMfd.of (n := n) (ordMask (geoTransformAlong 𝔪 T₀) o)) :=
  companionOf n (M := CMfd.of (n := n) (ordMask (geoTransformAlong 𝔪 T₀) o))
    (MarkedIdeal.pullback (Subtype.val : ordMask (geoTransformAlong 𝔪 T₀) o → Y₀) (geoTransformAlong 𝔪 T₀)) o

variable {Λ : Type v} [LinearOrder Λ]
  (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ)

open Classical in
/-- **The companion value**: the value of `M` for the companion ideal formed at the last stage of `T₀` on the mask `{ν ≤ o}`,
along the restricted tail `T₁`, at `y` (`∞` if the image of `y` is off the mask). -/
def genLowerValue (𝔪 : MarkedIdeal n X) (o : ℕ) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀) (T₁ : BlowupTower Y₀ Y)
    (y : Y) : WithTop Λ :=
  if h : T₁.proj y ∈ ordMask (geoTransformAlong 𝔪 T₀) o then
    ((M (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) T₁)
      (⟨y, h⟩ : openPreimage T₁ (ordMask (geoTransformAlong 𝔪 T₀) o)) : Λ) : WithTop Λ)
  else ⊤

/-- **The second entry of the general value**: `γ` of the transform at points of order `0`, the companion value along the part
of the tower since the start of the run of the point in its order otherwise. -/
def genSecond (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ :=
  if nmOrd (geoTransformAlong 𝔪 T) y = 0 then
    toLex (Sum.inl (gammaAlong n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal (geoTransformAlong 𝔪 T).E
      (geoTransformAlong 𝔪 T).d y))
  else
    toLex (Sum.inr (genLowerValue M 𝔪 (nmOrd (geoTransformAlong 𝔪 T) y)
      (head T (regimeRun (OrdRegime 𝔪 (nmOrd (geoTransformAlong 𝔪 T) y)) T y))
      (tail T (regimeRun (OrdRegime 𝔪 (nmOrd (geoTransformAlong 𝔪 T) y)) T y)) y))

/-- **The value function of the general step**: `(ν(y), second entry)`, lexicographically. -/
def genInv (𝔪 : MarkedIdeal n X) {Y : CMfd.{u} n} (T : BlowupTower X Y) (y : Y) :
    ℕ ×ₗ (WithBot MonomialInvariant.Val ⊕ₗ WithTop Λ) :=
  toLex (nmOrd (geoTransformAlong 𝔪 T) y, genSecond M 𝔪 T y)

/-- **Lower data of the general value** at the split `T₀ T₁`: the image of `y` lies in the mask, the companion ideal formed
there lies in the domain and is of maximal order, the restricted tail is one of its canonical segments for `M`, and `y` lies in
the cosupport of its transform. -/
def GenLowerData (k : ℕ) (𝔪 : MarkedIdeal n X) (o : ℕ) {Y₀ Y : CMfd.{u} n} (T₀ : BlowupTower X Y₀)
    (T₁ : BlowupTower Y₀ Y) (y : Y) : Prop :=
  ∃ h : T₁.proj y ∈ ordMask (geoTransformAlong 𝔪 T₀) o,
    IsInvDomain k (compAt 𝔪 o T₀) ∧
    IsMaximalOrderAlong (compAt 𝔪 o T₀).N (compAt 𝔪 o T₀).ideal (compAt 𝔪 o T₀).d ∧
    IsCanonical (compAt 𝔪 o T₀) (M (compAt 𝔪 o T₀)) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) T₁) ∧
    (⟨y, h⟩ : openPreimage T₁ (ordMask (geoTransformAlong 𝔪 T₀) o)) ∈
      (geoTransformAlong (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) T₁)).cosupp

end Defs

/-! ### Basic facts -/

section Basic

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]
  (M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) (𝔪 : MarkedIdeal n X)

/-- **The general value dominates the order of the nonmonomial part** (the hypothesis `OrdMonotone` of
`NonmonomialOrder*` modules). -/
theorem ordMonotone_genInv : OrdMonotone 𝔪 (genInv M 𝔪) :=
  ordMonotone_toLex 𝔪 (genSecond M 𝔪)

/-- A point of smaller order has a smaller value. -/
theorem genInv_lt_of_nmOrd_lt {Y Z : CMfd.{u} n} {T : BlowupTower X Y} {T' : BlowupTower X Z} {y : Y} {z : Z}
    (h : nmOrd (geoTransformAlong 𝔪 T') z < nmOrd (geoTransformAlong 𝔪 T) y) : genInv M 𝔪 T' z < genInv M 𝔪 T y := by
  rw [genInv, genInv, Prod.Lex.toLex_lt_toLex]
  exact Or.inl h

/-- At a point of order `0` the value is `(0, γ)`. -/
theorem genInv_of_nmOrd_eq_zero {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y}
    (h : nmOrd (geoTransformAlong 𝔪 T) y = 0) :
    genInv M 𝔪 T y = toLex (0, toLex (Sum.inl (gammaAlong n (geoTransformAlong 𝔪 T).N (geoTransformAlong 𝔪 T).ideal
      (geoTransformAlong 𝔪 T).E (geoTransformAlong 𝔪 T).d y))) := by
  rw [genInv, genSecond, if_pos h, h]

/-- At a point of order `o ≠ 0` the value is `(o, companion value)`. -/
theorem genInv_of_nmOrd_ne_zero {Y : CMfd.{u} n} (T : BlowupTower X Y) {y : Y} {o : ℕ}
    (h : nmOrd (geoTransformAlong 𝔪 T) y = o) (ho : o ≠ 0) :
    genInv M 𝔪 T y = toLex (o, toLex (Sum.inr (genLowerValue M 𝔪 o (head T (regimeRun (OrdRegime 𝔪 o) T y))
      (tail T (regimeRun (OrdRegime 𝔪 o) T y)) y))) := by
  subst h
  rw [genInv, genSecond, if_neg ho]

/-- When the image of `y` lies in the mask, the companion value is the value of `M` along the restricted tail. -/
theorem genLowerValue_eq_of_mem {o : ℕ} {Y₀ Y : CMfd.{u} n} {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y} {y : Y}
    (h : T₁.proj y ∈ ordMask (geoTransformAlong 𝔪 T₀) o) :
    genLowerValue M 𝔪 o T₀ T₁ y = ((M (compAt 𝔪 o T₀) (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) T₁)
      (⟨y, h⟩ : openPreimage T₁ (ordMask (geoTransformAlong 𝔪 T₀) o)) : Λ) : WithTop Λ) := by
  classical
  rw [genLowerValue, dif_pos h]

end Basic

/-! ### The general value under one blowup, at points of positive order keeping their order -/

section Step

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {k : ℕ}
  {M : ∀ {X : CMfd.{u} n}, MarkedIdeal n X → ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ} (𝔪 : MarkedIdeal n X)

/-- **Off the centre of a blowup appended to the tail, the companion value does not change** (given lower data; (3) and (4)
of `M` along the restricted tail). -/
theorem genLowerValue_step_of_notMem (hM : IsMaxOrderValue n k M) {o : ℕ} {Y₀ Y Z : CMfd.{u} n}
    {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y} {C : Set Y} {π : Z → Y} {hπ : IsBlowupAlong n C π} {z : Z}
    (hd : GenLowerData M k 𝔪 o T₀ (.step T₁ C π hπ) z) (hzC : π z ∉ C) :
    genLowerValue M 𝔪 o T₀ (.step T₁ C π hπ) z = genLowerValue M 𝔪 o T₀ T₁ (π z) := by
  obtain ⟨h, hdom, hmax, hcan, hcos⟩ := hd
  have h' : T₁.proj (π z) ∈ ordMask (geoTransformAlong 𝔪 T₀) o := h
  rw [genLowerValue_eq_of_mem M 𝔪 h, genLowerValue_eq_of_mem M 𝔪 h']
  congr 1
  exact hM.step_of_notMem hdom hmax (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) T₁) _ _ _ hcan hcos hzC

/-- **Over the centre of a blowup appended to the tail, the companion value drops** (given lower data; (3) of `M`). -/
theorem genLowerValue_step_lt_of_mem (hM : IsMaxOrderValue n k M) {o : ℕ} {Y₀ Y Z : CMfd.{u} n}
    {T₀ : BlowupTower X Y₀} {T₁ : BlowupTower Y₀ Y} {C : Set Y} {π : Z → Y} {hπ : IsBlowupAlong n C π} {z : Z}
    (hd : GenLowerData M k 𝔪 o T₀ (.step T₁ C π hπ) z) (hzC : π z ∈ C) :
    genLowerValue M 𝔪 o T₀ (.step T₁ C π hπ) z < genLowerValue M 𝔪 o T₀ T₁ (π z) := by
  obtain ⟨h, hdom, hmax, hcan, hcos⟩ := hd
  have h' : T₁.proj (π z) ∈ ordMask (geoTransformAlong 𝔪 T₀) o := h
  rw [genLowerValue_eq_of_mem M 𝔪 h, genLowerValue_eq_of_mem M 𝔪 h', WithTop.coe_lt_coe]
  exact hM.step_lt_of_mem hdom hmax (restrict (ordMask (geoTransformAlong 𝔪 T₀) o) T₁) _ _ _ hcan hcos hzC

variable (M) in
/-- **The value after a blowup at a point of order `o ≠ 0` whose image is in the regime of order `o`** is computed from the
same stage, along the tail extended by the blowup. -/
theorem genInv_step_eq_of_regime {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) {z : Z} {o : ℕ} (hz : nmOrd (geoTransformAlong 𝔪 (.step T C π hπ)) z = o) (ho : o ≠ 0)
    (hreg : OrdRegime 𝔪 o T (π z)) :
    genInv M 𝔪 (.step T C π hπ) z = toLex (o, toLex (Sum.inr (genLowerValue M 𝔪 o
      (head T (regimeRun (OrdRegime 𝔪 o) T (π z)))
      (.step (tail T (regimeRun (OrdRegime 𝔪 o) T (π z))) C π hπ) z))) := by
  rw [genInv_of_nmOrd_ne_zero M 𝔪 _ hz ho, regimeRun_step_of _ T C π hπ hreg]
  rfl

/-- **Properties (3) "equal off the centre" and (4) of the general value, at a point of positive order**: along a multiple
test blow-up `T` of `𝔪` (in the domain, `0 < n`) followed by a test blowup along `C`, at a point `z` of the new cosupport with
`π z ∉ C` and `ν(π z) = o ≠ 0`, the value at `z` is that at `π z`, given lower data of `z` at the split of `T` at the start of
the run of `π z` followed by the blowup. -/
theorem genInv_step_of_notMem (hM : IsMaxOrderValue n k M) (hn : 0 < n) {k' : ℕ} (h : IsInvDomain k' 𝔪)
    {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y) (hπ : IsBlowupAlong n C π)
    (hT : IsGeoTestTower 𝔪 (.step T C π hπ)) {z : Z} (hz : z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp)
    (hzC : π z ∉ C) {o : ℕ} (ho : o ≠ 0) (hzo : nmOrd (geoTransformAlong 𝔪 T) (π z) = o)
    (hd : GenLowerData M k 𝔪 o (head T (regimeRun (OrdRegime 𝔪 o) T (π z)))
      (.step (tail T (regimeRun (OrdRegime 𝔪 o) T (π z))) C π hπ) z) :
    genInv M 𝔪 (.step T C π hπ) z = genInv M 𝔪 T (π z) := by
  have hreg : OrdRegime 𝔪 o (.step T C π hπ) z := ⟨hz, by
    obtain ⟨hTT, hC⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
    have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hTT
    show nmOrd ((geoTransformAlong 𝔪 T).geoTransform C π) z = o
    rw [nmOrd_geoTransform_of_notMem hn hdomT hC hπ hzC, hzo]⟩
  have hregT : OrdRegime 𝔪 o T (π z) := (ordRegime_step_iff_of_notMem hn h o T C π hπ hT hzC).mp hreg
  rw [genInv_step_eq_of_regime M 𝔪 T C π hπ hreg.2 ho hregT, genInv_of_nmOrd_ne_zero M 𝔪 T hzo ho,
    genLowerValue_step_of_notMem 𝔪 hM hd hzC]

/-- **Property (3) of the general value, drop over the centre, at a point keeping its positive order** (given lower data). -/
theorem genInv_step_lt_of_mem (hM : IsMaxOrderValue n k M) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y)
    (π : Z → Y) (hπ : IsBlowupAlong n C π) {z : Z} (hzC : π z ∈ C) {o : ℕ} (ho : o ≠ 0)
    (hz : nmOrd (geoTransformAlong 𝔪 (.step T C π hπ)) z = o) (hregT : OrdRegime 𝔪 o T (π z))
    (hd : GenLowerData M k 𝔪 o (head T (regimeRun (OrdRegime 𝔪 o) T (π z)))
      (.step (tail T (regimeRun (OrdRegime 𝔪 o) T (π z))) C π hπ) z) :
    genInv M 𝔪 (.step T C π hπ) z < genInv M 𝔪 T (π z) := by
  rw [genInv_step_eq_of_regime M 𝔪 T C π hπ hz ho hregT, genInv_of_nmOrd_ne_zero M 𝔪 T hregT.2 ho,
    Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨rfl, ?_⟩
  exact Sum.Lex.inr_lt_inr_iff.mpr (genLowerValue_step_lt_of_mem 𝔪 hM hd hzC)

end Step

end

end Hironaka.GeneralValue
