/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.NonmonomialOrderMonomial
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Blowup.BlowupTowers
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.Invariant.InvDomainTowerAlong
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.MaxLocusLocal
import Hironaka.Invariant.MonomialCaseAlong
import Hironaka.Invariant.MonomialInvariant
import Hironaka.Invariant.MonomialStepAlong
import Hironaka.Invariant.NonmonomialOrderCanonical
import Hironaka.Invariant.NonmonomialOrderLocal
import Hironaka.Invariant.ResolutionDriver
import Hironaka.Invariant.ResolutionInvariantExt
import Hironaka.Invariant.ResolutionInvariantSpec
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The monomial phase of the general step along canonical segments

Sources: Włodarczyk 2005 (`wlodarczyk05-hironaka`), Step 2 of Proposition `pr:resol` (Step 2b, the monomial case,
where the nonmonomial part is trivial); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), Step II.A.

The value `f` of the general step has as first entry the order `ν` of the nonmonomial part (`OrdMonotone 𝔪 f`,
`NonmonomialOrderCanonical`), and at the cosupport points of order `0` it is a fixed strictly monotone function `ψ` of the
monomial invariant `γ_T = MonomialStepAlong.towerInvAlong 𝔪 T` of the current transform (`OrdZeroValue 𝔪 f ψ`; for the value
`toLex (ν, ·)` with second entry `toLex (Sum.inl γ)` at order `0`, `ψ = fun w => toLex (0, toLex (Sum.inl w))`,
`ordZeroValue_toLex`, `strictMono_toLex_zero_inl`).  For every such `f`, with `𝔪` in the domain and `n > 0`, this module proves the case `o = 0`
of the properties of `hir:centre-function` that the general step needs, from the one-stage facts of
`NonmonomialOrderMonomial`:

* `nmOrd_eq_zero_of_mem_maxLocus`, **`maxLocus_eq_maxLocus_towerInvAlong`**: a point of order `0` on the maximum locus of
  `f` forces order `0` on the whole cosupport, and then the maximum locus of `f` is that of `γ_T`;
* **`isAdmissibleCentre_level_of_nmOrd_eq_zero`** (property (1) at `o = 0`, the field shape): a level set of `f` over an open
  `W` containing a point of order `0` is an admissible centre of the restriction;
* **`eventually_le_of_nmOrd_eq_zero`** (property (2) at `o = 0`, the hypothesis of
  `NonmonomialOrderCanonical.isInvUSCOn_of_ordMonotone`): near a cosupport point of order `0`, the cosupport points of order
  `0` have values `≤`;
* **`towerInvAlong_step_of_nmOrd_eq_zero`**, **`value_step_of_nmOrd_eq_zero`** (properties (3), (4) at `o = 0`, the shape of
  `StepOneWellFounded.StepDrop`): along a canonical step, at a point `z` of the new cosupport with `ν(π z) = 0`, `π z` lies in
  the old cosupport, `ν(z) = 0`, and `γ` (hence `f`) drops if `π z ∈ C` and is unchanged otherwise;
-/

open Set Filter TopologicalSpace
open scoped Topology Manifold ContDiff

universe u v

namespace Hironaka.NonmonomialOrderMonomialCanonical

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.MarkedIdeals Hironaka.MarkedIdeals.MarkedIdeal Hironaka.MarkedIdealBiholomorphism Hironaka.MonomialInvariant Hironaka.MonomialCaseAlong Hironaka.MonomialStepAlong Hironaka.BlowupTowers Hironaka.BlowupTowerTransforms Hironaka.NonmonomialOrderLocal Hironaka.NonmonomialOrderCanonical Hironaka.NonmonomialOrderMonomial Hironaka.DivisorExponentAlong
open Hironaka.ResolutionInvariantSpec (IsInvDomain IsCanonical)
open Hironaka.ResolutionDriver (maxLocus)

noncomputable section

variable {n : ℕ}

/-! ### The value at the points of order zero -/

section Defs

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ]

/-- **At the cosupport points of order `0` the value is a function `ψ` of the monomial invariant**: along every multiple test
blow-up `T` of `𝔪`, at every point `y` of the cosupport with `ν(y) = 0`, `f T y = ψ (γ_T y)`, where
`γ_T = MonomialStepAlong.towerInvAlong 𝔪 T` is the invariant of the monomial case of the transform. -/
def OrdZeroValue (𝔪 : MarkedIdeal n X) (f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ) (ψ : WithBot Val → Λ) : Prop :=
  ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T →
    ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, nmOrd (geoTransformAlong 𝔪 T) y = 0 → f T y = ψ (towerInvAlong 𝔪 T y)

/-- `OrdZeroValue` at one point, with the value written as an application of `f`. -/
theorem OrdZeroValue.apply {𝔪 : MarkedIdeal n X} {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ}
    {ψ : WithBot Val → Λ} (hv : OrdZeroValue 𝔪 f ψ) {Y : CMfd.{u} n} {T : BlowupTower X Y} (hT : IsGeoTestTower 𝔪 T)
    (y : Y) (hy : y ∈ (geoTransformAlong 𝔪 T).cosupp) (hy0 : nmOrd (geoTransformAlong 𝔪 T) y = 0) :
    f T y = ψ (towerInvAlong 𝔪 T y) :=
  hv T hT y hy hy0

/-- **The order-`0` entry of a lexicographic value is strictly monotone**: `w ↦ (0, inl w)` in `ℕ ×ₗ (α ⊕ₗ β)`. -/
theorem strictMono_toLex_zero_inl {α β : Type*} [Preorder α] [Preorder β] :
    StrictMono (fun a : α => (toLex ((0 : ℕ), (toLex (Sum.inl a) : α ⊕ₗ β)) : ℕ ×ₗ (α ⊕ₗ β))) := by
  intro a b hab
  rw [Prod.Lex.toLex_lt_toLex]
  exact Or.inr ⟨rfl, Sum.Lex.inl_lt_inl_iff.mpr hab⟩

/-- **The lexicographic value `(ν, g)` with `g = inl γ` at order `0`** is of this form, with
`ψ = fun w => toLex (0, toLex (Sum.inl w))` (strictly monotone, `strictMono_toLex_zero_inl`). -/
theorem ordZeroValue_toLex (𝔪 : MarkedIdeal n X) {β : Type v} [LinearOrder β]
    (g : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → WithBot Val ⊕ₗ β)
    (hg : ∀ {Y : CMfd.{u} n} (T : BlowupTower X Y), IsGeoTestTower 𝔪 T → ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp,
      nmOrd (geoTransformAlong 𝔪 T) y = 0 → g T y = toLex (Sum.inl (towerInvAlong 𝔪 T y))) :
    OrdZeroValue 𝔪 (fun {Y} T y => toLex (nmOrd (geoTransformAlong 𝔪 T) y, g (Y := Y) T y))
      (fun w => toLex ((0 : ℕ), (toLex (Sum.inl w) : WithBot Val ⊕ₗ β))) := by
  intro Y T hT y hy hy0
  simp only [hy0, hg T hT y hy hy0]

end Defs

/-! ### Maximum loci and level sets of order zero -/

section MaxLocus

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {𝔪 : MarkedIdeal n X}
  {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ} {ψ : WithBot Val → Λ}

/-- **A point of order `0` on the maximum locus forces order `0` on the cosupport.** -/
theorem nmOrd_eq_zero_of_mem_maxLocus (hf : OrdMonotone 𝔪 f) {Y : CMfd.{u} n} {T : BlowupTower X Y}
    (hT : IsGeoTestTower 𝔪 T) {c : Y} (hc : c ∈ maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp)
    (hc0 : nmOrd (geoTransformAlong 𝔪 T) c = 0) {y : Y} (hy : y ∈ (geoTransformAlong 𝔪 T).cosupp) :
    nmOrd (geoTransformAlong 𝔪 T) y = 0 := by
  have := nmOrd_le_of_mem_maxLocus hf hT hc hy
  omega

/-- **A point of order `0` is off `{ν ≥ 1}`** (`𝔫` well formed and nonzero along `N`; off `N` there is nothing to prove). -/
theorem notMem_ordGe_one_of_nmOrd_eq_zero {Y : CMfd.{u} n} {𝔫 : MarkedIdeal n Y} (h𝔫 : 𝔫.IsWellFormed)
    (hne : ∀ y ∈ 𝔫.N, IsNonzeroAlongAt 𝔫.N 𝔫.ideal y) {y : Y} (hy0 : nmOrd 𝔫 y = 0) : y ∉ ordGe 𝔫 1 := by
  intro hmem
  have := (mem_ordGe_iff h𝔫 hne (ordGe_subset_N 𝔫 1 hmem) 1).mp hmem
  omega

/-- **The maximum locus of order `0` is that of `γ`**: if a point of order `0` lies on the maximum locus of `f` on the
cosupport, the maximum locus of `f` is the maximum locus of `γ_T` on the cosupport (`f = ψ ∘ γ_T` there, `ψ` strictly
monotone). -/
theorem maxLocus_eq_maxLocus_towerInvAlong (hf : OrdMonotone 𝔪 f) (hψ : StrictMono ψ) (hv : OrdZeroValue 𝔪 f ψ)
    {Y : CMfd.{u} n} {T : BlowupTower X Y} (hT : IsGeoTestTower 𝔪 T)
    {c : Y} (hc : c ∈ maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp) (hc0 : nmOrd (geoTransformAlong 𝔪 T) c = 0) :
    maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp = maxLocus (towerInvAlong 𝔪 T) (geoTransformAlong 𝔪 T).cosupp := by
  rw [ResolutionInvariantExt.maxLocus_congr (g := ψ ∘ towerInvAlong 𝔪 T) fun y hy =>
    hv.apply hT y hy (nmOrd_eq_zero_of_mem_maxLocus hf hT hc hc0 hy)]
  exact MaxLocusLocal.maxLocus_comp_strictMono hψ _ _

/-- **Level sets of order `0` are admissible** (property (1) of `hir:centre-function` at `o = 0`, in the field shape; `n > 0`,
`𝔪` in the domain): along a multiple test blow-up `T`, for an open `W` of the last stage and a value `l` bounding `f T` on the
cosupport over `W`, if some point `y₀` of the cosupport of order `0` has value `l`, the points of the cosupport over
`W` with value `l` form an admissible centre of the restriction of `𝔪_T` to `W`.  Every point of the cosupport over `W` has
order `0` (`OrdMonotone`), so `f T = ψ ∘ γ_T` there and the level set is that of `γ_T` at `γ_T(y₀)`
(`NonmonomialOrderMonomial.isAdmissibleCentre_gammaAlong_level_of_ordZero`). -/
theorem isAdmissibleCentre_level_of_nmOrd_eq_zero (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f)
    (hψ : StrictMono ψ) (hv : OrdZeroValue 𝔪 f ψ) {Y : CMfd.{u} n} {T : BlowupTower X Y} (hT : IsGeoTestTower 𝔪 T)
    (W : Opens Y) {l : Λ} (hl : ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, y ∈ W → f T y ≤ l)
    {y₀ : Y} (hy₀ : y₀ ∈ (geoTransformAlong 𝔪 T).cosupp) (hy₀l : f T y₀ = l)
    (hy₀0 : nmOrd (geoTransformAlong 𝔪 T) y₀ = 0) :
    (MarkedIdeal.pullback (Subtype.val : W → Y) (geoTransformAlong 𝔪 T)).IsAdmissibleCentre
      ((Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ f T y = l}) := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have h0 : ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, y ∈ W → nmOrd (geoTransformAlong 𝔪 T) y = 0 := by
    intro y hy hyW
    have := hf T hT y hy y₀ hy₀ ((hl y hy hyW).trans hy₀l.ge)
    omega
  have hset : {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ f T y = l} ∩ (W : Set Y) =
      {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ towerInvAlong 𝔪 T y = towerInvAlong 𝔪 T y₀} ∩ (W : Set Y) := by
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨⟨hy, hyl⟩, hyW⟩
      refine ⟨⟨hy, hψ.injective ?_⟩, hyW⟩
      rw [← hv.apply hT y hy (h0 y hy hyW), ← hv.apply hT y₀ hy₀ hy₀0, hyl, hy₀l]
    · rintro ⟨⟨hy, hyγ⟩, hyW⟩
      refine ⟨⟨hy, ?_⟩, hyW⟩
      rw [hv.apply hT y hy (h0 y hy hyW), hyγ, ← hv.apply hT y₀ hy₀ hy₀0, hy₀l]
  have hpre : (Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧ f T y = l} =
      (Subtype.val : W → Y) ⁻¹' {y | y ∈ (geoTransformAlong 𝔪 T).cosupp ∧
        towerInvAlong 𝔪 T y = towerInvAlong 𝔪 T y₀} := by
    ext p
    have := congrArg (fun S : Set Y => (p : Y) ∈ S) hset
    simp only [mem_inter_iff, SetLike.mem_coe, p.2, and_true, eq_iff_iff] at this
    exact this
  rw [hpre]
  refine isAdmissibleCentre_gammaAlong_level_of_ordZero hn hdomT W _
    (fun y hy hyW => notMem_ordGe_one_of_nmOrd_eq_zero hdomT.isWellFormed hdomT.isNonzeroAlongAt (h0 y hy hyW))
    fun y hy hyW => ?_
  have hle := hl y hy hyW
  rw [hv.apply hT y hy (h0 y hy hyW), ← hy₀l, hv.apply hT y₀ hy₀ hy₀0] at hle
  exact hψ.le_iff_le.mp hle

end MaxLocus

/-! ### Upper semicontinuity at the points of order zero -/

section USC

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {𝔪 : MarkedIdeal n X}
  {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ} {ψ : WithBot Val → Λ}

/-- **Upper semicontinuity among the points of order `0`** (property (2) of `hir:centre-function` at `o = 0`; `𝔪` in the
domain, `n > 0`): near a cosupport point `y` of order `0`, every cosupport point of order `0` has value `≤ f T y`.  This is the
hypothesis of `NonmonomialOrderCanonical.isInvUSCOn_of_ordMonotone` at the points of order `0`; `γ_T` is upper
semicontinuous on `N_T` (`MonomialCaseAlong.eventually_gammaAlong_le`, which needs no monomiality) and `ψ` is monotone. -/
theorem eventually_le_of_nmOrd_eq_zero (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hψ : StrictMono ψ)
    (hv : OrdZeroValue 𝔪 f ψ) {Y : CMfd.{u} n} {T : BlowupTower X Y} (hT : IsGeoTestTower 𝔪 T) {y : Y}
    (hy : y ∈ (geoTransformAlong 𝔪 T).cosupp) (hy0 : nmOrd (geoTransformAlong 𝔪 T) y = 0) :
    ∀ᶠ y' in 𝓝 y, y' ∈ (geoTransformAlong 𝔪 T).cosupp → nmOrd (geoTransformAlong 𝔪 T) y' = 0 → f T y' ≤ f T y := by
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hT
  have hwf := hdomT.isWellFormed
  filter_upwards [eventually_gammaAlong_le hn hwf.isClosedSubmanifold_N hwf.isSNCDivisor hwf.isTransverse
    hwf.isCoherent hdomT.isNonzeroAlongAt (geoTransformAlong 𝔪 T).d ((geoTransformAlong 𝔪 T).cosupp_subset_N hy)]
    with y' hy' hy'c hy'0
  rw [hv.apply hT y' hy'c hy'0, hv.apply hT y hy hy0]
  exact hψ.monotone (hy' ((geoTransformAlong 𝔪 T).cosupp_subset_N hy'c))

end USC

/-! ### One canonical step at the points of order zero -/

section Step

variable {X : CMfd.{u} n} {Λ : Type v} [LinearOrder Λ] {𝔪 : MarkedIdeal n X}
  {f : ∀ {Y : CMfd.{u} n}, BlowupTower X Y → Y → Λ} {ψ : WithBot Val → Λ}

/-- **One canonical step at a point of order `0`: the invariant `γ`** (properties (3), (4) of `hir:centre-function` at `o = 0`;
`𝔪` in the domain, `n > 0`): if `T σ` (`σ` the blowup along `C`) is a multiple test blow-up of `𝔪` and a canonical segment of
`f`, and `z` is a point of the new cosupport with `ν(σ z) = 0`, then `σ z` lies in the old cosupport, `ν(z) = 0`, and
`γ_{Tσ}(z) < γ_T(σ z)` if `σ z ∈ C`, `γ_{Tσ}(z) = γ_T(σ z)` otherwise.  Over `C`, `C` is the maximum locus of `f`, which has a
point of order `0`, so the cosupport has order `0` and `C` is the maximum locus of `γ_T`
(`maxLocus_eq_maxLocus_towerInvAlong`), and `NonmonomialOrderMonomial.gammaAlong_geoTransform_lt_of_ordZero` applies; off
`C`, `NonmonomialOrderMonomial.gammaAlong_geoTransform_eq_of_notMem_of_ordZero`. -/
theorem towerInvAlong_step_of_nmOrd_eq_zero (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f)
    (hψ : StrictMono ψ) (hv : OrdZeroValue 𝔪 f ψ) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower 𝔪 (.step T C π hπ)) (hcan : IsCanonical 𝔪 f (.step T C π hπ))
    {z : Z} (hz : z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp)
    (h0 : nmOrd (geoTransformAlong 𝔪 T) (π z) = 0) :
    π z ∈ (geoTransformAlong 𝔪 T).cosupp ∧ nmOrd (geoTransformAlong 𝔪 (.step T C π hπ)) z = 0 ∧
      (π z ∈ C → towerInvAlong 𝔪 (.step T C π hπ) z < towerInvAlong 𝔪 T (π z)) ∧
      (π z ∉ C → towerInvAlong 𝔪 (.step T C π hπ) z = towerInvAlong 𝔪 T (π z)) := by
  obtain ⟨hTT, hCadm⟩ := (isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT
  have hC : C = ∅ ∨ C = maxLocus (f T) (geoTransformAlong 𝔪 T).cosupp := hcan.2
  have hdomT := InvDomainTowerAlong.isInvDomain_geoTransformAlong h T hTT
  obtain ⟨hπz, hle⟩ := nmOrd_step_le_of_canonical hn h hf T C π hπ hT hC hz
  have hz0 : nmOrd (geoTransformAlong 𝔪 (.step T C π hπ)) z = 0 := by omega
  have hzN : z ∈ ((geoTransformAlong 𝔪 T).geoTransform C π).N :=
    (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp_subset_N hz
  have h0' : π z ∉ ordGe (geoTransformAlong 𝔪 T) 1 :=
    notMem_ordGe_one_of_nmOrd_eq_zero hdomT.isWellFormed hdomT.isNonzeroAlongAt h0
  refine ⟨hπz, hz0, fun hzC => ?_, fun hzC => ?_⟩
  · rcases hC with hC | hC
    · rw [hC] at hzC
      exact absurd hzC (notMem_empty _)
    · have hzC' := hzC
      rw [hC] at hzC'
      have hcos : ∀ y ∈ (geoTransformAlong 𝔪 T).cosupp, y ∉ ordGe (geoTransformAlong 𝔪 T) 1 := fun y hy =>
        notMem_ordGe_one_of_nmOrd_eq_zero hdomT.isWellFormed hdomT.isNonzeroAlongAt
          (nmOrd_eq_zero_of_mem_maxLocus hf hTT hzC' h0 hy)
      have hCeq : C = maxLocus (towerInvAlong 𝔪 T) (geoTransformAlong 𝔪 T).cosupp := by
        rw [hC]
        exact maxLocus_eq_maxLocus_towerInvAlong hf hψ hv hTT hzC' h0
      exact gammaAlong_geoTransform_lt_of_ordZero hn hdomT hcos hCeq hCadm hπ hzN hzC
  · exact gammaAlong_geoTransform_eq_of_notMem_of_ordZero hn hdomT hCadm hπ hzN hzC h0' _

/-- **One canonical step at a point of order `0`: the value** (properties (3), (4) of `hir:centre-function` at `o = 0`, the
shape of `StepOneWellFounded.StepDrop` restricted to the points `z` with `ν(σ z) = 0`): `σ z` lies in the old cosupport,
`f (T σ) z < f T (σ z)` if `σ z ∈ C`, and `f (T σ) z = f T (σ z)` otherwise. -/
theorem value_step_of_nmOrd_eq_zero (hn : 0 < n) {k : ℕ} (h : IsInvDomain k 𝔪) (hf : OrdMonotone 𝔪 f)
    (hψ : StrictMono ψ) (hv : OrdZeroValue 𝔪 f ψ) {Y Z : CMfd.{u} n} (T : BlowupTower X Y) (C : Set Y) (π : Z → Y)
    (hπ : IsBlowupAlong n C π) (hT : IsGeoTestTower 𝔪 (.step T C π hπ)) (hcan : IsCanonical 𝔪 f (.step T C π hπ))
    {z : Z} (hz : z ∈ (geoTransformAlong 𝔪 (.step T C π hπ)).cosupp)
    (h0 : nmOrd (geoTransformAlong 𝔪 T) (π z) = 0) :
    π z ∈ (geoTransformAlong 𝔪 T).cosupp ∧ (π z ∈ C → f (.step T C π hπ) z < f T (π z)) ∧
      (π z ∉ C → f (.step T C π hπ) z = f T (π z)) := by
  obtain ⟨hπz, hz0, hlt, heq⟩ := towerInvAlong_step_of_nmOrd_eq_zero hn h hf hψ hv T C π hπ hT hcan hz h0
  have hTT : IsGeoTestTower 𝔪 T := ((isGeoTestTower_step_iff 𝔪 T C π hπ).mp hT).1
  refine ⟨hπz, fun hzC => ?_, fun hzC => ?_⟩
  · rw [hv.apply hT z hz hz0, hv.apply hTT (π z) hπz h0]
    exact hψ (hlt hzC)
  · rw [hv.apply hT z hz hz0, hv.apply hTT (π z) hπz h0, heq hzC]

end Step

end

end Hironaka.NonmonomialOrderMonomialCanonical
