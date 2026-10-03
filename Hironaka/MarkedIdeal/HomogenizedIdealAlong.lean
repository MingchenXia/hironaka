/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.DerivativeIdealAlongEtale
import Hironaka.MarkedIdeal.TangentDirectionAlong
import Hironaka.MarkedIdeal.HomogenizedEtale
import Hironaka.MarkedIdeal.MarkedIdealOperationsAlong
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.AnalyticSubsetOpens
import Hironaka.Blowup.BlowupExceptionalDivisor
import Hironaka.MarkedIdeal.CoefficientIdeal
import Hironaka.Invariant.CompanionReduction
import Hironaka.MarkedIdeal.DerivativeIdealAlong
import Hironaka.MarkedIdeal.DerivativeIdealAlongCoherent
import Hironaka.MarkedIdeal.DerivativeIdealTower
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.MarkedIdeal.GiraudAlong
import Hironaka.MarkedIdeal.HadamardBridge
import Hironaka.MarkedIdeal.HomogenizedEquivalence
import Hironaka.MarkedIdeal.HomogenizedGlueing
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdealBiholomorphism
import Hironaka.MarkedIdeal.MarkedIdealOperationsTransform
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Invariant.OrderMultiplicativity
import Hironaka.Invariant.OrderTaylor
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Homogenized and coefficient ideals along a submanifold (one stage)

Sources: Włodarczyk 2005, §2.10--2.11 (homogenized ideal `𝓗(𝓘, μ)`, coefficient ideal `𝓒(𝓘, μ)`), Włodarczyk 2009
(GGT 2008) §5.5--5.6, applied on the submanifold `N` of a marked ideal `(M, N, E, 𝔞, d)` with the derivative ideals
`𝓓_N` along `N` (`DerivativeIdealAlong.derivIdealAlong`) in place of `𝓓`; Bierstone--Milman 2008 §3 (the derivative
ideals of `𝔞|_N` are taken on `N`).

For a marked ideal `(𝔞|_N, μ)` put `T_N(𝔞) = 𝓓_N^{μ-1}(𝔞)` (`tangentIdealAlong`) and

* `homogenizedIdealAlong N 𝔞 μ = 𝓗_N(𝔞) = ∑_{i<μ} 𝓓_N^i(𝔞) · T_N(𝔞)^i` (`homSum`);
* `derivMarkedAlong 𝔪 j = (M, N, E, 𝓓_N^j 𝔞, d - j)` and `coeffMarkedAlong 𝔪 = 𝓒_N(𝔪) = ∑_{i<d} 𝓓_N^i(𝔪)`, Włodarczyk's
  sum of marked ideals (`CoefficientIdeal.msum`); `homMarkedAlong 𝔪 = (M, N, E, 𝓗_N(𝔞), d)`.

For `N = M` these are the constructions of `HomogenizedIdeal` / `CoefficientIdeal` / `HomogenizedEquivalence`.

* Coherence (`𝔞` coherent, `N` a closed submanifold): `isCoherent_homogenizedIdealAlong`, `isCoherent_coeffMarkedAlong`.
* Cosupports: `𝔞 ⊆ 𝓗_N(𝔞)` and `cosupp(𝓗_N(𝔞)|_N, μ) = cosupp(𝔞|_N, μ)` for every set `N` (Giraud's inclusion along `N`);
  `cosupp 𝓒_N(𝔪) = cosupp 𝔪` when `N` is regular at its points (orders of powers along `N`).
* Maximal order along `N`: `IsMaximalOrderAlong N 𝔞 μ` (`ord_x(𝔞|_N) ≤ μ` at every point; and on a submanifold it
  says `𝓓_N^μ(𝔞)` vanishes at no point of `N`). It passes to `𝓗_N` (mark `μ`) and to `𝓒_N` (mark `μ_𝓒`), globally
  and pointwise (`ord_x = μ` at a point of the cosupport).
* Étale invariance (Włodarczyk's `le:etale2` / `le:etale3` along `N`): for a holomorphic local biholomorphism `φ`,
  `φ^*𝓗_N(𝔞) = 𝓗_{φ⁻¹N}(φ^*𝔞)`, `φ^*𝓒_N(𝔪) = 𝓒_{φ⁻¹N}(φ^*𝔪)` and `φ^*𝓗_N(𝔪) = 𝓗_{φ⁻¹N}(φ^*𝔪)`; instances for
  biholomorphisms and for inclusions of open sets.  From `DerivativeIdealAlongEtale.pullback_iterDerivIdealAlong` and
  `HomogenizedEtale.pullback_homSum` / `pullback_finSumIdeal`.

Not here: the glueing lemma along `N` (step (4c)) and the statements along multiple test blow-ups (step (4d), after the
transforms along `N`, item (2) of `hir:along-calculus`).
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HomogenizedIdealAlong

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.DerivativeIdeal Hironaka.DerivativeIdealAlong Hironaka.GiraudAlong Hironaka.DerivativeIdealAlongCoherent Hironaka.DerivativeIdealAlongEtale Hironaka.TangentDirectionAlong Hironaka.IdealWeightPowers Hironaka.MarkedIdeals Hironaka.DerivativeIdealTower Hironaka.CoefficientIdeal Hironaka.HomogenizedGlueing Hironaka.HomogenizedEquivalence Hironaka.HomogenizedEtale Hironaka.MarkedIdealBiholomorphism Hironaka.GermIdealPullbackCalculus Hironaka.HadamardBridge

noncomputable section

/-! ### Definitions -/

section Defs

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]

/-- `T_N(𝔞) = 𝓓_N^{μ-1}(𝔞)` for the marked ideal `(𝔞|_N, μ)`. -/
def tangentIdealAlong (N : Set M) (𝔞 : GermIdeal n M) (μ : ℕ) : GermIdeal n M :=
  iterDerivIdealAlong N 𝔞 (μ - 1)

/-- **The homogenized ideal along `N`**: `𝓗_N(𝔞) = ∑_{i<μ} 𝓓_N^i(𝔞) · T_N(𝔞)^i` (Włodarczyk §2.10 on `N`). -/
def homogenizedIdealAlong (N : Set M) (𝔞 : GermIdeal n M) (μ : ℕ) : GermIdeal n M :=
  homSum (fun i => iterDerivIdealAlong N 𝔞 i) (tangentIdealAlong N 𝔞 μ) μ

/-- **The derivative marked ideal along `N`**: `𝓓_N^j(M, N, E, 𝔞, d) = (M, N, E, 𝓓_N^j 𝔞, d - j)`. -/
def derivMarkedAlong (𝔪 : MarkedIdeal n M) (j : ℕ) : MarkedIdeal n M where
  N := 𝔪.N
  E := 𝔪.E
  ideal := iterDerivIdealAlong 𝔪.N 𝔪.ideal j
  d := 𝔪.d - j

@[simp] theorem derivMarkedAlong_N (𝔪 : MarkedIdeal n M) (j : ℕ) : (derivMarkedAlong 𝔪 j).N = 𝔪.N := rfl

@[simp] theorem derivMarkedAlong_E (𝔪 : MarkedIdeal n M) (j : ℕ) : (derivMarkedAlong 𝔪 j).E = 𝔪.E := rfl

@[simp] theorem derivMarkedAlong_ideal (𝔪 : MarkedIdeal n M) (j : ℕ) :
    (derivMarkedAlong 𝔪 j).ideal = iterDerivIdealAlong 𝔪.N 𝔪.ideal j := rfl

@[simp] theorem derivMarkedAlong_d (𝔪 : MarkedIdeal n M) (j : ℕ) : (derivMarkedAlong 𝔪 j).d = 𝔪.d - j := rfl

/-- **The coefficient ideal along `N`** (Włodarczyk §2.11 on `N`): `𝓒_N(𝔪) = 𝔪 + 𝓓_N(𝔪) + … + 𝓓_N^{d-1}(𝔪)`, i.e.
`(𝔞, d) + (𝓓_N 𝔞, d - 1) + … + (𝓓_N^{d-1} 𝔞, 1)` in Włodarczyk's sum of marked ideals. -/
def coeffMarkedAlong (𝔪 : MarkedIdeal n M) : MarkedIdeal n M :=
  msum (fun i => derivMarkedAlong 𝔪 i) 𝔪.d

/-- **The homogenized marked ideal along `N`**: `𝓗_N(𝔪) = (M, N, E, 𝓗_N(𝔞), d)`. -/
def homMarkedAlong (𝔪 : MarkedIdeal n M) : MarkedIdeal n M where
  N := 𝔪.N
  E := 𝔪.E
  ideal := homogenizedIdealAlong 𝔪.N 𝔪.ideal 𝔪.d
  d := 𝔪.d

/-- **Maximal order along `N`** (Włodarczyk §2.7, Bierstone--Milman §3 on `N`): `ord_x(𝔞|_N) ≤ μ` at every point, i.e.
`cosupp(𝔞|_N, μ + 1) = ∅`. -/
def IsMaximalOrderAlong (N : Set M) (𝔞 : GermIdeal n M) (μ : ℕ) : Prop :=
  ∀ x, x ∉ cosupport n N 𝔞 (μ + 1)

end Defs

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {N : Set M} {𝔞 : GermIdeal n M}

/-! ### Coherence -/

section Coherence

theorem isCoherent_tangentIdealAlong (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (μ : ℕ) :
    (tangentIdealAlong N 𝔞 μ).IsCoherent :=
  isCoherent_iterDerivIdealAlong h𝔞 hN (μ - 1)

/-- **`𝓗_N(𝔞)` is coherent** (`𝔞` coherent, `N` a closed submanifold). -/
theorem isCoherent_homogenizedIdealAlong (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N) (μ : ℕ) :
    (homogenizedIdealAlong N 𝔞 μ).IsCoherent :=
  isCoherent_homSum (fun i _ => isCoherent_iterDerivIdealAlong h𝔞 hN i) (isCoherent_tangentIdealAlong h𝔞 hN μ)

/-- **`𝓒_N(𝔪)` has coherent ideal** (`𝔞` coherent, `N` a closed submanifold). -/
theorem isCoherent_coeffMarkedAlong {𝔪 : MarkedIdeal n M} (h𝔞 : 𝔪.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔪.N) :
    (coeffMarkedAlong 𝔪).ideal.IsCoherent :=
  show (finSumIdeal (fun i => idealPow (iterDerivIdealAlong 𝔪.N 𝔪.ideal i) (sumExp (fun j => 𝔪.d - j) 𝔪.d i))
      𝔪.d).IsCoherent from
    isCoherent_finSumIdeal_of_lt fun i _ => isCoherent_idealPow (isCoherent_iterDerivIdealAlong h𝔞 hN i) _

theorem isCoherent_homMarkedAlong {𝔪 : MarkedIdeal n M} (h𝔞 : 𝔪.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔪.N) :
    (homMarkedAlong 𝔪).ideal.IsCoherent :=
  isCoherent_homogenizedIdealAlong h𝔞 hN 𝔪.d

end Coherence

/-! ### Cosupports -/

section Cosupport

/-- **`𝔞 ⊆ 𝓗_N(𝔞)`** (`μ ≥ 1`). -/
theorem le_homogenizedIdealAlong (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {μ : ℕ} (hμ : 1 ≤ μ) :
    𝔞.Le (homogenizedIdealAlong N 𝔞 μ) :=
  le_homSum (A := fun i => iterDerivIdealAlong N 𝔞 i) hμ h𝔞

/-- At a point of `cosupp(𝔞|_N, μ)`, `ord_x(𝓗_N(𝔞)|_N) ≥ μ` (any `N`, `μ ≥ 1`). -/
theorem orderGE_homogenizedIdealAlong (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {μ : ℕ} (hμ : 1 ≤ μ) {x : M}
    (hx : x ∈ cosupport n N 𝔞 μ) : OrderGE n N (homogenizedIdealAlong N 𝔞 μ) x μ := by
  have hA : ∀ i < μ, OrderGE n N (iterDerivIdealAlong N 𝔞 i) x (μ - i) := fun i hi =>
    (cosupport_add_subset_cosupport_iterDerivIdealAlong h𝔞 (μ - i) i
      (by rwa [Nat.sub_add_cancel hi.le])).2
  have hB : OrderGE n N (tangentIdealAlong N 𝔞 μ) x 1 := by
    have := hA (μ - 1) (by omega)
    rwa [show μ - (μ - 1) = 1 by omega] at this
  exact orderGE_homSum hA hB

/-- **`cosupp(𝓗_N(𝔞)|_N, μ) = cosupp(𝔞|_N, μ)`** (any `N`, `μ ≥ 1`). -/
theorem cosupport_homogenizedIdealAlong (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {μ : ℕ} (hμ : 1 ≤ μ) :
    cosupport n N (homogenizedIdealAlong N 𝔞 μ) μ = cosupport n N 𝔞 μ :=
  Subset.antisymm (cosupport_subset_of_le (le_homogenizedIdealAlong h𝔞 hμ) μ)
    fun _ hx => ⟨hx.1, orderGE_homogenizedIdealAlong h𝔞 hμ hx⟩

/-- `cosupp 𝓗_N(𝔪) = cosupp 𝔪` (`d ≥ 1`). -/
theorem cosupp_homMarkedAlong {𝔪 : MarkedIdeal n M} (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x)
    (hd : 1 ≤ 𝔪.d) : (homMarkedAlong 𝔪).cosupp = 𝔪.cosupp :=
  cosupport_homogenizedIdealAlong h𝔞 hd

/-- The `i`-th summand of `𝓒_N(𝔪)` has the cosupport of `(𝓓_N^i 𝔞, d - i)` (`N` regular at its points). -/
theorem cosupport_coeffSummand {𝔪 : MarkedIdeal n M} (hN : ∀ x ∈ 𝔪.N, ∃ k, RegularAtDim (n := n) 𝔪.N x k)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) {i : ℕ} (hi : i < 𝔪.d) :
    cosupport n 𝔪.N (idealPow (iterDerivIdealAlong 𝔪.N 𝔪.ideal i) (sumExp (fun j => 𝔪.d - j) 𝔪.d i))
        ((Finset.range 𝔪.d).prod fun j => 𝔪.d - j) =
      cosupport n 𝔪.N (iterDerivIdealAlong 𝔪.N 𝔪.ideal i) (𝔪.d - i) := by
  have hpow := MarkedIdealOperationsAlong.cosupport_idealPow_mul_eq_along hN
    (holomorphicAt_of_mem_iterDerivIdealAlong (N := 𝔪.N) h𝔞 i)
    (one_le_sumExp (d := fun j => 𝔪.d - j) (m := 𝔪.d) (fun j hj => by omega) i) (𝔪.d - i)
  have hm : (𝔪.d - i) * sumExp (fun j => 𝔪.d - j) 𝔪.d i = (Finset.range 𝔪.d).prod fun j => 𝔪.d - j :=
    mul_sumExp (fun j => 𝔪.d - j) hi
  rw [hm] at hpow
  exact hpow

/-- **`cosupp 𝓒_N(𝔪) = cosupp 𝔪`** (`N` regular at its points, `d ≥ 1`): Włodarczyk's `supp 𝓒(𝓘, μ) = supp(𝓘, μ)` along
`N`, from Giraud's inclusion along `N` and `cosupp(𝔟^ν|_N, μν) = cosupp(𝔟|_N, μ)`. -/
theorem cosupp_coeffMarkedAlong {𝔪 : MarkedIdeal n M} (hN : ∀ x ∈ 𝔪.N, ∃ k, RegularAtDim (n := n) 𝔪.N x k)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (hd : 1 ≤ 𝔪.d) :
    (coeffMarkedAlong 𝔪).cosupp = 𝔪.cosupp := by
  ext x
  have hhol : ∀ i < 𝔪.d, ∀ y g, (idealPow (iterDerivIdealAlong 𝔪.N 𝔪.ideal i)
      (sumExp (fun j => 𝔪.d - j) 𝔪.d i)).mem y g → HolomorphicAt n g y :=
    fun _ _ _ _ hg => holomorphicAt_of_mem_idealPow hg
  show x ∈ cosupport n 𝔪.N (finSumIdeal (fun i => idealPow (iterDerivIdealAlong 𝔪.N 𝔪.ideal i)
      (sumExp (fun j => 𝔪.d - j) 𝔪.d i)) 𝔪.d) ((Finset.range 𝔪.d).prod fun j => 𝔪.d - j) ↔
    x ∈ cosupport n 𝔪.N 𝔪.ideal 𝔪.d
  rw [mem_cosupport_finSumIdeal hhol]
  constructor
  · rintro ⟨-, hall⟩
    have h0 := hall 0 hd
    rw [cosupport_coeffSummand hN h𝔞 hd, Nat.sub_zero] at h0
    exact h0
  · intro hx
    refine ⟨hx.1, fun i hi => ?_⟩
    rw [cosupport_coeffSummand hN h𝔞 hi]
    exact cosupport_add_subset_cosupport_iterDerivIdealAlong h𝔞 (𝔪.d - i) i (by rwa [Nat.sub_add_cancel hi.le])

end Cosupport

/-! ### Maximal order along `N` -/

section MaximalOrder

/-- **Orders of powers along `N`, strict form**: if `ord_x(g|_N) ≤ o` then `ord_x(g^e|_N) ≤ e o` (at a regular point of `N`;
`g` holomorphic).  Through a local retraction `r` onto `N`, `g ∘ r` has the order of `g|_N`, and orders add in `𝒪_x`. -/
theorem not_vanishesToOrderOn_pow {x : M} {k : ℕ} (hN : RegularAtDim (n := n) N x k) {g : M → ℂ}
    (hg : HolomorphicAt n g x) {o : ℕ} (hgo : ¬ VanishesToOrderOn n N x (o + 1) g) (e : ℕ) :
    ¬ VanishesToOrderOn n N x (e * o + 1) (fun p => g p ^ e) := by
  rintro ⟨h, hh, hgh⟩
  obtain ⟨r, hrx, hrd, hrN, hrid⟩ := MarkedIdealOperationsAlong.exists_localRetraction hN
  have hrT : Tendsto r (𝓝 x) (𝓝 x) := by
    have := hrd.self_of_nhds.continuousAt.tendsto
    rwa [hrx] at this
  have hĝ : HolomorphicAt n (g ∘ r) x := holomorphicAt_comp_map hrd (by rw [hrx]; exact hg)
  have hh' : (idealPow (pointIdeal n (r x)) (e * o + 1)).mem (r x) h := by rw [hrx]; exact hh
  have hhr := comp_mem_idealPow_pointIdeal hrd (e * o + 1) hh'
  have heq : (fun p => (g ∘ r) p ^ e) =ᶠ[𝓝 x] h ∘ r := by
    filter_upwards [hrN, hrT.eventually hgh] with p hp1 hp2
    exact hp2 hp1
  have hpow : (idealPow (pointIdeal n x) (e * o + 1)).mem x (fun p => (g ∘ r) p ^ e) :=
    OrderTaylor.mem_idealPow_congr hhr heq.symm
  have hĝo : (idealPow (pointIdeal n x) (o + 1)).mem x (g ∘ r) := by
    by_contra hno
    exact CompanionReduction.pow_notMem_idealPow hĝ hno e hpow
  refine hgo ⟨g ∘ r, hĝo, ?_⟩
  filter_upwards [hrid] with p hp hpN
  simp [hp hpN]

/-- On a submanifold, **maximal order along `N` says that `𝓓_N^μ(𝔞)` vanishes at no point of `N`**
(`(𝓓_N^μ 𝔞)|_N = 𝒪_N`), by Giraud--Villamayor along `N`. -/
theorem isMaximalOrderAlong_iff_inter_zeroLocus (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    (hN : ∀ x ∈ N, ∃ k, RegularAtDim (n := n) N x k) (μ : ℕ) :
    IsMaximalOrderAlong N 𝔞 μ ↔ N ∩ (iterDerivIdealAlong N 𝔞 μ).zeroLocus = ∅ := by
  rw [← cosupport_succ_eq_inter_zeroLocus_iterDerivIdealAlong h𝔞 hN μ, Set.eq_empty_iff_forall_notMem]
  rfl

/-- **`𝓗_N(𝔞)` is of maximal order along `N` when `𝔞` is** (`μ ≥ 1`). -/
theorem IsMaximalOrderAlong.homogenizedIdealAlong (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) {μ : ℕ}
    (hμ : 1 ≤ μ) (h : IsMaximalOrderAlong N 𝔞 μ) : IsMaximalOrderAlong N (homogenizedIdealAlong N 𝔞 μ) μ :=
  fun x hx => h x (cosupport_subset_of_le (le_homogenizedIdealAlong h𝔞 hμ) _ hx)

/-- The mark of `𝓒_N(𝔪)` is the exponent of its last summand `(𝓓_N^{d-1} 𝔞)^{μ_𝓒}`. -/
theorem coeffMarkedAlong_d {𝔪 : MarkedIdeal n M} (hd : 1 ≤ 𝔪.d) :
    (coeffMarkedAlong 𝔪).d = sumExp (fun j => 𝔪.d - j) 𝔪.d (𝔪.d - 1) := by
  have := mul_sumExp (fun j => 𝔪.d - j) (show 𝔪.d - 1 < 𝔪.d by omega)
  simp only [show 𝔪.d - (𝔪.d - 1) = 1 by omega, one_mul] at this
  exact this.symm

/-- **`𝓒_N` keeps the maximal order at a point**: at `x ∈ N` with `ord_x(𝔞|_N) ≤ d`, `ord_x(𝓒_N(𝔪)|_N) ≤ μ_𝓒`
(`N` regular at its points, `d ≥ 1`).  Some `g ∈ 𝓓_N^{d-1}(𝔞)_x` has `ord_x(g|_N) ≤ 1`, and `g^{μ_𝓒}` is a germ of the last
summand. -/
theorem not_orderGE_coeffMarkedAlong {𝔪 : MarkedIdeal n M} (hN : ∀ x ∈ 𝔪.N, ∃ k, RegularAtDim (n := n) 𝔪.N x k)
    (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x) (hd : 1 ≤ 𝔪.d) {x : M} (hxN : x ∈ 𝔪.N)
    (hmax : ¬ OrderGE n 𝔪.N 𝔪.ideal x (𝔪.d + 1)) :
    ¬ OrderGE n 𝔪.N (coeffMarkedAlong 𝔪).ideal x ((coeffMarkedAlong 𝔪).d + 1) := by
  set T := iterDerivIdealAlong 𝔪.N 𝔪.ideal (𝔪.d - 1) with hT
  -- `ord_x(T|_N) ≤ 1`, by Giraud--Villamayor along `N`
  have hx2 : ¬ OrderGE n 𝔪.N T x 2 := by
    intro h2
    have hc : x ∈ cosupport n 𝔪.N T 2 := ⟨hxN, h2⟩
    rw [← cosupport_add_eq_cosupport_iterDerivIdealAlong h𝔞 hN (𝔪.d - 1) (by omega : 1 ≤ 2),
      show 2 + (𝔪.d - 1) = 𝔪.d + 1 by omega] at hc
    exact hmax hc.2
  obtain ⟨g, hg, hgno⟩ : ∃ g, T.mem x g ∧ ¬ VanishesToOrderOn n 𝔪.N x 2 g := by
    by_contra! hall
    exact hx2 hall
  have hghol : HolomorphicAt n g x := holomorphicAt_of_mem_iterDerivIdealAlong h𝔞 (𝔪.d - 1) x g hg
  obtain ⟨k, hk⟩ := hN x hxN
  set e := sumExp (fun j => 𝔪.d - j) 𝔪.d (𝔪.d - 1) with he
  have hpow : (idealPow (derivMarkedAlong 𝔪 (𝔪.d - 1)).ideal e).mem x (fun p => g p ^ e) :=
    OrderMultiplicativity.pow_mem_idealPow hg hghol e
  have hmem : (coeffMarkedAlong 𝔪).ideal.mem x (fun p => g p ^ e) :=
    (InvertibleIdealQuotient.isInSpanAt_self
      (S := fun s => ∃ i, i < 𝔪.d ∧ (idealPow (derivMarkedAlong 𝔪 i).ideal
        (sumExp (fun j => (derivMarkedAlong 𝔪 j).d) 𝔪.d i)).mem x s)
      ⟨𝔪.d - 1, by omega, hpow⟩ (holomorphicAt_of_mem_idealPow hpow) : IsInSpanAt (n := n) _ x _)
  intro hge
  have hv := hge _ hmem
  rw [coeffMarkedAlong_d hd, ← he, show e + 1 = e * 1 + 1 by omega] at hv
  exact not_vanishesToOrderOn_pow hk hghol (o := 1) hgno e hv

/-- **`𝓒_N(𝔪)` is of maximal order along `N` when `𝔪` is** (`N` regular at its points, `d ≥ 1`), with its mark `μ_𝓒`. -/
theorem IsMaximalOrderAlong.coeffMarkedAlong {𝔪 : MarkedIdeal n M}
    (hN : ∀ x ∈ 𝔪.N, ∃ k, RegularAtDim (n := n) 𝔪.N x k) (h𝔞 : ∀ x g, 𝔪.ideal.mem x g → HolomorphicAt n g x)
    (hd : 1 ≤ 𝔪.d) (h : IsMaximalOrderAlong 𝔪.N 𝔪.ideal 𝔪.d) :
    IsMaximalOrderAlong 𝔪.N (coeffMarkedAlong 𝔪).ideal (coeffMarkedAlong 𝔪).d :=
  fun x hx => not_orderGE_coeffMarkedAlong hN h𝔞 hd hx.1 (fun hge => h x ⟨hx.1, hge⟩) hx.2

end MaximalOrder

/-! ### Étale invariance -/

section Pullback

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']
  {φ : M' → M}

theorem pullback_tangentIdealAlong (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (μ : ℕ) :
    GermIdeal.pullback (m := n) φ (tangentIdealAlong N 𝔞 μ) =
      tangentIdealAlong (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) μ :=
  pullback_iterDerivIdealAlong hloc h𝔞 (μ - 1)

/-- **`𝓗_N` commutes with pullback by a holomorphic local biholomorphism**: `φ^*𝓗_N(𝔞) = 𝓗_{φ⁻¹N}(φ^*𝔞)`
(`𝔞` coherent, `N` a closed submanifold, `μ ≥ 1`). -/
theorem pullback_homogenizedIdealAlong (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
    (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y) (h𝔞 : 𝔞.IsCoherent) (hN : IsClosedSubmanifold n N)
    {μ : ℕ} (hμ : 1 ≤ μ) :
    GermIdeal.pullback (m := n) φ (homogenizedIdealAlong N 𝔞 μ) =
      homogenizedIdealAlong (φ ⁻¹' N) (GermIdeal.pullback (m := n) φ 𝔞) μ := by
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  unfold homogenizedIdealAlong
  rw [pullback_homSum hφ (fun i => isCoherent_iterDerivIdealAlong h𝔞 hN i) (isCoherent_tangentIdealAlong h𝔞 hN μ) hμ]
  exact homSum_congr (fun i _ => pullback_iterDerivIdealAlong hloc hhol i) (pullback_tangentIdealAlong hloc hhol μ)

/-- **`𝓒_N` commutes with pullback by a holomorphic local biholomorphism**: `φ^*𝓒_N(𝔪) = 𝓒_{φ⁻¹N}(φ^*𝔪)`
(`𝔞` coherent, `N` a closed submanifold, `d ≥ 1`). -/
theorem pullback_coeffMarkedAlong (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
    (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y) (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n 𝔪.N) (hd : 1 ≤ 𝔪.d) :
    MarkedIdeal.pullback φ (coeffMarkedAlong 𝔪) = coeffMarkedAlong (MarkedIdeal.pullback φ 𝔪) := by
  have hhol := MarkedIdealOperationsAlong.MarkedIdeal.hol_of_isCoherent h𝔞
  refine MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl ?_ rfl
  show GermIdeal.pullback (m := n) φ (finSumIdeal (fun i => idealPow (iterDerivIdealAlong 𝔪.N 𝔪.ideal i)
      (sumExp (fun j => 𝔪.d - j) 𝔪.d i)) 𝔪.d) =
    finSumIdeal (fun i => idealPow (iterDerivIdealAlong (φ ⁻¹' 𝔪.N) (GermIdeal.pullback (m := n) φ 𝔪.ideal) i)
      (sumExp (fun j => 𝔪.d - j) 𝔪.d i)) 𝔪.d
  rw [pullback_finSumIdeal hφ (fun i => isCoherent_idealPow (isCoherent_iterDerivIdealAlong h𝔞 hN i) _) hd]
  refine finSumIdeal_congr fun i _ => ?_
  rw [BlowupExceptionalDivisor.pullback_idealPow hφ (isCoherent_iterDerivIdealAlong h𝔞 hN i),
    pullback_iterDerivIdealAlong hloc hhol i]

/-- **`𝓗_N` commutes with pullback by a holomorphic local biholomorphism**, marked form. -/
theorem pullback_homMarkedAlong (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
    (hloc : ∀ y : M', ∃ ψ : M → M', IsLocalInverseAt n φ ψ y) (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n 𝔪.N) (hd : 1 ≤ 𝔪.d) :
    MarkedIdeal.pullback φ (homMarkedAlong 𝔪) = homMarkedAlong (MarkedIdeal.pullback φ 𝔪) :=
  MarkedIdealOperationsTransform.MarkedIdeal.ext_of rfl rfl (pullback_homogenizedIdealAlong hφ hloc h𝔞 hN hd) rfl

/-! #### Biholomorphisms -/

variable {ψ : M → M'}

theorem isLocalInverseAt_of_contMDiff (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
    (hψ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ) (hφψ : ∀ x, φ (ψ x) = x)
    (hψφ : ∀ p, ψ (φ p) = p) (y : M') : IsLocalInverseAt n φ ψ y :=
  isLocalInverseAt_of_inverse (fun p => (hφ p).mdifferentiableAt (by simp))
    (fun x => (hψ x).mdifferentiableAt (by simp)) hφψ hψφ y

/-- **`𝓒_N` commutes with biholomorphisms.** -/
theorem pullback_coeffMarkedAlong_of_inverse
    (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
    (hψ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ) (hφψ : ∀ x, φ (ψ x) = x)
    (hψφ : ∀ p, ψ (φ p) = p) (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔪.N)
    (hd : 1 ≤ 𝔪.d) :
    MarkedIdeal.pullback φ (coeffMarkedAlong 𝔪) = coeffMarkedAlong (MarkedIdeal.pullback φ 𝔪) :=
  pullback_coeffMarkedAlong hφ (fun y => ⟨ψ, isLocalInverseAt_of_contMDiff hφ hψ hφψ hψφ y⟩) 𝔪 h𝔞 hN hd

/-- **`𝓗_N` commutes with biholomorphisms**, marked form. -/
theorem pullback_homMarkedAlong_of_inverse
    (hφ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ φ)
    (hψ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ ψ) (hφψ : ∀ x, φ (ψ x) = x)
    (hψφ : ∀ p, ψ (φ p) = p) (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent) (hN : IsClosedSubmanifold n 𝔪.N)
    (hd : 1 ≤ 𝔪.d) :
    MarkedIdeal.pullback φ (homMarkedAlong 𝔪) = homMarkedAlong (MarkedIdeal.pullback φ 𝔪) :=
  pullback_homMarkedAlong hφ (fun y => ⟨ψ, isLocalInverseAt_of_contMDiff hφ hψ hφψ hψφ y⟩) 𝔪 h𝔞 hN hd

end Pullback

/-! ### Restriction to an open set -/

section OpenRestriction

variable (U : TopologicalSpace.Opens M)

/-- **`𝓒_N` commutes with restriction to an open set.** -/
theorem pullback_val_coeffMarkedAlong (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n 𝔪.N) (hd : 1 ≤ 𝔪.d) :
    MarkedIdeal.pullback (Subtype.val : U → M) (coeffMarkedAlong 𝔪) =
      coeffMarkedAlong (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪) :=
  pullback_coeffMarkedAlong contMDiff_subtype_val (fun y => ⟨openInv U y, isLocalInverseAt_val U y⟩) 𝔪 h𝔞 hN hd

/-- **`𝓗_N` commutes with restriction to an open set**, marked form. -/
theorem pullback_val_homMarkedAlong (𝔪 : MarkedIdeal n M) (h𝔞 : 𝔪.ideal.IsCoherent)
    (hN : IsClosedSubmanifold n 𝔪.N) (hd : 1 ≤ 𝔪.d) :
    MarkedIdeal.pullback (Subtype.val : U → M) (homMarkedAlong 𝔪) =
      homMarkedAlong (MarkedIdeal.pullback (Subtype.val : U → M) 𝔪) :=
  pullback_homMarkedAlong contMDiff_subtype_val (fun y => ⟨openInv U y, isLocalInverseAt_val U y⟩) 𝔪 h𝔞 hN hd

end OpenRestriction

end

end Hironaka.HomogenizedIdealAlong
