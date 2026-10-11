/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Invariant.DivisorExponent
import Hironaka.Invariant.AmbientDivisorExponent
import Hironaka.Invariant.DivisorExponentAlong
import Hironaka.Invariant.CompanionReduction

set_option autoImplicit false

/-!
# Genuine ideal powers scale divisor exponents

The exponent is the existing neighbourhood-divisibility exponent `divExp`,
and the power is the existing stalkwise product power `idealPow`.
The successor-threshold calculation supplies an upper bound, in addition
to the lower bound supplied by products.  No multiplicity identity is an
input.  Blueprint: `hironaka-divisor-extension.tex`.

Source relation: Włodarczyk 2005, Step 2 decomposes the monomial factor into
principal divisor ideals.  The results here are local algebra needed to
track their multiplicities; they do not construct that global decomposition.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaDivisorPowers

open Hironaka.HolomorphicIdealSheaves
open Hironaka.IdealWeightPowers
  Hironaka.GermIdealOrder
  Hironaka.IdealOrderArithmetic
  Hironaka.OrderMultiplicativity
  Hironaka.HadamardBridge
  Hironaka.OrderTaylor
  Hironaka.DivisorExponent
  Hironaka.DivisorExponentAlong
  Hironaka.CompanionReduction

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  {𝔞 : GermIdeal n M}

/-- The strict threshold above `k * e` for a genuine ideal power is exactly
the strict threshold above `e` for the original ideal. -/
theorem cosupport_idealPow_mul_succ_eq
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    {k : ℕ} (hk : 1 ≤ k) (e : ℕ) :
    cosupport n univ (idealPow 𝔞 k) (k * e + 1) =
      cosupport n univ 𝔞 (e + 1) := by
  apply Subset.antisymm
  · intro x hx
    by_contra hno
    obtain ⟨g, hg, hgn⟩ := exists_notMem_idealPow_of_notMem_cosupport hno
    exact pow_notMem_idealPow (h𝔞 x g hg) hgn k
      (mem_idealPow_of_vanishesToOrderOn_univ
        (hx.2 _ (OrderMultiplicativity.pow_mem_idealPow hg (h𝔞 x g hg) k)))
  · intro x hx
    apply cosupport_anti (show k * e + 1 ≤ (e + 1) * k by nlinarith)
    exact cosupport_subset_cosupport_idealPow (e + 1) k hx

/-- Successor divisibility thresholds of genuine powers, along any subset. -/
theorem isDivNear_idealPow_mul_succ_iff
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    {k : ℕ} (hk : 1 ≤ k) {H : Set M} (e : ℕ) (x : M) :
    IsDivNear n (idealPow 𝔞 k) H (k * e + 1) x ↔
      IsDivNear n 𝔞 H (e + 1) x := by
  unfold IsDivNear
  rw [cosupport_idealPow_mul_succ_eq h𝔞 hk e]

/-- Powers retain an actual nonzero stalk member, including the zeroth power. -/
theorem isNonzeroAt_idealPow
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    {x : M} (hne : IsNonzeroAt 𝔞 x) (k : ℕ) :
    IsNonzeroAt (idealPow 𝔞 k) x := by
  obtain ⟨g, hg, hgne⟩ := hne
  exact ⟨fun y => g y ^ k, OrderMultiplicativity.pow_mem_idealPow hg (h𝔞 x g hg) k,
    hgne.mono fun y hy => pow_ne_zero k hy⟩

/-- The existing divisor exponent of a genuine ideal power is multiplied by
the power.  The identity is produced from order arithmetic and nonvanishing. -/
theorem divExp_idealPow
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    {H : Set M} {x : M} (hx : x ∈ H) (hne : IsNonzeroAt 𝔞 x) (k : ℕ) :
    divExp n (idealPow 𝔞 k) H x = k * divExp n 𝔞 H x := by
  have hhol : ∀ y g, (idealPow 𝔞 k).mem y g → HolomorphicAt n g y :=
    fun y g hg => holomorphicAt_of_mem_idealPow hg
  have hnz := isNonzeroAt_idealPow h𝔞 hne k
  apply Nat.le_antisymm
  · by_cases hk : k = 0
    · subst k
      simp only [zero_mul]
      by_contra hno
      have hdiv := (isDivNear_divExp hhol x).mono (show 1 ≤ divExp n (idealPow 𝔞 0) H x by omega)
      have hcos := hdiv.self_of_nhds hx
      have hone : (idealPow 𝔞 0).mem x (fun _ => (1 : ℂ)) := holomorphicAt_const 1
      have hz := apply_eq_zero_of_mem_idealPow_pointIdeal le_rfl
        (mem_idealPow_of_vanishesToOrderOn_univ (hcos.2 _ hone))
      simp at hz
    · by_contra hno
      have hdiv := (isDivNear_divExp hhol x).mono
        (show k * divExp n 𝔞 H x + 1 ≤ divExp n (idealPow 𝔞 k) H x by omega)
      exact not_isDivNear_divExp_succ h𝔞 hx hne
        ((isDivNear_idealPow_mul_succ_iff h𝔞 (show 1 ≤ k by omega) _ x).mp hdiv)
  · apply (isDivNear_iff_le_divExp hhol hx hnz).mp
    filter_upwards [isDivNear_divExp h𝔞 x] with y hy hyH
    have hp := cosupport_subset_cosupport_idealPow (divExp n 𝔞 H x) k (hy hyH)
    simpa only [Nat.mul_comm] using hp

/-- Strict successor thresholds also agree in the actual restricted stalks
of a submanifold. -/
theorem cosupport_idealPow_mul_succ_eq_along
    {N : Set M} (hN : ∀ x ∈ N, ∃ d, RegularAtDim (n := n) N x d)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    {k : ℕ} (hk : 1 ≤ k) (e : ℕ) :
    cosupport n N (idealPow 𝔞 k) (k * e + 1) =
      cosupport n N 𝔞 (e + 1) := by
  apply Subset.antisymm
  · intro x hx
    refine ⟨hx.1, fun g hg => ?_⟩
    by_contra hno
    obtain ⟨d, hd⟩ := hN x hx.1
    obtain ⟨r, hr⟩ := exists_isLocalRetraction hd
    have hgn : ¬ (idealPow (pointIdeal n x) (e + 1)).mem x (g ∘ r) :=
      fun h => hno (hr.vanishesToOrderOn_iff.mpr h)
    have hp := hr.vanishesToOrderOn_iff.mp
      (hx.2 _ (OrderMultiplicativity.pow_mem_idealPow hg (h𝔞 x g hg) k))
    exact pow_notMem_idealPow (hr.holomorphicAt_comp (h𝔞 x g hg)) hgn k hp
  · intro x hx
    apply cosupport_anti (show k * e + 1 ≤ (e + 1) * k by nlinarith)
    exact cosupport_subset_cosupport_idealPow (e + 1) k hx

/-- Neighbourhood divisibility along a submanifold has the same strict
successor threshold before and after taking a genuine ideal power. -/
theorem isDivNearAlong_idealPow_mul_succ_iff
    {N : Set M} (hN : ∀ x ∈ N, ∃ d, RegularAtDim (n := n) N x d)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    {k : ℕ} (hk : 1 ≤ k) {H : Set M} (e : ℕ) (x : M) :
    IsDivNearAlong n N (idealPow 𝔞 k) H (k * e + 1) x ↔
      IsDivNearAlong n N 𝔞 H (e + 1) x := by
  unfold IsDivNearAlong
  rw [cosupport_idealPow_mul_succ_eq_along hN h𝔞 hk e]

/-- A nonzero restricted stalk supplies a nonzero restricted member of
every genuine ideal power. -/
theorem isNonzeroAlongAt_idealPow
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x)
    {N : Set M} {x : M} (hne : IsNonzeroAlongAt N 𝔞 x) (k : ℕ) :
    IsNonzeroAlongAt N (idealPow 𝔞 k) x := by
  obtain ⟨g, hg, hgne⟩ := hne
  exact ⟨fun y => g y ^ k, OrderMultiplicativity.pow_mem_idealPow hg (h𝔞 x g hg) k,
    hgne.mono fun y hy => ⟨hy.1, pow_ne_zero k hy.2⟩⟩

/-- Genuine ideal powers scale the actual divisor exponent along a
submanifold, with nonvanishing produced for the power. -/
theorem divExpAlong_idealPow
    {N : Set M} (hN : ∀ y ∈ N, ∃ d, RegularAtDim (n := n) N y d)
    (h𝔞 : ∀ y g, 𝔞.mem y g → HolomorphicAt n g y)
    {H : Set M} {x : M} (hxN : x ∈ N) (hxH : x ∈ H)
    (hne : IsNonzeroAlongAt N 𝔞 x) (k : ℕ) :
    divExpAlong n N (idealPow 𝔞 k) H x = k * divExpAlong n N 𝔞 H x := by
  obtain ⟨d, hd⟩ := hN x hxN
  obtain ⟨r, hr⟩ := exists_isLocalRetraction hd
  have hhol : ∀ y g, (idealPow 𝔞 k).mem y g → HolomorphicAt n g y :=
    fun y g hg => holomorphicAt_of_mem_idealPow hg
  have hnz := isNonzeroAlongAt_idealPow h𝔞 hne k
  apply Nat.le_antisymm
  · by_cases hk : k = 0
    · subst k
      simp only [zero_mul]
      by_contra hno
      have hdiv := (isDivNearAlong_divExpAlong hhol x).mono
        (show 1 ≤ divExpAlong n N (idealPow 𝔞 0) H x by omega)
      have hcos := hdiv.self_of_nhds hxN hxH
      have hone : (idealPow 𝔞 0).mem x (fun _ => (1 : ℂ)) := holomorphicAt_const 1
      have hz := apply_eq_zero_of_mem_idealPow_pointIdeal le_rfl
        (hr.vanishesToOrderOn_iff.mp (hcos.2 _ hone))
      simp at hz
    · by_contra hno
      have hdiv := (isDivNearAlong_divExpAlong hhol x).mono
        (show k * divExpAlong n N 𝔞 H x + 1 ≤ divExpAlong n N (idealPow 𝔞 k) H x by omega)
      exact not_isDivNearAlong_divExpAlong_succ hr hxH hne h𝔞
        ((isDivNearAlong_idealPow_mul_succ_iff hN h𝔞 (show 1 ≤ k by omega) _ x).mp hdiv)
  · apply (isDivNearAlong_iff_le_divExpAlong hr hxH hnz hhol).mp
    filter_upwards [isDivNearAlong_divExpAlong h𝔞 x] with y hy hyN hyH
    have hp := cosupport_subset_cosupport_idealPow (divExpAlong n N 𝔞 H x) k (hy hyN hyH)
    simpa only [Nat.mul_comm] using hp

/-- The local nonvanishing clause of invertibility supplies an actual
nonzero holomorphic member of every stalk. -/
theorem isNonzeroAt_of_isInvertible {𝔟 : GermIdeal n M}
    (h𝔟 : 𝔟.IsInvertible) (x : M) : IsNonzeroAt 𝔟 x := by
  obtain ⟨U, hU, hxU, g, hg, hnon, hgen⟩ := h𝔟 x
  have hghol : HolomorphicAt n g x := holomorphicAt_of_mdifferentiableOn_open hU hg hxU
  refine ⟨g, (hgen x hxU g).mpr (isInSpanAt_of_eq_mul rfl hghol
    (holomorphicAt_const 1) (Eventually.of_forall fun _ => by simp)), ?_⟩
  rw [frequently_nhds_iff]
  intro V hxV hV
  obtain ⟨y, hy, hy0⟩ := hnon (V ∩ U) (hV.inter hU) inter_subset_right ⟨x, hxV, hxU⟩
  exact ⟨y, hy.1, hy0⟩

/-- Multiplicities of genuine powers of an actual effective divisor ideal
are produced from invertibility, without a nonzero-stalk assumption. -/
theorem divExp_divisor_idealPow (D : EffectiveDivisor n M)
    {H : Set M} {x : M} (hx : x ∈ H) (k : ℕ) :
    divExp n (idealPow D.ideal k) H x = k * divExp n D.ideal H x :=
  divExp_idealPow (fun _ _ hg =>
    RelativePrincipalizationSpan.GermIdeal.IsInvertible.holomorphicAt_mem D.isInvertible hg)
    hx (isNonzeroAt_of_isInvertible D.isInvertible x) k

end

end Hironaka.HironakaDivisorPowers
