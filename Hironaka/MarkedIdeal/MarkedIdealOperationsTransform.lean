/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.MarkedIdealGeoTransform
import Hironaka.Invariant.OrderMultiplicativity
import Hironaka.Blowup.BlowupSequences
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.MarkedIdeal.DerivativeIdeal
import Hironaka.MarkedIdeal.GermIdealOrder
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Invariant.IdealOrderArithmetic
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.MarkedIdeal.MarkedIdeals
import Hironaka.Blowup.NormalCrossings
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.MarkedIdeal.RestrictedIdealExtension
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Sums and products of marked ideals under admissible blowups

Source: Włodarczyk 2005 §2.9, the operations `(𝓘, μ) + (𝓙, ν) = (𝓘^ν + 𝓙^μ, μν)` and `(𝓘, μ) · (𝓙, ν) = (𝓘𝓙, μ + ν)`
and Lemma `le:operations` (the transform half; the cosupport half is `IdealOrderArithmetic` /
`OrderMultiplicativity`).

## Controlled transforms (`BlowupControlledTransform.controlledTransform`, `σ^c(𝔞, μ) = 𝓘_D^{-μ} π^*𝔞`)

For coherent `𝔞 ⊆ 𝓘_C^μ` and `𝔟 ⊆ 𝓘_C^ν`:

## Marked ideals with `N = M` (corrected transform `MarkedIdeal.geoTransform`)

* `MarkedIdeal.add` (`(𝓘^ν + 𝓙^μ, μν)`) and `MarkedIdeal.mul` (`(𝓘𝓙, μ + ν)`), on `N`, `E` of the first;
* (Le:operations (1)--(2) of Włodarczyk for two summands / factors, `N = M`, same `E`, marks `≥ 1` for the sum.)
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.MarkedIdealOperationsTransform

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.GermIdealOrder Hironaka.IdealWeightPowers Hironaka.RestrictedIdealExtension Hironaka.GermIdealTotalTransform Hironaka.GermIdealPullbackCalculus Hironaka.BlowupExceptionalDivisor Hironaka.BlowupControlledTransform Hironaka.IdealOrderArithmetic Hironaka.BlowupTowers Hironaka.MarkedIdeals

noncomputable section

/-! ### Ideal algebra -/

section Algebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **`(𝔞^μ)^k = 𝔞^{μk}`** for a coherent ideal. -/
theorem idealPow_idealPow {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (μ : ℕ) :
    ∀ k : ℕ, idealPow (idealPow 𝔞 μ) k = idealPow 𝔞 (μ * k)
  | 0 => by rw [Nat.mul_zero, idealPow_zero, idealPow_zero]
  | k + 1 => by
      rw [idealPow_succ, idealPow_idealPow h𝔞 μ k, Nat.mul_succ,
        RestrictLeCalculus.idealPow_add h𝔞]

/-- **`𝔩(𝔞 + 𝔟) = 𝔩𝔞 + 𝔩𝔟`.** -/
theorem mul_sumIdeal {𝔩 𝔞 𝔟 : GermIdeal n M} (h𝔩 : ∀ x g, 𝔩.mem x g → HolomorphicAt n g x)
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) :
    𝔩.mul (sumIdeal 𝔞 𝔟) = sumIdeal (𝔩.mul 𝔞) (𝔩.mul 𝔟) := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · refine mem_sumIdeal_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.trans ?_ (mem_mul_iff.mp hg))
    rintro s ⟨l, t, hl, ht, rfl⟩
    obtain ⟨-, K, r, c, hr, hc, hsum⟩ := mem_sumIdeal_iff.mp ht
    have hlhol := h𝔩 x l hl
    have hrhol : ∀ k, HolomorphicAt n (r k) x := fun k => (hr k).elim (h𝔞 x _) (h𝔟 x _)
    have heq : (fun p => ∑ k, c k p * (l p * r k p)) =ᶠ[𝓝 x] l * t := by
      filter_upwards [hsum] with p hp
      simp only [Pi.mul_apply, hp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    refine DerivativeIdeal.isInSpanAt_congr
      (RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun k _ => ?_) heq
    refine RelativePrincipalizationSpan.IsInSpanAt.mul_left (hc k) ?_
    rcases hr k with hrk | hrk
    · exact InvertibleIdealQuotient.isInSpanAt_self
        (S := fun s => (𝔩.mul 𝔞).mem x s ∨ (𝔩.mul 𝔟).mem x s)
        (Or.inl (mul_mem_mul hl hrk (hlhol.mul (hrhol k)))) (hlhol.mul (hrhol k))
    · exact InvertibleIdealQuotient.isInSpanAt_self
        (S := fun s => (𝔩.mul 𝔞).mem x s ∨ (𝔩.mul 𝔟).mem x s)
        (Or.inr (mul_mem_mul hl hrk (hlhol.mul (hrhol k)))) (hlhol.mul (hrhol k))
  · refine mem_mul_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.trans ?_ (mem_sumIdeal_iff.mp hg))
    rintro s (hs | hs)
    · exact (mem_mul_iff.mp hs).mono fun _ ⟨l, a, hl, ha, h⟩ =>
        ⟨l, a, hl, le_sumIdeal_left' h𝔞 x a ha, h⟩
    · exact (mem_mul_iff.mp hs).mono fun _ ⟨l, b, hl, hb, h⟩ =>
        ⟨l, b, hl, le_sumIdeal_right' h𝔟 x b hb, h⟩

variable {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- **`f^*(𝔞 + 𝔟) = f^*𝔞 + f^*𝔟`** for ideals of holomorphic germs and a holomorphic map `f`. -/
theorem pullback_sumIdeal {f : Y → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f) {𝔞 𝔟 : GermIdeal n M}
    (h𝔞 : ∀ x g, 𝔞.mem x g → HolomorphicAt n g x) (h𝔟 : ∀ x g, 𝔟.mem x g → HolomorphicAt n g x) :
    GermIdeal.pullback (m := n) f (sumIdeal 𝔞 𝔟) =
      sumIdeal (GermIdeal.pullback (m := n) f 𝔞) (GermIdeal.pullback (m := n) f 𝔟) := by
  have hfat : ∀ {y : Y}, ∀ᶠ y' in 𝓝 y, ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f y' :=
    Eventually.of_forall fun _ => hf.contMDiffAt
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · refine mem_sumIdeal_iff.mpr (RelativePrincipalizationSpan.IsInSpanAt.trans ?_
      (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hg))
    rintro s ⟨a, ha, rfl⟩
    obtain ⟨-, K, r, c, hr, hc, hsum⟩ := mem_sumIdeal_iff.mp ha
    have heq : (fun p => ∑ k, (c k ∘ f) p * (r k ∘ f) p) =ᶠ[𝓝 y] a ∘ f :=
      ((hf.continuous.tendsto y).eventually hsum).mono fun p hp => hp.symm
    refine DerivativeIdeal.isInSpanAt_congr
      (RelativePrincipalizationSpan.IsInSpanAt.sum Finset.univ fun k _ => ?_) heq
    refine RelativePrincipalizationSpan.IsInSpanAt.mul_left ((hc k).comp_contMDiff hfat) ?_
    rcases hr k with hrk | hrk
    · refine InvertibleIdealQuotient.isInSpanAt_self (Or.inl ?_)
        ((h𝔞 _ _ hrk).comp_contMDiff hfat)
      exact RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
        (InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f)
          ⟨r k, hrk, rfl⟩ ((h𝔞 _ _ hrk).comp_contMDiff hfat))
    · refine InvertibleIdealQuotient.isInSpanAt_self (Or.inr ?_)
        ((h𝔟 _ _ hrk).comp_contMDiff hfat)
      exact RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
        (InvertibleIdealQuotient.isInSpanAt_self (S := fun s => ∃ a, 𝔟.mem (f y) a ∧ s = a ∘ f)
          ⟨r k, hrk, rfl⟩ ((h𝔟 _ _ hrk).comp_contMDiff hfat))
  · refine RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mpr
      (RelativePrincipalizationSpan.IsInSpanAt.trans ?_ (mem_sumIdeal_iff.mp hg))
    rintro s (hs | hs)
    · exact (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hs).mono
        fun _ ⟨a, ha, h⟩ => ⟨a, le_sumIdeal_left' h𝔞 _ a ha, h⟩
    · exact (RelativePrincipalizationSpan.GermIdeal.mem_pullback_iff.mp hs).mono
        fun _ ⟨b, hb, h⟩ => ⟨b, le_sumIdeal_right' h𝔟 _ b hb, h⟩

end Algebra

/-! ### Sums and products of marked ideals -/

namespace MarkedIdeal

open MarkedIdeals.MarkedIdeal

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]

/-- **The sum of marked ideals** (Włodarczyk §2.9): `(𝓘, μ) + (𝓙, ν) = (𝓘^ν + 𝓙^μ, μν)`, on `N` and `E` of the
first. -/
def add (𝔪₁ 𝔪₂ : MarkedIdeal n M) : MarkedIdeal n M where
  N := 𝔪₁.N
  E := 𝔪₁.E
  ideal := sumIdeal (idealPow 𝔪₁.ideal 𝔪₂.d) (idealPow 𝔪₂.ideal 𝔪₁.d)
  d := 𝔪₁.d * 𝔪₂.d

/-- **The product of marked ideals** (Włodarczyk §2.9): `(𝓘, μ) · (𝓙, ν) = (𝓘𝓙, μ + ν)`, on `N` and `E` of
the first. -/
def mul (𝔪₁ 𝔪₂ : MarkedIdeal n M) : MarkedIdeal n M where
  N := 𝔪₁.N
  E := 𝔪₁.E
  ideal := 𝔪₁.ideal.mul 𝔪₂.ideal
  d := 𝔪₁.d + 𝔪₂.d

variable [IsComplexManifold n M]

/-- The cosupport of a product contains the intersection of the cosupports. -/
theorem inter_cosupp_subset_cosupp_mul {𝔪₁ 𝔪₂ : MarkedIdeal n M} (hN : 𝔪₁.N = 𝔪₂.N) :
    𝔪₁.cosupp ∩ 𝔪₂.cosupp ⊆ (mul 𝔪₁ 𝔪₂).cosupp := by
  simp only [MarkedIdeals.MarkedIdeal.cosupp, mul]
  rw [← hN] at *
  exact inter_cosupport_subset_cosupport_mul _ _

/-- Marked ideals with the same four fields are equal. -/
theorem ext_of {𝔪 𝔫 : MarkedIdeal n M} (hN : 𝔪.N = 𝔫.N) (hE : 𝔪.E = 𝔫.E) (hI : 𝔪.ideal = 𝔫.ideal)
    (hd : 𝔪.d = 𝔫.d) : 𝔪 = 𝔫 := by
  cases 𝔪; cases 𝔫; simp_all

variable {M' : Type u} [TopologicalSpace M'] [ChartedSpace (ComplexModel n) M'] [IsComplexManifold n M']

/-- **A centre admissible for both factors is admissible for the product** (same `N`). -/
theorem IsAdmissibleCentre.mul {𝔪₁ 𝔪₂ : MarkedIdeal n M} (hN : 𝔪₁.N = 𝔪₂.N) {C : Set M}
    (hC₁ : 𝔪₁.IsAdmissibleCentre C) (hC₂ : 𝔪₂.IsAdmissibleCentre C) :
    (mul 𝔪₁ 𝔪₂).IsAdmissibleCentre C :=
  ⟨hC₁.1, (subset_inter hC₁.2.1 hC₂.2.1).trans (inter_cosupp_subset_cosupp_mul hN), hC₁.2.2⟩

end MarkedIdeal

end

end Hironaka.MarkedIdealOperationsTransform
