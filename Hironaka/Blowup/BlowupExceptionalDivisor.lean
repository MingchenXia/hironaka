/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.MarkedIdeal.GermIdealTotalTransform
import Hironaka.MarkedIdeal.RestrictLeCalculus
import Hironaka.Blowup.BlowupIsomorphismOff
import Hironaka.Blowup.ExceptionalFibres
import Hironaka.Blowup.BlowupSequences
import Hironaka.Analytic.ComplexAnalyticSubvarieties
import Hironaka.Manifold.ComplexManifold
import Hironaka.Analytic.HolomorphicIdealSheaves
import Hironaka.Analytic.InvertibleIdealCoherent
import Hironaka.MarkedIdeal.GermIdealPullbackCalculus
import Hironaka.Analytic.HolomorphicGermAlgebra
import Hironaka.Analytic.IdealPowers
import Hironaka.MarkedIdeal.InvertibleIdealQuotient
import Hironaka.Analytic.IdealSpanCalculus
import Hironaka.Coherence.VanishingIdealCoherent
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The exceptional divisor of a blowup

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.1 (the exceptional divisor `D_i` of `σ_i` and its ideal
`𝓘(D_i)`); Bierstone--Milman 2008 (`bierstone-milman08-functoriality`), §2.

Let `π : Y → X` be the blowup of `X` along the nowhere dense closed submanifold `C`
(`IsBlowupAlong`).  By the universal property `π^* 𝓘_C = 𝓘_C 𝒪_Y` is invertible, so it is the
ideal `𝒪_Y(-D)` of an effective divisor `D`, the **exceptional divisor**.  This module records

* `exceptionalDivisor hπ` — the effective divisor with ideal `π^* 𝓘_C`;
* `support_exceptionalDivisor` — its support is `π⁻¹ C`;
* `interior_exceptionalLocus_eq_empty` — `Exc π` has empty interior, which is what makes total
  transforms of divisors along `π` defined (`GermIdealTotalTransform.EffectiveDivisor.totalTransform`);
* `pullback_idealPow_vanishingIdeal` — `π^* (𝓘_C^μ) = 𝒪_Y(-μ D)`.

Together with the small ideal calculus it needs (`isInvertible_unitIdeal`,
`isInvertible_idealPow`, `pullback_unitIdeal`, `pullback_idealPow`, `zeroLocus_pullback`,
`zeroLocus_vanishingIdeal`).

The ideal lemmas below therefore re-prove, in a few lines each, statements that exist in modules inside that
closure.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupExceptionalDivisor

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences GermIdealTotalTransform GermIdealPullbackCalculus IdealWeightPowers InvertibleIdealQuotient RelativePrincipalizationSpan

noncomputable section

/-! ### Ideal calculus -/

section Ideals

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The unit ideal is invertible, with generator `1`. -/
theorem isInvertible_unitIdeal : (unitIdeal n M).IsInvertible := by
  intro x
  refine ⟨univ, isOpen_univ, mem_univ x, (1 : M → ℂ),
    (mdifferentiable_const (I := 𝓘(ℂ, ComplexModel n)) (I' := 𝓘(ℂ, ℂ))
      (c := (1 : ℂ))).mdifferentiableOn,
    fun W _ _ hW => ?_, fun y _ g => ?_⟩
  · obtain ⟨y, hy⟩ := hW
    exact ⟨y, hy, by simp⟩
  · rw [mem_unitIdeal_iff]
    constructor
    · exact IsInSpanAt.mono fun s ⟨i, hi⟩ => hi.symm
    · exact IsInSpanAt.mono fun s hs => ⟨0, hs.symm⟩

/-- Powers of an invertible ideal are invertible. -/
theorem isInvertible_idealPow {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsInvertible) :
    ∀ q : ℕ, (idealPow 𝔞 q).IsInvertible
  | 0 => isInvertible_unitIdeal
  | q + 1 => isInvertible_mul (isInvertible_idealPow h𝔞 q) h𝔞

/-- The ideal of an effective divisor is coherent. -/
theorem isCoherent_ideal (D : EffectiveDivisor n M) : D.ideal.IsCoherent :=
  DivisorMetric.isCoherent_of_isInvertible D.isInvertible

/-- **`Z(𝓘_A) = A`** for a closed set `A`: off `A` the constant `1` lies in `𝓘_A`. -/
theorem zeroLocus_vanishingIdeal {A : Set M} (hA : IsClosed A) :
    (vanishingIdeal (n := n) A).zeroLocus = A := by
  ext x
  constructor
  · intro hx
    by_contra hxA
    have hmem : (vanishingIdeal (n := n) A).mem x (fun _ => (1 : ℂ)) := by
      refine ⟨holomorphicAt_const 1, ?_⟩
      filter_upwards [hA.isOpen_compl.mem_nhds hxA] with y hy hyA
      exact absurd hyA hy
    exact one_ne_zero (hx _ hmem)
  · intro hx g hg
    exact hg.2.self_of_nhds hx

variable {m : ℕ} {Y : Type*} [TopologicalSpace Y] [ChartedSpace (ComplexModel m) Y]
  [IsComplexManifold m Y]

/-- **`Z(𝔞 𝒪_Y) = f⁻¹ Z(𝔞)`** for a coherent ideal `𝔞` and a holomorphic map `f`. -/
theorem zeroLocus_pullback {f : Y → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    (GermIdeal.pullback (m := m) f 𝔞).zeroLocus = f ⁻¹' 𝔞.zeroLocus := by
  ext y
  constructor
  · intro hy
    by_contra hfy
    obtain ⟨b, hb, hby⟩ : ∃ b, 𝔞.mem (f y) b ∧ b (f y) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hfy hcon
    have hcomp : HolomorphicAt m (b ∘ f) y :=
      (GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hb).comp_contMDiff
        (Eventually.of_forall fun y' => hf y')
    have hmem : (GermIdeal.pullback (m := m) f 𝔞).mem y (b ∘ f) :=
      isInSpanAt_self (S := fun s => ∃ a, 𝔞.mem (f y) a ∧ s = a ∘ f) ⟨b, hb, rfl⟩ hcomp
    exact hby (hy (b ∘ f) hmem)
  · intro hy g hg
    obtain ⟨-, K, s, a, hs, -, hsum⟩ := hg
    rw [hsum.self_of_nhds]
    refine Finset.sum_eq_zero fun k _ => ?_
    obtain ⟨b, hb, hbk⟩ := hs k
    rw [hbk, Function.comp_apply, hy b hb, mul_zero]

end Ideals

section SameDim

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y]

/-- The pullback of the unit ideal is the unit ideal. -/
theorem pullback_unitIdeal {f : Y → M} :
    GermIdeal.pullback (m := n) f (unitIdeal n M) = unitIdeal n Y := by
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => hg.1, fun hg => ?_⟩)
  exact isInSpanAt_of_eq_mul (S := fun s => ∃ a, (unitIdeal n M).mem (f y) a ∧ s = a ∘ f)
    (s := fun _ => (1 : ℂ)) (a := g)
    ⟨fun _ => (1 : ℂ), holomorphicAt_const 1, rfl⟩ hg hg (Eventually.of_forall fun _ => by simp)

/-- **The pullback of a power is the power of the pullback**, for a coherent ideal. -/
theorem pullback_idealPow {f : Y → M}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    ∀ q : ℕ, GermIdeal.pullback (m := n) f (idealPow 𝔞 q) =
      idealPow (GermIdeal.pullback (m := n) f 𝔞) q
  | 0 => pullback_unitIdeal
  | q + 1 => by
      rw [idealPow_succ, idealPow_succ, pullback_mul hf (isCoherent_idealPow h𝔞 q) h𝔞,
        pullback_idealPow hf h𝔞 q]

end SameDim

/-! ### The exceptional divisor -/

section Blowup

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- The exceptional locus of a blowup has empty interior. -/
theorem interior_exceptionalLocus_eq_empty (hπ : IsBlowupAlong n C π) :
    interior (exceptionalLocus n π) = ∅ :=
  subset_empty_iff.mp
    ((interior_mono (BlowupIsomorphismOff.exceptionalLocus_subset_preimage hπ)).trans
      (ExceptionalFibres.interior_preimage_eq_empty hπ).subset)

/-- The ideal `𝓘_C` of the centre is coherent. -/
theorem isCoherent_vanishingIdeal_centre (hπ : IsBlowupAlong n C π) :
    (vanishingIdeal (n := n) C).IsCoherent :=
  VanishingIdealCoherent.isCoherent_vanishingIdeal hπ.1

/-- **The exceptional divisor** `D` of the blowup `π` along `C`: the effective divisor whose
ideal `𝒪_Y(-D)` is `π^* 𝓘_C = 𝓘_C 𝒪_Y`, invertible by the universal property. -/
def exceptionalDivisor (hπ : IsBlowupAlong n C π) : EffectiveDivisor n Y where
  ideal := GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C)
  isInvertible := hπ.2.2.2.1

@[simp] theorem exceptionalDivisor_ideal (hπ : IsBlowupAlong n C π) :
    (exceptionalDivisor hπ).ideal = GermIdeal.pullback (m := n) π (vanishingIdeal (n := n) C) :=
  rfl

/-- **The support of the exceptional divisor is `π⁻¹ C`.** -/
theorem support_exceptionalDivisor (hπ : IsBlowupAlong n C π) :
    (exceptionalDivisor hπ).support = π ⁻¹' C := by
  rw [EffectiveDivisor.support, exceptionalDivisor_ideal,
    zeroLocus_pullback hπ.contMDiff (isCoherent_vanishingIdeal_centre hπ),
    zeroLocus_vanishingIdeal hπ.1.1]

/-- **`π^*(𝓘_C^μ) = 𝒪_Y(-μ D)`.** -/
theorem pullback_idealPow_vanishingIdeal (hπ : IsBlowupAlong n C π) (μ : ℕ) :
    GermIdeal.pullback (m := n) π (idealPow (vanishingIdeal (n := n) C) μ) =
      idealPow (exceptionalDivisor hπ).ideal μ :=
  pullback_idealPow hπ.contMDiff (isCoherent_vanishingIdeal_centre hπ) μ

/-- The total transform of an effective divisor along a blowup. -/
abbrev totalTransform (hπ : IsBlowupAlong n C π) (D : EffectiveDivisor n X) :
    EffectiveDivisor n Y :=
  EffectiveDivisor.totalTransform hπ.contMDiff (interior_exceptionalLocus_eq_empty hπ) D

/-- **The support of a total transform along a blowup is the preimage of the support.** -/
theorem support_totalTransform (hπ : IsBlowupAlong n C π) (D : EffectiveDivisor n X) :
    (totalTransform hπ D).support = π ⁻¹' D.support :=
  zeroLocus_pullback hπ.contMDiff (isCoherent_ideal D)

end Blowup

end

end Hironaka.BlowupExceptionalDivisor
