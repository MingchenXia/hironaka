import Hironaka.Blowup.BlowupExceptionalDivisor

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The controlled transform of a marked ideal under a blowup

Source: Wlodarczyk 2005 (`wlodarczyk05-hironaka`), §2.1 condition (3) of a resolution and §2.2
("Transforms of marked ideals and controlled transforms of functions", including the lemma
`𝓘 ⊆ 𝓘_C^μ`, `σ^*𝓘 ⊆ 𝓘_D^μ` that makes the transform well defined); Bierstone--Milman 2008
(`bierstone-milman08-functoriality`), §2 (`𝓘' = 𝓘_{σ⁻¹C}^{-d} σ^*𝓘`); blueprint
`bcalc:controlled-transform` (chapter `blowup-calculus.tex`).

Let `π : Y → X` be the blowup along `C` with exceptional divisor `D`
(`BlowupExceptionalDivisor.exceptionalDivisor`) and let `𝔞` be a coherent ideal with
`𝔞 ⊆ 𝓘_C^μ`.  Then `π^*𝔞 ⊆ π^*(𝓘_C^μ) = 𝒪_Y(-μD)` and, `𝒪_Y(-μD)` being invertible,

  `π^* 𝔞 = 𝒪_Y(-μD) · σ^c(𝔞, μ)`   with `σ^c(𝔞, μ)` coherent and uniquely determined.

`σ^c(𝔞, μ) = 𝓘_D^{-μ} π^*𝔞` is the **controlled transform** of the marked ideal `(𝔞, μ)`.  It is
defined here as the colon ideal `(π^*𝔞 : 𝓘_D^μ)` (`InvertibleIdealQuotient.colon`), which needs
no hypothesis; the hypothesis `𝔞 ⊆ 𝓘_C^μ` is what makes it the quotient.

In the sources the hypothesis is `C ⊆ supp(𝔞, μ) = {x : ord_x 𝔞 ≥ μ}`; that `C ⊆ supp(𝔞, μ)`
gives `𝔞 ⊆ 𝓘_C^μ` for a smooth `C` is Wlodarczyk's lemma in §2.2 (a Hadamard-type statement
about orders of germs), which belongs to the local algebra of orders (H1 of the Hironaka plan)
and is NOT used here: every statement below takes `𝔞 ⊆ 𝓘_C^μ` directly.

* `controlledTransform hπ 𝔞 μ` — the colon ideal `(π^*𝔞 : 𝓘_D^μ)`;
* `pullback_le_idealPow_exceptionalDivisor` — `𝔞 ⊆ 𝓘_C^μ ⟹ π^*𝔞 ⊆ 𝒪_Y(-μD)`;
* `pullback_eq_mul_controlledTransform` — `π^*𝔞 = 𝒪_Y(-μD) · σ^c(𝔞, μ)`;
* `isCoherent_controlledTransform`;
* `eq_controlledTransform_of_eq_mul` — uniqueness: any coherent `𝔠` with
  `π^*𝔞 = 𝒪_Y(-μD) · 𝔠` is the controlled transform (from `colon_mul_eq`, cancellation of an
  invertible ideal);
* `controlledTransform_zero` — `σ^c(𝔞, 0) = π^*𝔞`;
* the ideal algebra used along sequences of blowups: `pullback_id`, `idealPow_unitIdeal`,
  `unitIdeal_mul`, `mul_mul_mul_comm`, `idealPow_mul` (`(𝔞𝔟)^μ = 𝔞^μ 𝔟^μ`).

Everything here is sorry-free, and outside the import closure of the two Hironaka statements.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.BlowupControlledTransform

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  GermIdealTotalTransform GermIdealPullbackCalculus IdealWeightPowers InvertibleIdealQuotient
  RelativePrincipalizationSpan BlowupExceptionalDivisor

noncomputable section

/-! ### Cancellation of an invertible ideal -/

section Cancel

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- **Cancellation of an invertible ideal**: `(𝔩 𝔠 : 𝔩) = 𝔠` for `𝔩` invertible and `𝔠`
coherent. -/
theorem colon_mul_eq {𝔩 𝔠 : GermIdeal n M} (h𝔩 : 𝔩.IsInvertible) (h𝔠 : 𝔠.IsCoherent) :
    colon (𝔩.mul 𝔠) 𝔩 = 𝔠 := by
  refine GermIdeal.ext (funext fun x => funext fun f => propext ⟨fun hf => ?_, fun hf => ?_⟩)
  · obtain ⟨hfhol, hfmul⟩ := mem_colon_iff.mp hf
    obtain ⟨U, hU, hxU, h₀, hh₀d, hnon, hgen⟩ := h𝔩 x
    have hh₀ : HolomorphicAt n h₀ x := holomorphicAt_of_mdifferentiableOn hU hh₀d hxU
    have hh₀mem : 𝔩.mem x h₀ := (hgen x hxU h₀).mpr (isInSpanAt_self rfl hh₀)
    obtain ⟨-, K, u, c, hu, hc, husum⟩ := mem_mul_iff.mp (hfmul h₀ hh₀mem)
    choose p q hp hq hpq using hu
    choose e he hee using fun j => (isInSpanAt_eq_iff.mp ((hgen x hxU (p j)).mp (hp j))).2
    have hqhol : ∀ j, HolomorphicAt n (q j) x :=
      fun j => GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 (hq j)
    have hFhol : HolomorphicAt n (fun y => ∑ j, (c j y * e j y) * q j y) x :=
      HolomorphicAt.sum _ fun j _ => ((hc j).mul (he j)).mul (hqhol j)
    have hfeq : f =ᶠ[𝓝 x] fun y => ∑ j, (c j y * e j y) * q j y := by
      refine eventuallyEq_of_mul_eventuallyEq hU hnon hxU hfhol hFhol ?_
      filter_upwards [husum, eventually_all.mpr hee] with y hy hy'
      rw [hy, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hpq j]
      show c j y * (p j y * q j y) = h₀ y * (c j y * e j y * q j y)
      rw [hy' j]
      ring
    exact mem_of_isInSpanAt_mem h𝔠
      ⟨hfhol, K, q, fun j y => c j y * e j y, hq, fun j => (hc j).mul (he j), hfeq⟩
  · refine mem_colon_iff.mpr ⟨GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 hf, fun g hg => ?_⟩
    have hghol : HolomorphicAt n g x := GermIdeal.IsInvertible.holomorphicAt_mem h𝔩 hg
    exact mem_mul_of_mem_mem hg hf (hghol.mul (GermIdeal.IsCoherent.holomorphicAt_mem h𝔠 hf))

/-- The colon ideal by the unit ideal is the ideal itself, for a coherent ideal. -/
theorem colon_unitIdeal {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    colon 𝔞 (unitIdeal n M) = 𝔞 := by
  have h := colon_mul_eq (isInvertible_unitIdeal (n := n) (M := M)) h𝔞
  rwa [RestrictLeCalculus.mul_comm', RestrictLeCalculus.mul_unitIdeal h𝔞] at h

end Cancel

/-! ### Ideal algebra for powers and products -/

section Algebra

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsComplexManifold n M]

/-- The pullback along the identity is the identity on coherent ideals. -/
theorem pullback_id {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    GermIdeal.pullback (m := n) (id : M → M) 𝔞 = 𝔞 := by
  refine GermIdeal.ext (funext fun x => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · refine mem_of_isInSpanAt_mem h𝔞 (IsInSpanAt.mono ?_ (GermIdeal.mem_pullback_iff.mp hg))
    rintro s ⟨a, ha, rfl⟩
    exact ha
  · exact GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨g, hg, rfl⟩ (GermIdeal.IsCoherent.holomorphicAt_mem h𝔞 hg))

/-- Powers of the unit ideal are the unit ideal. -/
theorem idealPow_unitIdeal : ∀ μ : ℕ, idealPow (unitIdeal n M) μ = unitIdeal n M
  | 0 => rfl
  | μ + 1 => by
      rw [idealPow_succ, idealPow_unitIdeal μ,
        RestrictLeCalculus.mul_unitIdeal isCoherent_unitIdeal]

/-- The unit ideal is neutral on the left, for a coherent ideal. -/
theorem unitIdeal_mul {𝔞 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) :
    (unitIdeal n M).mul 𝔞 = 𝔞 := by
  rw [RestrictLeCalculus.mul_comm', RestrictLeCalculus.mul_unitIdeal h𝔞]

/-- `(𝔞𝔟)(𝔠𝔡) = (𝔞𝔠)(𝔟𝔡)` for coherent ideals. -/
theorem mul_mul_mul_comm {𝔞 𝔟 𝔠 𝔡 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent)
    (h𝔟 : 𝔟.IsCoherent) (h𝔠 : 𝔠.IsCoherent) (h𝔡 : 𝔡.IsCoherent) :
    (𝔞.mul 𝔟).mul (𝔠.mul 𝔡) = (𝔞.mul 𝔠).mul (𝔟.mul 𝔡) := by
  rw [mul_assoc h𝔞 h𝔟 (IdealWeightPowers.isCoherent_mul h𝔠 h𝔡),
    ← mul_assoc h𝔟 h𝔠 h𝔡, RestrictLeCalculus.mul_comm' 𝔟 𝔠, mul_assoc h𝔠 h𝔟 h𝔡,
    ← mul_assoc h𝔞 h𝔠 (IdealWeightPowers.isCoherent_mul h𝔟 h𝔡)]

/-- **`(𝔞𝔟)^μ = 𝔞^μ 𝔟^μ`** for coherent ideals. -/
theorem idealPow_mul {𝔞 𝔟 : GermIdeal n M} (h𝔞 : 𝔞.IsCoherent) (h𝔟 : 𝔟.IsCoherent) :
    ∀ μ : ℕ, idealPow (𝔞.mul 𝔟) μ = (idealPow 𝔞 μ).mul (idealPow 𝔟 μ)
  | 0 => by
      rw [idealPow_zero, idealPow_zero, idealPow_zero,
        RestrictLeCalculus.mul_unitIdeal isCoherent_unitIdeal]
  | μ + 1 => by
      rw [idealPow_succ, idealPow_succ, idealPow_succ, idealPow_mul h𝔞 h𝔟 μ,
        mul_mul_mul_comm (isCoherent_idealPow h𝔞 μ) (isCoherent_idealPow h𝔟 μ) h𝔞 h𝔟]

end Algebra

/-! ### The controlled transform -/

section Controlled

variable {n : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {Y : Type u} [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y]
  [IsComplexManifold n Y] {C : Set X} {π : Y → X}

/-- **The controlled transform** `σ^c(𝔞, μ) = 𝓘_D^{-μ} π^*𝔞` of the marked ideal `(𝔞, μ)` under
the blowup `π` along `C`, as the colon ideal `(π^*𝔞 : 𝒪_Y(-μD))`.  It is the quotient of
`π^*𝔞` by `𝒪_Y(-μD)` when `𝔞 ⊆ 𝓘_C^μ` (`pullback_eq_mul_controlledTransform`). -/
def controlledTransform (hπ : IsBlowupAlong n C π) (𝔞 : GermIdeal n X) (μ : ℕ) :
    GermIdeal n Y :=
  colon (GermIdeal.pullback (m := n) π 𝔞) (idealPow (exceptionalDivisor hπ).ideal μ)

/-- `𝒪_Y(-μD)` is invertible. -/
theorem isInvertible_idealPow_exceptionalDivisor (hπ : IsBlowupAlong n C π) (μ : ℕ) :
    (idealPow (exceptionalDivisor hπ).ideal μ).IsInvertible :=
  isInvertible_idealPow (exceptionalDivisor hπ).isInvertible μ

/-- **`𝔞 ⊆ 𝓘_C^μ ⟹ π^*𝔞 ⊆ 𝒪_Y(-μD)`** (Wlodarczyk §2.2, lemma, part (2)). -/
theorem pullback_le_idealPow_exceptionalDivisor (hπ : IsBlowupAlong n C π)
    {𝔞 : GermIdeal n X} {μ : ℕ} (hle : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) μ)) :
    (GermIdeal.pullback (m := n) π 𝔞).Le (idealPow (exceptionalDivisor hπ).ideal μ) := by
  rw [← pullback_idealPow_vanishingIdeal hπ μ]
  exact pullback_le_pullback hle

/-- **`π^*𝔞 = 𝒪_Y(-μD) · σ^c(𝔞, μ)`** for a coherent `𝔞 ⊆ 𝓘_C^μ`. -/
theorem pullback_eq_mul_controlledTransform (hπ : IsBlowupAlong n C π)
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ}
    (hle : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) μ)) :
    GermIdeal.pullback (m := n) π 𝔞 =
      (idealPow (exceptionalDivisor hπ).ideal μ).mul (controlledTransform hπ 𝔞 μ) := by
  have hcoh := isCoherent_pullback hπ.contMDiff h𝔞
  refine GermIdeal.ext (funext fun y => funext fun g => propext ⟨fun hg => ?_, fun hg => ?_⟩)
  · exact le_mul_colon hcoh (isInvertible_idealPow_exceptionalDivisor hπ μ)
      (pullback_le_idealPow_exceptionalDivisor hπ hle) y g hg
  · exact mul_colon_le hcoh y g hg

/-- **The controlled transform of a coherent marked ideal is coherent.** -/
theorem isCoherent_controlledTransform (hπ : IsBlowupAlong n C π)
    {𝔞 : GermIdeal n X} (h𝔞 : 𝔞.IsCoherent) {μ : ℕ}
    (hle : 𝔞.Le (idealPow (vanishingIdeal (n := n) C) μ)) :
    (controlledTransform hπ 𝔞 μ).IsCoherent :=
  isCoherent_colon (isCoherent_pullback hπ.contMDiff h𝔞)
    (isInvertible_idealPow_exceptionalDivisor hπ μ)
    (pullback_le_idealPow_exceptionalDivisor hπ hle)

/-- **Uniqueness of the controlled transform**: a coherent `𝔠` with `π^*𝔞 = 𝒪_Y(-μD) · 𝔠` is the
controlled transform (Wlodarczyk: "the controlled transform is well defined"). -/
theorem eq_controlledTransform_of_eq_mul (hπ : IsBlowupAlong n C π)
    {𝔞 : GermIdeal n X} {μ : ℕ} {𝔠 : GermIdeal n Y} (h𝔠 : 𝔠.IsCoherent)
    (heq : GermIdeal.pullback (m := n) π 𝔞 = (idealPow (exceptionalDivisor hπ).ideal μ).mul 𝔠) :
    𝔠 = controlledTransform hπ 𝔞 μ := by
  rw [controlledTransform, heq, colon_mul_eq (isInvertible_idealPow_exceptionalDivisor hπ μ) h𝔠]

/-- With the mark `μ = 0` the controlled transform is the total transform `π^*𝔞`. -/
theorem controlledTransform_zero (hπ : IsBlowupAlong n C π) {𝔞 : GermIdeal n X}
    (h𝔞 : 𝔞.IsCoherent) :
    controlledTransform hπ 𝔞 0 = GermIdeal.pullback (m := n) π 𝔞 := by
  rw [controlledTransform, idealPow_zero, colon_unitIdeal (isCoherent_pullback hπ.contMDiff h𝔞)]

end Controlled

end

end Hironaka.BlowupControlledTransform
