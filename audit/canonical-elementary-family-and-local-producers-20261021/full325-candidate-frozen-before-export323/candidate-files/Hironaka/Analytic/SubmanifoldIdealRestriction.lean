/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Analytic.SubmanifoldChartedSpace
import Hironaka.MarkedIdeal.RestrictedIdealQuotient
import Hironaka.Analytic.HolomorphicGermAlgebra

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Restricting an ideal sheaf to a closed submanifold, and the divisor it defines

Source: Copy-4, `sec:fixed-data` and the proof of `prop:principalization`, Step 1: the
manuscript writes `G_m`, `G_M` and `F_B` as effective divisors **on the strict transform**
`W_m`, and `𝔠_M` restricted to `W_m`.  Until now the project had no `EffectiveDivisor` on a
submanifold, because the subtype carried no manifold structure; `Hironaka.SubmanifoldChartedSpace`
supplies it, and this file turns an ambient ideal into an ideal — and, when it is invertible
along `W`, a divisor — on the submanifold.

The restriction used is the pullback along the inclusion, `Res_W 𝔞 = 𝔞 𝒪_W`
(`GermIdeal.pullback Subtype.val`).  The one nonformal point is invertibility:
`IsInvertibleAlong n W 𝔩` (`Hironaka.RestrictedIdealQuotient`) tests nonvanishing of the local
generator on nonempty relatively open subsets **of `W`**, which is exactly the hypothesis the
`IsInvertible` clause on `↥W` needs — an ambient `IsInvertible` would not do, since the
generator may vanish identically on `W`.

## Hypotheses

The charted-space and complex structures on `↥W` and holomorphy of the inclusion are taken as
hypotheses, so nothing here depends on how they were built; `Hironaka.SubmanifoldChartedSpace`
provides them for any closed complex submanifold of dimension `k`, and the last two theorems
instantiate them.
-/

open Set Filter
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.SubmanifoldIdealRestriction

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
open Hironaka.RestrictedIdealQuotient
open Hironaka.SubmanifoldChartedSpace

noncomputable section

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X] {W : Set X}
  [ChartedSpace (ComplexModel k) W] [IsComplexManifold k W]

/-! ### The restricted ideal -/

/-- **`Res_W 𝔞 = 𝔞 𝒪_W`**, the restriction of an ambient ideal sheaf to the submanifold: the
pullback along the inclusion. -/
def restrictIdeal (𝔞 : GermIdeal n X) : GermIdeal k W :=
  GermIdeal.pullback (m := k) Subtype.val 𝔞

theorem mem_restrictIdeal_iff (𝔞 : GermIdeal n X) (p : W) (g : W → ℂ) :
    (restrictIdeal (k := k) (W := W) 𝔞).mem p g ↔
      IsInSpanAt (n := k) (fun s => ∃ a, 𝔞.mem p.1 a ∧ s = a ∘ Subtype.val) p g := Iff.rfl

/-! ### Invertibility along `W` becomes invertibility on `↥W` -/

variable (hval : ContMDiff 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n) ∞ (Subtype.val : W → X))

include hval in
/-- A germ holomorphic at a point of `W` restricts to a germ holomorphic on `↥W`. -/
theorem holomorphicAt_comp_val {a : X → ℂ} {p : W} (ha : HolomorphicAt n a p.1) :
    HolomorphicAt k (fun q : W => a q.1) p :=
  ha.comp_contMDiff (Filter.Eventually.of_forall fun q => hval q)

/-- A map holomorphic on an open set has a holomorphic germ at each of its points. -/
theorem holomorphicAt_of_mdifferentiableOn {U : Set X} (hU : IsOpen U) {h : X → ℂ}
    (hhol : MDifferentiableOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h U) {x : X} (hx : x ∈ U) :
    HolomorphicAt n h x := by
  filter_upwards [hU.mem_nhds hx] with y hy
  exact (hhol y hy).mdifferentiableAt (hU.mem_nhds hy)

include hval in
/-- **The restriction of an ideal invertible along `W` is invertible on `↥W`.**  The nonvanishing
clause of `IsInvertibleAlong` is tested on nonempty relatively open subsets of `W`, which is
exactly what the `IsInvertible` clause on `↥W` asks for; an ambient `IsInvertible` would not
suffice, its generator being allowed to vanish identically on `W`. -/
theorem isInvertible_restrictIdeal {𝔩 : GermIdeal n X} (h𝔩 : IsInvertibleAlong n W 𝔩) :
    (restrictIdeal (k := k) (W := W) 𝔩).IsInvertible := by
  intro p
  obtain ⟨U, hU, hpU, h, hhol, hnv, hgen⟩ := h𝔩 p.1 p.2
  refine ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hpU,
    fun q : W => h q.1, ?_, ?_, ?_⟩
  · intro q hq
    have h1 : MDifferentiableAt 𝓘(ℂ, ComplexModel k) 𝓘(ℂ, ComplexModel n)
        (Subtype.val : W → X) q := (hval q).mdifferentiableAt (by simp)
    have h2 : MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) h q.1 :=
      (hhol q.1 hq).mdifferentiableAt (hU.mem_nhds hq)
    exact (h2.comp q h1).mdifferentiableWithinAt
  · intro V hV hVsub hVne
    obtain ⟨V₀, hV₀, hVeq⟩ := isOpen_induced_iff.mp hV
    obtain ⟨q₀, hq₀⟩ := hVne
    have hq₀V₀ : q₀.1 ∈ V₀ := by rw [← hVeq] at hq₀; exact hq₀
    obtain ⟨y, ⟨⟨hyV₀, _⟩, hyW⟩, hy⟩ :=
      hnv (V₀ ∩ U) (hV₀.inter hU) inter_subset_right ⟨q₀.1, ⟨hq₀V₀, hVsub hq₀⟩, q₀.2⟩
    exact ⟨⟨y, hyW⟩, by rw [← hVeq]; exact hyV₀, hy⟩
  · intro q hqU g
    have hhq : HolomorphicAt n h q.1 := holomorphicAt_of_mdifferentiableOn hU hhol hqU
    constructor
    · intro hg
      have hg' : IsInSpanAt (n := k)
          (fun s => ∃ a, 𝔩.mem q.1 a ∧ s = a ∘ (Subtype.val : W → X)) q g := hg
      refine IsInSpanAt.of_forall_eq_mul ?_ hg'
      rintro s ⟨a, hamem, rfl⟩
      obtain ⟨-, c, hc, hceq⟩ := isInSpanAt_eq_iff.mp ((hgen q.1 hqU a).mp hamem)
      refine ⟨fun r : W => c r.1, holomorphicAt_comp_val hval hc, ?_⟩
      exact (continuous_subtype_val.continuousAt (x := q)).eventually
        (p := fun y => a y = c y * h y) hceq
    · intro hg
      obtain ⟨hgh, c, hc, hceq⟩ := isInSpanAt_eq_iff.mp hg
      have hmem : 𝔩.mem q.1 h :=
        (hgen q.1 hqU h).mpr
          (isInSpanAt_of_eq_mul rfl hhq (holomorphicAt_const 1) (by simp))
      show IsInSpanAt (n := k)
        (fun s => ∃ a, 𝔩.mem q.1 a ∧ s = a ∘ (Subtype.val : W → X)) q g
      exact isInSpanAt_of_eq_mul ⟨h, hmem, rfl⟩ hgh hc hceq

include hval in
/-- **The divisor `Res_W D` on the submanifold.**  This is the object Copy-4's `G_m`, `G_M` and
`F_B` live in, and the reason the submanifold needed its own manifold structure. -/
def restrictDivisor {𝔩 : GermIdeal n X} (h𝔩 : IsInvertibleAlong n W 𝔩) :
    EffectiveDivisor k W where
  ideal := restrictIdeal 𝔩
  isInvertible := isInvertible_restrictIdeal hval h𝔩

end

/-! ### Instantiation for a closed complex submanifold -/

variable {n k : ℕ} {X : Type u} [TopologicalSpace X] [ChartedSpace (ComplexModel n) X]
  [IsComplexManifold n X]

variable (n) in
/-- Invertibility of `Res_W 𝔩` for a *given* charted-space structure on the subtype.  Naming it
lets the conclusion be stated as one existential. -/
def RestrictIsInvertibleFor (k : ℕ) (W : Set X) (cs : ChartedSpace (ComplexModel k) W)
    (𝔩 : GermIdeal n X) : Prop :=
  letI := cs
  (GermIdeal.pullback (m := k) (Subtype.val : W → X) 𝔩).IsInvertible

/-- **An ideal invertible along a closed complex submanifold defines an effective divisor on
it.**  The charted-space structure is the flattening atlas of `Hironaka.SubmanifoldChartedSpace`;
the divisor is the pullback of the ideal along the inclusion. -/
theorem exists_chartedSpace_restrictIsInvertible {W : Set X} {k : ℕ} (hk : k ≤ n)
    (hW : ∀ x ∈ W, RegularAtDim (n := n) W x k) {𝔩 : GermIdeal n X}
    (h𝔩 : IsInvertibleAlong n W 𝔩) :
    ∃ cs : ChartedSpace (ComplexModel k) W,
      @IsComplexManifold k W _ cs ∧ InclusionHolomorphicFor n k W cs ∧
        RestrictIsInvertibleFor n k W cs 𝔩 := by
  refine ⟨chartedSpace hk hW, isComplexManifold_chartedSpace hk hW, contMDiff_val hk hW, ?_⟩
  let := chartedSpace hk hW
  have := isComplexManifold_chartedSpace hk hW
  exact isInvertible_restrictIdeal (contMDiff_val hk hW) h𝔩

/-- `exists_chartedSpace_restrictIsInvertible` for the project's
`IsClosedConnectedSubmanifold`. -/
theorem exists_chartedSpace_restrictIsInvertible_of_isClosedConnectedSubmanifold
    {W : Set X} {k : ℕ} (hW : IsClosedConnectedSubmanifold n W k)
    {𝔩 : GermIdeal n X} (h𝔩 : IsInvertibleAlong n W 𝔩) :
    ∃ cs : ChartedSpace (ComplexModel k) W,
      @IsComplexManifold k W _ cs ∧ InclusionHolomorphicFor n k W cs ∧
        RestrictIsInvertibleFor n k W cs 𝔩 :=
  exists_chartedSpace_restrictIsInvertible (le_of_isClosedConnectedSubmanifold hW)
    hW.2.2 h𝔩

end Hironaka.SubmanifoldIdealRestriction
