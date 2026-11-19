import Hironaka.Analytic.QuantitativeRegularizationSmoothWeightLimit
import Hironaka.Analytic.BergmanOverlapFixedCover

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# `eq:reg-overlap` for the singular weight `e^{-mΨ}`

Source: Copy-4, `lem:regularization`, Step 2 (`transcendental-nakamaye-copy4-20260911`);
blueprint `ana:regularization`.

`BergmanOverlapFixedCover.exists_overlapConst_finite` closes two gaps of the regularization
chain: for a *finite* family of
coordinate balls inside a convex bounded `D` there is ONE constant `C_B`, fixed by the
family alone, comparing the two Bergman sup-weights at every point of the intersection of
the inner half-balls, in **both** directions and for **every** smooth psh weight `ϕ`
bounded below on `D`.  Its scope note records what was still missing: Copy-4 applies the
estimate to `ϕ = m Ψ` with `Ψ` merely plurisubharmonic, hence `-∞` on a polar set, and
none of the upstream Bergman machinery admits such a weight.

`QuantitativeRegularizationSmoothWeightLimit.bergmanSup_multiplierWeight_le_mul_of_smoothPsh`
is precisely the converter for that gap, and its hypothesis is precisely what
`exists_overlapConst_finite` delivers.  This module performs the composition, and that
closes this gap for the overlap estimate:

> `exists_overlapConst_finite_multiplierWeight`: one constant `C`, fixed by the finite
> ball family alone, with
> `bergmanSup (B i) (e^{-mΨ}) ≤ C · bergmanSup (B j) (e^{-mΨ})`
> for **every** plurisubharmonic `Ψ` on a neighbourhood of `A`, every `m > 0`, and every
> pair of indices — `Ψ` and `m` both chosen after `C`.

Two remarks on the hypotheses.

* The `ϕ`-boundedness hypothesis `hBϕ` of the smooth theory is **not** removed and does
  not need to be: the mollifier layer supplies smooth approximants that are bounded below on `A`
  by construction, so `hBϕ` is discharged rather than dropped.  The singular weight itself is
  unbounded below and never has to satisfy it.
* `m` is a real parameter, quantified after `C`, so the logarithmic form below divides
  by `m` to give Copy-4's `|ψ_{i,m} - ψ_{j,m}| ≤ C_B / m` with the same `C_B` for all
  `m`.  This is the quantifier order Copy-4's Step 3 consumes.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal Topology ContDiff

namespace Hironaka.QuantitativeRegularizationSingularOverlap

noncomputable section

open Hironaka.MongeAmpere BergmanSupWeight
open Hironaka.BergmanOverlapFixedCover
open Hironaka.QuantitativeRegularizationSmoothWeightLimit

variable {d : ℕ}

/-! ### The smooth comparison, applied to a rescaled smooth psh weight -/

/-- A smooth psh function bounded below on `A`, multiplied by `m ≥ 0`, satisfies the three
hypotheses `exists_overlapConst_finite` places on its weight `ϕ`: it is `C^∞` on `A`, its
Levi form is nonnegative on `A`, and it is bounded below on `A`. -/
theorem smul_isAdmissibleWeight {A : Opens (ComplexModel d)} {g : ComplexModel d → ℝ}
    (hg : IsSmoothPshOn A g) {m : ℝ} (hm : 0 ≤ m) :
    ContDiffOn ℝ ∞ (fun z => m * g z) (A : Set (ComplexModel d)) ∧
      (∀ z ∈ (A : Set (ComplexModel d)), ∀ ξ, 0 ≤ leviForm (fun z => m * g z) z ξ) := by
  refine ⟨contDiffOn_const.mul hg.1, fun z hz ξ => ?_⟩
  have hgz : ContDiffAt ℝ 2 g z :=
    (hg.1.contDiffAt (A.isOpen.mem_nhds hz)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hsm : (fun z => m * g z) = m • g := by
    funext y; simp [Pi.smul_apply, smul_eq_mul]
  rw [hsm, leviForm_smul hgz]
  exact mul_nonneg hm
    (leviForm_nonneg_of_contDiffOn_plurisubharmonicOn hg.1 hg.2.1 hz ξ)

/-! ### The overlap estimate for a singular weight -/

/-- **The fixed-cover overlap comparison for an arbitrary plurisubharmonic weight.**
One constant `C > 0`, depending only on the dimension and the finite ball family, with

`bergmanSup (ball (c i) (β i)) (e^{-mΨ}) x ≤ C · bergmanSup (ball (c j) (β j)) (e^{-mΨ}) x`

for every plurisubharmonic `Ψ` on `Ω`, every `m > 0`, every pair `(i, j)` and every
`x` in both inner half-balls.  `Ψ` may take the value `-∞`.

This is `BergmanOverlapFixedCover.exists_overlapConst_finite` composed with the two-layer
singular-weight limit; `A` is boundedly exhausted by `Ω`, which is what lets the mollifier
layer run on `A`. -/
theorem exists_overlapConst_finite_multiplierWeight (hd : 0 < d)
    {A Ω : Opens (ComplexModel d)}
    (hAconv : Convex ℝ (A : Set (ComplexModel d)))
    (hAΩ : RelativelyCompactIn A Ω)
    {ι : Type*} [Finite ι] (c : ι → ComplexModel d) (ρ β : ι → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hρβ : ∀ i, ρ i < β i)
    (hcA : ∀ i, closedBall (c i) (β i) ⊆ (A : Set (ComplexModel d))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : ComplexModel d → EReal), PlurisubharmonicOn u Ω →
        ∀ m : ℝ, 0 < m →
          ∀ (i j : ι) (x : ComplexModel d), x ∈ ball (c i) (ρ i / 2) →
            x ∈ ball (c j) (ρ j / 2) →
            bergmanSup (ball (c i) (β i)) (fun z => multiplierWeight m (u z)) x ≤
              ENNReal.ofReal C *
                bergmanSup (ball (c j) (β j)) (fun z => multiplierWeight m (u z)) x := by
  have hAb : Bornology.IsBounded (A : Set (ComplexModel d)) :=
    hAΩ.1.isBounded.subset subset_closure
  obtain ⟨C, hC, hCle⟩ :=
    exists_overlapConst_finite hd A.isOpen hAconv hAb c ρ β hρ hρβ hcA
  refine ⟨C, hC, ?_⟩
  intro u hu m hm i j x hxi hxj
  have hxjβ : x ∈ ball (c j) (β j) :=
    ball_subset_ball (by have := hρβ j; have := hρ j; linarith) hxj
  refine bergmanSup_multiplierWeight_le_mul_of_smoothPsh hAΩ hu hm
    measurableSet_ball ((ball_subset_closedBall).trans (hcA i)) isOpen_ball
    ((ball_subset_closedBall).trans (hcA j))
    (by simpa using hC) ENNReal.ofReal_ne_top hxjβ ?_
  intro g hg hgB
  obtain ⟨B, hB⟩ := hgB
  obtain ⟨hsmooth, hlevi⟩ := smul_isAdmissibleWeight hg hm.le
  have hlower : ∀ z ∈ (A : Set (ComplexModel d)), -(-(m * B)) ≤ m * g z := by
    intro z hz
    simpa using mul_le_mul_of_nonneg_left (hB z hz) hm.le
  have := hCle (fun z => m * g z) hsmooth hlevi (-(m * B)) hlower i j x hxi hxj
  simpa only [multiplierWeight_coe] using this

/-! ### Both directions, and the logarithmic normalization -/

/-- The same comparison in both directions, with the one constant: the statement of
`exists_overlapConst_finite_multiplierWeight` is symmetric in `(i, j)`. -/
theorem exists_overlapConst_finite_multiplierWeight_pair (hd : 0 < d)
    {A Ω : Opens (ComplexModel d)}
    (hAconv : Convex ℝ (A : Set (ComplexModel d)))
    (hAΩ : RelativelyCompactIn A Ω)
    {ι : Type*} [Finite ι] (c : ι → ComplexModel d) (ρ β : ι → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hρβ : ∀ i, ρ i < β i)
    (hcA : ∀ i, closedBall (c i) (β i) ⊆ (A : Set (ComplexModel d))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : ComplexModel d → EReal), PlurisubharmonicOn u Ω →
        ∀ m : ℝ, 0 < m →
          ∀ (i j : ι) (x : ComplexModel d), x ∈ ball (c i) (ρ i / 2) →
            x ∈ ball (c j) (ρ j / 2) →
            bergmanSup (ball (c i) (β i)) (fun z => multiplierWeight m (u z)) x ≤
                ENNReal.ofReal C *
                  bergmanSup (ball (c j) (β j)) (fun z => multiplierWeight m (u z)) x ∧
              bergmanSup (ball (c j) (β j)) (fun z => multiplierWeight m (u z)) x ≤
                ENNReal.ofReal C *
                  bergmanSup (ball (c i) (β i)) (fun z => multiplierWeight m (u z)) x := by
  obtain ⟨C, hC, h⟩ :=
    exists_overlapConst_finite_multiplierWeight hd hAconv hAΩ c ρ β hρ hρβ hcA
  exact ⟨C, hC, fun u hu m hm i j x hxi hxj =>
    ⟨h u hu m hm i j x hxi hxj, h u hu m hm j i x hxj hxi⟩⟩

/-- **Copy-4's `|ψ_{i,m} - ψ_{j,m}| ≤ C_B` before dividing by `m`.**  The logarithmic
normalization of the singular-weight overlap comparison: the two Bergman logs differ by
at most `log C`, with `C` fixed by the cover, uniformly in the plurisubharmonic weight
`Ψ` and in `m > 0`. -/
theorem exists_overlapConst_finite_multiplierWeight_log (hd : 0 < d)
    {A Ω : Opens (ComplexModel d)}
    (hAconv : Convex ℝ (A : Set (ComplexModel d)))
    (hAΩ : RelativelyCompactIn A Ω)
    {ι : Type*} [Finite ι] (c : ι → ComplexModel d) (ρ β : ι → ℝ)
    (hρ : ∀ i, 0 < ρ i) (hρβ : ∀ i, ρ i < β i)
    (hcA : ∀ i, closedBall (c i) (β i) ⊆ (A : Set (ComplexModel d))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : ComplexModel d → EReal), PlurisubharmonicOn u Ω →
        ∀ m : ℝ, 0 < m →
          ∀ (i j : ι) (x : ComplexModel d), x ∈ ball (c i) (ρ i / 2) →
            x ∈ ball (c j) (ρ j / 2) →
            bergmanLog (ball (c i) (β i)) (fun z => multiplierWeight m (u z)) x ≤
                bergmanLog (ball (c j) (β j)) (fun z => multiplierWeight m (u z)) x
                  + (Real.log C : EReal) ∧
              bergmanLog (ball (c j) (β j)) (fun z => multiplierWeight m (u z)) x ≤
                bergmanLog (ball (c i) (β i)) (fun z => multiplierWeight m (u z)) x
                  + (Real.log C : EReal) := by
  obtain ⟨C, hC, h⟩ :=
    exists_overlapConst_finite_multiplierWeight_pair hd hAconv hAΩ c ρ β hρ hρβ hcA
  refine ⟨C, hC, ?_⟩
  intro u hu m hm i j x hxi hxj
  obtain ⟨hle₁, hle₂⟩ := h u hu m hm i j x hxi hxj
  have key : ∀ {P Q : ℝ≥0∞}, P ≤ ENNReal.ofReal C * Q →
      ENNReal.log P ≤ ENNReal.log Q + (Real.log C : EReal) := by
    intro P Q hPQ
    calc ENNReal.log P ≤ ENNReal.log (ENNReal.ofReal C * Q) := ENNReal.log_monotone hPQ
      _ = (Real.log C : EReal) + ENNReal.log Q := by
          rw [ENNReal.log_mul_add, ENNReal.log_ofReal_of_pos hC]
      _ = ENNReal.log Q + (Real.log C : EReal) := add_comm _ _
  exact ⟨key hle₁, key hle₂⟩

end

end Hironaka.QuantitativeRegularizationSingularOverlap
