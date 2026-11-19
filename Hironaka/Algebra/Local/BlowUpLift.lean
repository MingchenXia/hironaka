/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.Snc.ChartDerivations
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The lift of a derivation to the chart of a blow-up: the construction

Włodarczyk's proof of [Wlo05, Lemma 2.6.3]: "any derivation `D` of `𝒪_X` induces a derivation
`y σ^*(D)` of `𝒪_{X'}`", `y` the local equation of the exceptional divisor.  In the local model
of `Hironaka/Algebra/Local/ChartRing.lean` (`R` a commutative ring, `x : Fin n → R`, the centre
`P = ⟨x₀, …, x_r⟩`, the chart ring `R' = R[xᵢ/x_r : i < r] ⊆ R[1/x_r]`, `y = x_r`), a
`k`-derivation `δ` of `R` extends to `R[1/x_r]` by the quotient rule
(`Derivation.localization`), and `x_r · δ̃` preserves `R'`: on the generators `yⱼ = xⱼ/x_r` the
Leibniz rule for `yⱼ · x_r = xⱼ` gives `x_r · δ̃(yⱼ) = δ(xⱼ) − yⱼ · δ(x_r) ∈ R'` (the table of
derivatives in Włodarczyk's proof), on the image of `R` it is `x_r · δ(a)`, and `R'` is closed
under sums and Leibniz products (`Algebra.adjoin_induction`, as for the coordinate derivations in
`Hironaka/Algebra/Local/Chart.lean`).  The restriction `Derivation.blowupLift δ` is Włodarczyk's
`y σ^*(D)`; `coe_blowupLift` is its defining identity.  The exceptional identity `D'(y) ∈ (y)`,
the transform identity `π⁻¹_*(δ f, m) = D'(π⁻¹_*(f, m+1)) + (m+1) δ(x_r) π⁻¹_*(f, m+1)` and the
inclusion `π⁻¹_*(D(I), m) ⊆ D(π⁻¹_*(I, m+1))` are proved in
`Hironaka/Algebra/Local/BlowUpLiftTransform.lean`; the logarithmic variant is in
`Hironaka/Algebra/Local/BlowUpLiftLog.lean`.

For the coordinate derivations `∂ᵢ` this lift is the `x_r ∂ᵢ` of
`Hironaka/Algebra/Local/TransformDeriv.lean` (`smul_awayPderiv_mem`); the construction here takes an
arbitrary `k`-derivation, as Włodarczyk's argument does, because the stalk of the derivative
ideal sheaf at a non-closed point involves `k`-derivations that are not combinations of the `∂ᵢ`
(`Hironaka/Scheme/IdealSheaf/Derivative/StalkCoords.lean`).  Compare Kollár's computation of the
transformed derivatives in the chart, [Kol07, 75].
-/

@[expose] public section

namespace Derivation

open IsLocalRing

universe u

variable {k : Type*} {R : Type u} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
  (x : Fin n → R) (r : Fin n) (δ : Derivation k R R)

/-- The derivation `x_r · δ̃` of `R[1/x_r]`, `δ̃` the extension of `δ` by the quotient rule:
Włodarczyk's "any derivation `D` of `𝒪_X` induces a derivation `y σ^*(D)` of `𝒪_{X'}`" (the
proof of [Wlo05, Lemma 2.6.3]), before restriction to the chart ring. -/
noncomputable def awayBlowUpLift :
    Derivation k (Localization.Away (x r)) (Localization.Away (x r)) :=
  algebraMap R (Localization.Away (x r)) (x r) • δ.localization (Submonoid.powers (x r))

theorem awayBlowUpLift_apply (z : Localization.Away (x r)) :
    δ.awayBlowUpLift x r z =
      algebraMap R (Localization.Away (x r)) (x r) *
        δ.localization (Submonoid.powers (x r)) z := by
  rw [awayBlowUpLift, Derivation.smul_apply, smul_eq_mul]

/-- `x_r · δ̃` agrees with `x_r · δ` on the image of `R`. -/
theorem awayBlowUpLift_algebraMap (a : R) :
    δ.awayBlowUpLift x r (algebraMap R (Localization.Away (x r)) a) =
      algebraMap R (Localization.Away (x r)) (x r * δ a) := by
  rw [awayBlowUpLift_apply, Derivation.localization_algebraMap, map_mul]

/-- The table of derivatives of the proof of [Wlo05, Lemma 2.6.3], for an arbitrary derivation:
on the chart function `yⱼ = xⱼ/x_r`, `x_r · δ̃(yⱼ) = δ(xⱼ) − yⱼ · δ(x_r)` (Leibniz for
`yⱼ · x_r = xⱼ`). -/
theorem awayBlowUpLift_chartY {j : Fin n} (hj : j < r) :
    δ.awayBlowUpLift x r (chartY x r j) =
      algebraMap R (Localization.Away (x r)) (δ (x j)) -
        chartY x r j * algebraMap R (Localization.Away (x r)) (δ (x r)) := by
  have h := congrArg (δ.localization (Submonoid.powers (x r)))
    (AlgebraicGeometry.chartY_mul_algebraMap x r hj)
  rw [Derivation.leibniz, Derivation.localization_algebraMap, Derivation.localization_algebraMap,
    smul_eq_mul, smul_eq_mul] at h
  rw [awayBlowUpLift_apply]
  linear_combination h

/-- `x_r · δ̃` preserves the chart ring `R' = R[yⱼ : j < r]` — it sends the generators `yⱼ` and
the image of `R` into `R'`, and `R'` is closed under sums and Leibniz products. -/
theorem awayBlowUpLift_mem : ∀ z ∈ chartRing x r, δ.awayBlowUpLift x r z ∈ chartRing x r := by
  intro z hz
  refine Algebra.adjoin_induction (p := fun z _ => δ.awayBlowUpLift x r z ∈ chartRing x r) ?_ ?_
    ?_ ?_ hz
  · rintro _ ⟨j, hj, rfl⟩
    have : δ.awayBlowUpLift x r (chartY x r j) ∈ chartRing x r := by
      rw [awayBlowUpLift_chartY x r δ hj]
      exact Subalgebra.sub_mem _ (Subalgebra.algebraMap_mem _ _)
        (Subalgebra.mul_mem _ (chartY_mem x r j) (Subalgebra.algebraMap_mem _ _))
    rwa [show chartY x r j = Localization.mk (x j) ⟨x r, Submonoid.mem_powers (x r)⟩ from
      chartYOf_of_lt x r (x r) hj] at this
  · intro a
    rw [awayBlowUpLift_algebraMap]
    exact Subalgebra.algebraMap_mem _ _
  · intro a b _ _ ha hb
    rw [map_add]
    exact Subalgebra.add_mem _ ha hb
  · intro a b hab hbb ha hb
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hab hb) (Subalgebra.mul_mem _ hbb ha)

/-- The derivation `D' = y σ^*(D)` of the chart ring `R'` induced by a `k`-derivation `D = δ` of
`R` (the proof of [Wlo05, Lemma 2.6.3]) — `x_r · δ̃` restricted to `R' ⊆ R[1/x_r]`. -/
noncomputable def blowupLift : Derivation k (chartRing x r) (chartRing x r) :=
  (δ.awayBlowUpLift x r).restrictSubalgebra (chartRing x r) (δ.awayBlowUpLift_mem x r)

/-- The defining identity of the lift: in `R[1/x_r]`, `D'(z) = x_r · δ̃(z)`. -/
@[simp]
theorem coe_blowupLift (z : chartRing x r) :
    (δ.blowupLift x r z : Localization.Away (x r)) =
      algebraMap R (Localization.Away (x r)) (x r) *
        δ.localization (Submonoid.powers (x r)) z := by
  rw [blowupLift, Derivation.coe_restrictSubalgebra_apply, awayBlowUpLift_apply]

end Derivation
