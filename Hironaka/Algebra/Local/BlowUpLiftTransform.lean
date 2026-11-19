/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Derivative.Basic
public import Hironaka.Algebra.Local.BlowUpLift
public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Algebra.Order.Cosupport
import Hironaka.Algebra.Local.Transform
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The transform of a derivative in the chart of a blow-up: the identities

The computation of Włodarczyk's proof of [Wlo05, Lemma 2.6.3] for an arbitrary derivation, in the
local model: `R` a commutative `k`-algebra, the centre `P = ⟨x₀, …, x_r⟩`, the chart ring
`R' = R[xᵢ/x_r : i < r]`, `y = x_r`, `φ : R → R'`, a `k`-derivation `δ` of `R` and its lift
`D' = Derivation.blowupLift` to `R'` (`Hironaka/Algebra/Local/BlowUpLift.lean`, Włodarczyk's `y
σ^*(D)`):

* `D'(φ a) = φ(x_r · δ a)` (`blowupLift_algebraMap`) and in particular `D'(y) = y · φ(δ y) ∈ (y)`
  (`blowupLift_exc`, Włodarczyk's "`y` divides `D'(y)`").
* **The transform identity** (`transformElem_derivation`). For `f ∈ P^{m+1}` write
  `g = π⁻¹_*(f, m+1) = f / y^{m+1}`; then `δ f ∈ Pᵐ` (a derivation lowers the `P`-order by at most
  one) and `π⁻¹_*(δ f, m) = D'(g) + (m+1) · φ(δ y) · g`. Proof: apply the extension `δ̃` of `δ` to
  `R[1/y]` to `y^{m+1} g = φ f`:
  `φ(δ f) = (m+1) yᵐ δ̃(y) g + y^{m+1} δ̃(g) = yᵐ ((m+1) φ(δ y) g + D'(g))`,
  and `π⁻¹_*(δ f, m)` is the unique element of `R'` whose product with `yᵐ` is `φ(δ f)`
  (`eq_transformElem_of_pow_mul_eq`, `Hironaka/Algebra/Local/Transform.lean`). This is Włodarczyk's
  `D'(y f) = y D'(f) + D'(y) f`, `D'(y^μ J) ⊆ y^μ (D'(J) + J)`, and it specialises to Kollár's
  (75.1)–(75.3) for `δ = ∂ⱼ` (`Hironaka/Algebra/Local/TransformDeriv.lean`: `δ y = 0` for `j ≠ r`,
  `δ y = 1` for `j = r`).
* **The inclusion** (`transformIdeal_derivative_le`): for `I ≤ P^{m+1}`,
  `π⁻¹_*(D(I), m) ≤ D(π⁻¹_*(I, m+1))`. Since `yᵐ · π⁻¹_*(D(I), m) = D(I) R'`
  (`span_pow_mul_transformIdeal`) and multiplication by `yᵐ` is injective on `R'`, it suffices that
  `D(I) R' ⊆ yᵐ · D(J)`, `J = π⁻¹_*(I, m+1)`; by `derivative_le_iff` this is checked on the
  generators of `D(I)`: `φ f = yᵐ · (y g)` with `g ∈ J`, and `φ(δ f) = yᵐ · π⁻¹_*(δ f, m)` with
  `π⁻¹_*(δ f, m) = D'(g) + (m+1) φ(δ y) g ∈ D(J)` by the transform identity. This is Włodarczyk's
  `σ^c(D(I)) = y^{−μ+1} σ^*(D(I)) ⊆ y^{−μ} D'(y^μ σ^c(I)) ⊆ D(σ^c(I))` and Kollár's observation
  in [Kol07, 75] that "the right-hand sides of these equations are in `D(π⁻¹_*(f, m))`".

The derivative ideal `D` is `Ideal.derivative k` of `Hironaka/Algebra/Derivative/Basic.lean`, over
all `k`-derivations, for the `k`-algebra structure of `R' ⊆ R[1/x_r]` induced through `R`. The
inclusion is the local input of [Kol07, Theorem 76] for one blow-up on schemes
(`Hironaka/Scheme/BlowUpSequence/TransformDerivative.lean`); its logarithmic version is
`Hironaka/Algebra/Local/BlowUpLiftLog.lean`.
-/

public section

namespace Derivation

open IsLocalRing

universe u

variable {k : Type*} {R : Type u} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
  (x : Fin n → R) (r : Fin n) (δ : Derivation k R R)

/-- The lift agrees with `x_r · δ` on the image of `R` (the proof of [Wlo05, Lemma 2.6.3]). -/
theorem blowupLift_algebraMap (a : R) :
    δ.blowupLift x r (algebraMap R (chartRing x r) a) =
      algebraMap R (chartRing x r) (x r * δ a) := by
  apply Subtype.ext
  rw [coe_blowupLift, Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap,
    Derivation.localization_algebraMap, map_mul]

/-- Włodarczyk's "`y` divides `D'(y)`" (the proof of [Wlo05, Lemma 2.6.3]):
`D'(x_r) = x_r · φ(δ x_r) ∈ (x_r)`. -/
theorem blowupLift_exc :
    δ.blowupLift x r (algebraMap R (chartRing x r) (x r)) ∈
      Ideal.span {algebraMap R (chartRing x r) (x r)} := by
  rw [blowupLift_algebraMap, map_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-- **The transform identity** (the proof of [Wlo05, Lemma 2.6.3]; [Kol07, (75.1)–(75.3)] for an
arbitrary derivation): for `f ∈ P^{m+1}`,
`π⁻¹_*(δ f, m) = D'(π⁻¹_*(f, m+1)) + (m+1) · φ(δ x_r) · π⁻¹_*(f, m+1)`. -/
theorem transformElem_derivation {m : ℕ} {f : R} (hf : f ∈ chartCenter x r ^ (m + 1)) :
    transformElem x r (δ f) (derivation_mem_pow δ _ m hf) =
      δ.blowupLift x r (transformElem x r f hf) +
        (m + 1) • (algebraMap R (chartRing x r) (δ (x r)) * transformElem x r f hf) := by
  symm
  apply eq_transformElem_of_pow_mul_eq
  -- `y^{m+1} · g = φ f` in `R[1/x_r]`
  have hg := congrArg (fun z : chartRing x r => (z : Localization.Away (x r)))
    (algebraMap_pow_mul_transformElem x r f hf)
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap] at hg
  -- apply `δ̃`
  have hδ := congrArg (δ.localization (Submonoid.powers (x r))) hg
  rw [Derivation.leibniz, Derivation.leibniz_pow, Derivation.localization_algebraMap,
    Derivation.localization_algebraMap, Nat.add_sub_cancel, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    nsmul_eq_mul] at hδ
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, Subalgebra.coe_add,
    nsmul_eq_mul, SubringClass.coe_natCast, coe_blowupLift]
  rw [← hδ]
  ring

/-- **The transform of the derivative ideal** ([Wlo05, Lemma 2.6.3], `σ^c(D(I)) ⊆ D(σ^c(I))`;
[Kol07, 75] and [Kol07, Theorem 76] for one blow-up): for `I ≤ P^{m+1}`,
`π⁻¹_*(D(I), m) ≤ D(π⁻¹_*(I, m+1))` in the chart ring. -/
theorem transformIdeal_derivative_le {I : Ideal R} {m : ℕ} (hI : I ≤ chartCenter x r ^ (m + 1)) :
    transformIdeal x r (Ideal.derivative k I) m ≤
      Ideal.derivative k (transformIdeal x r I (m + 1)) := by
  have hD : Ideal.derivative k I ≤ chartCenter x r ^ m := Ideal.derivative_le_pow hI
  -- `D(I) R' ⊆ y^m · D(J)`, checked on the generators of `D(I)`
  have key : (Ideal.derivative k I).map (algebraMap R (chartRing x r)) ≤
      Ideal.span {algebraMap R (chartRing x r) (x r) ^ m} *
        Ideal.derivative k (transformIdeal x r I (m + 1)) := by
    rw [Ideal.map_le_iff_le_comap]
    refine Ideal.derivative_le_iff.mpr ⟨fun f hf => ?_, fun δ f hf => ?_⟩
    · rw [Ideal.mem_comap, ← algebraMap_pow_mul_transformElem x r f (hI hf), pow_succ, mul_assoc]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.le_derivative _
        (Ideal.mul_mem_left _ _ (transformElem_mem_transformIdeal x r hf (hI hf))))
    · rw [Ideal.mem_comap,
        ← algebraMap_pow_mul_transformElem x r (δ f) (derivation_mem_pow δ _ m (hI hf)),
        transformElem_derivation x r δ (hI hf)]
      refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.add_mem _ ?_ ?_)
      · exact Ideal.derivation_apply_mem_derivative _
          (transformElem_mem_transformIdeal x r hf (hI hf))
      · rw [nsmul_eq_mul]
        exact Ideal.le_derivative _ (Ideal.mul_mem_left _ _
          (Ideal.mul_mem_left _ _ (transformElem_mem_transformIdeal x r hf (hI hf))))
  intro z hz
  have h1 : algebraMap R (chartRing x r) (x r) ^ m * z ∈
      Ideal.span {algebraMap R (chartRing x r) (x r) ^ m} *
        Ideal.derivative k (transformIdeal x r I (m + 1)) := by
    apply key
    rw [← span_pow_mul_transformIdeal x r hD, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_mul.mpr ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwz⟩ := Ideal.mem_span_singleton_mul.mp h1
  rwa [← algebraMap_pow_mul_right_injective x r m hwz]

end Derivation
