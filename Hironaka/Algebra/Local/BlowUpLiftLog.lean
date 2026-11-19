/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.BirationalTransform
public import Hironaka.Algebra.Local.BlowUpLift
public import Hironaka.Scheme.IdealSheaf.Derivative.Logarithmic
import Hironaka.Algebra.Local.BlowUpLiftTransform
import Hironaka.Algebra.Local.Transform
import Hironaka.Scheme.IdealSheaf.Derivative.LogarithmicLocalization
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# The blow-up lift of a logarithmic derivation

[Kol07, (87.3)], "proved the same way using (75.4)": the logarithmic version of Theorem 76 at the
chart level, for an arbitrary ideal. `R` is any commutative `k`-algebra, `x : Fin n → R`,
`P = chartCenter x r = (x₀, …, x_r)`, `R' = chartRing x r = R[xᵢ/x_r] ⊆ R[1/x_r]`, `φ : R → R'`, and
`J ⊆ R` any ideal (the ideal of the hypersurface `S`).

* A `k`-derivation `δ` of `R` preserving `J` lifts, by `Derivation.blowupLift` of
  `Hironaka/Algebra/Local/BlowUpLift.lean` (Włodarczyk's `D' = y σ^*(D)`, `D'(φ a) = φ(x_r · δ a)`),
  to a derivation of `R'` preserving `J R'` (`blowupLift_preservesIdeal_map`; Leibniz on the
  generators `φ(J)`) and preserving the `x_r`-saturation `(J R')^{sat} = ⋃ᵢ (J R' : x_rⁱ)`, the
  chart-level ideal of the strict transform of `V(J)` (`blowupLift_preservesIdeal_saturation`): for
  `z · x_rⁱ ∈ J R'`, applying `D'` gives `z · D'(x_rⁱ) + x_rⁱ · D'(z) ∈ J R'`, and
  `D'(x_rⁱ) ∈ (x_rⁱ)` because `D'(x_r) = x_r φ(δ x_r)` (Włodarczyk's "`y` divides `D'(y)`" in the
  proof of [Wlo05, Lemma 2.6.3]), so `x_rⁱ D'(z) ∈ J R'`.
* Hence, for `I ⊆ P^{m+1}`, `π⁻¹_*(D(−log J)(I), m) ⊆ D(−log (J R')^{sat})(π⁻¹_*(I, m+1))`
  (`transformIdeal_logDerivative_le`): on the generators `f` and `δ f` of `D(−log J)(I)`, by the
  transform identity `π⁻¹_*(δ f, m) = D'(π⁻¹_*(f, m+1)) + (m+1) φ(δ x_r) π⁻¹_*(f, m+1)` of
  `Hironaka/Algebra/Local/BlowUpLiftTransform.lean` (Kollár's (75.1)–(75.3) for an arbitrary
  derivation), with `D'` now a logarithmic derivation along the saturation. In coordinates with `J =
  (x_h)`, `h < r`, this is `transform_Dlog_le_chartDlog` of
  `Hironaka/Algebra/Local/TransformLogDeriv.lean`.

The logarithmic derivative ideal `D(−log J)` is `Ideal.logDerivative k J` of
`Hironaka/Scheme/IdealSheaf/Derivative/Logarithmic.lean`. Used for (87.3) on schemes
(`Hironaka/Scheme/BlowUpSequence/TransformLogDerivative.lean`).
-/

public section

namespace Derivation

open IsLocalRing

universe u

variable {k : Type*} {R : Type u} [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
  (x : Fin n → R) (r : Fin n) (δ : Derivation k R R) (J : Ideal R)

/-- A derivation preserving `J` lifts to a derivation of the chart ring preserving `J R'`. -/
theorem blowupLift_preservesIdeal_map (hδ : δ.PreservesIdeal J) :
    (δ.blowupLift x r).PreservesIdeal (J.map (algebraMap R (chartRing x r))) := by
  have hδ' : (x r • δ).PreservesIdeal J := (Derivation.preserving k J).smul_mem (x r) hδ
  exact hδ'.map_of_forall (algebraMap R (chartRing x r)) _ fun a => by
    rw [blowupLift_algebraMap, Derivation.smul_apply, smul_eq_mul]

/-- Włodarczyk's "`y` divides `D'(y)`" for the powers: `D'(x_rⁱ) ∈ (x_rⁱ)`. -/
theorem blowupLift_pow_algebraMap_mem (i : ℕ) :
    δ.blowupLift x r (algebraMap R (chartRing x r) (x r) ^ i) ∈
      Ideal.span {algebraMap R (chartRing x r) (x r) ^ i} := by
  cases i with
  | zero => rw [pow_zero, Derivation.map_one_eq_zero]; exact Ideal.zero_mem _
  | succ i =>
    rw [Derivation.leibniz_pow, Nat.add_sub_cancel, blowupLift_algebraMap, map_mul, smul_eq_mul,
      ← mul_assoc, ← pow_succ]
    exact nsmul_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)) _

/-- The lift also preserves the `x_r`-saturation `⋃ᵢ (J R' : x_rⁱ)` of `J R'`, the chart-level ideal
of the strict transform of `V(J)`, because `D'(x_r) ∈ (x_r)`. -/
theorem blowupLift_preservesIdeal_saturation (hδ : δ.PreservesIdeal J) :
    (δ.blowupLift x r).PreservesIdeal (⨆ i : ℕ, (J.map (algebraMap R (chartRing x r))).colon
      ((Ideal.span {algebraMap R (chartRing x r) (x r)} ^ i : Ideal (chartRing x r)) :
        Set (chartRing x r))) := by
  have hJR := blowupLift_preservesIdeal_map x r δ J hδ
  have hmono : Monotone fun i : ℕ => (J.map (algebraMap R (chartRing x r))).colon
      ((Ideal.span {algebraMap R (chartRing x r) (x r)} ^ i : Ideal (chartRing x r)) :
        Set (chartRing x r)) :=
    fun i j hij => Submodule.colon_mono le_rfl (Ideal.pow_le_pow_right hij)
  intro z hz
  obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp hz
  refine Submodule.mem_iSup_of_mem i (Submodule.mem_colon.mpr fun w hw => ?_)
  rw [SetLike.mem_coe, Ideal.span_singleton_pow] at hw
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
  have hzy : z * algebraMap R (chartRing x r) (x r) ^ i ∈
      J.map (algebraMap R (chartRing x r)) := by
    have := Submodule.mem_colon.mp hi (algebraMap R (chartRing x r) (x r) ^ i)
      (by rw [SetLike.mem_coe, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _)
    rwa [smul_eq_mul] at this
  have hD := hJR _ hzy
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul] at hD
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp (blowupLift_pow_algebraMap_mem x r δ i)
  have h1 : z * δ.blowupLift x r (algebraMap R (chartRing x r) (x r) ^ i) ∈
      J.map (algebraMap R (chartRing x r)) := by
    rw [← hc', mul_left_comm]
    exact Ideal.mul_mem_left _ _ hzy
  have h2 := (Ideal.add_mem_iff_right _ h1).mp hD
  rw [smul_eq_mul, mul_left_comm]
  exact Ideal.mul_mem_left _ _ (by rwa [mul_comm] at h2)

omit δ in
/-- [Kol07, (87.3)] for one blow-up and `j = 1`, at the chart level, for an arbitrary ideal `J`:
for `I ⊆ P^{m+1}`, `π⁻¹_*(D(−log J)(I), m) ⊆ D(−log (J R')^{sat})(π⁻¹_*(I, m + 1))`. -/
theorem transformIdeal_logDerivative_le {I : Ideal R} {m : ℕ}
    (hI : I ≤ chartCenter x r ^ (m + 1)) :
    transformIdeal x r (Ideal.logDerivative k J I) m ≤
      Ideal.logDerivative k
        (⨆ i : ℕ, (J.map (algebraMap R (chartRing x r))).colon
          ((Ideal.span {algebraMap R (chartRing x r) (x r)} ^ i : Ideal (chartRing x r)) :
            Set (chartRing x r)))
        (transformIdeal x r I (m + 1)) := by
  have hD : Ideal.logDerivative k J I ≤ chartCenter x r ^ m :=
    (Ideal.logDerivative_le_derivative J I).trans (Ideal.derivative_le_pow hI)
  -- `D(−log J)(I) R' ⊆ y^m · D(−log (J R')^{sat})(π_*^{-1}(I, m+1))`, checked on the generators
  have key : (Ideal.logDerivative k J I).map (algebraMap R (chartRing x r)) ≤
      Ideal.span {algebraMap R (chartRing x r) (x r) ^ m} *
        Ideal.logDerivative k
          (⨆ i : ℕ, (J.map (algebraMap R (chartRing x r))).colon
            ((Ideal.span {algebraMap R (chartRing x r) (x r)} ^ i : Ideal (chartRing x r)) :
              Set (chartRing x r)))
          (transformIdeal x r I (m + 1)) := by
    rw [Ideal.map_le_iff_le_comap]
    refine Ideal.logDerivative_le_iff.mpr ⟨fun f hf => ?_, fun δ hδ f hf => ?_⟩
    · rw [Ideal.mem_comap, ← algebraMap_pow_mul_transformElem x r f (hI hf), pow_succ, mul_assoc]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.le_logDerivative _ _
        (Ideal.mul_mem_left _ _ (transformElem_mem_transformIdeal x r hf (hI hf))))
    · rw [Ideal.mem_comap,
        ← algebraMap_pow_mul_transformElem x r (δ f) (derivation_mem_pow δ _ m (hI hf)),
        transformElem_derivation x r δ (hI hf)]
      refine Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) (Ideal.add_mem _ ?_ ?_)
      · exact Ideal.derivation_apply_mem_logDerivative
          (blowupLift_preservesIdeal_saturation x r δ J hδ)
          (transformElem_mem_transformIdeal x r hf (hI hf))
      · rw [nsmul_eq_mul]
        exact Ideal.le_logDerivative _ _ (Ideal.mul_mem_left _ _
          (Ideal.mul_mem_left _ _ (transformElem_mem_transformIdeal x r hf (hI hf))))
  intro z hz
  have h1 : algebraMap R (chartRing x r) (x r) ^ m * z ∈
      Ideal.span {algebraMap R (chartRing x r) (x r) ^ m} *
        Ideal.logDerivative k
          (⨆ i : ℕ, (J.map (algebraMap R (chartRing x r))).colon
            ((Ideal.span {algebraMap R (chartRing x r) (x r)} ^ i : Ideal (chartRing x r)) :
              Set (chartRing x r)))
          (transformIdeal x r I (m + 1)) := by
    apply key
    rw [← span_pow_mul_transformIdeal x r hD, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_mul.mpr ⟨z, hz, rfl⟩
  obtain ⟨w, hw, hwz⟩ := Ideal.mem_span_singleton_mul.mp h1
  rwa [← algebraMap_pow_mul_right_injective x r m hwz]

end Derivation
