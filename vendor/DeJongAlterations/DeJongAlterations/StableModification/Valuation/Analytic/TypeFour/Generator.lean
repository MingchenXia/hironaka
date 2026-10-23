import Mathlib.Algebra.Polynomial.EraseLead
import DeJongAlterations.StableModification.Valuation.Analytic.TypeFour.Dirty

/-!
# Temkin's Proposition 6.2.4 for type 4 fields in characteristic `p`

Let `k` be an algebraically closed non-archimedean field of characteristic `p` and `z` a type 4
generator of a non-archimedean field `K ⊇ k`. This file proves the type 4 case of Temkin,
*Stable modification of relative curves*, J. Algebraic Geom. 19 (2010), Proposition 6.2.4
(`semi-stable.tex`, lines 3723–3728; proof lines 3966–3978) in characteristic `p`: every special
coset `b + S_{a,s}(K)` contains an element `β₀ + β₁ z` with `β₀, β₁ ∈ k`, hence an element of `k`
or a type 4 generator of `K`.

As in the source, the proof moves a polynomial representative `g(z)` of the coset inside the coset
and lowers its degree: a leading term of degree divisible by `p` is removed by subtracting
`℘_a(c)` with `c = b_m^{1/p} z^{m/p}`, and a leading term of degree `m > 1` prime to `p` is
removed by subtracting `b_m (z - z₀) ^ m`, which is small by Lemma 6.2.9. In characteristic `p` no
coordinate change is needed.

## Main results

* `IsTypeFourGenerator.exists_linear_memCoset`: **Temkin, Proposition 6.2.4, type 4**.
* `IsTypeFourGenerator.affine`: `β₀ + β₁ z` (`β₁ ≠ 0`) is again a type 4 generator.

## References

Blueprint `sm-val-onedim-t34.tex`: `prop:sm-an-type4-cosets`.
-/

noncomputable section

open Polynomial Filter Topology

namespace DeJongAlterations.StableModification.Valuation

variable {k K : Type*} [NormedField k] [IsAlgClosed k] [NormedField K] [IsUltrametricDist K]
  [NormedAlgebra k K]

section Affine

omit [IsAlgClosed k] [IsUltrametricDist K] in
theorem norm_affine_sub (z : K) (β₀ : k) {β₁ : k} (hβ : β₁ ≠ 0) (c : k) :
    ‖(algebraMap k K β₀ + algebraMap k K β₁ * z) - algebraMap k K c‖ =
      ‖β₁‖ * ‖z - algebraMap k K ((c - β₀) / β₁)‖ := by
  have hβ' : algebraMap k K β₁ ≠ 0 := by simpa using hβ
  have : (algebraMap k K β₀ + algebraMap k K β₁ * z) - algebraMap k K c =
      algebraMap k K β₁ * (z - algebraMap k K ((c - β₀) / β₁)) := by
    rw [map_div₀, map_sub]
    field_simp
    ring
  rw [this, norm_mul, norm_algebraMap']

omit [IsAlgClosed k] [IsUltrametricDist K] in
/-- If `z` is a type 4 generator and `β₁ ≠ 0`, then `β₀ + β₁ z` is a type 4 generator, with
radius at least `‖β₁‖ r(z)`. -/
theorem IsTypeFourGenerator.affine {z : K} (hz : IsTypeFourGenerator k z) (β₀ : k) {β₁ : k}
    (hβ : β₁ ≠ 0) : IsTypeFourGenerator k (algebraMap k K β₀ + algebraMap k K β₁ * z) := by
  set y := algebraMap k K β₀ + algebraMap k K β₁ * z with hy
  have hadj : IntermediateField.adjoin k {y} = IntermediateField.adjoin k {z} := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact add_mem (IntermediateField.algebraMap_mem _ _)
        (mul_mem (IntermediateField.algebraMap_mem _ _)
          (IntermediateField.mem_adjoin_simple_self k z))
    · rw [IntermediateField.adjoin_simple_le_iff]
      have hz' : z = algebraMap k K β₁⁻¹ * (y - algebraMap k K β₀) := by
        have hβ' : algebraMap k K β₁ ≠ 0 := by simpa using hβ
        rw [hy, map_inv₀]
        field_simp
        ring
      rw [hz']
      exact mul_mem (IntermediateField.algebraMap_mem _ _)
        (sub_mem (IntermediateField.mem_adjoin_simple_self k y)
          (IntermediateField.algebraMap_mem _ _))
  have hβn : 0 < ‖β₁‖ := norm_pos_iff.mpr hβ
  refine ⟨by rw [hadj]; exact hz.dense_adjoin, fun a => ?_, ?_⟩
  · obtain ⟨a'', ha''⟩ := hz.exists_norm_sub_lt_norm_sub ((a - β₀) / β₁)
    refine ⟨β₀ + β₁ * a'', ?_⟩
    rw [norm_affine_sub z β₀ hβ, norm_affine_sub z β₀ hβ,
      show (β₀ + β₁ * a'' - β₀) / β₁ = a'' by field_simp; ring]
    exact mul_lt_mul_of_pos_left ha'' hβn
  · refine (mul_pos hβn hz.radius_pos).trans_le (le_ciInf fun c => ?_)
    rw [norm_affine_sub z β₀ hβ]
    exact mul_le_mul_of_nonneg_left (radius_le z _) hβn.le

end Affine

variable {p : ℕ} [Fact p.Prime] [CharP k p]

/-- The degree-lowering step of the proof of Proposition 6.2.4 (type 4): a polynomial
representative of degree `≥ 2` of a special coset can be replaced by one of smaller degree. -/
theorem IsTypeFourGenerator.exists_natDegree_lt_memCoset {z : K}
    (hz : IsTypeFourGenerator k z) {a₀ : k} {s : ℝ} {b : K}
    (hsp : IsSpecialCoset p (algebraMap k K a₀) s b) {g : k[X]}
    (hg : MemCoset p (algebraMap k K a₀) s b (aeval z g)) (h2 : 2 ≤ g.natDegree) :
    ∃ g₁ : k[X], g₁.natDegree < g.natDegree ∧
      MemCoset p (algebraMap k K a₀) s b (aeval z g₁) := by
  have hp := (Fact.out : p.Prime)
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  set m := g.natDegree with hmdef
  set bm := g.leadingCoeff with hbm
  have hg0 : g ≠ 0 := by rintro rfl; simp [hmdef] at h2
  by_cases hpm : p ∣ m
  · -- remove the leading term with `℘_a(β z^{m/p})`
    obtain ⟨n', hn'⟩ := hpm
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq bm hp.pos
    set c : k[X] := C β * X ^ n' with hc
    refine ⟨g.eraseLead + C (a₀ * β) * X ^ n', ?_, ?_⟩
    · have hn'lt : n' < m := by
        rw [hn']
        have : 0 < n' := by
          rcases Nat.eq_zero_or_pos n' with h | h
          · rw [h, mul_zero] at hn'; omega
          · exact h
        nlinarith [hp.two_le]
      refine (natDegree_add_le _ _).trans_lt (max_lt ?_ ?_)
      · exact (eraseLead_natDegree_le g).trans_lt (by omega)
      · exact (natDegree_C_mul_X_pow_le _ _).trans_lt hn'lt
    · have heq : aeval z (g.eraseLead + C (a₀ * β) * X ^ n') =
          aeval z g - asMap p (algebraMap k K a₀) (aeval z c) := by
        rw [← self_sub_C_mul_X_pow, hc, asMap]
        simp only [map_add, map_sub, map_mul, map_pow, aeval_C, aeval_X]
        rw [← hmdef, ← hbm, ← hβ, hn', map_pow, mul_pow, ← pow_mul, mul_comm n' p]
        ring
      rw [heq]
      exact hg.sub_asMap _
  · -- `p ∤ m`, `m > 1`: Lemma 6.2.9 makes `bm (z - z₀) ^ m` small
    have hsp' : IsSpecialCoset p (algebraMap k K a₀) s (aeval z g) := hg.isSpecialCoset_iff.mpr hsp
    have hlt := hz.norm_leadingCoeff_mul_radius_pow_lt hpm (by omega) hsp'
    set r := radius k z
    have hcont : ContinuousAt (fun x : ℝ => ‖bm‖ * x ^ m) r := by fun_prop
    obtain ⟨ε, hε, hεball⟩ := Metric.eventually_nhds_iff.mp
      (hcont.eventually_lt continuousAt_const hlt)
    obtain ⟨z₀, hz₀⟩ := exists_norm_sub_lt_of_radius_lt (k := k) (z := z)
      (lt_add_of_pos_right r hε)
    have hsmall : ‖bm‖ * ‖z - algebraMap k K z₀‖ ^ m < s := by
      refine hεball ?_
      rw [Real.dist_eq, abs_lt]
      constructor
      · linarith [radius_le (k := k) z z₀]
      · linarith
    set h : k[X] := C bm * (X - C z₀) ^ m with hh
    have hbm0 : bm ≠ 0 := leadingCoeff_ne_zero.mpr hg0
    have hhdeg : h.natDegree = m := by
      rw [hh, natDegree_C_mul hbm0, natDegree_pow, natDegree_X_sub_C, mul_one]
    have hhlc : h.leadingCoeff = bm := by
      rw [hh, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow, leadingCoeff_X_sub_C, one_pow,
        mul_one]
    have hhnorm : ‖aeval z h‖ < s := by
      rw [hh, map_mul, map_pow, map_sub, aeval_C, aeval_X, aeval_C, norm_mul, norm_pow,
        norm_algebraMap']
      exact hsmall
    refine ⟨g - h, ?_, ?_⟩
    · by_cases h0 : g - h = 0
      · rw [h0, natDegree_zero]; omega
      · refine natDegree_lt_natDegree h0 (degree_sub_lt_left ?_ hg0 hhlc.symm)
        have hh0 : h ≠ 0 := by
          intro h0'
          rw [h0', natDegree_zero] at hhdeg
          omega
        rw [degree_eq_natDegree hg0, degree_eq_natDegree hh0, hhdeg]
    · rw [map_sub]
      exact hg.sub_of_norm_lt hhnorm

/-- **Temkin, Proposition 6.2.4, type 4** (characteristic `p`): every special coset
`b + S_{a,s}(K)` contains an element `β₀ + β₁ z` with `β₀, β₁ ∈ k`; thus it contains an element
of `k` (`β₁ = 0`) or a type 4 generator of `K` (`β₁ ≠ 0`, `IsTypeFourGenerator.affine`). -/
theorem IsTypeFourGenerator.exists_linear_memCoset {z : K} (hz : IsTypeFourGenerator k z)
    {a b : K} {s : ℝ} (hsp : IsSpecialCoset p a s b) :
    ∃ β₀ β₁ : k, MemCoset p a s b (algebraMap k K β₀ + algebraMap k K β₁ * z) := by
  have : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  obtain ⟨a₀, rfl⟩ : ∃ a₀ : k, algebraMap k K a₀ = a := by
    rcases hsp.2 with rfl | ⟨rfl, -⟩
    · exact ⟨0, map_zero _⟩
    · exact ⟨1, map_one _⟩
  obtain ⟨_, ⟨g, rfl⟩, hg⟩ :=
    exists_mem_memCoset_of_dense hz.dense_aeval (memCoset_self hsp.1.pos b)
  induction hn : g.natDegree using Nat.strong_induction_on generalizing g with
  | _ n ih =>
    by_cases h1 : n ≤ 1
    · refine ⟨g.coeff 0, g.coeff 1, ?_⟩
      have hg1 := eq_X_add_C_of_natDegree_le_one (hn ▸ h1 : g.natDegree ≤ 1)
      rw [hg1] at hg
      simpa [add_comm] using hg
    · obtain ⟨g₁, hlt, hg₁⟩ := hz.exists_natDegree_lt_memCoset hsp hg (by omega)
      exact ih _ (hn ▸ hlt) g₁ hg₁ rfl

end DeJongAlterations.StableModification.Valuation
