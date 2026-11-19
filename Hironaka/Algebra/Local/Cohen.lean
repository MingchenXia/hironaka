/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CohenMap
import Mathlib.Combinatorics.Matroid.Init

/-!
# Surjectivity of `Φ : K⟦X⟧ → R̂`

The surjectivity half of Kollár's `Ô_{p,X} ≅ k(p)⟦x₁, …, xₙ⟧` [Kol07, Definition 55], proved by
successive approximation.  For `ρ ∈ R̂` one chooses homogeneous polynomials `H₀, H₁, …` with `H_a`
of degree `a` and
`ρ − Φ(H₀ + ⋯ + H_a) ∈ 𝔪̂^{a+1}`: this is possible because `𝔪̂^a/𝔪̂^{a+1}` is spanned over the
coefficient field by the degree-`a` monomials in the `ι(xᵢ)` — every element of `R̂` is a constant
of the coefficient field plus an element of `𝔪̂` (`sub_algebraMap_mem_maximalIdeal`, the section
property `IsCoefficientAlgebra R` of the coefficient field, the only place it is used), and
`𝔪̂ = ⟨ι x₁, …, ι x_d⟩`.  The power series `H = ∑ H_a` (coefficientwise: the degree-`a` part is
`H_a`) then satisfies `Φ(H) ≡ Φ(H₀ + ⋯ + H_{a-1}) ≡ ρ (mod 𝔪̂^a)` for every `a`, because `Φ`
computes modulo `𝔪̂^a` through the truncation below degree `a` (`mk_cohenMap`), and `R̂` is
Hausdorff.

Lifting coherently through the finite levels would instead need `ker(K⟦X⟧ → R̂/𝔪̂^a) = (X)^a`,
which is equivalent to the injectivity proved in `Hironaka/Algebra/Local/CohenIso.lean`; the
homogeneous construction avoids it.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing MvPowerSeries

section Surjective

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {d : ℕ} (x : Fin d → R)

local notation "R̂" => AdicCompletion (maximalIdeal R) R

omit [IsNoetherianRing R] in
theorem x_mem_maximalIdeal_of_eq_span (hx : maximalIdeal R = Ideal.span (Set.range x))
    (i : Fin d) : x i ∈ maximalIdeal R := by
  rw [hx]
  exact Ideal.subset_span ⟨i, rfl⟩

theorem maximalIdeal_adicCompletion_eq_span (hx : maximalIdeal R = Ideal.span (Set.range x)) :
    maximalIdeal R̂ = Ideal.span (Set.range fun i => algebraMap R R̂ (x i)) := by
  rw [AdicCompletion.maximalIdeal_eq_map, hx, Ideal.map_span, ← Set.range_comp]
  rfl

variable [Algebra (ResidueField R) (AdicCompletion (maximalIdeal R) R)]

/-- The map `Φ` of `Hironaka/Algebra/Local/CohenMap.lean` for a generating family `x` of `𝔪`. -/
noncomputable abbrev cohenMap' (hx : maximalIdeal R = Ideal.span (Set.range x)) :
    MvPowerSeries (Fin d) (ResidueField R) →ₐ[ResidueField R] R̂ :=
  cohenMap R x (x_mem_maximalIdeal_of_eq_span R x hx)

/-- On polynomials, `Φ` is the evaluation at `ι(x)`. -/
theorem cohenMap_coe (hx : maximalIdeal R = Ideal.span (Set.range x))
    (P : MvPolynomial (Fin d) (ResidueField R)) :
    cohenMap' R x hx (P : MvPowerSeries (Fin d) (ResidueField R)) =
      MvPolynomial.aeval (fun i => algebraMap R R̂ (x i)) P := by
  have h : (cohenMap' R x hx).comp (MvPolynomial.coeToMvPowerSeries.algHom (ResidueField R)) =
      MvPolynomial.aeval (fun i => algebraMap R R̂ (x i)) := by
    rw [MvPolynomial.aeval_unique ((cohenMap' R x hx).comp
      (MvPolynomial.coeToMvPowerSeries.algHom (ResidueField R)))]
    congr 1
    funext i
    simp only [Function.comp_apply, AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
      MvPolynomial.coe_X]
    exact cohenMap_X R x _ i
  exact AlgHom.congr_fun h P

/-- One step of the successive approximation: an element of `𝔪̂^a` is, modulo `𝔪̂^{a+1}`, the
value of a homogeneous polynomial of degree `a` over the coefficient field. -/
theorem exists_isHomogeneous_sub_cohenMap_mem (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (a : ℕ) :
    ∀ ρ ∈ maximalIdeal R̂ ^ a, ∃ H : MvPolynomial (Fin d) (ResidueField R),
      H.IsHomogeneous a ∧ ρ - cohenMap' R x hx H ∈ maximalIdeal R̂ ^ (a + 1) := by
  induction a with
  | zero =>
    intro ρ _
    refine ⟨MvPolynomial.C ((residueFieldEquiv R).symm (residue R̂ ρ)),
      MvPolynomial.isHomogeneous_C (σ := Fin d) _, ?_⟩
    rw [MvPolynomial.coe_C, cohenMap_C, zero_add, pow_one]
    exact sub_algebraMap_mem_maximalIdeal R hι ρ
  | succ a ih =>
    intro ρ hρ
    rw [pow_succ'] at hρ
    refine Submodule.mul_induction_on (C := fun ρ => ∃ H : MvPolynomial (Fin d) (ResidueField R),
      H.IsHomogeneous (a + 1) ∧ ρ - cohenMap' R x hx H ∈ maximalIdeal R̂ ^ (a + 1 + 1))
      hρ ?_ ?_
    · intro m hm p hp
      obtain ⟨Hp, hHp, hp'⟩ := ih p hp
      rw [maximalIdeal_adicCompletion_eq_span R x hx] at hm
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hm
      let k : Fin d → ResidueField R := fun i => (residueFieldEquiv R).symm (residue R̂ (c i))
      refine ⟨∑ i, MvPolynomial.X i * MvPolynomial.C (k i) * Hp, ?_, ?_⟩
      · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
        have := ((MvPolynomial.isHomogeneous_X (R := ResidueField R) i).mul
          (MvPolynomial.isHomogeneous_C (σ := Fin d) (k i))).mul hHp
        rwa [add_zero, add_comm] at this
      · have hA := cohenMap_coe R x hx Hp
        rw [cohenMap_coe, map_sum]
        simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
        rw [← hA, ← hc, Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Submodule.sum_mem _ fun i _ => ?_
        have hxi : algebraMap R R̂ (x i) ∈ maximalIdeal R̂ := by
          rw [maximalIdeal_adicCompletion_eq_span R x hx]
          exact Ideal.subset_span ⟨i, rfl⟩
        have hti : c i - algebraMap (ResidueField R) R̂ (k i) ∈ maximalIdeal R̂ :=
          sub_algebraMap_mem_maximalIdeal R hι (c i)
        have : c i * algebraMap R R̂ (x i) * p -
            algebraMap R R̂ (x i) * algebraMap (ResidueField R) R̂ (k i) * cohenMap' R x hx Hp =
            algebraMap R R̂ (x i) * ((c i - algebraMap (ResidueField R) R̂ (k i)) * p +
              algebraMap (ResidueField R) R̂ (k i) * (p - cohenMap' R x hx Hp)) := by
          ring
        rw [this, pow_succ']
        refine Ideal.mul_mem_mul hxi (add_mem ?_ (Ideal.mul_mem_left _ _ hp'))
        rw [pow_succ']
        exact Ideal.mul_mem_mul hti hp
    · rintro ρ₁ ρ₂ ⟨H₁, hH₁, h₁⟩ ⟨H₂, hH₂, h₂⟩
      refine ⟨H₁ + H₂, hH₁.add hH₂, ?_⟩
      rw [MvPolynomial.coe_add, map_add,
        show ρ₁ + ρ₂ - (cohenMap' R x hx H₁ + cohenMap' R x hx H₂) =
          (ρ₁ - cohenMap' R x hx H₁) + (ρ₂ - cohenMap' R x hx H₂) by ring]
      exact add_mem h₁ h₂

/-- One step of the successive approximation: the homogeneous polynomial of degree `a` chosen for
a remainder `r ∈ 𝔪̂^a`. -/
noncomputable def approxStep (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (a : ℕ)
    (r : {r : R̂ // r ∈ maximalIdeal R̂ ^ a}) : MvPolynomial (Fin d) (ResidueField R) :=
  Classical.choose (exists_isHomogeneous_sub_cohenMap_mem R x hι hx a r.1 r.2)

theorem approxStep_spec (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (a : ℕ)
    (r : {r : R̂ // r ∈ maximalIdeal R̂ ^ a}) :
    (approxStep R x hι hx a r).IsHomogeneous a ∧
      r.1 - cohenMap' R x hx (approxStep R x hι hx a r : MvPowerSeries (Fin d) (ResidueField R)) ∈
        maximalIdeal R̂ ^ (a + 1) :=
  Classical.choose_spec (exists_isHomogeneous_sub_cohenMap_mem R x hι hx a r.1 r.2)

/-- The remainders of the successive approximation of `ρ`: `rem₀ = ρ`,
`rem_{a+1} = rem_a − Φ(H_a)` with `H_a` homogeneous of degree `a` and `rem_a ∈ 𝔪̂^a`. -/
noncomputable def approxRem (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (ρ : R̂) :
    (a : ℕ) → {r : R̂ // r ∈ maximalIdeal R̂ ^ a}
  | 0 => ⟨ρ, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩
  | a + 1 =>
    ⟨(approxRem hι hx ρ a).1 - cohenMap' R x hx
      (approxStep R x hι hx a (approxRem hι hx ρ a) : MvPowerSeries (Fin d) (ResidueField R)),
      (approxStep_spec R x hι hx a (approxRem hι hx ρ a)).2⟩

/-- The homogeneous pieces `H_a` of the successive approximation of `ρ`. -/
noncomputable def approxPoly (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (ρ : R̂) (a : ℕ) :
    MvPolynomial (Fin d) (ResidueField R) :=
  approxStep R x hι hx a (approxRem R x hι hx ρ a)

theorem approxPoly_isHomogeneous (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (ρ : R̂) (a : ℕ) :
    (approxPoly R x hι hx ρ a).IsHomogeneous a :=
  (approxStep_spec R x hι hx a (approxRem R x hι hx ρ a)).1

theorem approxRem_zero (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (ρ : R̂) :
    (approxRem R x hι hx ρ 0).1 = ρ := rfl

theorem approxRem_succ (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (ρ : R̂) (a : ℕ) :
    (approxRem R x hι hx ρ (a + 1)).1 = (approxRem R x hι hx ρ a).1 -
      cohenMap' R x hx (approxPoly R x hι hx ρ a : MvPowerSeries (Fin d) (ResidueField R)) := rfl

/-- The partial sums `H₀ + ⋯ + H_{a-1}`. -/
noncomputable def approxPartial (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (ρ : R̂) (a : ℕ) :
    MvPolynomial (Fin d) (ResidueField R) :=
  ∑ b ∈ Finset.range a, approxPoly R x hι hx ρ b

theorem approxRem_eq (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (ρ : R̂) (a : ℕ) :
    (approxRem R x hι hx ρ a).1 = ρ -
      cohenMap' R x hx (approxPartial R x hι hx ρ a : MvPowerSeries (Fin d) (ResidueField R)) := by
  induction a with
  | zero =>
    rw [approxRem_zero, approxPartial, Finset.sum_range_zero, MvPolynomial.coe_zero, map_zero,
      sub_zero]
  | succ a ih =>
    rw [approxRem_succ, ih, approxPartial, approxPartial, Finset.sum_range_succ,
      MvPolynomial.coe_add, map_add]
    ring

/-- The power series `∑ₐ H_a` of the successive approximation. -/
noncomputable def approxSeries (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (ρ : R̂) :
    MvPowerSeries (Fin d) (ResidueField R) :=
  fun α => (approxPoly R x hι hx ρ α.degree).coeff α

theorem coeff_approxSeries (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (ρ : R̂)
    (α : Fin d →₀ ℕ) :
    coeff α (approxSeries R x hι hx ρ) = (approxPoly R x hι hx ρ α.degree).coeff α := rfl

theorem coeff_approxPartial (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (ρ : R̂) (a : ℕ)
    (α : Fin d →₀ ℕ) :
    (approxPartial R x hι hx ρ a).coeff α =
      if α.degree < a then (approxPoly R x hι hx ρ α.degree).coeff α else 0 := by
  rw [approxPartial, MvPolynomial.coeff_sum]
  split_ifs with h
  · rw [Finset.sum_eq_single α.degree]
    · intro b _ hb
      exact (approxPoly_isHomogeneous R x hι hx ρ b).coeff_eq_zero (Ne.symm hb)
    · intro hnot
      exact absurd (Finset.mem_range.mpr h) hnot
  · refine Finset.sum_eq_zero fun b hb => (approxPoly_isHomogeneous R x hι hx ρ b).coeff_eq_zero ?_
    have := Finset.mem_range.mp hb
    omega

theorem truncTotal_approxSeries (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (ρ : R̂) (a : ℕ) :
    truncTotal a (approxSeries R x hι hx ρ) = approxPartial R x hι hx ρ a := by
  ext α
  rw [coeff_truncTotal_eq_ite, coeff_approxPartial, coeff_approxSeries]

theorem truncTotal_coe_approxPartial (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) (ρ : R̂)
    (a : ℕ) :
    truncTotal a (approxPartial R x hι hx ρ a : MvPowerSeries (Fin d) (ResidueField R)) =
      approxPartial R x hι hx ρ a := by
  ext α
  rw [coeff_truncTotal_eq_ite, MvPolynomial.coeff_coe, coeff_approxPartial]
  split_ifs with h
  · rfl
  · rfl

/-- `Φ` is surjective, for any coefficient field (the surjectivity half of
[Kol07, Definition 55], by successive approximation). -/
theorem cohenMap_surjective_of_residue (hι : IsCoefficientAlgebra R)
    (hx : maximalIdeal R = Ideal.span (Set.range x)) :
    Function.Surjective (cohenMap' R x hx) := by
  intro ρ
  refine ⟨approxSeries R x hι hx ρ, eq_of_forall_mk_pow_eq (maximalIdeal R̂) fun a => ?_⟩
  have h1 : Ideal.Quotient.mk (maximalIdeal R̂ ^ a)
      (cohenMap' R x hx (approxPartial R x hι hx ρ a : MvPowerSeries (Fin d) (ResidueField R))) =
      Ideal.Quotient.mk (maximalIdeal R̂ ^ a) ρ := by
    have h := approxRem_eq R x hι hx ρ a
    have hmem := (approxRem R x hι hx ρ a).2
    rw [h, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at hmem
    exact hmem.symm
  have h2 := mk_cohenMap R x (x_mem_maximalIdeal_of_eq_span R x hx) a
    (approxPartial R x hι hx ρ a : MvPowerSeries (Fin d) (ResidueField R))
  rw [levelEval_apply, truncTotal_coe_approxPartial] at h2
  rw [mk_cohenMap, levelEval_apply, truncTotal_approxSeries, ← h2]
  exact h1

end Surjective

section SurjectiveRat

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [Algebra ℚ R] {d : ℕ}
  (x : Fin d → R)

/-- `Φ` is surjective — the specialization of `cohenMap_surjective_of_residue` at the chosen
coefficient field (`ℚ ⊆ R`). -/
theorem cohenMap_surjective (hx : maximalIdeal R = Ideal.span (Set.range x)) :
    Function.Surjective (cohenMap' R x hx) :=
  cohenMap_surjective_of_residue R x (isCoefficientAlgebra_coefficientAlgebra R) hx

end SurjectiveRat

end IsLocalRing
