/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
import Hironaka.Geometry.ProperSteinProjectiveCechCohenEvaluation
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Genuine homogeneous approximation and complete split-quotient Noetherianity

Closed native successive-approximation proof adapted from
`EnvelopeProperty/deps/hironaka-ep33/Hironaka/Algebra/Local/Cohen.lean`,
SHA256 b1d06ef3efd1da7e0715a550b16b6fae2269f67326ecd2f959226c39d9c62d8c.
The source is generalized to the SAME original complete ideal and actual split
quotient coefficient action. No characteristic restriction, coefficient-field
existence, Hironaka import, or desired Noetherianity certificate is used.
-/
noncomputable section
universe u
namespace Hironaka.Geometry.ProperSteinProjectiveCech.CohenSurjective
open MvPowerSeries CohenEvaluation
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
variable {K B : Type u} [CommRing K] [CommRing B] [Algebra K B]
  (I : Ideal B) [IsAdicComplete I B] {d : ℕ} (x : Fin d → B)

omit [IsAdicComplete I B] in
private theorem x_mem_ideal_of_eq_span (hx : I = Ideal.span (Set.range x)) (i : Fin d) : x i ∈ I := by
  rw [hx]
  exact Ideal.subset_span ⟨i, rfl⟩

omit [IsAdicComplete I B] in
/-- The actual split ORIGINAL quotient derives the literal original coefficient remainder identity. -/
theorem sub_coefficient_mem (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I) (y : B) : y - algebraMap K B (γ y) ∈ I := by
  rw [← hker]
  change γ (y - algebraMap K B (γ y)) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr (RingHom.congr_fun hγ (γ y)).symm

/-- The map `Φ` of the actual original finite-level construction for a generating family `x` of `I`. -/
noncomputable abbrev cohenMap' (hx : I = Ideal.span (Set.range x)) :
    MvPowerSeries (Fin d) K →ₐ[K] B :=
  cohenMap (K := K) I x (x_mem_ideal_of_eq_span I x hx)

/-- On polynomials, `Φ` is the evaluation at the SAME original `x`. -/
theorem cohenMap_coe (hx : I = Ideal.span (Set.range x))
    (P : MvPolynomial (Fin d) K) :
    cohenMap' (K := K) I x hx (P : MvPowerSeries (Fin d) K) =
      MvPolynomial.aeval (fun i => x i) P := by
  have h : (cohenMap' (K := K) I x hx).comp (MvPolynomial.coeToMvPowerSeries.algHom K) =
      MvPolynomial.aeval (fun i => x i) := by
    rw [MvPolynomial.aeval_unique ((cohenMap' (K := K) I x hx).comp
      (MvPolynomial.coeToMvPowerSeries.algHom K))]
    congr 1
    funext i
    simp only [Function.comp_apply, AlgHom.comp_apply, MvPolynomial.coeToMvPowerSeries.algHom_apply,
      MvPolynomial.coe_X]
    exact cohenMap_X (K := K) I x _ i
  exact AlgHom.congr_fun h P

/-- One step of the successive approximation: an element of `I^a` is, modulo `I^{a+1}`, the
value of a homogeneous polynomial of degree `a` over the original coefficient ring. -/
theorem exists_isHomogeneous_sub_cohenMap_mem (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (a : ℕ) :
    ∀ ρ ∈ I ^ a, ∃ H : MvPolynomial (Fin d) K,
      H.IsHomogeneous a ∧ ρ - cohenMap' (K := K) I x hx H ∈ I ^ (a + 1) := by
  induction a with
  | zero =>
    intro ρ _
    refine ⟨MvPolynomial.C (γ ρ),
      MvPolynomial.isHomogeneous_C (σ := Fin d) _, ?_⟩
    rw [MvPolynomial.coe_C, cohenMap_C, zero_add, pow_one]
    exact sub_coefficient_mem I γ hγ hker ρ
  | succ a ih =>
    intro ρ hρ
    rw [pow_succ'] at hρ
    refine Submodule.mul_induction_on (C := fun ρ => ∃ H : MvPolynomial (Fin d) K,
      H.IsHomogeneous (a + 1) ∧ ρ - cohenMap' (K := K) I x hx H ∈ I ^ (a + 1 + 1))
      hρ ?_ ?_
    · intro m hm p hp
      obtain ⟨Hp, hHp, hp'⟩ := ih p hp
      rw [hx] at hm
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hm
      let k : Fin d → K := fun i => γ (c i)
      refine ⟨∑ i, MvPolynomial.X i * MvPolynomial.C (k i) * Hp, ?_, ?_⟩
      · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
        have := ((MvPolynomial.isHomogeneous_X (R := K) i).mul
          (MvPolynomial.isHomogeneous_C (σ := Fin d) (k i))).mul hHp
        rwa [add_zero, add_comm] at this
      · have hA := cohenMap_coe I x hx Hp
        rw [cohenMap_coe, map_sum]
        simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
        rw [← hA, ← hc, Finset.sum_mul, ← Finset.sum_sub_distrib]
        refine Submodule.sum_mem _ fun i _ => ?_
        have hxi : x i ∈ I := by
          rw [hx]
          exact Ideal.subset_span ⟨i, rfl⟩
        have hti : c i - algebraMap K B (k i) ∈ I :=
          sub_coefficient_mem I γ hγ hker (c i)
        have : c i * x i * p -
            x i * algebraMap K B (k i) * cohenMap' (K := K) I x hx Hp =
            x i * ((c i - algebraMap K B (k i)) * p +
              algebraMap K B (k i) * (p - cohenMap' (K := K) I x hx Hp)) := by
          ring
        rw [this, pow_succ']
        refine Ideal.mul_mem_mul hxi (add_mem ?_ (Ideal.mul_mem_left _ _ hp'))
        rw [pow_succ']
        exact Ideal.mul_mem_mul hti hp
    · rintro ρ₁ ρ₂ ⟨H₁, hH₁, h₁⟩ ⟨H₂, hH₂, h₂⟩
      refine ⟨H₁ + H₂, hH₁.add hH₂, ?_⟩
      rw [MvPolynomial.coe_add, map_add,
        show ρ₁ + ρ₂ - (cohenMap' (K := K) I x hx H₁ + cohenMap' (K := K) I x hx H₂) =
          (ρ₁ - cohenMap' (K := K) I x hx H₁) + (ρ₂ - cohenMap' (K := K) I x hx H₂) by ring]
      exact add_mem h₁ h₂

/-- One step of the successive approximation: the homogeneous polynomial of degree `a` chosen for
a remainder `r ∈ 𝔪̂^a`. -/
noncomputable def approxStep (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (a : ℕ)
    (r : {r : B // r ∈ I ^ a}) : MvPolynomial (Fin d) K :=
  Classical.choose (exists_isHomogeneous_sub_cohenMap_mem I x γ hγ hker hx a r.1 r.2)

theorem approxStep_spec (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (a : ℕ)
    (r : {r : B // r ∈ I ^ a}) :
    (approxStep I x γ hγ hker hx a r).IsHomogeneous a ∧
      r.1 - cohenMap' (K := K) I x hx (approxStep I x γ hγ hker hx a r : MvPowerSeries (Fin d) K) ∈
        I ^ (a + 1) :=
  Classical.choose_spec (exists_isHomogeneous_sub_cohenMap_mem I x γ hγ hker hx a r.1 r.2)

/-- The remainders of the successive approximation of `ρ`: `rem₀ = ρ`,
`rem_{a+1} = rem_a − Φ(H_a)` with `H_a` homogeneous of degree `a` and `rem_a ∈ 𝔪̂^a`. -/
noncomputable def approxRem (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (ρ : B) :
    (a : ℕ) → {r : B // r ∈ I ^ a}
  | 0 => ⟨ρ, by rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top⟩
  | a + 1 =>
    ⟨(approxRem γ hγ hker hx ρ a).1 - cohenMap' (K := K) I x hx
      (approxStep I x γ hγ hker hx a (approxRem γ hγ hker hx ρ a) : MvPowerSeries (Fin d) K),
      (approxStep_spec I x γ hγ hker hx a (approxRem γ hγ hker hx ρ a)).2⟩

/-- The homogeneous pieces `H_a` of the successive approximation of `ρ`. -/
noncomputable def approxPoly (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (ρ : B) (a : ℕ) :
    MvPolynomial (Fin d) K :=
  approxStep I x γ hγ hker hx a (approxRem I x γ hγ hker hx ρ a)

theorem approxPoly_isHomogeneous (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (ρ : B) (a : ℕ) :
    (approxPoly I x γ hγ hker hx ρ a).IsHomogeneous a :=
  (approxStep_spec I x γ hγ hker hx a (approxRem I x γ hγ hker hx ρ a)).1

theorem approxRem_zero (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (ρ : B) :
    (approxRem I x γ hγ hker hx ρ 0).1 = ρ := rfl

theorem approxRem_succ (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (ρ : B) (a : ℕ) :
    (approxRem I x γ hγ hker hx ρ (a + 1)).1 = (approxRem I x γ hγ hker hx ρ a).1 -
      cohenMap' (K := K) I x hx (approxPoly I x γ hγ hker hx ρ a : MvPowerSeries (Fin d) K) := rfl

/-- The partial sums `H₀ + ⋯ + H_{a-1}`. -/
noncomputable def approxPartial (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (ρ : B) (a : ℕ) :
    MvPolynomial (Fin d) K :=
  ∑ b ∈ Finset.range a, approxPoly I x γ hγ hker hx ρ b

theorem approxRem_eq (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (ρ : B) (a : ℕ) :
    (approxRem I x γ hγ hker hx ρ a).1 = ρ -
      cohenMap' (K := K) I x hx (approxPartial I x γ hγ hker hx ρ a : MvPowerSeries (Fin d) K) := by
  induction a with
  | zero =>
    rw [approxRem_zero, approxPartial, Finset.sum_range_zero, MvPolynomial.coe_zero, map_zero,
      sub_zero]
  | succ a ih =>
    rw [approxRem_succ, ih, approxPartial, approxPartial, Finset.sum_range_succ,
      MvPolynomial.coe_add, map_add]
    ring

/-- The power series `∑ₐ H_a` of the successive approximation. -/
noncomputable def approxSeries (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (ρ : B) :
    MvPowerSeries (Fin d) K :=
  fun α => (approxPoly I x γ hγ hker hx ρ α.degree).coeff α

theorem coeff_approxSeries (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (ρ : B)
    (α : Fin d →₀ ℕ) :
    coeff α (approxSeries I x γ hγ hker hx ρ) = (approxPoly I x γ hγ hker hx ρ α.degree).coeff α := rfl

theorem coeff_approxPartial (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (ρ : B) (a : ℕ)
    (α : Fin d →₀ ℕ) :
    (approxPartial I x γ hγ hker hx ρ a).coeff α =
      if α.degree < a then (approxPoly I x γ hγ hker hx ρ α.degree).coeff α else 0 := by
  rw [approxPartial, MvPolynomial.coeff_sum]
  split_ifs with h
  · rw [Finset.sum_eq_single α.degree]
    · intro b _ hb
      exact (approxPoly_isHomogeneous I x γ hγ hker hx ρ b).coeff_eq_zero (Ne.symm hb)
    · intro hnot
      exact absurd (Finset.mem_range.mpr h) hnot
  · refine Finset.sum_eq_zero fun b hb => (approxPoly_isHomogeneous I x γ hγ hker hx ρ b).coeff_eq_zero ?_
    have := Finset.mem_range.mp hb
    omega

theorem truncTotal_approxSeries (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (ρ : B) (a : ℕ) :
    truncTotal a (approxSeries I x γ hγ hker hx ρ) = approxPartial I x γ hγ hker hx ρ a := by
  ext α
  rw [coeff_truncTotal_eq_ite, coeff_approxPartial, coeff_approxSeries]

theorem truncTotal_coe_approxPartial (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) (ρ : B)
    (a : ℕ) :
    truncTotal a (approxPartial I x γ hγ hker hx ρ a : MvPowerSeries (Fin d) K) =
      approxPartial I x γ hγ hker hx ρ a := by
  ext α
  rw [coeff_truncTotal_eq_ite, MvPolynomial.coeff_coe, coeff_approxPartial]
  split_ifs with h
  · rfl
  · rfl

/-- `Φ` is surjective, for any original coefficient ring (the surjectivity half of
[Kol07, Definition 55], by successive approximation). -/
theorem cohenMap_surjective (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I)
    (hx : I = Ideal.span (Set.range x)) :
    Function.Surjective (cohenMap' (K := K) I x hx) := by
  intro ρ
  refine ⟨approxSeries I x γ hγ hker hx ρ, eq_of_forall_mk_pow_eq (I) fun a => ?_⟩
  have h1 : Ideal.Quotient.mk (I ^ a)
      (cohenMap' (K := K) I x hx (approxPartial I x γ hγ hker hx ρ a : MvPowerSeries (Fin d) K)) =
      Ideal.Quotient.mk (I ^ a) ρ := by
    have h := approxRem_eq I x γ hγ hker hx ρ a
    have hmem := (approxRem I x γ hγ hker hx ρ a).2
    rw [h, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero] at hmem
    exact hmem.symm
  have h2 := mk_cohenMap (K := K) I x (x_mem_ideal_of_eq_span I x hx) a
    (approxPartial I x γ hγ hker hx ρ a : MvPowerSeries (Fin d) K)
  rw [levelEval_apply, truncTotal_coe_approxPartial] at h2
  rw [mk_cohenMap, levelEval_apply, truncTotal_approxSeries, ← h2]
  exact h1

/-- The SAME actual complete ring is Noetherian from its original finite ideal and actual Noetherian split coefficient quotient. -/
theorem isNoetherianRing_of_complete_split_quotient [IsNoetherianRing K]
    (γ : B →+* K) (hγ : γ.comp (algebraMap K B) = RingHom.id K)
    (hker : RingHom.ker γ = I) (hfg : I.FG) : IsNoetherianRing B := by
  obtain ⟨d, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  exact isNoetherianRing_of_surjective (MvPowerSeries (Fin d) K) B
    (cohenMap' (K := K) I x hx.symm).toRingHom (cohenMap_surjective I x γ hγ hker hx.symm)

end Hironaka.Geometry.ProperSteinProjectiveCech.CohenSurjective
