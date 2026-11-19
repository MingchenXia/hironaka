/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.BlowUp.CoordinateSubspace.Split

/-!
# The initial-form map from the Rees algebra of the centre to `𝒪(L)[u]`

For `I = (x_0, …, x_{r-1}) ⊆ A[x]` (`r ≤ n`) and `𝒪(L) = A[x]/I`, the graded ring homomorphism
`Φ : R̃ = ⊕ I^k t^k → 𝒪(L)[u_0, …, u_{r-1}]`, `c t^k ↦ in_k(c)`: the degree-`k` homogeneous
component (the *initial form*) of the image of `c ∈ I^k` under `A[x] ≃ 𝒪(L)[u]`
(`centerSplitEquiv`, `Hironaka.Scheme.BlowUp.CoordinateSubspace.Split`).  It is additive, and
multiplicative because initial forms multiply (`homogeneousComponent_mul_of_mem`); it sends
`x_j t ↦ u_j`, constants `c ∈ A[x]` to `c̄`, it is surjective in each degree, and its kernel in
degree `k` is `I^{k+1} t^k` — so it is the identification `R̃/I·R̃ = ⊕ I^k/I^{k+1} ≅ 𝒪(L)[u]` of
the associated graded ring of the coordinate ideal with the polynomial ring
([Mat89, Theorem 16.2] for this monomial case).  `Proj` of it is the closed immersion
`ℙ^{r-1}_L ⟶ B` onto the exceptional divisor
(`Hironaka.Scheme.BlowUp.CoordinateSubspace.ExceptionalProj`).
-/

@[expose] public section

universe u

open MvPolynomial reesAlgebra

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry.CoordinateSubspace

variable (A : Type u) [CommRing A] (n r : ℕ) (hrn : r ≤ n)

/-- The initial-form map on polynomials in `t`: `∑ c_k t^k ↦ ∑ in_k(c_k)`. -/
noncomputable def initialAux :
    Polynomial (MvPolynomial (Fin n) A) →+
      MvPolynomial (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) where
  toFun p := p.sum fun k c => homogeneousComponent k (centerSplitEquiv A n r hrn c)
  map_zero' :=
    Polynomial.sum_zero_index
      (S := MvPolynomial (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r))
      fun k c => homogeneousComponent k (centerSplitEquiv A n r hrn c)
  map_add' p q :=
    Polynomial.sum_add_index
      (S := MvPolynomial (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r))
      p q (fun k c => homogeneousComponent k (centerSplitEquiv A n r hrn c))
      (fun _ => by rw [map_zero, map_zero]) fun _ _ _ => by rw [map_add, map_add]

theorem initialAux_monomial (k : ℕ) (c : MvPolynomial (Fin n) A) :
    initialAux A n r hrn (Polynomial.monomial k c) =
      homogeneousComponent k (centerSplitEquiv A n r hrn c) := by
  change (Polynomial.monomial k c).sum
    (fun k c => homogeneousComponent k (centerSplitEquiv A n r hrn c)) = _
  rw [Polynomial.sum_monomial_index]
  simp

/-- The variable `u_j` of `𝒪(L)[u]`, `j : Fin r`, as the generator `x_j` of the center. -/
noncomputable abbrev genXOfFin (j : Fin r) : centerIdeal A n r :=
  ⟨X ⟨j.val, lt_of_lt_of_le j.2 hrn⟩, X_mem_centerIdeal A n r j.2⟩

/-- The presentation of the Rees algebra: `A[x][u_0, …, u_{r-1}] → R̃`, `u_j ↦ x_j t`. -/
noncomputable def reesPresentation :
    MvPolynomial (Fin r) (MvPolynomial (Fin n) A) →ₐ[MvPolynomial (Fin n) A]
      reesAlgebra (centerIdeal A n r) :=
  MvPolynomial.aeval fun j => degreeOne (centerIdeal A n r) (genXOfFin A n r hrn j)

/-- The generators of the presentation, in the ambient polynomial ring: `x_j t = C x_j · t`. -/
noncomputable abbrev genMonomial (j : Fin r) : Polynomial (MvPolynomial (Fin n) A) :=
  Polynomial.C (X ⟨j.val, lt_of_lt_of_le j.2 hrn⟩) * Polynomial.X

/-- The presentation followed by the inclusion of the Rees algebra into `A[x][t]`. -/
noncomputable abbrev ambientPresentation :
    MvPolynomial (Fin r) (MvPolynomial (Fin n) A) →ₐ[MvPolynomial (Fin n) A]
      Polynomial (MvPolynomial (Fin n) A) :=
  MvPolynomial.aeval (genMonomial A n r hrn)

theorem val_comp_reesPresentation :
    (Subalgebra.val (reesAlgebra (centerIdeal A n r))).comp (reesPresentation A n r hrn) =
      ambientPresentation A n r hrn := by
  refine MvPolynomial.algHom_ext fun j => ?_
  rw [AlgHom.comp_apply, reesPresentation, aeval_X, ambientPresentation, aeval_X,
    Subalgebra.coe_val, reesAlgebra.coe_degreeOne, genMonomial,
    ← Polynomial.C_mul_X_pow_eq_monomial, pow_one]

theorem coe_reesPresentation (F : MvPolynomial (Fin r) (MvPolynomial (Fin n) A)) :
    ((reesPresentation A n r hrn F : reesAlgebra (centerIdeal A n r)) :
        Polynomial (MvPolynomial (Fin n) A)) =
      ambientPresentation A n r hrn F :=
  AlgHom.congr_fun (val_comp_reesPresentation A n r hrn) F

/-- The presentation is onto: the Rees algebra is generated over `A[x]` by the `x_j t`. -/
theorem reesPresentation_surjective : Function.Surjective (reesPresentation A n r hrn) := by
  intro p
  have hp : (p : Polynomial (MvPolynomial (Fin n) A)) ∈ (ambientPresentation A n r hrn).range := by
    have hmem : (p : Polynomial (MvPolynomial (Fin n) A)) ∈ Algebra.adjoin (MvPolynomial (Fin n) A)
        (Submodule.map (Polynomial.monomial 1 : MvPolynomial (Fin n) A →ₗ[MvPolynomial (Fin n) A]
          Polynomial (MvPolynomial (Fin n) A)) (centerIdeal A n r) : Set _) :=
      (adjoin_monomial_eq_reesAlgebra (I := centerIdeal A n r)).ge p.2
    refine Algebra.adjoin_le ?_ hmem
    rintro _ ⟨a, ha, rfl⟩
    change Polynomial.monomial 1 a ∈ (ambientPresentation A n r hrn).range
    have hspan : Submodule.span (MvPolynomial (Fin n) A) (X '' center n r) ≤
        Submodule.comap (Polynomial.monomial 1 : MvPolynomial (Fin n) A →ₗ[MvPolynomial (Fin n) A]
          Polynomial (MvPolynomial (Fin n) A))
          (Subalgebra.toSubmodule (ambientPresentation A n r hrn).range) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, hi, rfl⟩
      change Polynomial.monomial 1 (X i) ∈ (ambientPresentation A n r hrn).range
      refine (AlgHom.mem_range _).mpr ⟨X ⟨i.val, hi⟩, ?_⟩
      rw [ambientPresentation, aeval_X, genMonomial, ← Polynomial.C_mul_X_pow_eq_monomial, pow_one]
    exact hspan ha
  obtain ⟨F, hF⟩ := hp
  refine ⟨F, Subtype.ext ?_⟩
  rw [coe_reesPresentation]
  exact hF

/-- The coefficient map `A[x][u] → 𝒪(L)[u]`. -/
noncomputable abbrev coeffQuotient :
    MvPolynomial (Fin r) (MvPolynomial (Fin n) A) →+*
      MvPolynomial (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) :=
  MvPolynomial.map (Ideal.Quotient.mk (centerIdeal A n r))

/-- `x^β ↦ u^β` under `centerSplitEquiv`. -/
theorem centerSplitEquiv_prod_X_pow (β : Fin r →₀ ℕ) :
    centerSplitEquiv A n r hrn (∏ j ∈ β.support, X ⟨j.val, lt_of_lt_of_le j.2 hrn⟩ ^ β j) =
      monomial β 1 := by
  rw [map_prod]
  have h : ∀ j ∈ β.support,
      centerSplitEquiv A n r hrn (X ⟨j.val, lt_of_lt_of_le j.2 hrn⟩ ^ β j) = X j ^ β j :=
    fun j _ => by rw [map_pow, centerSplitEquiv_X_of_lt A n r hrn j.2]
  rw [Finset.prod_congr rfl h, monomial_eq, C_1, one_mul, Finsupp.prod]

/-- The key identity: the initial form of the image of `F` in the Rees algebra is the reduction of
the coefficients of `F` modulo `I`. -/
theorem initialAux_coe_reesPresentation (F : MvPolynomial (Fin r) (MvPolynomial (Fin n) A)) :
    initialAux A n r hrn (reesPresentation A n r hrn F : Polynomial (MvPolynomial (Fin n) A)) =
      coeffQuotient A n r F := by
  rw [coe_reesPresentation]
  induction F using MvPolynomial.induction_on' with
  | monomial β c =>
    rw [ambientPresentation, aeval_monomial, map_monomial]
    have hprod : (β.prod fun j e => genMonomial A n r hrn j ^ e) =
        Polynomial.C (∏ j ∈ β.support, X ⟨j.val, lt_of_lt_of_le j.2 hrn⟩ ^ β j) *
          Polynomial.X ^ β.degree := by
      rw [Finsupp.prod, Finsupp.degree_apply,
        _root_.map_prod (Polynomial.C (R := MvPolynomial (Fin n) A)),
        ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [genMonomial, mul_pow, map_pow]
    rw [hprod, Polynomial.algebraMap_eq, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.C_mul_X_pow_eq_monomial, initialAux_monomial, map_mul,
      centerSplitEquiv_prod_X_pow]
    have h0 : centerSplitEquiv A n r hrn c ∈ (Ideal.span (Set.range (X : Fin r →
        MvPolynomial (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)))) ^ 0 := by
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    have hβ : (monomial β (1 : MvPolynomial (Fin n) A ⧸ centerIdeal A n r)) ∈
        (Ideal.span (Set.range (X : Fin r →
          MvPolynomial (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)))) ^ β.degree := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod, Finsupp.degree_apply]
      exact prod_pow_mem_pow (Ideal.span (Set.range X)) β.support β X
        fun j => Ideal.subset_span ⟨j, rfl⟩
    have hcc := RingHom.congr_fun (constantCoeff_comp_centerSplitEquiv A n r hrn) c
    rw [RingHom.comp_apply, RingHom.coe_coe] at hcc
    rw [show β.degree = 0 + β.degree from (zero_add _).symm, homogeneousComponent_mul_of_mem h0 hβ,
      homogeneousComponent_eq_self (isHomogeneous_monomial _ rfl),
      homogeneousComponent_zero, ← constantCoeff_eq, hcc, C_mul_monomial, mul_one]
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, map_add]

/-- The initial-form ring homomorphism `Φ : R̃ → 𝒪(L)[u]`,
`c t^k ↦ in_k(c)`, defined through the presentation `A[x][u] → R̃`: it is `A[x][u] → 𝒪(L)[u]`
(reduction of the coefficients) on the quotient of `A[x][u]` by the kernel of the presentation. -/
noncomputable def reesInitial :
    reesAlgebra (centerIdeal A n r) →+*
      MvPolynomial (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) :=
  (Ideal.Quotient.lift (RingHom.ker (reesPresentation A n r hrn).toRingHom) (coeffQuotient A n r)
    fun F hF => by
      rw [RingHom.mem_ker] at hF
      change reesPresentation A n r hrn F = 0 at hF
      rw [← initialAux_coe_reesPresentation A n r hrn F, hF, ZeroMemClass.coe_zero,
        map_zero]).comp
    (RingHom.quotientKerEquivOfSurjective (reesPresentation_surjective A n r hrn)).symm.toRingHom

theorem reesInitial_apply (p : reesAlgebra (centerIdeal A n r)) :
    reesInitial A n r hrn p = initialAux A n r hrn (p : Polynomial (MvPolynomial (Fin n) A)) := by
  obtain ⟨F, rfl⟩ := reesPresentation_surjective A n r hrn p
  rw [reesInitial, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    initialAux_coe_reesPresentation]
  have : (RingHom.quotientKerEquivOfSurjective (reesPresentation_surjective A n r hrn)).symm
      (reesPresentation A n r hrn F) = Ideal.Quotient.mk _ F :=
    RingHom.quotientKerEquivOfSurjective_symm_apply _ F
  rw [this, Ideal.Quotient.lift_mk]

theorem reesInitial_mk_monomial {k : ℕ} {c : MvPolynomial (Fin n) A}
    (hc : c ∈ centerIdeal A n r ^ k) :
    reesInitial A n r hrn ⟨Polynomial.monomial k c, reesAlgebra.monomial_mem.mpr hc⟩ =
      homogeneousComponent k (centerSplitEquiv A n r hrn c) := by
  rw [reesInitial_apply]
  exact initialAux_monomial A n r hrn k c

/-- `Φ` is graded. -/
theorem reesInitial_mem {k : ℕ} {p : reesAlgebra (centerIdeal A n r)}
    (hp : p ∈ grading (centerIdeal A n r) k) :
    reesInitial A n r hrn p ∈
      homogeneousSubmodule (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) k := by
  obtain ⟨c, -, hpc⟩ := reesAlgebra.mem_grading_iff_exists.mp hp
  rw [reesInitial_apply A n r hrn, hpc, initialAux_monomial]
  exact homogeneousComponent_mem _ _

/-- `Φ` as a graded ring homomorphism `R̃ →+*ᵍ 𝒪(L)[u]`. -/
noncomputable def reesInitialGraded :
    grading (centerIdeal A n r) →+*ᵍ
      homogeneousSubmodule (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) where
  toRingHom := reesInitial A n r hrn
  map_mem hp := reesInitial_mem A n r hrn hp

theorem coe_reesInitialGraded :
    ⇑(reesInitialGraded A n r hrn) = ⇑(reesInitial A n r hrn) := rfl

/-- `Φ (x_j t) = u_j`. -/
theorem reesInitial_degreeOne_genX (j : Fin n) (hj : j.val < r) :
    reesInitial A n r hrn (degreeOne (centerIdeal A n r) ⟨X j, X_mem_centerIdeal A n r hj⟩) =
      X ⟨j, hj⟩ := by
  rw [reesInitial_apply A n r hrn, reesAlgebra.coe_degreeOne, initialAux_monomial]
  change homogeneousComponent 1 (centerSplitEquiv A n r hrn (X j)) = _
  rw [centerSplitEquiv_X_of_lt A n r hrn hj]
  exact homogeneousComponent_eq_self (isHomogeneous_X _ _)

/-- `Φ` on the constants: `c ↦ c̄`. -/
theorem reesInitial_algebraMap (c : MvPolynomial (Fin n) A) :
    reesInitial A n r hrn
        (algebraMap (MvPolynomial (Fin n) A) (reesAlgebra (centerIdeal A n r)) c) =
      C (Ideal.Quotient.mk (centerIdeal A n r) c) := by
  rw [reesInitial_apply A n r hrn]
  change initialAux A n r hrn (Polynomial.C c) = _
  rw [← Polynomial.monomial_zero_left, initialAux_monomial, homogeneousComponent_zero]
  congr 1
  rw [← constantCoeff_eq]
  exact RingHom.congr_fun (constantCoeff_comp_centerSplitEquiv A n r hrn) c

/-- `Φ` is surjective in each degree: a homogeneous `F` of degree `k` is the image of the monomial
`c t^k`, `c` the preimage of `F` under `centerSplitEquiv` (which lies in `I^k`). -/
theorem exists_reesInitial_eq {k : ℕ}
    {F : MvPolynomial (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)}
    (hF : F ∈ homogeneousSubmodule (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r) k) :
    ∃ p ∈ grading (centerIdeal A n r) k, reesInitial A n r hrn p = F := by
  have hFhom : F.IsHomogeneous k := (mem_homogeneousSubmodule k F).mp hF
  have hFk : F ∈ (Ideal.span (Set.range (X : Fin r →
      MvPolynomial (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)))) ^ k :=
    mem_span_range_X_pow_of_forall fun d hd => by
      have h1 : d.degree = k := by
        have := hFhom (mem_support_iff.mp hd)
        rwa [Finsupp.degree_eq_weight_one]
      exact h1.ge
  have hc : (centerSplitEquiv A n r hrn).symm F ∈ centerIdeal A n r ^ k := by
    rw [mem_pow_iff_centerSplitEquiv_mem A n r hrn, AlgEquiv.apply_symm_apply]
    exact hFk
  refine ⟨⟨Polynomial.monomial k _, reesAlgebra.monomial_mem.mpr hc⟩,
    reesAlgebra.mem_grading_of_coe_eq_monomial rfl, ?_⟩
  rw [reesInitial_mk_monomial A n r hrn hc, AlgEquiv.apply_symm_apply]
  exact homogeneousComponent_eq_self hFhom

/-- The hypothesis of `Proj.map`: the irrelevant ideal of `𝒪(L)[u]` is contained in the image of
the irrelevant ideal of `R̃`. -/
theorem irrelevant_le_map_reesInitialGraded :
    HomogeneousIdeal.irrelevant
        (homogeneousSubmodule (Fin r) (MvPolynomial (Fin n) A ⧸ centerIdeal A n r)) ≤
      (HomogeneousIdeal.irrelevant (grading (centerIdeal A n r))).map
        (reesInitialGraded A n r hrn) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map,
    HomogeneousIdeal.toIdeal_irrelevant_le]
  intro i hi F hF
  obtain ⟨p, hp, rfl⟩ := exists_reesInitial_eq A n r hrn hF
  have h := Ideal.mem_map_of_mem (reesInitialGraded A n r hrn)
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hi hp)
  rw [coe_reesInitialGraded] at h
  exact h

/-- The kernel of `Φ` in degree `k`: `Φ (c t^k) = 0` iff `c ∈ I^{k+1}` (for `c ∈ I^k`). -/
theorem reesInitial_mk_monomial_eq_zero_iff {k : ℕ} {c : MvPolynomial (Fin n) A}
    (hc : c ∈ centerIdeal A n r ^ k) :
    reesInitial A n r hrn ⟨Polynomial.monomial k c, reesAlgebra.monomial_mem.mpr hc⟩ = 0 ↔
      c ∈ centerIdeal A n r ^ (k + 1) := by
  rw [reesInitial_mk_monomial A n r hrn hc,
    homogeneousComponent_eq_zero_iff_mem_succ ((mem_pow_iff_centerSplitEquiv_mem A n r hrn).mp hc),
    ← mem_pow_iff_centerSplitEquiv_mem]

end AlgebraicGeometry.CoordinateSubspace
