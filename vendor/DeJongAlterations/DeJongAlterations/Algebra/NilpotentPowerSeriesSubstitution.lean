import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Actual multivariate substitutions that are identity modulo a nilpotent coefficient ideal

All coefficient ideals are interpreted coefficientwise; finite generation and
adic completeness are not assumed. The nilpotent difference from the identity
is proved using the native finite substitution coefficient formula. No inverse
substitution or automorphism certificate is an input.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NilpotentPowerSeriesSubstitution

open MvPowerSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

variable {R : Type u} [CommRing R] {σ : Type v}
  (I : Ideal R) {a : σ → MvPowerSeries σ R}

/-- The exact original-coordinate equation after actual coefficient reduction. -/
def ReducesToVariables (a : σ → MvPowerSeries σ R) : Prop :=
  ∀ i, MvPowerSeries.map (Ideal.Quotient.mk I) (a i) = MvPowerSeries.X i

/-- The constant coefficient is in the actual coefficient ideal. -/
theorem constantCoeff_mem (hred : ReducesToVariables I a) (i : σ) :
    (a i).constantCoeff ∈ I := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  have h := congrArg MvPowerSeries.constantCoeff (hred i)
  simpa using h

/-- Nilpotent coefficient reduction internally supplies the native admissibility proof. -/
theorem hasSubst [Finite σ] (hI : IsNilpotent I) (hred : ReducesToVariables I a) :
    MvPowerSeries.HasSubst a where
  const_coeff i := by
    obtain ⟨n, hn⟩ := hI
    refine ⟨n, ?_⟩
    have h := Ideal.pow_mem_pow (constantCoeff_mem I hred i) n
    rw [hn] at h
    simpa using h
  coeff_zero _ := Set.toFinite _

/-- Every substituted monomial differs from its original monomial coefficientwise in I. -/
theorem monomialDifference_coeff_mem (hred : ReducesToVariables I a)
    (n d : σ →₀ ℕ) :
    MvPowerSeries.coeff d
      ((n.prod fun i k => a i ^ k) -
        (n.prod fun i k => (MvPowerSeries.X i : MvPowerSeries σ R) ^ k)) ∈ I := by
  change ∀ i, MvPowerSeries.map (Ideal.Quotient.mk I) (a i) = MvPowerSeries.X i at hred
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [← MvPowerSeries.coeff_map]
  simp only [map_sub, Finsupp.prod, map_prod, map_pow, hred,
    MvPowerSeries.map_X, sub_self, map_zero]

/-- Substitution minus the identity as an actual linear endomorphism. -/
def difference (ha : MvPowerSeries.HasSubst a) : Module.End R (MvPowerSeries σ R) :=
  (MvPowerSeries.substAlgHom (R := R) (S := R) ha).toLinearMap - LinearMap.id

/-- The native coefficient formula raises every coefficientwise ideal power by one. -/
theorem difference_coeff_mem (ha : MvPowerSeries.HasSubst a)
    (hred : ReducesToVariables I a) (n : ℕ) (f : MvPowerSeries σ R)
    (hf : ∀ d, MvPowerSeries.coeff d f ∈ I ^ n) :
    ∀ d, MvPowerSeries.coeff d (difference ha f) ∈ I ^ (n + 1) := by
  intro d
  change MvPowerSeries.coeff d (MvPowerSeries.substAlgHom (R := R) (S := R) ha f - f) ∈ I ^ (n + 1)
  rw [map_sub, MvPowerSeries.substAlgHom_apply, MvPowerSeries.coeff_subst ha]
  let hx : MvPowerSeries.HasSubst (fun i : σ => (MvPowerSeries.X i : MvPowerSeries σ R)) := .X
  have hX : MvPowerSeries.coeff d f =
      ∑ᶠ e, MvPowerSeries.coeff e f •
        MvPowerSeries.coeff d (e.prod fun i k => (MvPowerSeries.X i : MvPowerSeries σ R) ^ k) := by
    simpa only [MvPowerSeries.subst_self, id_eq] using
      (MvPowerSeries.coeff_subst hx f d)
  rw [hX, ← finsum_sub_distrib (MvPowerSeries.coeff_subst_finite ha f d)
    (MvPowerSeries.coeff_subst_finite hx f d)]
  have hfinite : (fun e : σ →₀ ℕ =>
      MvPowerSeries.coeff e f • MvPowerSeries.coeff d (e.prod fun i k => a i ^ k) -
      MvPowerSeries.coeff e f • MvPowerSeries.coeff d
        (e.prod fun i k => (MvPowerSeries.X i : MvPowerSeries σ R) ^ k)).HasFiniteSupport :=
    (MvPowerSeries.coeff_subst_finite ha f d).sub (MvPowerSeries.coeff_subst_finite hx f d)
  rw [finsum_eq_sum _ hfinite]
  apply Ideal.sum_mem
  intro e _
  simp only [smul_eq_mul]
  rw [← mul_sub, pow_succ]
  apply Ideal.mul_mem_mul (hf e)
  simpa only [map_sub] using monomialDifference_coeff_mem I hred e d

/-- Iterated differences have their actual coefficients in the corresponding powers of I. -/
theorem difference_pow_coeff_mem (ha : MvPowerSeries.HasSubst a)
    (hred : ReducesToVariables I a) (n : ℕ) (f : MvPowerSeries σ R) :
    ∀ d, MvPowerSeries.coeff d ((difference ha ^ n) f) ∈ I ^ n := by
  induction n with
  | zero => intro d; simp
  | succ n ih =>
    simpa only [pow_succ', Module.End.mul_apply] using
      difference_coeff_mem I ha hred n ((difference ha ^ n) f) ih

/-- The difference from the identity is actually nilpotent, without any supplied operator certificate. -/
theorem difference_isNilpotent (ha : MvPowerSeries.HasSubst a)
    (hI : IsNilpotent I) (hred : ReducesToVariables I a) : IsNilpotent (difference ha) := by
  obtain ⟨n, hn⟩ := hI
  refine ⟨n, ?_⟩
  apply LinearMap.ext
  intro f
  apply MvPowerSeries.ext
  intro d
  have h := difference_pow_coeff_mem I ha hred n f d
  rw [hn] at h
  simpa using h

/-- The original native substitution is bijective. -/
theorem substAlgHom_bijective (ha : MvPowerSeries.HasSubst a)
    (hI : IsNilpotent I) (hred : ReducesToVariables I a) :
    Function.Bijective (MvPowerSeries.substAlgHom (R := R) (S := R) ha) := by
  have hu := (difference_isNilpotent I ha hI hred).isUnit_one_add
  have he : (1 : Module.End R (MvPowerSeries σ R)) + difference ha =
      (MvPowerSeries.substAlgHom (R := R) (S := R) ha).toLinearMap := by
    unfold difference
    change LinearMap.id + ((MvPowerSeries.substAlgHom (R := R) (S := R) ha).toLinearMap - LinearMap.id) = _
    abel
  rw [he] at hu
  exact (Module.End.isUnit_iff _).mp hu

/-- The actual coefficient-preserving substitution automorphism. -/
def substAlgEquiv (ha : MvPowerSeries.HasSubst a)
    (hI : IsNilpotent I) (hred : ReducesToVariables I a) :
    MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R :=
  AlgEquiv.ofBijective (MvPowerSeries.substAlgHom (R := R) (S := R) ha) (substAlgHom_bijective I ha hI hred)

@[simp]
theorem substAlgEquiv_toAlgHom (ha : MvPowerSeries.HasSubst a)
    (hI : IsNilpotent I) (hred : ReducesToVariables I a) :
    (substAlgEquiv I ha hI hred).toAlgHom = MvPowerSeries.substAlgHom (R := R) (S := R) ha := rfl

@[simp]
theorem substAlgEquiv_X (ha : MvPowerSeries.HasSubst a)
    (hI : IsNilpotent I) (hred : ReducesToVariables I a) (i : σ) :
    substAlgEquiv I ha hI hred (MvPowerSeries.X i) = a i :=
  MvPowerSeries.substAlgHom_X ha i

@[simp]
theorem substAlgEquiv_C (ha : MvPowerSeries.HasSubst a)
    (hI : IsNilpotent I) (hred : ReducesToVariables I a) (r : R) :
    substAlgEquiv I ha hI hred (MvPowerSeries.C r) = MvPowerSeries.C r := by
  simpa only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    using (substAlgEquiv I ha hI hred).commutes r

/-- Every actual admissible substitution preserves every coefficientwise ideal. -/
theorem subst_coeff_mem (ha : MvPowerSeries.HasSubst a) (J : Ideal R)
    (f : MvPowerSeries σ R) (hf : ∀ d, MvPowerSeries.coeff d f ∈ J) :
    ∀ d, MvPowerSeries.coeff d (MvPowerSeries.substAlgHom (R := R) (S := R) ha f) ∈ J := by
  intro d
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.coeff_subst ha,
    finsum_eq_sum _ (MvPowerSeries.coeff_subst_finite ha f d)]
  apply Ideal.sum_mem
  intro n _
  simpa only [smul_eq_mul] using J.mul_mem_right _ (hf n)

/-- The exact reduction equation holds on every formal series, not merely on coordinates. -/
theorem map_substAlgHom (ha : MvPowerSeries.HasSubst a)
    (hred : ReducesToVariables I a) (f : MvPowerSeries σ R) :
    MvPowerSeries.map (Ideal.Quotient.mk I)
      (MvPowerSeries.substAlgHom (R := R) (S := R) ha f) =
        MvPowerSeries.map (Ideal.Quotient.mk I) f := by
  rw [MvPowerSeries.substAlgHom_apply, MvPowerSeries.map_subst ha]
  rw [show (fun i => MvPowerSeries.map (Ideal.Quotient.mk I) (a i)) =
    (MvPowerSeries.X : σ → MvPowerSeries σ (R ⧸ I)) from funext hred]
  exact congrFun MvPowerSeries.subst_self _

/-- The inverse coordinates are internally computed from the actual algebra automorphism. -/
def inverseVariables (ha : MvPowerSeries.HasSubst a)
    (hI : IsNilpotent I) (hred : ReducesToVariables I a) (i : σ) : MvPowerSeries σ R :=
  (substAlgEquiv I ha hI hred).symm (MvPowerSeries.X i)

/-- The internally produced inverse coordinate family has the exact original reduction. -/
theorem inverseVariables_reduces (ha : MvPowerSeries.HasSubst a)
    (hI : IsNilpotent I) (hred : ReducesToVariables I a) :
    ReducesToVariables I (inverseVariables I ha hI hred) := by
  intro i
  have he : MvPowerSeries.substAlgHom (R := R) (S := R) ha
      (inverseVariables I ha hI hred i) = MvPowerSeries.X i :=
    (substAlgEquiv I ha hI hred).apply_symm_apply _
  have hm := map_substAlgHom I ha hred (inverseVariables I ha hI hred i)
  rw [he, MvPowerSeries.map_X] at hm
  exact hm.symm

/-- In particular the actual inverse constants belong to I, rather than being assumed zero. -/
theorem inverseVariables_constantCoeff_mem (ha : MvPowerSeries.HasSubst a)
    (hI : IsNilpotent I) (hred : ReducesToVariables I a) (i : σ) :
    (inverseVariables I ha hI hred i).constantCoeff ∈ I :=
  constantCoeff_mem I (inverseVariables_reduces I ha hI hred) i

/-- The inverse coordinate family internally satisfies the native substitution condition. -/
theorem hasSubst_inverseVariables [Finite σ] (ha : MvPowerSeries.HasSubst a)
    (hI : IsNilpotent I) (hred : ReducesToVariables I a) :
    MvPowerSeries.HasSubst (inverseVariables I ha hI hred) :=
  hasSubst I hI (inverseVariables_reduces I ha hI hred)

/-- The entire actual inverse is a native admissible substitution in its internally produced coordinates. -/
theorem symm_toAlgHom_eq_substAlgHom [Finite σ] (ha : MvPowerSeries.HasSubst a)
    (hI : IsNilpotent I) (hred : ReducesToVariables I a) :
    (substAlgEquiv I ha hI hred).symm.toAlgHom =
      MvPowerSeries.substAlgHom (R := R) (S := R)
        (hasSubst_inverseVariables I ha hI hred) := by
  apply AlgHom.ext
  intro f
  apply (substAlgEquiv I ha hI hred).injective
  change substAlgEquiv I ha hI hred ((substAlgEquiv I ha hI hred).symm f) =
    substAlgEquiv I ha hI hred
      (MvPowerSeries.substAlgHom (R := R) (S := R)
        (hasSubst_inverseVariables I ha hI hred) f)
  rw [AlgEquiv.apply_symm_apply]
  change f = MvPowerSeries.substAlgHom (R := R) (S := R) ha
    (MvPowerSeries.substAlgHom (R := R) (S := R) (hasSubst_inverseVariables I ha hI hred) f)
  simp only [MvPowerSeries.substAlgHom_apply]
  rw [MvPowerSeries.subst_comp_subst_apply (hasSubst_inverseVariables I ha hI hred) ha]
  have hv : (fun i => MvPowerSeries.subst a (inverseVariables I ha hI hred i)) =
      (MvPowerSeries.X : σ → MvPowerSeries σ R) := by
    funext i
    rw [← MvPowerSeries.substAlgHom_apply (R := R) (S := R) ha]
    change substAlgEquiv I ha hI hred ((substAlgEquiv I ha hI hred).symm (MvPowerSeries.X i)) = _
    exact (substAlgEquiv I ha hI hred).apply_symm_apply _
  rw [hv, MvPowerSeries.subst_self]
  rfl

/-- Main finite-family endpoint: actual coefficient reduction and nilpotence alone construct the automorphism. -/
def equivOfReduction [Finite σ] (hI : IsNilpotent I) (hred : ReducesToVariables I a) :
    MvPowerSeries σ R ≃ₐ[R] MvPowerSeries σ R :=
  substAlgEquiv I (hasSubst I hI hred) hI hred

@[simp]
theorem equivOfReduction_X [Finite σ] (hI : IsNilpotent I)
    (hred : ReducesToVariables I a) (i : σ) :
    equivOfReduction I hI hred (MvPowerSeries.X i) = a i :=
  substAlgEquiv_X I (hasSubst I hI hred) hI hred i

@[simp]
theorem equivOfReduction_C [Finite σ] (hI : IsNilpotent I)
    (hred : ReducesToVariables I a) (r : R) :
    equivOfReduction I hI hred (MvPowerSeries.C r) = MvPowerSeries.C r :=
  substAlgEquiv_C I (hasSubst I hI hred) hI hred r

end DeJongAlterations.Algebra.NilpotentPowerSeriesSubstitution
