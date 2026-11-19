/-
Copyright (c) 2026. All rights reserved.
-/
import Hironaka.Algebra.ImperfectFieldExample
import Hironaka.Geometry.RegularNode
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.RingTheory.AdjoinRoot

/-!
# The actual regular curve in the imperfect-field example

The coordinate ring is the native polynomial quotient
`k[y][x] / (x² - (y³ - t))`, for `k = F₃(t)`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Polynomial IsLocalRing

namespace Hironaka.Algebra.ImperfectFieldExample

section General

variable {A : Type*} [CommRing A]

theorem polynomial_eval_mem_comap_iff (M : Ideal A[X])
    (hX : X ∈ M) (H : A[X]) : H.eval 0 ∈ M.comap C ↔ H ∈ M := by
  have hd : H - C (H.eval 0) ∈ M := by
    obtain ⟨q, hq⟩ := X_dvd_sub_C (p := H)
    have h := M.mul_mem_right q hX
    simpa only [← hq, coeff_zero_eq_eval_zero] using h
  constructor
  · intro h
    simpa only [sub_add_cancel] using M.add_mem hd h
  · intro h
    change C (H.eval 0) ∈ M
    simpa only [sub_sub_cancel] using M.sub_mem h hd

theorem quadraticEquation_not_mem_square (t : A) (htwo : IsUnit (2 : A))
    (hparam : ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉
        maximalIdeal (Localization.AtPrime p) ^ 2)
    (M : Ideal A[X]) [M.IsPrime] (hF : X ^ 2 - C t ∈ M) :
    algebraMap A[X] (Localization.AtPrime M) (X ^ 2 - C t) ∉
      maximalIdeal (Localization.AtPrime M) ^ 2 := by
  by_cases hX : X ∈ M
  · let p := M.comap C
    have ht : t ∈ p := by
      change C t ∈ M
      have h := M.sub_mem (show X ^ 2 ∈ M by simpa [pow_two] using M.mul_mem_left X hX) hF
      simpa only [sub_sub_cancel] using h
    intro h
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow] at h
    obtain ⟨s, hs, hsf⟩ :=
      (IsLocalization.algebraMap_mem_map_algebraMap_iff M.primeCompl
        (Localization.AtPrime M) (M ^ 2) (X ^ 2 - C t)).mp h
    let e : A[X] →+* A := Polynomial.evalRingHom 0
    have hMp : M.map e ≤ p := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro H hH
      exact (polynomial_eval_mem_comap_iff M hX H).mpr hH
    have he : e (s * (X ^ 2 - C t)) ∈ p ^ 2 := by
      apply pow_le_pow_left' hMp 2
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem e hsf
    have hunit : IsUnit (algebraMap A (Localization.AtPrime p) (e s)) := by
      apply (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p _).mpr
      intro hmem
      exact hs ((polynomial_eval_mem_comap_iff M hX s).mp hmem)
    have hlocal : algebraMap A (Localization.AtPrime p) (-(e s * t)) ∈
        maximalIdeal (Localization.AtPrime p) ^ 2 := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
      apply Ideal.mem_map_of_mem
      simpa [e] using he
    apply hparam p ht
    apply (Ideal.unit_mul_mem_iff_mem _ hunit).mp
    simpa only [map_neg, map_mul, neg_neg] using
      (maximalIdeal (Localization.AtPrime p) ^ 2).neg_mem hlocal
  · apply Geometry.RegularNode.not_mem_square_of_derivation M Polynomial.derivative' hF
    have htwoM : (2 : A[X]) ∉ M := M.notMem_of_isUnit (htwo.map C)
    have hprod : (2 : A[X]) * X ∉ M := by
      intro h
      exact (‹M.IsPrime›.mem_or_mem h).elim htwoM hX
    simpa [one_add_one_eq_two, C_ofNat] using hprod

theorem isRegularRing_quadratic [IsRegularRing A] (t : A) (htwo : IsUnit (2 : A))
    (hparam : ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉
        maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsRegularRing (AdjoinRoot (X ^ 2 - C t)) := by
  let : IsRegularRing A[X] := Polynomial.isRegularRing_of_isRegularRing A
  let : IsNoetherianRing A[X] := inferInstance
  let : IsNoetherianRing (A[X] ⧸ Ideal.span {X ^ 2 - C t}) :=
    Ideal.Quotient.isNoetherianRing _
  change IsRegularRing (A[X] ⧸ Ideal.span {X ^ 2 - C t})
  refine (isRegularRing_iff (R := A[X] ⧸ Ideal.span {X ^ 2 - C t})).mpr ?_
  intro q hq
  let : q.IsPrime := hq
  let I : Ideal A[X] := Ideal.span {X ^ 2 - C t}
  let M := q.comap (Ideal.Quotient.mk I)
  let : M.IsPrime := Ideal.comap_isPrime _ q
  let L := Localization.AtPrime M
  have hF : X ^ 2 - C t ∈ M := by
    change Ideal.Quotient.mk I (X ^ 2 - C t) ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))]
    exact q.zero_mem
  have hmem : algebraMap A[X] L (X ^ 2 - C t) ∈ maximalIdeal L :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L M _).mpr hF
  let : IsRegularLocalRing (L ⧸ Ideal.span {algebraMap A[X] L (X ^ 2 - C t)}) :=
    RegularQuotient.isRegularLocalRing_quotient_parameter L _ hmem
      (quadraticEquation_not_mem_square t htwo hparam M hF)
  have hmap : I.map (algebraMap A[X] L) =
      Ideal.span {algebraMap A[X] L (X ^ 2 - C t)} := by
    simp only [I, Ideal.map_span, Set.image_singleton]
  let : IsRegularLocalRing (L ⧸ I.map (algebraMap A[X] L)) := by
    rw [hmap]
    infer_instance
  exact IsRegularLocalRing.of_ringEquiv (Geometry.RegularNode.quotientLocalizationEquiv I q)

theorem generator_not_mem_square [IsDomain A] {t : A} (ht0 : t ≠ 0)
    (ht : ¬ IsUnit t) : t ∉ Ideal.span ({t} : Set A) ^ 2 := by
  intro h
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨a, ha⟩ := h
  have he : t * 1 = t * (t * a) := by simpa [pow_two, mul_assoc] using ha
  have hu : t * a = 1 := (mul_left_cancel₀ ht0 he).symm
  exact ht (isUnit_iff_dvd_one.mpr ⟨a, hu.symm⟩)

theorem irreducible_not_mem_local_square [IsDomain A] [IsPrincipalIdealRing A]
    {t : A} (ht : Irreducible t) (p : Ideal A) [p.IsPrime] (htp : t ∈ p) :
    algebraMap A (Localization.AtPrime p) t ∉
      maximalIdeal (Localization.AtPrime p) ^ 2 := by
  have heq : Ideal.span ({t} : Set A) = p :=
    (PrincipalIdealRing.isMaximal_of_irreducible ht).eq_of_le
      (‹p.IsPrime›.ne_top) ((Ideal.span_singleton_le_iff_mem p).mpr htp)
  have hm : maximalIdeal (Localization.AtPrime p) =
      Ideal.span {algebraMap A (Localization.AtPrime p) t} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    calc
      p.map (algebraMap A (Localization.AtPrime p)) =
          (Ideal.span {t}).map (algebraMap A (Localization.AtPrime p)) :=
        congrArg (Ideal.map (algebraMap A (Localization.AtPrime p))) heq.symm
      _ = _ := by rw [Ideal.map_span, Set.image_singleton]
  have ht0 : algebraMap A (Localization.AtPrime p) t ≠ 0 :=
    by simpa using
      (IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors).ne ht.ne_zero
  have htunit : ¬ IsUnit (algebraMap A (Localization.AtPrime p) t) := by
    exact (IsLocalization.AtPrime.isUnit_to_map_iff
      (Localization.AtPrime p) p t).not.mpr (not_not.mpr htp)
  rw [hm]
  exact generator_not_mem_square ht0 htunit

end General

/-- The polynomial ring in the source coordinate `y`. -/
abbrev CoefficientRing := BaseField[X]

def cubic : CoefficientRing := X ^ 3 - C alpha

theorem cubic_irreducible : Irreducible cubic :=
  X_pow_sub_C_irreducible_of_prime (by decide : Nat.Prime 3) alpha_not_cube

def quadraticEquation : CoefficientRing[X] := X ^ 2 - C cubic

/-- The native actual quotient defining the source's curve. -/
abbrev CurveRing := AdjoinRoot quadraticEquation

instance curveRing_isRegular : IsRegularRing CurveRing := by
  apply isRegularRing_quadratic cubic
  · exact isUnit_iff_dvd_one.mpr ⟨2, by
      have h : (3 : CoefficientRing) = 0 := CharP.cast_eq_zero _ 3
      linear_combination -h⟩
  · exact irreducible_not_mem_local_square cubic_irreducible

theorem quadraticEquation_monic : quadraticEquation.Monic :=
  monic_X_pow_sub_C cubic (by decide)

theorem quadraticEquation_irreducible : Irreducible quadraticEquation := by
  let P : Ideal CoefficientRing := Ideal.span {cubic}
  have hP : P.IsPrime := (PrincipalIdealRing.isMaximal_of_irreducible cubic_irreducible).isPrime
  have hE : quadraticEquation.IsEisensteinAt P := by
    refine ⟨?_, ?_, ?_⟩
    · rw [quadraticEquation_monic.leadingCoeff]
      exact hP.one_notMem
    · intro n hn
      have hn2 : n < 2 := by simpa [quadraticEquation] using hn
      interval_cases n
      · simpa [quadraticEquation] using
          P.neg_mem (Ideal.subset_span (Set.mem_singleton cubic))
      · simp [quadraticEquation]
    · have hn : -cubic ∉ P ^ 2 := by
        intro h
        exact generator_not_mem_square cubic_irreducible.ne_zero
          cubic_irreducible.not_isUnit (by simpa using (P ^ 2).neg_mem h)
      simpa [quadraticEquation] using hn
  exact hE.irreducible hP quadraticEquation_monic.isPrimitive (by simp [quadraticEquation])

instance curveRing_isDomain : IsDomain CurveRing :=
  AdjoinRoot.isDomain_of_prime quadraticEquation_irreducible.prime

def curveX : CurveRing := AdjoinRoot.root quadraticEquation

def curveY : CurveRing := AdjoinRoot.of quadraticEquation (X : CoefficientRing)

theorem curveX_sq : curveX ^ 2 = algebraMap CoefficientRing CurveRing cubic := by
  have h := AdjoinRoot.eval₂_root quadraticEquation
  change (X ^ 2 - C cubic).eval₂ (AdjoinRoot.of quadraticEquation)
    (AdjoinRoot.root quadraticEquation) = 0 at h
  apply sub_eq_zero.mp
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, AdjoinRoot.algebraMap_eq, curveX] using h

theorem curveX_sq_eq_curveY_cube :
    curveX ^ 2 = curveY ^ 3 - algebraMap BaseField CurveRing alpha := by
  rw [curveX_sq]
  change (AdjoinRoot.of quadraticEquation) (X ^ 3 - C alpha) = _
  rw [map_sub, map_pow]
  congr 1

theorem curveX_ne_zero : curveX ≠ 0 := by
  change AdjoinRoot.mk quadraticEquation X ≠ 0
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt quadraticEquation_monic X_ne_zero
    (by simp [quadraticEquation])

end Hironaka.Algebra.ImperfectFieldExample
