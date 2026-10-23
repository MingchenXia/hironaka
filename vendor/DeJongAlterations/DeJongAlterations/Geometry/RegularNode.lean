import DeJongAlterations.Algebra.NodeChart
import DeJongAlterations.Algebra.RegularQuotient
import DeJongAlterations.Regular
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# Regularity of the actual node ring

The equation `u * w - t` is a local parameter whenever the base coefficient
is a parameter at primes where it vanishes. No regularity certificate for
the node ring or its localizations is assumed.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial IsLocalRing AlgebraicGeometry

namespace DeJongAlterations.Geometry.RegularNode

variable {R : Type*} [CommRing R]

/-- A derivation takes the square of an ideal into the ideal. -/
theorem derivation_mem_of_mem_square {S : Type*} [CommRing S] [Algebra S R]
    (I : Ideal R) (D : Derivation S R R)
    {f : R} (hf : f ∈ I ^ 2) : D f ∈ I := by
  rw [pow_two, ← Ideal.smul_eq_mul] at hf
  refine Submodule.smul_induction_on hf ?_ ?_
  · intro x hx y hy
    simpa only [smul_eq_mul, Derivation.leibniz] using
      I.add_mem (I.mul_mem_right (D y) hx) (I.mul_mem_right (D x) hy)
  · intro x y hx hy
    simpa only [map_add] using I.add_mem hx hy

/-- A nonzero derivative modulo a prime detects a parameter after localization. -/
theorem not_mem_square_of_derivation {S : Type*} [CommRing S] [Algebra S R]
    (p : Ideal R) [p.IsPrime] (D : Derivation S R R) {f : R}
    (hf : f ∈ p) (hDf : D f ∉ p) :
    algebraMap R (Localization.AtPrime p) f ∉
      maximalIdeal (Localization.AtPrime p) ^ 2 := by
  intro h
  rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow] at h
  obtain ⟨s, hs, hsf⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
      (Localization.AtPrime p) (p ^ 2) f).mp h
  have hDsf := derivation_mem_of_mem_square p D hsf
  have hsmul : s * D f ∈ p := by
    have h := p.sub_mem hDsf (p.mul_mem_right (D s) hf)
    simpa only [Derivation.leibniz, smul_eq_mul, add_sub_cancel_right] using h
  exact hs ((‹p.IsPrime›.mem_or_mem hsmul).resolve_right hDf)

/-- Quotient and localization commute at the actual corresponding primes. -/
def quotientLocalizationEquiv (I : Ideal R) (q : Ideal (R ⧸ I)) [q.IsPrime] :
    ((Localization.AtPrime (q.comap (Ideal.Quotient.mk I))) ⧸
      I.map (algebraMap R (Localization.AtPrime (q.comap (Ideal.Quotient.mk I))))) ≃+*
      Localization.AtPrime q := by
  let p := q.comap (Ideal.Quotient.mk I)
  let L := Localization.AtPrime p
  let T := L ⧸ I.map (algebraMap R L)
  have heq : Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl = q.primeCompl :=
    q.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I)
      Ideal.Quotient.mk_surjective
  let : IsLocalization q.primeCompl T := by
    rw [← heq]
    infer_instance
  exact (IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)).toRingEquiv

variable {A : Type*} [CommRing A]

/-- Evaluation at zero differs from a polynomial by an element of any ideal
containing both variables. -/
theorem sub_C_eval_mem (M : Ideal (MvPolynomial (Fin 2) A))
    (hX : ∀ i : Fin 2, X i ∈ M) (H : MvPolynomial (Fin 2) A) :
    H - C (eval (fun _ : Fin 2 ↦ 0) H) ∈ M := by
  induction H using MvPolynomial.induction_on with
  | C a => simp
  | add H K hH hK =>
      simpa only [map_add, add_sub_add_comm] using M.add_mem hH hK
  | mul_X H i _ =>
      simpa only [map_mul, eval_X, mul_zero, map_zero, sub_zero] using
        M.mul_mem_left H (hX i)

/-- If both variables lie in an ideal, evaluation contracts it to the base. -/
theorem eval_mem_comap_iff (M : Ideal (MvPolynomial (Fin 2) A))
    (hX : ∀ i : Fin 2, X i ∈ M) (H : MvPolynomial (Fin 2) A) :
    eval (fun _ : Fin 2 ↦ 0) H ∈ M.comap C ↔ H ∈ M := by
  change C (eval (fun _ : Fin 2 ↦ 0) H) ∈ M ↔ H ∈ M
  constructor
  · intro h
    simpa only [sub_add_cancel] using M.add_mem (sub_C_eval_mem M hX H) h
  · intro h
    simpa only [sub_sub_cancel] using M.sub_mem h (sub_C_eval_mem M hX H)

/-- The actual node equation is a parameter in every ambient local ring
where it vanishes, assuming the corresponding base divisor is a parameter. -/
theorem nodeEquation_not_mem_square (t : A)
    (hparam : ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉
        maximalIdeal (Localization.AtPrime p) ^ 2)
    (M : Ideal (MvPolynomial (Fin 2) A)) [M.IsPrime]
    (hF : X 0 * X 1 - C t ∈ M) :
    algebraMap (MvPolynomial (Fin 2) A) (Localization.AtPrime M)
      (X 0 * X 1 - C t) ∉ maximalIdeal (Localization.AtPrime M) ^ 2 := by
  by_cases hu : X (0 : Fin 2) ∈ M
  · by_cases hw : X (1 : Fin 2) ∈ M
    · have hX : ∀ i : Fin 2, X i ∈ M := by
        intro i
        fin_cases i
        · exact hu
        · exact hw
      let p : Ideal A := M.comap C
      let : p.IsPrime := Ideal.comap_isPrime C M
      have ht : t ∈ p := by
        change C t ∈ M
        have h := M.sub_mem (M.mul_mem_right (X 1) hu) hF
        simpa only [sub_sub_cancel] using h
      intro h
      rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow] at h
      obtain ⟨s, hs, hsF⟩ :=
        (IsLocalization.algebraMap_mem_map_algebraMap_iff M.primeCompl
          (Localization.AtPrime M) (M ^ 2) (X 0 * X 1 - C t)).mp h
      let e : MvPolynomial (Fin 2) A →+* A := eval (fun _ ↦ 0)
      have hMp : M.map e ≤ p := by
        apply Ideal.map_le_iff_le_comap.mpr
        intro H hH
        exact (eval_mem_comap_iff M hX H).mpr hH
      have he : e (s * (X 0 * X 1 - C t)) ∈ p ^ 2 := by
        apply pow_le_pow_left' hMp 2
        rw [← Ideal.map_pow]
        exact Ideal.mem_map_of_mem e hsF
      have hunit : IsUnit (algebraMap A (Localization.AtPrime p) (e s)) := by
        apply (IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime p) p _).mpr
        intro hmem
        exact hs ((eval_mem_comap_iff M hX s).mp hmem)
      have hlocal : algebraMap A (Localization.AtPrime p) (-(e s * t)) ∈
          maximalIdeal (Localization.AtPrime p) ^ 2 := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
        apply Ideal.mem_map_of_mem
        simpa [e] using he
      apply hparam p ht
      apply (Ideal.unit_mul_mem_iff_mem _ hunit).mp
      simpa only [map_neg, map_mul, neg_neg] using
        (maximalIdeal (Localization.AtPrime p) ^ 2).neg_mem hlocal
    · apply not_mem_square_of_derivation M (pderiv (0 : Fin 2)) hF
      simpa using hw
  · apply not_mem_square_of_derivation M (pderiv (1 : Fin 2)) hF
    simpa using hu

/-- The actual `A[u,w]/(uw-t)` is regular when the base divisor is a parameter
at every prime containing it. -/
theorem isRegularRing_nodeQuotient [IsRegularRing A] (t : A)
    (hparam : ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉
        maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsRegularRing (MvPolynomial (Fin 2) A ⧸ Algebra.NodeChart.uChartIdeal A t) := by
  apply isRegularRing_iff.mpr
  intro q hq
  let I := Algebra.NodeChart.uChartIdeal A t
  let M := q.comap (Ideal.Quotient.mk I)
  let L := Localization.AtPrime M
  have hF : X 0 * X 1 - C t ∈ M := by
    change Ideal.Quotient.mk I (X 0 * X 1 - C t) ∈ q
    have hzero : Ideal.Quotient.mk I (X 0 * X 1 - C t) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [hzero]
    exact q.zero_mem
  have hmem : algebraMap (MvPolynomial (Fin 2) A) L (X 0 * X 1 - C t) ∈
      maximalIdeal L :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff L M _).mpr hF
  let : IsRegularLocalRing (L ⧸ Ideal.span
      {algebraMap (MvPolynomial (Fin 2) A) L (X 0 * X 1 - C t)}) :=
    Algebra.RegularQuotient.isRegularLocalRing_quotient_parameter L _ hmem
      (nodeEquation_not_mem_square t hparam M hF)
  have hmap : I.map (algebraMap (MvPolynomial (Fin 2) A) L) =
      Ideal.span {algebraMap (MvPolynomial (Fin 2) A) L (X 0 * X 1 - C t)} := by
    simp only [I, Algebra.NodeChart.uChartIdeal, Ideal.map_span, Set.image_singleton]
  let : IsRegularLocalRing (L ⧸ I.map (algebraMap (MvPolynomial (Fin 2) A) L)) := by
    rw [hmap]
    infer_instance
  exact IsRegularLocalRing.of_ringEquiv (quotientLocalizationEquiv I q)

/-- The native spectrum of the node quotient has regular actual scheme stalks. -/
theorem isRegularScheme_nodeQuotient [IsRegularRing A] (t : A)
    (hparam : ∀ (p : Ideal A) [p.IsPrime], t ∈ p →
      algebraMap A (Localization.AtPrime p) t ∉
        maximalIdeal (Localization.AtPrime p) ^ 2) :
    IsRegularScheme (Spec (CommRingCat.of
      (MvPolynomial (Fin 2) A ⧸ Algebra.NodeChart.uChartIdeal A t))) := by
  let B := MvPolynomial (Fin 2) A ⧸ Algebra.NodeChart.uChartIdeal A t
  let : IsRegularRing B := isRegularRing_nodeQuotient t hparam
  intro x
  let p : PrimeSpectrum B := x
  let : p.asIdeal.IsPrime := p.isPrime
  exact IsRegularLocalRing.of_ringEquiv
    (Spec.stalkIso (CommRingCat.of B) p).symm.commRingCatIsoToRingEquiv

end DeJongAlterations.Geometry.RegularNode
