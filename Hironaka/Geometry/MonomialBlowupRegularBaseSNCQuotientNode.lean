import Hironaka.Geometry.MonomialBlowupRegularBaseSNCQuotientParameters

/-! Actual regular node rings over genuine regular SNC component intersections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCQuotientNode

open SpecIdealSheaf Scheme.IdealSheafData MonomialBlowupRegularBaseSNCIntersection
open MonomialBlowupRegularBaseSNCQuotientParameters

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A]

/-- The actual quotient-localization equivalence with its actual quotient-coefficient algebra structure. -/
def quotientLocalizationCoeffEquiv (I : Ideal A) (q : Ideal (A ⧸ I)) [q.IsPrime] :
    (Localization.AtPrime (q.comap (Ideal.Quotient.mk I)) ⧸
      I.map (algebraMap A (Localization.AtPrime (q.comap (Ideal.Quotient.mk I))))) ≃ₐ[A ⧸ I]
      Localization.AtPrime q := by
  let p := q.comap (Ideal.Quotient.mk I)
  let L := Localization.AtPrime p
  let T := L ⧸ I.map (algebraMap A L)
  have heq : Algebra.algebraMapSubmonoid (A ⧸ I) p.primeCompl = q.primeCompl :=
    q.map_primeCompl_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalization q.primeCompl T := by rw [← heq]; infer_instance
  exact IsLocalization.algEquiv q.primeCompl T (Localization.AtPrime q)

/-- The actual equivalence preserves each original coefficient, before and after both quotients. -/
theorem quotientLocalizationCoeffEquiv_algebraMap (I : Ideal A) (q : Ideal (A ⧸ I)) [q.IsPrime]
    (a : A) :
    quotientLocalizationCoeffEquiv I q
      (Ideal.Quotient.mk _ (algebraMap A
        (Localization.AtPrime (q.comap (Ideal.Quotient.mk I))) a)) =
      algebraMap (A ⧸ I) (Localization.AtPrime q) (Ideal.Quotient.mk I a) := by
  change quotientLocalizationCoeffEquiv I q
    (algebraMap (A ⧸ I) _ (Ideal.Quotient.mk I a)) = _
  exact (quotientLocalizationCoeffEquiv I q).commutes _

/-- Actual local-ring isomorphisms preserve the original parameter's nonzero cotangent class. -/
theorem not_mem_maximal_square_map {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (t : R)
    (ht : t ∉ maximalIdeal R ^ 2) : e t ∉ maximalIdeal S ^ 2 := by
  intro h
  apply ht
  have hm : e t ∈ (maximalIdeal R ^ 2).map e.toRingHom := by
    have he : (maximalIdeal R).map e.toRingHom = maximalIdeal S := map_ringEquiv_maximalIdeal e
    rw [Ideal.map_pow, he]
    exact h
  exact Ideal.apply_mem_of_equiv_iff.mp hm

variable [IsRegularRing A]

/-- The original equation of a remaining genuine component is a parameter at every actual quotient prime. -/
theorem remaining_equation_parameter_atPrime
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (J : Finset (DivisorComponent D)) (hJ : J.Nonempty)
    (C : DivisorComponent D) (hC : C ∉ J) (t : A)
    (heq : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (q : Ideal (A ⧸ intersectionIdeal D J)) [q.IsPrime]
    (ht : Ideal.Quotient.mk (intersectionIdeal D J) t ∈ q) :
    algebraMap (A ⧸ intersectionIdeal D J) (Localization.AtPrime q)
      (Ideal.Quotient.mk (intersectionIdeal D J) t) ∉ maximalIdeal (Localization.AtPrime q) ^ 2 := by
  let I := intersectionIdeal D J
  let p := q.comap (Ideal.Quotient.mk I)
  have hIp : I ≤ p := by
    intro a ha
    change Ideal.Quotient.mk I a ∈ q
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact q.zero_mem
  have htp : t ∈ p := ht
  obtain ⟨hlocal, _, hparam⟩ := remaining_equation_local_parameter D hD J hJ C hC t heq p hIp htp
  let := hlocal
  have h := not_mem_maximal_square_map (quotientLocalizationCoeffEquiv I q).toRingEquiv _ hparam
  change quotientLocalizationCoeffEquiv I q
    (Ideal.Quotient.mk _ (algebraMap A
      (Localization.AtPrime (q.comap (Ideal.Quotient.mk I))) t)) ∉
      maximalIdeal (Localization.AtPrime q) ^ 2 at h
  rw [quotientLocalizationCoeffEquiv_algebraMap I q t] at h
  exact h

/-- A literal node over the actual intersection quotient is regular, with the remaining parameter derived from SNC. -/
theorem remaining_node_isRegularRing
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (J : Finset (DivisorComponent D)) (hJ : J.Nonempty)
    (C : DivisorComponent D) (hC : C ∉ J) (t : A)
    (heq : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val) :
    IsRegularRing (Algebra.NodeBlowupChart.Node (A ⧸ intersectionIdeal D J)
      (Ideal.Quotient.mk (intersectionIdeal D J) t)) := by
  let I := intersectionIdeal D J
  let : IsRegularRing (A ⧸ I) := SNCSubdivisorComponent.isRegularRing_quotient_of_specIdealSheaf I (by
    rw [intersectionIdeal_spec]
    exact hD.intersectionsRegular J hJ)
  apply RegularNode.isRegularRing_nodeQuotient
  exact remaining_equation_parameter_atPrime D hD J hJ C hC t heq

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCQuotientNode
