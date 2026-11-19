import Hironaka.Geometry.SNCSubdivisorLocal
import Hironaka.Geometry.MonomialBlowupTowerRegular

/-!
# Actual SNC component equations supply the node parameters

The original principal ideal is identified with the reduced ideal of a genuine
component. Its height, quotient regularity and local parameter property follow
from the full native SNC divisor.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCParameters

open SpecIdealSheaf Scheme.IdealSheafData ReducedClosedSubscheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

variable {A : Type u} [CommRing A] [IsRegularRing A] [IsDomain A]

omit [IsDomain A] in
/-- A literal equation of an actual SNC component has its genuine prime, height and regular quotient. -/
theorem component_equation_data
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C : DivisorComponent D) (t : A)
    (heq : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val) :
    (Ideal.span {t}).IsPrime ∧ (Ideal.span {t}).height = 1 ∧
      IsRegularRing (A ⧸ Ideal.span {t}) := by
  let I : Ideal A := Ideal.span {t}
  have hrad : I.radical = I := by
    apply (specIdealSheafEquiv A).symm.injective
    change specIdealSheaf A I.radical = specIdealSheaf A I
    rw [← specIdealSheaf_radical, heq, radical_vanishingIdeal]
  have hirr : IsIrreducible ((specIdealSheaf A I).support : Set (Spec (CommRingCat.of A))) := by
    rw [heq, support_vanishingIdeal]
    exact SNCLocality.divisorComponent_isIrreducible D C
  let : I.IsPrime :=
    (PrimeSpectrum.isIrreducible_zeroLocus_iff_of_radical I
      (Ideal.radical_eq_iff.mp hrad)).mp (by rwa [← specIdealSheaf_support])
  have hregular : IsRegularScheme (specIdealSheaf A I).subscheme := by
    rw [heq]
    simpa only [componentIntersection, Finset.mem_singleton, iSup_iSup_eq_left] using
      hD.intersectionsRegular {C} (Finset.singleton_nonempty C)
  have hcodim : HasPureCodimension (specIdealSheaf A I).support 1 := by
    rw [heq, support_vanishingIdeal]
    simpa only [componentIntersection, Finset.mem_singleton, iSup_iSup_eq_left,
      support_vanishingIdeal, Finset.card_singleton] using
      hD.intersectionsCodimension {C} (Finset.singleton_nonempty C)
  exact ⟨inferInstance, SNCSubdivisorAffine.height_eq_of_hasPureCodimension I 1 hcodim,
    SNCSubdivisorComponent.isRegularRing_quotient_of_specIdealSheaf I hregular⟩

/-- The actual component equation is nonzero; this is derived from its native codimension. -/
theorem component_equation_ne_zero
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C : DivisorComponent D) (t : A)
    (heq : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val) : t ≠ 0 := by
  have hh := (component_equation_data D hD C t heq).2.1
  intro h
  have hI : Ideal.span {t} = ⊥ := by rw [h]; simp
  exact (Ideal.ne_bot_of_height_eq_one hh) hI

/-- A genuine height-one principal regular quotient gives the original local parameter,
rather than an arbitrarily selected replacement equation. -/
theorem principal_parameter_atPrime (t : A)
    [(Ideal.span {t}).IsPrime] [IsRegularRing (A ⧸ Ideal.span {t})]
    (hheight : (Ideal.span {t}).height = 1) (p : Ideal A) [p.IsPrime] (ht : t ∈ p) :
    algebraMap A (Localization.AtPrime p) t ∉ maximalIdeal (Localization.AtPrime p) ^ 2 := by
  let I : Ideal A := Ideal.span {t}
  have hIp : I ≤ p := Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ht)
  let q := p.map (Ideal.Quotient.mk I)
  let : q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hIp)
  have hqp : q.comap (Ideal.Quotient.mk I) = p := by
    simp only [q, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_of_le_left hIp]
  let L := Localization.AtPrime p
  let J := I.map (algebraMap A L)
  have hnot : ∀ x : A, Ideal.Quotient.mk I x ∉ q ↔ x ∉ p := by
    intro x
    apply not_congr
    change x ∈ q.comap (Ideal.Quotient.mk I) ↔ x ∈ p
    rw [hqp]
  have heq : Algebra.algebraMapSubmonoid (A ⧸ I) p.primeCompl = q.primeCompl := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hnot x).mpr hx
    · intro hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨x, (hnot x).mp hy, rfl⟩
  let : IsLocalization q.primeCompl (L ⧸ J) := by rw [← heq]; infer_instance
  let : IsRegularLocalRing (L ⧸ J) := IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv q.primeCompl (L ⧸ J) (Localization.AtPrime q)).symm.toRingEquiv
  have hd : Disjoint (p.primeCompl : Set A) (I : Set A) :=
    Set.disjoint_left.mpr (fun x hxM hxI ↦ hxM (hIp hxI))
  have hJheight : J.height = 1 :=
    (IsLocalization.height_map_of_disjoint (S := L) p.primeCompl I hd).trans hheight
  obtain ⟨b, _, hb, _, hspan⟩ :=
    SNCSubdivisorAlgebra.exists_regular_kernel_generator (Ideal.Quotient.mk J)
      Ideal.Quotient.mk_surjective
      (by simpa only [Ideal.mk_ker] using Ideal.ne_bot_of_height_eq_one hJheight)
      (by simpa only [Ideal.mk_ker, hJheight] using (le_refl (1 : ℕ∞)))
  have hbt : algebraMap A L t ∣ b := by
    apply Ideal.mem_span_singleton.mp
    have hspan' : Ideal.span {b} = J := by simpa only [Ideal.mk_ker] using hspan
    have hmem : b ∈ J := by rw [← hspan']; exact Ideal.subset_span (Set.mem_singleton _)
    simpa only [J, I, Ideal.map_span, Set.image_singleton] using hmem
  intro h
  obtain ⟨c, hc⟩ := hbt
  apply hb
  rw [hc]
  exact (maximalIdeal L ^ 2).mul_mem_right c h

/-- Every literal genuine SNC component equation has the actual local parameter property. -/
theorem component_equation_parameter
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C : DivisorComponent D) (t : A)
    (heq : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (p : Ideal A) [p.IsPrime] (ht : t ∈ p) :
    algebraMap A (Localization.AtPrime p) t ∉ maximalIdeal (Localization.AtPrime p) ^ 2 := by
  obtain ⟨hp, hh, hq⟩ := component_equation_data D hD C t heq
  let := hp
  let := hq
  exact principal_parameter_atPrime t hh p ht


/-- Genuine SNC component equations internally produce the actual regular projective tower alteration. -/
theorem regular_projective_alteration_of_snc_components
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (l : List A)
    (hfactors : ∀ t ∈ l, ∃ C : DivisorComponent D,
      specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val) :
    IsRegularScheme (MonomialBlowupTower.resolved l) ∧
      IsProjectiveOver (MonomialBlowupTower.resolutionMorphism l) ∧
      IsAlteration (MonomialBlowupTower.resolutionMorphism l) := by
  apply MonomialBlowupTowerRegular.regular_projective_alteration
  · intro h
    obtain ⟨C, hC⟩ := hfactors 0 h
    exact component_equation_ne_zero D hD C 0 hC rfl
  · intro t ht p hp htp
    obtain ⟨C, hC⟩ := hfactors t ht
    exact component_equation_parameter D hD C t hC p htp

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCParameters
