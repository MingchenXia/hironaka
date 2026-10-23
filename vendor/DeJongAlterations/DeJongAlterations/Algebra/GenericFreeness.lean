/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import DeJongAlterations.Algebra.StandardMonomials
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
# Generic freeness of a polynomial quotient

Extracted from the characteristic-free algebra prefix of
`TranscendentalNakamaye/Pending/HironakaRelativeNormalUniformLocalization.lean`.
Original SHA-256: `24028e360f442aa62b12494b0e6c18c74efadefffad2b7e4d0d94785be59407f`.
For an ideal in a finite polynomial algebra over any domain, a nonzero product of leading
coefficients gives a free coefficient-localized quotient. Its basis uses every standard exponent
over the fraction field.
-/

set_option autoImplicit false
open Set
open scoped nonZeroDivisors
namespace DeJongAlterations.Algebra.GenericFreeness
noncomputable section
open DeJongAlterations.Algebra.StandardMonomials

/-- A genuinely injective coefficient map preserves the whole original leading exponent. -/
theorem degree_map_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (t : ℕ) (m : MonomialOrder (Fin t)) (f : R →+* S) (hf : Function.Injective f)
    (P : MvPolynomial (Fin t) R) : m.degree (MvPolynomial.map f P) = m.degree P := by
  classical
  simp only [MonomialOrder.degree,MvPolynomial.support_map_of_injective P hf]

variable {B K : Type*} [CommRing B] [IsDomain B] [Field K] [Algebra B K] [IsFractionRing B K]

/-- The SAME whole original ideal under the true fraction-field coefficient extension. -/
def fractionExtendedIdeal (t : ℕ) (H : Ideal (MvPolynomial (Fin t) B)) :
    Ideal (MvPolynomial (Fin t) K) := Ideal.map (MvPolynomial.map (algebraMap B K)) H

/-- Actual polynomial localization internally lifts a nonzero whole field ideal member to an original member with the SAME leading exponent. -/
theorem exists_original_leading_lift (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) (g : MvPolynomial (Fin t) K)
    (hg : g ∈ fractionExtendedIdeal t H) (hg0 : g ≠ 0) :
    ∃ h : MvPolynomial (Fin t) B, h ∈ H ∧ h ≠ 0 ∧ m.degree h = m.degree g := by
  let : Algebra (MvPolynomial (Fin t) B) (MvPolynomial (Fin t) K) := MvPolynomial.algebraMvPolynomial
  have hmem : g ∈ Ideal.map (algebraMap (MvPolynomial (Fin t) B) (MvPolynomial (Fin t) K)) H := by
    simpa only [MvPolynomial.algebraMap_def,fractionExtendedIdeal] using hg
  obtain ⟨⟨h,s⟩,he⟩ := (IsLocalization.mem_map_algebraMap_iff
    ((nonZeroDivisors B).map (MvPolynomial.C (σ := Fin t))) (MvPolynomial (Fin t) K)).mp hmem
  obtain ⟨r,hr,hrs⟩ := Submonoid.mem_map.mp s.property
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  have hcr0 : MvPolynomial.C (σ := Fin t) (algebraMap B K r) ≠ 0 := by
    simpa only [ne_eq,MvPolynomial.C_eq_zero,map_zero] using (IsFractionRing.injective B K).ne hr0
  have he' : g * MvPolynomial.C (algebraMap B K r) = MvPolynomial.map (algebraMap B K) h.val := by
    simpa only [MvPolynomial.algebraMap_def,← hrs,MvPolynomial.map_C] using he
  have hmap0 : MvPolynomial.map (algebraMap B K) h.val ≠ 0 := by
    rw [← he']
    exact mul_ne_zero hg0 hcr0
  have hh0 : h.val ≠ 0 := by
    intro hz
    exact hmap0 (by rw [hz,map_zero])
  refine ⟨h.val,h.property,hh0,?_⟩
  have hdeg := congrArg m.degree he'
  rw [m.degree_mul hg0 hcr0,m.degree_C,add_zero,
    degree_map_of_injective t m (algebraMap B K) (IsFractionRing.injective B K)] at hdeg
  exact hdeg.symm

/-- Internally selected ACTUAL original ideal lift of each internally selected field generator. -/
def originalLeadingLift (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B))
    (g : (actualLeadingGenerators t m (fractionExtendedIdeal (K := K) t H) : Set (MvPolynomial (Fin t) K))) :
    MvPolynomial (Fin t) B := Classical.choose (exists_original_leading_lift t m H g.val
      (actualLeadingGenerators_mem t m _ g.val g.property).1
      (actualLeadingGenerators_mem t m _ g.val g.property).2)

/-- Every ACTUAL selected original lift is a nonzero WHOLE ideal member with the true field leading exponent. -/
theorem originalLeadingLift_spec (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B))
    (g : (actualLeadingGenerators t m (fractionExtendedIdeal (K := K) t H) : Set (MvPolynomial (Fin t) K))) :
    originalLeadingLift t m H g ∈ H ∧ originalLeadingLift t m H g ≠ 0 ∧
      m.degree (originalLeadingLift t m H g) = m.degree g.val :=
  Classical.choose_spec (exists_original_leading_lift t m H g.val
    (actualLeadingGenerators_mem t m _ g.val g.property).1
    (actualLeadingGenerators_mem t m _ g.val g.property).2)

/-- The internally produced genuine finite family of actual original leading lifts. -/
def originalLeadingLiftFamily (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) : Finset (MvPolynomial (Fin t) B) := by
  classical
  exact (actualLeadingGenerators t m (fractionExtendedIdeal (K := K) t H)).attach.image
    (fun g => originalLeadingLift t m H g)

/-- ALL members of the actual finite original family are genuine nonzero WHOLE ideal polynomials. -/
theorem originalLeadingLiftFamily_mem (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) :
    ∀ h ∈ originalLeadingLiftFamily (K := K) t m H, h ∈ H ∧ h ≠ 0 := by
  classical
  intro h hh
  obtain ⟨g,_hg,he⟩ := Finset.mem_image.mp hh
  exact he ▸ ⟨(originalLeadingLift_spec t m H g).1,(originalLeadingLift_spec t m H g).2.1⟩

/-- Each internally chosen field generator has its ACTUAL original lift in the genuine finite original family. -/
theorem originalLeadingLift_mem_family (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B))
    (g : (actualLeadingGenerators t m (fractionExtendedIdeal (K := K) t H) : Set (MvPolynomial (Fin t) K))) :
    originalLeadingLift t m H g ∈ originalLeadingLiftFamily (K := K) t m H := by
  classical
  exact Finset.mem_image.mpr ⟨g,Finset.mem_attach _ _,rfl⟩

/-- The ACTUAL single original base denominator is the true finite product of original leading coefficients. -/
def uniformLeadingDenominator (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) : B := by
  classical
  exact ∏ h ∈ originalLeadingLiftFamily (K := K) t m H, m.leadingCoeff h

/-- The genuine SAME denominator is nonzero as an ENTIRE original base element. -/
theorem uniformLeadingDenominator_ne_zero (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) : uniformLeadingDenominator (K := K) t m H ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun h hh =>
    m.leadingCoeff_ne_zero_iff.mpr (originalLeadingLiftFamily_mem t m H h hh).2)

/-- The actual injective localized coefficient map to the GENUINE original fraction field. -/
def uniformLocalizedFractionMap (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) :
    Localization.Away (uniformLeadingDenominator (K := K) t m H) →+* K :=
  IsLocalization.Away.lift _ (isUnit_iff_ne_zero.mpr (by
    simpa only [map_zero] using (IsFractionRing.injective B K).ne
      (uniformLeadingDenominator_ne_zero (K := K) t m H)))

/-- The true localized map restricts to the LITERAL original fraction map. -/
theorem uniformLocalizedFractionMap_eq (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) (x : B) :
    uniformLocalizedFractionMap (K := K) t m H
      (algebraMap B (Localization.Away (uniformLeadingDenominator (K := K) t m H)) x) =
        algebraMap B K x := IsLocalization.Away.lift_eq _ _ x

/-- Genuine original fraction injectivity proves actual WHOLE localized fraction-map injectivity. -/
theorem uniformLocalizedFractionMap_injective (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) : Function.Injective (uniformLocalizedFractionMap (K := K) t m H) := by
  apply IsLocalization.injective_of_map_algebraMap_zero
    (M := Submonoid.powers (uniformLeadingDenominator (K := K) t m H))
    (f := uniformLocalizedFractionMap (K := K) t m H)
  intro x hx
  rw [uniformLocalizedFractionMap_eq] at hx
  have hz : x = 0 := (IsFractionRing.injective B K) (by simpa only [map_zero] using hx)
  rw [hz,map_zero]

/-- The ACTUAL original coefficient map into the same true localization is injective. -/
theorem uniformLocalizedCoefficientMap_injective (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) : Function.Injective
      (algebraMap B (Localization.Away (uniformLeadingDenominator (K := K) t m H))) := by
  intro x y hxy
  apply IsFractionRing.injective B K
  simpa only [uniformLocalizedFractionMap_eq] using
    congrArg (uniformLocalizedFractionMap (K := K) t m H) hxy

/-- Every original leading coefficient becomes a genuine UNIT at the SAME actual original denominator. -/
theorem originalLeadingLiftFamily_leadingCoeff_unit (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) (h : MvPolynomial (Fin t) B)
    (hh : h ∈ originalLeadingLiftFamily (K := K) t m H) :
    IsUnit (algebraMap B (Localization.Away (uniformLeadingDenominator (K := K) t m H))
      (m.leadingCoeff h)) := by
  classical
  apply IsLocalization.Away.isUnit_of_dvd (uniformLeadingDenominator (K := K) t m H)
  exact Finset.dvd_prod_of_mem (fun h => m.leadingCoeff h) hh

/-- Genuine coefficient extension preserves the ACTUAL whole leading coefficient under injectivity. -/
theorem leadingCoeff_map_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (t : ℕ) (m : MonomialOrder (Fin t)) (f : R →+* S) (hf : Function.Injective f)
    (P : MvPolynomial (Fin t) R) : m.leadingCoeff (MvPolynomial.map f P) = f (m.leadingCoeff P) := by
  rw [MonomialOrder.leadingCoeff,degree_map_of_injective t m f hf,MvPolynomial.coeff_map]
  rfl

/-- The ACTUAL common-denominator coefficient localization of the SAME whole original polynomial ideal. -/
def uniformLocalizedIdeal (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) :
    Ideal (MvPolynomial (Fin t) (Localization.Away (uniformLeadingDenominator (K := K) t m H))) :=
  Ideal.map (MvPolynomial.map (algebraMap B (Localization.Away (uniformLeadingDenominator (K := K) t m H)))) H

/-- The ACTUAL finite localized image of the internally produced whole original leading lifts. -/
def uniformLocalizedLeadingFamily (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) :
    Finset (MvPolynomial (Fin t) (Localization.Away (uniformLeadingDenominator (K := K) t m H))) := by
  classical
  exact (originalLeadingLiftFamily (K := K) t m H).image
    (MvPolynomial.map (algebraMap B (Localization.Away (uniformLeadingDenominator (K := K) t m H))))

/-- EVERY actual localized leading polynomial belongs to the SAME whole localized original ideal and has a true UNIT leading coefficient. -/
theorem uniformLocalizedLeadingFamily_spec (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) :
    ∀ p ∈ uniformLocalizedLeadingFamily (K := K) t m H,
      p ∈ uniformLocalizedIdeal (K := K) t m H ∧ IsUnit (m.leadingCoeff p) := by
  classical
  intro p hp
  obtain ⟨h,hh,rfl⟩ := Finset.mem_image.mp hp
  constructor
  · exact Ideal.mem_map_of_mem _ (originalLeadingLiftFamily_mem t m H h hh).1
  · rw [leadingCoeff_map_of_injective t m _ (uniformLocalizedCoefficientMap_injective t m H)]
    exact originalLeadingLiftFamily_leadingCoeff_unit t m H h hh

/-- ACTUAL original-lift division standardness is the full internally produced FIELD-standard exponent predicate. -/
theorem uniformLocalized_standard_of_division_standard (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) (α : Fin t →₀ ℕ)
    (hstd : ∀ p ∈ uniformLocalizedLeadingFamily (K := K) t m H, ¬ m.degree p ≤ α) :
    ∀ g ∈ actualLeadingGenerators t m (fractionExtendedIdeal (K := K) t H), ¬ m.degree g ≤ α := by
  classical
  intro g hg
  let g' : (actualLeadingGenerators t m (fractionExtendedIdeal (K := K) t H) : Set (MvPolynomial (Fin t) K)) := ⟨g,hg⟩
  have hh := originalLeadingLift_mem_family t m H g'
  have hmem : MvPolynomial.map (algebraMap B (Localization.Away (uniformLeadingDenominator (K := K) t m H)))
      (originalLeadingLift t m H g') ∈ uniformLocalizedLeadingFamily (K := K) t m H :=
    Finset.mem_image.mpr ⟨_,hh,rfl⟩
  have hz := hstd _ hmem
  rw [degree_map_of_injective t m _ (uniformLocalizedCoefficientMap_injective t m H),
    (originalLeadingLift_spec t m H g').2.2] at hz
  exact hz

/-- TRUE unit-leading division gives EVERY actual whole localized class an entire FIELD-standard remainder on the SAME localization. -/
theorem exists_uniformLocalized_standard_remainder (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B))
    (P : MvPolynomial (Fin t) (Localization.Away (uniformLeadingDenominator (K := K) t m H))) :
    ∃ r, P-r ∈ uniformLocalizedIdeal (K := K) t m H ∧
      ∀ α ∈ r.support, ∀ g ∈ actualLeadingGenerators t m (fractionExtendedIdeal (K := K) t H), ¬ m.degree g ≤ α := by
  classical
  obtain ⟨a,r,he,_hdeg,hstd⟩ := m.div_set
    (B := (uniformLocalizedLeadingFamily (K := K) t m H : Set _))
    (fun g hg => (uniformLocalizedLeadingFamily_spec t m H g hg).2) P
  refine ⟨r,?_,fun α hα => uniformLocalized_standard_of_division_standard t m H α (hstd α hα)⟩
  rw [he,add_sub_cancel_right,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Ideal.sum_mem
  intro g _
  exact (uniformLocalizedIdeal (K := K) t m H).mul_mem_left _
    (uniformLocalizedLeadingFamily_spec t m H g.val g.property).1

/-- Literal coefficient extension at the SAME actual denominator followed by the actual fraction map gives the SAME original whole field ideal. -/
theorem uniformLocalizedIdeal_map_fraction (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) :
    Ideal.map (MvPolynomial.map (uniformLocalizedFractionMap (K := K) t m H))
      (uniformLocalizedIdeal (K := K) t m H) = fractionExtendedIdeal (K := K) t H := by
  have hc : (uniformLocalizedFractionMap (K := K) t m H).comp
      (algebraMap B (Localization.Away (uniformLeadingDenominator (K := K) t m H))) = algebraMap B K :=
    RingHom.ext (uniformLocalizedFractionMap_eq t m H)
  have hp : (MvPolynomial.map (σ := Fin t) (uniformLocalizedFractionMap (K := K) t m H)).comp
      (MvPolynomial.map (algebraMap B (Localization.Away (uniformLeadingDenominator (K := K) t m H)))) =
        MvPolynomial.map (algebraMap B K) := by
    apply RingHom.ext
    intro P
    simp only [RingHom.comp_apply,MvPolynomial.map_map,hc]
  rw [uniformLocalizedIdeal,Ideal.map_map,hp]
  rfl

/-- Actual whole localized original-ideal membership of a field-standard supported polynomial forces the ENTIRE polynomial to vanish. -/
theorem uniformLocalized_standard_polynomial_eq_zero_of_mem (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B))
    (P : MvPolynomial (Fin t) (Localization.Away (uniformLeadingDenominator (K := K) t m H)))
    (hP : P ∈ uniformLocalizedIdeal (K := K) t m H)
    (hstd : ∀ α ∈ P.support, ∀ g ∈ actualLeadingGenerators t m (fractionExtendedIdeal (K := K) t H), ¬ m.degree g ≤ α) :
    P = 0 := by
  have hm : MvPolynomial.map (uniformLocalizedFractionMap (K := K) t m H) P ∈ fractionExtendedIdeal (K := K) t H := by
    have hh := Ideal.mem_map_of_mem (MvPolynomial.map (uniformLocalizedFractionMap (K := K) t m H)) hP
    rwa [uniformLocalizedIdeal_map_fraction] at hh
  have hs : ∀ α ∈ (MvPolynomial.map (uniformLocalizedFractionMap (K := K) t m H) P).support,
      ∀ g ∈ actualLeadingGenerators t m (fractionExtendedIdeal (K := K) t H), ¬ m.degree g ≤ α := by
    rw [MvPolynomial.support_map_of_injective P (uniformLocalizedFractionMap_injective t m H)]
    exact hstd
  have hz := actual_standard_polynomial_eq_zero_of_mem t m (fractionExtendedIdeal (K := K) t H) _ hm hs
  apply MvPolynomial.map_injective _ (uniformLocalizedFractionMap_injective t m H)
  simpa only [map_zero] using hz

/-- The ENTIRE internally produced field-standard exponent family on the SAME genuine base localization. -/
abbrev uniformStandardExponentIndex (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) := actualStandardExponentIndex t m (fractionExtendedIdeal (K := K) t H)

/-- True entire localized coefficients mapped into their ORIGINAL actual standard normal monomials. -/
def uniformStandardPolynomialMap (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) :
    (uniformStandardExponentIndex (K := K) t m H →₀ Localization.Away (uniformLeadingDenominator (K := K) t m H)) →ₗ[Localization.Away (uniformLeadingDenominator (K := K) t m H)]
      MvPolynomial (Fin t) (Localization.Away (uniformLeadingDenominator (K := K) t m H)) :=
  (AddMonoidAlgebra.coeffLinearEquiv _).symm.toLinearMap.comp (Finsupp.lmapDomain _ _ Subtype.val)

/-- Every ACTUAL support exponent of the genuine entire localized coefficient polynomial is field-standard. -/
theorem uniformStandardPolynomialMap_support (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B))
    (a : uniformStandardExponentIndex (K := K) t m H →₀ Localization.Away (uniformLeadingDenominator (K := K) t m H)) :
    ∀ α ∈ (uniformStandardPolynomialMap (K := K) t m H a).support,
      ∀ g ∈ actualLeadingGenerators t m (fractionExtendedIdeal (K := K) t H), ¬ m.degree g ≤ α := by
  classical
  intro α hα
  have hmem : α ∈ (Finsupp.mapDomain Subtype.val a).support := hα
  obtain ⟨β,_hβ,he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
  exact he ▸ β.property

/-- The entire actual original standard coefficient embedding is truly injective into WHOLE localized polynomials. -/
theorem uniformStandardPolynomialMap_injective (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) : Function.Injective (uniformStandardPolynomialMap (K := K) t m H) :=
  AddMonoidAlgebra.ofCoeff_injective.comp (Finsupp.mapDomain_injective Subtype.val_injective)

/-- Genuine whole original standard monomial combination into the ACTUAL SAME-denominator original polynomial quotient. -/
def uniformStandardMonomialCombination (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) :
    (uniformStandardExponentIndex (K := K) t m H →₀ Localization.Away (uniformLeadingDenominator (K := K) t m H)) →ₗ[Localization.Away (uniformLeadingDenominator (K := K) t m H)]
      (MvPolynomial (Fin t) (Localization.Away (uniformLeadingDenominator (K := K) t m H)) ⧸ uniformLocalizedIdeal (K := K) t m H) :=
  (Ideal.Quotient.mkₐ _ (uniformLocalizedIdeal (K := K) t m H)).toLinearMap.comp (uniformStandardPolynomialMap (K := K) t m H)

/-- WHOLE original localized ideal membership proves true entire standard coefficient combination injectivity. -/
theorem uniformStandardMonomialCombination_injective (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) : Function.Injective (uniformStandardMonomialCombination (K := K) t m H) := by
  intro a b hab
  have hm : uniformStandardPolynomialMap (K := K) t m H (a-b) ∈ uniformLocalizedIdeal (K := K) t m H := by
    rw [map_sub]
    exact Ideal.Quotient.eq.mp hab
  have hz := uniformLocalized_standard_polynomial_eq_zero_of_mem t m H _ hm
    (uniformStandardPolynomialMap_support t m H (a-b))
  have he : uniformStandardPolynomialMap (K := K) t m H (a-b) = uniformStandardPolynomialMap (K := K) t m H 0 := by
    simpa only [map_zero] using hz
  exact sub_eq_zero.mp (uniformStandardPolynomialMap_injective t m H he)

/-- EVERY actual whole localized quotient class has a genuine entire actual standard coefficient representative. -/
theorem uniformStandardMonomialCombination_surjective (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) : Function.Surjective (uniformStandardMonomialCombination (K := K) t m H) := by
  classical
  intro x
  obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨r,hrem,hstd⟩ := exists_uniformLocalized_standard_remainder t m H P
  let a := Finsupp.comapDomain (Subtype.val : uniformStandardExponentIndex (K := K) t m H → Fin t →₀ ℕ)
    (AddMonoidAlgebra.coeff r) Subtype.val_injective.injOn
  have hmap : uniformStandardPolynomialMap (K := K) t m H a = r := by
    apply AddMonoidAlgebra.coeff_injective
    change Finsupp.mapDomain Subtype.val a = AddMonoidAlgebra.coeff r
    apply Finsupp.mapDomain_comapDomain (Subtype.val : uniformStandardExponentIndex (K := K) t m H → Fin t →₀ ℕ) Subtype.val_injective
    intro α hα
    exact ⟨⟨α,hstd α hα⟩,rfl⟩
  refine ⟨a,?_⟩
  change Ideal.Quotient.mk _ (uniformStandardPolynomialMap (K := K) t m H a) = Ideal.Quotient.mk _ P
  rw [hmap]
  exact Ideal.Quotient.eq.mpr (by simpa only [neg_sub] using (uniformLocalizedIdeal (K := K) t m H).neg_mem hrem)

/-- Genuine SAME-denominator ENTIRE original standard monomial quotient linear equivalence. -/
def uniformStandardMonomialLinearEquiv (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) :
    (uniformStandardExponentIndex (K := K) t m H →₀ Localization.Away (uniformLeadingDenominator (K := K) t m H)) ≃ₗ[Localization.Away (uniformLeadingDenominator (K := K) t m H)]
      (MvPolynomial (Fin t) (Localization.Away (uniformLeadingDenominator (K := K) t m H)) ⧸ uniformLocalizedIdeal (K := K) t m H) :=
  LinearEquiv.ofBijective (uniformStandardMonomialCombination (K := K) t m H)
    ⟨uniformStandardMonomialCombination_injective t m H,uniformStandardMonomialCombination_surjective t m H⟩

/-- TRUE entire ORIGINAL standard monomial basis at ONE genuine nonzero original base denominator. -/
def uniformStandardMonomialBasis (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) :
    Module.Basis (uniformStandardExponentIndex (K := K) t m H) (Localization.Away (uniformLeadingDenominator (K := K) t m H))
      (MvPolynomial (Fin t) (Localization.Away (uniformLeadingDenominator (K := K) t m H)) ⧸ uniformLocalizedIdeal (K := K) t m H) :=
  Finsupp.basisSingleOne.map (uniformStandardMonomialLinearEquiv (K := K) t m H)

/-- Every actual SAME-denominator basis vector is the LITERAL original normal monomial quotient class. -/
theorem uniformStandardMonomialBasis_apply (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) (α : uniformStandardExponentIndex (K := K) t m H) :
    uniformStandardMonomialBasis (K := K) t m H α = Ideal.Quotient.mk (uniformLocalizedIdeal (K := K) t m H)
      (MvPolynomial.monomial α.val (1 : Localization.Away (uniformLeadingDenominator (K := K) t m H))) := by
  rw [uniformStandardMonomialBasis,Module.Basis.map_apply,Finsupp.coe_basisSingleOne]
  change Ideal.Quotient.mk _ (AddMonoidAlgebra.ofCoeff (Finsupp.mapDomain Subtype.val (Finsupp.single α 1))) = _
  rw [Finsupp.mapDomain_single]
  rfl

/-- Genuine entire original polynomial quotient freeness at ONE internally produced original denominator. -/
theorem moduleFree_uniform_localized_quotient (t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) B)) :
    Module.Free (Localization.Away (uniformLeadingDenominator (K := K) t m H))
      (MvPolynomial (Fin t) (Localization.Away (uniformLeadingDenominator (K := K) t m H)) ⧸ uniformLocalizedIdeal (K := K) t m H) :=
  Module.Free.of_basis (uniformStandardMonomialBasis (K := K) t m H)


end

end DeJongAlterations.Algebra.GenericFreeness
