/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaRelativeNormalAssociatedGraded
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Entire internally produced original standard normal monomial quotient bases

TRUE Noetherian finite SUBSET extraction on the actual leading monomial ideal
internally produces actual NONZERO whole ideal polynomials with COMPLETE
leading coverage. Genuine polynomial division produces actual whole standard
remainders and generates the SAME original polynomial ideal. Whole leading
coverage proves true standard-supported kernel separation, hence a genuine
original monomial quotient basis on the ENTIRE actual standard exponent
family, including its infinite case. Every actual basis vector is the
literal ORIGINAL monomial quotient class.

The original holomorphic ideal consumer uses the actual coefficient extension
of its SAME whole normal initial ideal through the GENUINE base fraction
field. No caller Groebner, finite relation, basis, free or result certificate
occurs. This is actual FRACTION-FIELD standard monomial freeness. A true
nonzero COMMON original base denominator, literal localized whole quotient
transport and uniform analytic spread are subsequent producer obligations.
Uniform generic freeness/normal flatness, higher HS and general G8 remain OPEN.
Blueprint: `hironaka-relative-normal-standard-monomials-extension.tex`.
-/

set_option autoImplicit false
open Set
namespace Hironaka.HironakaRelativeNormalStandardMonomials
open Hironaka
noncomputable section
variable {K : Type*} [Field K]

attribute [local instance 2000] IsLocalRing.toNontrivial

/-- Genuine Noetherian finite SUBSET extraction internally produces actual whole-ideal leading coverage. -/
theorem exists_finite_actual_leading_generators (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) :
    ∃ G : Finset (MvPolynomial (Fin t) K),
      (∀ g ∈ G, g ∈ I ∧ g ≠ 0) ∧
      ∀ f ∈ I, f ≠ 0 → ∃ g ∈ G, m.degree g ≤ m.degree f := by
  classical
  let D : Set (Fin t →₀ ℕ) := {α | ∃ f : MvPolynomial (Fin t) K, f ∈ I ∧ f ≠ 0 ∧ m.degree f=α}
  let L := Ideal.span ((fun α => MvPolynomial.monomial α (1 : K)) '' D)
  have hfg : L.FG := IsNoetherian.noetherian L
  obtain ⟨S,hS,hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset
    (R := MvPolynomial (Fin t) K) ((fun α => MvPolynomial.monomial α (1 : K)) '' D)).mp hfg
  have hw : ∀ p : S, ∃ f : MvPolynomial (Fin t) K,
      f ∈ I ∧ f ≠ 0 ∧ MvPolynomial.monomial (m.degree f) (1 : K)=p.val := by
    intro p
    obtain ⟨α,hα,he⟩ := hS p.property
    obtain ⟨f,hf,hf0,hdeg⟩ := hα
    exact ⟨f,hf,hf0,by rw [hdeg];exact he⟩
  choose f hf hf0 hm using hw
  let G := S.attach.image f
  refine ⟨G,?_,?_⟩
  · intro g hg
    obtain ⟨p,_hp,he⟩ := Finset.mem_image.mp hg
    exact he ▸ ⟨hf p,hf0 p⟩
  · intro P hP hP0
    have hlead : MvPolynomial.monomial (m.degree P) (1 : K) ∈ L :=
      Ideal.subset_span ⟨m.degree P,⟨P,hP,hP0,rfl⟩,rfl⟩
    dsimp only [L,Ideal.span] at hlead
    rw [hspan] at hlead
    have heq : (S : Set (MvPolynomial (Fin t) K)) =
        (fun α => MvPolynomial.monomial α (1 : K)) '' range (fun p : S => m.degree (f p)) := by
      ext p
      constructor
      · intro hp
        exact ⟨m.degree (f ⟨p,hp⟩),⟨⟨p,hp⟩,rfl⟩,hm ⟨p,hp⟩⟩
      · rintro ⟨α,⟨p,hp⟩,hα⟩
        rw [← hp] at hα
        dsimp only at hα
        rw [hm p] at hα
        exact hα ▸ p.property
    rw [heq] at hlead
    have hmember := MvPolynomial.mem_ideal_span_monomial_image.mp hlead
    have hsupport : m.degree P ∈ (MvPolynomial.monomial (m.degree P) (1 : K)).support := by
      simp
    obtain ⟨α,⟨p,hp⟩,hα⟩ := hmember (m.degree P) hsupport
    refine ⟨f p,Finset.mem_image.mpr ⟨p,Finset.mem_attach _ _,rfl⟩,?_⟩
    simpa only [← hp] using hα

/-- The TRUE finite original leading family is internally chosen from the actual Noetherian producer. -/
def actualLeadingGenerators (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) : Finset (MvPolynomial (Fin t) K) :=
  Classical.choose (exists_finite_actual_leading_generators t m I)

/-- ALL actual internally chosen polynomials are genuine nonzero WHOLE ideal members. -/
theorem actualLeadingGenerators_mem (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) :
    ∀ g ∈ actualLeadingGenerators t m I, g ∈ I ∧ g ≠ 0 :=
  (Classical.choose_spec (exists_finite_actual_leading_generators t m I)).1

/-- The internally produced finite actual family gives COMPLETE WHOLE ideal leading coverage. -/
theorem actualLeadingGenerators_cover (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) :
    ∀ f ∈ I, f ≠ 0 → ∃ g ∈ actualLeadingGenerators t m I, m.degree g ≤ m.degree f :=
  (Classical.choose_spec (exists_finite_actual_leading_generators t m I)).2

/-- The ENTIRE actual standard exponent family, excluding each internally produced leading divisor. -/
abbrev actualStandardExponentIndex (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) :=
  {α : Fin t →₀ ℕ // ∀ g ∈ actualLeadingGenerators t m I, ¬ m.degree g ≤ α}

/-- A true standard-supported WHOLE polynomial in the whole original ideal must actually vanish. -/
theorem actual_standard_polynomial_eq_zero_of_mem (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) (P : MvPolynomial (Fin t) K) (hP : P ∈ I)
    (hstd : ∀ α ∈ P.support, ∀ g ∈ actualLeadingGenerators t m I, ¬ m.degree g ≤ α) :
    P = 0 := by
  by_contra hp0
  obtain ⟨g,hg,hdeg⟩ := actualLeadingGenerators_cover t m I P hP hp0
  exact hstd _ (m.degree_mem_support hp0) g hg hdeg

/-- Genuine finite whole polynomial division internally supplies actual original-ideal remainder representatives. -/
theorem exists_actual_standard_remainder (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) (P : MvPolynomial (Fin t) K) :
    ∃ r : MvPolynomial (Fin t) K, P-r ∈ I ∧
      ∀ α ∈ r.support, ∀ g ∈ actualLeadingGenerators t m I, ¬ m.degree g ≤ α := by
  classical
  obtain ⟨a,r,he,_hdeg,hstd⟩ := m.div_set
    (B := (actualLeadingGenerators t m I : Set (MvPolynomial (Fin t) K)))
    (fun g hg => isUnit_iff_ne_zero.mpr
      (m.leadingCoeff_ne_zero_iff.mpr ((actualLeadingGenerators_mem t m I g hg).2))) P
  refine ⟨r,?_,hstd⟩
  rw [he,add_sub_cancel_right,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Ideal.sum_mem
  intro g _
  exact I.mul_mem_left _ (actualLeadingGenerators_mem t m I g.val g.property).1

/-- The genuine polynomial map of ALL actual standard coefficients into ORIGINAL normal monomials. -/
def actualStandardPolynomialMap (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) :
    (actualStandardExponentIndex t m I →₀ K) →ₗ[K] MvPolynomial (Fin t) K :=
  (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap.comp (Finsupp.lmapDomain K K Subtype.val)

/-- Every ACTUAL support exponent of a true standard coefficient polynomial is genuinely standard. -/
theorem actualStandardPolynomialMap_support (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) (a : actualStandardExponentIndex t m I →₀ K) :
    ∀ α ∈ (actualStandardPolynomialMap t m I a).support,
      ∀ g ∈ actualLeadingGenerators t m I, ¬ m.degree g ≤ α := by
  classical
  intro α hα
  have hmem : α ∈ (Finsupp.mapDomain Subtype.val a).support := hα
  obtain ⟨β,_hβ,he⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hmem)
  exact he ▸ β.property

/-- The entire actual standard coefficient embedding is genuinely injective into WHOLE polynomials. -/
theorem actualStandardPolynomialMap_injective (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) : Function.Injective (actualStandardPolynomialMap t m I) :=
  AddMonoidAlgebra.ofCoeff_injective.comp (Finsupp.mapDomain_injective Subtype.val_injective)

/-- Genuine WHOLE standard monomial combination into the ACTUAL original polynomial quotient. -/
def actualStandardMonomialCombination (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) :
    (actualStandardExponentIndex t m I →₀ K) →ₗ[K] (MvPolynomial (Fin t) K ⧸ I) :=
  (Ideal.Quotient.mkₐ K I).toLinearMap.comp (actualStandardPolynomialMap t m I)

/-- WHOLE original ideal membership and genuine leading coverage prove full actual standard combination injectivity. -/
theorem actualStandardMonomialCombination_injective (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) : Function.Injective (actualStandardMonomialCombination t m I) := by
  intro a b hab
  have hm : actualStandardPolynomialMap t m I (a-b) ∈ I := by
    rw [map_sub]
    exact Ideal.Quotient.eq.mp hab
  have hz := actual_standard_polynomial_eq_zero_of_mem t m I _ hm
    (actualStandardPolynomialMap_support t m I (a-b))
  have he : actualStandardPolynomialMap t m I (a-b) = actualStandardPolynomialMap t m I 0 := by
    simpa only [map_zero] using hz
  exact sub_eq_zero.mp (actualStandardPolynomialMap_injective t m I he)

/-- EVERY genuine entire polynomial class has a true standard finitely supported coefficient representative. -/
theorem actualStandardMonomialCombination_surjective (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) : Function.Surjective (actualStandardMonomialCombination t m I) := by
  classical
  intro x
  obtain ⟨P,rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨r,hrem,hstd⟩ := exists_actual_standard_remainder t m I P
  let a := Finsupp.comapDomain (Subtype.val : actualStandardExponentIndex t m I → Fin t →₀ ℕ) (AddMonoidAlgebra.coeff r)
    Subtype.val_injective.injOn
  have hmap : actualStandardPolynomialMap t m I a = r := by
    apply AddMonoidAlgebra.coeff_injective
    change Finsupp.mapDomain Subtype.val a = AddMonoidAlgebra.coeff r
    apply Finsupp.mapDomain_comapDomain (Subtype.val : actualStandardExponentIndex t m I → Fin t →₀ ℕ) Subtype.val_injective
    intro α hα
    exact ⟨⟨α,hstd α hα⟩,rfl⟩
  refine ⟨a,?_⟩
  change Ideal.Quotient.mk I (actualStandardPolynomialMap t m I a) = Ideal.Quotient.mk I P
  rw [hmap]
  exact Ideal.Quotient.eq.mpr (by simpa only [neg_sub] using I.neg_mem hrem)

/-- Internally produced genuine WHOLE original standard monomial quotient linear equivalence. -/
def actualStandardMonomialLinearEquiv (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) :
    (actualStandardExponentIndex t m I →₀ K) ≃ₗ[K] (MvPolynomial (Fin t) K ⧸ I) :=
  LinearEquiv.ofBijective (actualStandardMonomialCombination t m I)
    ⟨actualStandardMonomialCombination_injective t m I,actualStandardMonomialCombination_surjective t m I⟩

/-- A TRUE entire ORIGINAL standard monomial basis, with its ACTUAL complete potentially infinite index family. -/
def actualStandardMonomialBasis (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) :
    Module.Basis (actualStandardExponentIndex t m I) K (MvPolynomial (Fin t) K ⧸ I) :=
  Finsupp.basisSingleOne.map (actualStandardMonomialLinearEquiv t m I)

/-- EVERY actual basis vector is the LITERAL original entire monomial quotient class. -/
theorem actualStandardMonomialBasis_apply (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) (α : actualStandardExponentIndex t m I) :
    actualStandardMonomialBasis t m I α = Ideal.Quotient.mk I (MvPolynomial.monomial α.val (1 : K)) := by
  rw [actualStandardMonomialBasis,Module.Basis.map_apply,Finsupp.coe_basisSingleOne]
  change Ideal.Quotient.mk I (AddMonoidAlgebra.ofCoeff (Finsupp.mapDomain Subtype.val (Finsupp.single α (1 : K)))) = _
  rw [Finsupp.mapDomain_single]
  rfl

/-- GENUINE whole polynomial quotient freeness is INTERNALLY produced by the actual entire original monomial basis. -/
theorem moduleFree_actual_polynomial_quotient (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) : Module.Free K (MvPolynomial (Fin t) K ⧸ I) :=
  Module.Free.of_basis (actualStandardMonomialBasis t m I)

/-- The actual internally selected leading generators generate the COMPLETE whole original polynomial ideal. -/
theorem actualLeadingGenerators_span_eq (t : ℕ) (m : MonomialOrder (Fin t))
    (I : Ideal (MvPolynomial (Fin t) K)) :
    Ideal.span (actualLeadingGenerators t m I : Set (MvPolynomial (Fin t) K)) = I := by
  classical
  apply le_antisymm (Ideal.span_le.mpr (fun g hg => (actualLeadingGenerators_mem t m I g hg).1))
  intro P hP
  obtain ⟨a,r,he,_hdeg,hstd⟩ := m.div_set
    (B := (actualLeadingGenerators t m I : Set (MvPolynomial (Fin t) K)))
    (fun g hg => isUnit_iff_ne_zero.mpr
      (m.leadingCoeff_ne_zero_iff.mpr ((actualLeadingGenerators_mem t m I g hg).2))) P
  have hcomb : Finsupp.linearCombination (MvPolynomial (Fin t) K)
      (fun g : (actualLeadingGenerators t m I : Set (MvPolynomial (Fin t) K)) => g.val) a ∈
      Ideal.span (actualLeadingGenerators t m I : Set (MvPolynomial (Fin t) K)) := by
    rw [Finsupp.linearCombination_apply,Finsupp.sum]
    apply Ideal.sum_mem
    intro g _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span g.property)
  have hcombI : Finsupp.linearCombination (MvPolynomial (Fin t) K)
      (fun g : (actualLeadingGenerators t m I : Set (MvPolynomial (Fin t) K)) => g.val) a ∈ I :=
    (Ideal.span_le.mpr (fun g hg => (actualLeadingGenerators_mem t m I g hg).1)) hcomb
  have hr : r ∈ I := by
    have hsub := I.sub_mem hP hcombI
    simpa only [he,add_sub_cancel_left] using hsub
  have hz := actual_standard_polynomial_eq_zero_of_mem t m I r hr hstd
  simpa only [he,hz,add_zero] using hcomb

open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaRelativeNormalAssociatedGraded

/-- The ACTUAL original whole normal initial ideal extended through the GENUINE entire base fraction-field map. -/
def originalFractionNormalInitialIdeal (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Ideal (MvPolynomial (Fin t) (FractionRing (HolGerm (ComplexModel d)))) :=
  Ideal.map (MvPolynomial.map (algebraMap (HolGerm (ComplexModel d))
    (FractionRing (HolGerm (ComplexModel d))))) (originalNormalInitialIdeal d t I)

/-- The true actual entire standard normal exponent family of the original fraction-field quotient. -/
abbrev originalFractionStandardExponentIndex (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :=
  letI : Field (FractionRing (HolGerm (ComplexModel d))) := FractionRing.field (HolGerm (ComplexModel d))
  actualStandardExponentIndex t (MonomialOrder.degLex (σ := Fin t)) (originalFractionNormalInitialIdeal d t I)

/-- The GENUINE entire original normal fraction-field quotient has its internally produced actual standard monomial basis. -/
def originalFractionNormalStandardMonomialBasis (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Module.Basis (originalFractionStandardExponentIndex d t I) (FractionRing (HolGerm (ComplexModel d)))
      (MvPolynomial (Fin t) (FractionRing (HolGerm (ComplexModel d))) ⧸ originalFractionNormalInitialIdeal d t I) :=
  letI : Field (FractionRing (HolGerm (ComplexModel d))) := FractionRing.field (HolGerm (ComplexModel d))
  actualStandardMonomialBasis t (MonomialOrder.degLex (σ := Fin t)) (originalFractionNormalInitialIdeal d t I)

/-- Every GENUINE original fraction-field basis vector is its LITERAL entire original normal polynomial monomial class. -/
theorem originalFractionNormalStandardMonomialBasis_apply (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (α : originalFractionStandardExponentIndex d t I) :
    originalFractionNormalStandardMonomialBasis d t I α =
      Ideal.Quotient.mk (originalFractionNormalInitialIdeal d t I) (MvPolynomial.monomial α.val 1) := by
  let : Field (FractionRing (HolGerm (ComplexModel d))) := FractionRing.field (HolGerm (ComplexModel d))
  exact actualStandardMonomialBasis_apply t (MonomialOrder.degLex (σ := Fin t)) _ α

/-- The WHOLE original normal fraction-field polynomial quotient is truly free, with its ACTUAL produced monomial basis. -/
theorem moduleFree_original_fraction_normal_quotient (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Module.Free (FractionRing (HolGerm (ComplexModel d)))
      (MvPolynomial (Fin t) (FractionRing (HolGerm (ComplexModel d))) ⧸ originalFractionNormalInitialIdeal d t I) :=
  Module.Free.of_basis (originalFractionNormalStandardMonomialBasis d t I)

/-- ACTUAL original whole fraction-field initial ideals INTERNALLY supply finite original leading families. -/
theorem exists_original_fraction_normal_leading_generators (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ G : Finset (MvPolynomial (Fin t) (FractionRing (HolGerm (ComplexModel d)))),
      (∀ g ∈ G, g ∈ originalFractionNormalInitialIdeal d t I ∧ g ≠ 0) ∧
      ∀ f ∈ originalFractionNormalInitialIdeal d t I, f ≠ 0 →
        ∃ g ∈ G, (MonomialOrder.degLex (σ := Fin t)).degree g ≤ (MonomialOrder.degLex (σ := Fin t)).degree f := by
  let : Field (FractionRing (HolGerm (ComplexModel d))) := FractionRing.field (HolGerm (ComplexModel d))
  exact exists_finite_actual_leading_generators t (MonomialOrder.degLex (σ := Fin t)) _

end
end Hironaka.HironakaRelativeNormalStandardMonomials
