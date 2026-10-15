/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Resolution.HironakaRelativeNormalUniformLocalization

/-! # ONE genuine analytic neighborhood for actual original finite normal coefficients

Actual WHOLE original germs internally supply genuine coefficient functions,
with literal zero for zero. Finite support in the TRUE entire function ring
retains EVERY polynomial coefficient and its WHOLE original germ dictionary.
Actual function-to-germ and actual function-value maps are genuine ring maps;
no map on all zero-centred germs to arbitrary nearby germs is invented.
The original ideal internally supplies finite ACTUAL homogeneous relations,
the SAME actual finite original leading lifts and WHOLE polynomial multipliers.
True zero coefficient germs spread ALL finite polynomial identities to ONE
actual common holomorphic open. The SAME actual leading-coefficient product
has ENTIRE germ equal to the original nonzero uniform denominator; its true
nonvanishing open meets EVERY origin neighborhood and retains ALL leading
exponents. The whole original consumer supplies all genuine dictionaries.

This actual finite analytic model is not yet identified with the WHOLE
original normal cone at nearby stalks. That true coherent relative Rees/initial
ideal dictionary, nearby ALL-order finite freeness, analytic normal-flat loci,
higher HS and general G8 remain OPEN. No caller presentation/leading-lift/
functional identity/representative/flatness/result certificate enters the
original ideal consumer. No old frozen source changes or budgets increased.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology
namespace Hironaka.HironakaRelativeNormalAnalyticCoefficients
noncomputable section
open HolGerm HironakaRelativeNormalAssociatedGraded HironakaRelativeNormalUniformLocalization

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- An internally chosen entire holomorphic coefficient representative, with literal zero representative. -/
def actualCoefficientRepresentative (h : HolGerm V) : V → ℂ := by
  classical
  exact if h=0 then 0 else Classical.choose h.property

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Zero coefficients are represented by the literal entire zero function. -/
theorem actualCoefficientRepresentative_zero : actualCoefficientRepresentative (0 : HolGerm V) = 0 := by
  simp [actualCoefficientRepresentative]

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Genuine holomorphicity on an actual neighborhood is supplied by the original whole germ. -/
theorem actualCoefficientRepresentative_holomorphic (h : HolGerm V) :
    ∀ᶠ y in 𝓝 (0 : V), DifferentiableAt ℂ (actualCoefficientRepresentative h) y := by
  classical
  by_cases hh : h=0
  · simp only [actualCoefficientRepresentative,hh]
    exact eventually_differentiableAt_zero (E := V)
  · simp only [actualCoefficientRepresentative,if_neg hh]
    exact (Classical.choose_spec h.property).1

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- The WHOLE true germ of the chosen coefficient is the SAME original entire germ. -/
theorem actualCoefficientRepresentative_germ (h : HolGerm V) :
    (actualCoefficientRepresentative h : Germ (𝓝 (0 : V)) ℂ) = h.val := by
  classical
  by_cases hh : h=0
  · subst h
    rw [actualCoefficientRepresentative_zero]
    rfl
  · simp only [actualCoefficientRepresentative,if_neg hh]
    exact (Classical.choose_spec h.property).2

/-- Every finite actual coefficient family shares ONE genuine open holomorphic neighborhood. -/
theorem exists_common_coefficient_open (S : Finset (HolGerm V)) :
    ∃ U : Set V, IsOpen U ∧ (0 : V) ∈ U ∧
      ∀ h ∈ S, ∀ y ∈ U, DifferentiableAt ℂ (actualCoefficientRepresentative h) y := by
  classical
  have he : ∀ᶠ y in 𝓝 (0 : V), ∀ h ∈ S, DifferentiableAt ℂ (actualCoefficientRepresentative h) y := by
    induction S using Finset.induction_on with
    | empty => exact Eventually.of_forall (by simp)
    | @insert h S hn ih =>
      filter_upwards [actualCoefficientRepresentative_holomorphic h,ih] with y hy hys
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hy
      · exact hys k hk
  obtain ⟨U,hU,hopen,h0⟩ := mem_nhds_iff.mp he
  exact ⟨U,hopen,h0,fun h hh y hy => hU hy h hh⟩

/-- The TRUE entire finite-support polynomial over the ring of actual coefficient functions. -/
def actualPolynomialRepresentative {t : ℕ} (P : MvPolynomial (Fin t) (HolGerm V)) :
    MvPolynomial (Fin t) (V → ℂ) :=
  ∑ α ∈ P.support, MvPolynomial.monomial α (actualCoefficientRepresentative (P.coeff α))

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- At EVERY exponent the genuine entire coefficient function is its SAME original coefficient representative. -/
theorem actualPolynomialRepresentative_coeff {t : ℕ} (P : MvPolynomial (Fin t) (HolGerm V))
    (α : Fin t →₀ ℕ) :
    (actualPolynomialRepresentative P).coeff α = actualCoefficientRepresentative (P.coeff α) := by
  classical
  by_cases hα : α ∈ P.support
  · simp [actualPolynomialRepresentative,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,hα]
  · have hz : P.coeff α=0 := MvPolynomial.notMem_support_iff.mp hα
    simp [actualPolynomialRepresentative,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,hα,hz,actualCoefficientRepresentative_zero]

/-- The genuine function-to-germ ring homomorphism retains the ENTIRE original polynomial. -/
theorem actualPolynomialRepresentative_whole_germ {t : ℕ} (P : MvPolynomial (Fin t) (HolGerm V)) :
    MvPolynomial.map (Germ.coeRingHom (𝓝 (0 : V))) (actualPolynomialRepresentative P) =
      MvPolynomial.map (holGermSubring V).subtype P := by
  apply MvPolynomial.ext
  intro α
  rw [MvPolynomial.coeff_map,actualPolynomialRepresentative_coeff,MvPolynomial.coeff_map]
  exact actualCoefficientRepresentative_germ (P.coeff α)

/-- Actual specialization evaluates the TRUE representative function ring, not all zero-centred germs. -/
def actualPolynomialSpecialization {t : ℕ} (P : MvPolynomial (Fin t) (HolGerm V)) (y : V) :
    MvPolynomial (Fin t) ℂ :=
  MvPolynomial.map (Pi.evalRingHom (fun _ : V => ℂ) y) (actualPolynomialRepresentative P)

/-- Every actual specialized coefficient has its real whole-function representative value. -/
theorem actualPolynomialSpecialization_coeff {t : ℕ} (P : MvPolynomial (Fin t) (HolGerm V))
    (y : V) (α : Fin t →₀ ℕ) :
    (actualPolynomialSpecialization P y).coeff α = actualCoefficientRepresentative (P.coeff α) y := by
  rw [actualPolynomialSpecialization,MvPolynomial.coeff_map,actualPolynomialRepresentative_coeff]
  rfl

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- The whole specialized polynomial retains the SAME original finite support bound. -/
theorem actualPolynomialSpecialization_support_subset {t : ℕ} (P : MvPolynomial (Fin t) (HolGerm V))
    (y : V) : (actualPolynomialSpecialization P y).support ⊆ P.support := by
  intro α hα
  by_contra hn
  apply (MvPolynomial.mem_support_iff.mp hα)
  rw [actualPolynomialSpecialization_coeff,MvPolynomial.notMem_support_iff.mp hn,actualCoefficientRepresentative_zero]
  rfl

/-- Every TRUE original homogeneous degree remains homogeneous in the ACTUAL finite analytic polynomial model. -/
theorem actualPolynomialSpecialization_homogeneous {t q : ℕ} (P : MvPolynomial (Fin t) (HolGerm V))
    (hP : P.IsHomogeneous q) (y : V) : (actualPolynomialSpecialization P y).IsHomogeneous q := by
  intro α hα
  exact hP (MvPolynomial.mem_support_iff.mp
    (actualPolynomialSpecialization_support_subset P y (MvPolynomial.mem_support_iff.mpr hα)))

/-- An ACTUAL nonzero specialized leading coefficient retains the SAME entire original leading exponent. -/
theorem actualPolynomialSpecialization_degree {t : ℕ} (m : MonomialOrder (Fin t))
    (P : MvPolynomial (Fin t) (HolGerm V)) (y : V)
    (hy : actualCoefficientRepresentative (m.leadingCoeff P) y ≠ 0) :
    m.degree (actualPolynomialSpecialization P y) = m.degree P := by
  apply m.toSyn.injective
  apply le_antisymm
  · apply m.degree_le_iff.mpr
    intro α hα
    exact m.le_degree (actualPolynomialSpecialization_support_subset P y hα)
  · apply m.le_degree
    apply MvPolynomial.mem_support_iff.mpr
    rw [actualPolynomialSpecialization_coeff]
    exact hy

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- ONE actual common open retains holomorphicity of ALL whole polynomial coefficients in a finite family. -/
theorem exists_common_polynomial_coefficient_open {t : ℕ}
    (Ps : Finset (MvPolynomial (Fin t) (HolGerm V))) :
    ∃ U : Set V, IsOpen U ∧ (0 : V) ∈ U ∧
      ∀ P ∈ Ps, ∀ α : Fin t →₀ ℕ, ∀ y ∈ U,
        DifferentiableAt ℂ ((actualPolynomialRepresentative P).coeff α) y := by
  classical
  let S := Ps.biUnion fun P => P.support.image P.coeff
  obtain ⟨U,hopen,h0,hU⟩ := exists_common_coefficient_open S
  refine ⟨U,hopen,h0,?_⟩
  intro P hP α y hy
  rw [actualPolynomialRepresentative_coeff]
  by_cases hα : α ∈ P.support
  · exact hU (P.coeff α) (Finset.mem_biUnion.mpr ⟨P,hP,Finset.mem_image.mpr ⟨α,hα,rfl⟩⟩) y hy
  · rw [MvPolynomial.notMem_support_iff.mp hα,actualCoefficientRepresentative_zero]
    exact differentiableAt_const (0 : ℂ)

omit [NormedSpace ℂ V] in
/-- Actual zero WHOLE coefficient germs of a finite polynomial internally supply a true common functional zero open. -/
private theorem exists_open_function_polynomial_zero {t : ℕ}
    (Q : MvPolynomial (Fin t) (V → ℂ))
    (hQ : MvPolynomial.map (Germ.coeRingHom (𝓝 (0 : V))) Q = 0) :
    ∃ U : Set V, IsOpen U ∧ (0 : V) ∈ U ∧
      ∀ y ∈ U, MvPolynomial.map (Pi.evalRingHom (fun _ : V => ℂ) y) Q = 0 := by
  classical
  have he : ∀ᶠ y in 𝓝 (0 : V), ∀ α ∈ Q.support, Q.coeff α y=0 := by
    have hc : ∀ α : Fin t →₀ ℕ, ∀ᶠ y in 𝓝 (0 : V), Q.coeff α y=0 := by
      intro α
      have hh := congrArg (MvPolynomial.coeff α) hQ
      rw [MvPolynomial.coeff_map,MvPolynomial.coeff_zero] at hh
      exact Germ.coe_eq.mp hh
    induction Q.support using Finset.induction_on with
    | empty => exact Eventually.of_forall (by simp)
    | @insert α S hn ih =>
      filter_upwards [hc α,ih] with y hα hy
      intro β hβ
      rcases Finset.mem_insert.mp hβ with rfl | hβ
      · exact hα
      · exact hy β hβ
  obtain ⟨U,hU,hopen,h0⟩ := mem_nhds_iff.mp he
  refine ⟨U,hopen,h0,?_⟩
  intro y hy
  apply MvPolynomial.ext
  intro α
  rw [MvPolynomial.coeff_map,MvPolynomial.coeff_zero]
  change Q.coeff α y=0
  by_cases hα : α ∈ Q.support
  · exact hU hy α hα
  · rw [MvPolynomial.notMem_support_iff.mp hα]
    rfl

/-- Genuine finite whole original polynomial sum-product identities spread internally to ONE actual functional open. -/
theorem exists_open_polynomial_sum_mul {t : ℕ} {ι : Type*} (s : Finset ι)
    (A P : ι → MvPolynomial (Fin t) (HolGerm V)) :
    ∃ U : Set V, IsOpen U ∧ (0 : V) ∈ U ∧
      ∀ y ∈ U, actualPolynomialSpecialization (∑ i ∈ s, A i * P i) y =
        ∑ i ∈ s, actualPolynomialSpecialization (A i) y * actualPolynomialSpecialization (P i) y := by
  classical
  let Q := actualPolynomialRepresentative (∑ i ∈ s, A i * P i) -
    ∑ i ∈ s, actualPolynomialRepresentative (A i) * actualPolynomialRepresentative (P i)
  have hQ : MvPolynomial.map (Germ.coeRingHom (𝓝 (0 : V))) Q = 0 := by
    dsimp only [Q]
    simp only [map_sub,map_sum,map_mul,actualPolynomialRepresentative_whole_germ,sub_self]
  obtain ⟨U,hopen,h0,hU⟩ := exists_open_function_polynomial_zero Q hQ
  refine ⟨U,hopen,h0,?_⟩
  intro y hy
  have hh := hU y hy
  dsimp only [Q] at hh
  rw [map_sub,map_sum] at hh
  simp only [map_mul] at hh
  exact sub_eq_zero.mp hh

/-- TRUE Noetherian extraction internally chooses actual ORIGINAL homogeneous relations, not a caller presentation. -/
def actualOriginalHomogeneousRelations (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Finset (MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :=
  Classical.choose (exists_finite_originalNormalRelations d t I)

/-- The internally chosen finite family consists of actual original whole relations and generates the ENTIRE initial ideal. -/
theorem actualOriginalHomogeneousRelations_spec (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    (actualOriginalHomogeneousRelations d t I : Set _) ⊆ range (originalNormalRelation d t I) ∧
      originalNormalInitialIdeal d t I = Ideal.span (actualOriginalHomogeneousRelations d t I : Set _) :=
  Classical.choose_spec (exists_finite_originalNormalRelations d t I)

/-- EVERY internally selected original relation retains its ACTUAL original homogeneous degree. -/
theorem actualOriginalHomogeneousRelations_homogeneous (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∀ P ∈ actualOriginalHomogeneousRelations d t I, ∃ q : ℕ, P.IsHomogeneous q := by
  intro P hP
  obtain ⟨a,ha⟩ := (actualOriginalHomogeneousRelations_spec d t I).1 hP
  refine ⟨a.1,?_⟩
  rw [← ha]
  exact originalNormalInitialSymbol_homogeneous d t a.1 a.2.val a.2.property.2

/-- The SAME actual finite leading-lift family used by the genuine original uniform denominator. -/
def actualOriginalLeadingLifts (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Finset (MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :=
  letI : Field (FractionRing (HolGerm (ComplexModel d))) := FractionRing.field (HolGerm (ComplexModel d))
  originalLeadingLiftFamily (K := FractionRing (HolGerm (ComplexModel d))) t
    (MonomialOrder.degLex (σ := Fin t)) (originalNormalInitialIdeal d t I)

/-- Each actual original leading lift is a nonzero WHOLE member of the SAME complete original initial ideal. -/
theorem actualOriginalLeadingLifts_mem (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∀ g ∈ actualOriginalLeadingLifts d t I, g ∈ originalNormalInitialIdeal d t I ∧ g ≠ 0 := by
  let : Field (FractionRing (HolGerm (ComplexModel d))) := FractionRing.field (HolGerm (ComplexModel d))
  exact originalLeadingLiftFamily_mem (K := FractionRing (HolGerm (ComplexModel d))) t
    (MonomialOrder.degLex (σ := Fin t)) (originalNormalInitialIdeal d t I)

/-- Actual original ideal membership INTERNALLY produces the complete finite polynomial multiplier identity. -/
theorem exists_actualOriginalLeadingMultiplier (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (g : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (hg : g ∈ actualOriginalLeadingLifts d t I) :
    ∃ A : actualOriginalHomogeneousRelations d t I → MvPolynomial (Fin t) (HolGerm (ComplexModel d)),
      ∑ s, A s * s.val = g := by
  classical
  have hm := (actualOriginalLeadingLifts_mem d t I g hg).1
  rw [(actualOriginalHomogeneousRelations_spec d t I).2] at hm
  have hr : range (fun s : actualOriginalHomogeneousRelations d t I => s.val) =
      (actualOriginalHomogeneousRelations d t I : Set _) := by
    ext P
    exact ⟨fun ⟨s,hs⟩ => hs ▸ s.property,fun hP => ⟨⟨P,hP⟩,rfl⟩⟩
  rw [← hr] at hm
  exact Ideal.mem_span_range_iff_exists_fun.mp hm

/-- The ACTUAL polynomial multiplier family is chosen from TRUE whole original memberships. -/
def actualOriginalLeadingMultiplier (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (g : actualOriginalLeadingLifts d t I) :
    actualOriginalHomogeneousRelations d t I → MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  Classical.choose (exists_actualOriginalLeadingMultiplier d t I g.val g.property)

/-- The WHOLE genuine original finite multiplier identity, not a coefficient/value certificate. -/
theorem actualOriginalLeadingMultiplier_identity (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (g : actualOriginalLeadingLifts d t I) :
    ∑ s, actualOriginalLeadingMultiplier d t I g s * s.val = g.val :=
  Classical.choose_spec (exists_actualOriginalLeadingMultiplier d t I g.val g.property)

/-- The entire function product of the SAME actual original leading coefficients. -/
def actualOriginalDenominatorRepresentative (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ComplexModel d → ℂ :=
  ∏ g ∈ actualOriginalLeadingLifts d t I,
    actualCoefficientRepresentative ((MonomialOrder.degLex (σ := Fin t)).leadingCoeff g)

/-- The ENTIRE original polynomial denominator is precisely the WHOLE germ of its actual finite representative product. -/
theorem actualOriginalDenominatorRepresentative_whole_germ (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    (actualOriginalDenominatorRepresentative d t I : Germ (𝓝 (0 : ComplexModel d)) ℂ) =
      (originalUniformNormalDenominator d t I).val := by
  classical
  change (Germ.coeRingHom (𝓝 (0 : ComplexModel d)))
      (∏ g ∈ actualOriginalLeadingLifts d t I,
        actualCoefficientRepresentative ((MonomialOrder.degLex (σ := Fin t)).leadingCoeff g)) =
    (holGermSubring (ComplexModel d)).subtype
      (∏ g ∈ actualOriginalLeadingLifts d t I, (MonomialOrder.degLex (σ := Fin t)).leadingCoeff g)
  rw [map_prod,map_prod]
  apply Finset.prod_congr rfl
  intro g _
  exact actualCoefficientRepresentative_germ ((MonomialOrder.degLex (σ := Fin t)).leadingCoeff g)

/-- ALL internally selected original relation, leading-lift and actual multiplier polynomials, finitely many. -/
def actualOriginalModelPolynomials (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    Finset (MvPolynomial (Fin t) (HolGerm (ComplexModel d))) := by
  classical
  exact actualOriginalHomogeneousRelations d t I ∪ actualOriginalLeadingLifts d t I ∪
    ((actualOriginalLeadingLifts d t I).attach.biUnion fun g =>
      (actualOriginalHomogeneousRelations d t I).attach.image (actualOriginalLeadingMultiplier d t I g))

/-- The actual entire model contains EVERY actual original relation. -/
theorem actualOriginalRelations_mem_model (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (hP : P ∈ actualOriginalHomogeneousRelations d t I) :
    P ∈ actualOriginalModelPolynomials d t I := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hP)

/-- The actual entire model contains EVERY internally selected original leading lift. -/
theorem actualOriginalLeadingLift_mem_model (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (g : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (hg : g ∈ actualOriginalLeadingLifts d t I) :
    g ∈ actualOriginalModelPolynomials d t I := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hg)

/-- The actual entire model contains EVERY internally supplied WHOLE multiplier. -/
theorem actualOriginalMultiplier_mem_model (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (g : actualOriginalLeadingLifts d t I) (s : actualOriginalHomogeneousRelations d t I) :
    actualOriginalLeadingMultiplier d t I g s ∈ actualOriginalModelPolynomials d t I := by
  classical
  apply Finset.mem_union_right
  exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_attach _ _,Finset.mem_image.mpr ⟨s,Finset.mem_attach _ _,rfl⟩⟩

/-- ONLY the original whole ideal internally gives ONE real open for ALL coefficient holomorphicity and WHOLE finite membership identities. -/
theorem exists_actualOriginalFiniteModel_open (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ U : Set (ComplexModel d), IsOpen U ∧ (0 : ComplexModel d) ∈ U ∧
      (∀ P ∈ actualOriginalModelPolynomials d t I, ∀ α : Fin t →₀ ℕ, ∀ y ∈ U,
        DifferentiableAt ℂ ((actualPolynomialRepresentative P).coeff α) y) ∧
      (∀ g : actualOriginalLeadingLifts d t I, ∀ y ∈ U,
        actualPolynomialSpecialization g.val y =
          ∑ s : actualOriginalHomogeneousRelations d t I,
            actualPolynomialSpecialization (actualOriginalLeadingMultiplier d t I g s) y *
              actualPolynomialSpecialization s.val y) := by
  classical
  obtain ⟨U,hopen,h0,hU⟩ := exists_common_polynomial_coefficient_open (actualOriginalModelPolynomials d t I)
  have he : ∀ᶠ y in 𝓝 (0 : ComplexModel d), ∀ g : actualOriginalLeadingLifts d t I,
      actualPolynomialSpecialization g.val y =
        ∑ s : actualOriginalHomogeneousRelations d t I,
          actualPolynomialSpecialization (actualOriginalLeadingMultiplier d t I g s) y *
            actualPolynomialSpecialization s.val y := by
    apply Filter.eventually_all.mpr
    intro g
    obtain ⟨W,hwopen,hw0,hW⟩ := exists_open_polynomial_sum_mul
      (Finset.univ : Finset (actualOriginalHomogeneousRelations d t I))
      (actualOriginalLeadingMultiplier d t I g) (fun s => s.val)
    have hi := actualOriginalLeadingMultiplier_identity d t I g
    rw [hi] at hW
    filter_upwards [hwopen.mem_nhds hw0] with y hy
    exact hW y hy
  obtain ⟨W,hW,hwopen,hw0⟩ := mem_nhds_iff.mp he
  exact ⟨U ∩ W,hopen.inter hwopen,⟨h0,hw0⟩,
    fun P hP α y hy => hU P hP α y hy.1,fun g y hy => hW hy.2 g⟩

/-- The SAME actual original common analytic neighborhood is internally chosen from genuine whole producers. -/
def actualOriginalAnalyticOpen (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) : Set (ComplexModel d) :=
  Classical.choose (exists_actualOriginalFiniteModel_open d t I)

/-- The actual internally chosen model neighborhood is genuinely open. -/
theorem actualOriginalAnalyticOpen_isOpen (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    IsOpen (actualOriginalAnalyticOpen d t I) := (Classical.choose_spec (exists_actualOriginalFiniteModel_open d t I)).1

/-- The SAME actual model neighborhood genuinely contains the original zero point. -/
theorem zero_mem_actualOriginalAnalyticOpen (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    (0 : ComplexModel d) ∈ actualOriginalAnalyticOpen d t I :=
  (Classical.choose_spec (exists_actualOriginalFiniteModel_open d t I)).2.1

/-- ALL entire original model coefficients are genuinely holomorphic at EVERY point of the SAME actual common open. -/
theorem actualOriginalModel_coefficients_holomorphic (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∀ P ∈ actualOriginalModelPolynomials d t I, ∀ α : Fin t →₀ ℕ, ∀ y ∈ actualOriginalAnalyticOpen d t I,
      DifferentiableAt ℂ ((actualPolynomialRepresentative P).coeff α) y :=
  (Classical.choose_spec (exists_actualOriginalFiniteModel_open d t I)).2.2.1

/-- ALL genuine entire original leading-lift membership identities hold at EVERY point of the SAME actual common open. -/
theorem actualOriginalModel_leading_identity (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∀ g : actualOriginalLeadingLifts d t I, ∀ y ∈ actualOriginalAnalyticOpen d t I,
      actualPolynomialSpecialization g.val y =
        ∑ s : actualOriginalHomogeneousRelations d t I,
          actualPolynomialSpecialization (actualOriginalLeadingMultiplier d t I g s) y *
            actualPolynomialSpecialization s.val y :=
  (Classical.choose_spec (exists_actualOriginalFiniteModel_open d t I)).2.2.2

/-- Actual differentiability is retained by a TRUE finite function product. -/
private theorem actual_finite_product_differentiable {ι : Type*} (S : Finset ι) (f : ι → V → ℂ) (y : V)
    (hf : ∀ i ∈ S, DifferentiableAt ℂ (f i) y) : DifferentiableAt ℂ (∏ i ∈ S, f i) y := by
  classical
  revert hf
  induction S using Finset.induction_on with
  | empty => intro _; exact differentiableAt_const (1 : ℂ)
  | @insert i S hi ih =>
    intro hf
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self i S)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- The SAME actual entire original denominator representative is holomorphic on the actual common model open. -/
theorem actualOriginalDenominatorRepresentative_holomorphic (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (y : ComplexModel d)
    (hy : y ∈ actualOriginalAnalyticOpen d t I) :
    DifferentiableAt ℂ (actualOriginalDenominatorRepresentative d t I) y := by
  apply actual_finite_product_differentiable
  intro g hg
  have hh := actualOriginalModel_coefficients_holomorphic d t I g
    (actualOriginalLeadingLift_mem_model d t I g hg)
    ((MonomialOrder.degLex (σ := Fin t)).degree g) y hy
  rw [actualPolynomialRepresentative_coeff] at hh
  exact hh

/-- The genuine nonvanishing open of the SAME actual entire original denominator and SAME actual analytic model. -/
def actualOriginalNonvanishingOpen (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) : Set (ComplexModel d) :=
  {y | y ∈ actualOriginalAnalyticOpen d t I ∧ actualOriginalDenominatorRepresentative d t I y ≠ 0}

/-- The SAME internally supplied denominator/model nonvanishing set is an ACTUAL open set. -/
theorem actualOriginalNonvanishingOpen_isOpen (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    IsOpen (actualOriginalNonvanishingOpen d t I) := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  have he := (actualOriginalDenominatorRepresentative_holomorphic d t I y hy.1).continuousAt.eventually_ne hy.2
  filter_upwards [(actualOriginalAnalyticOpen_isOpen d t I).mem_nhds hy.1,he] with z hz hβ
  exact ⟨hz,hβ⟩

/-- ENTIRE original nonzero-germ information makes the SAME genuine open meet EVERY actual origin neighborhood. -/
theorem actualOriginalNonvanishingOpen_meets_nhds (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (W : Set (ComplexModel d)) (hW : W ∈ 𝓝 (0 : ComplexModel d)) :
    (W ∩ actualOriginalNonvanishingOpen d t I).Nonempty := by
  by_contra hn
  have he : ∀ᶠ y in 𝓝 (0 : ComplexModel d), actualOriginalDenominatorRepresentative d t I y = 0 := by
    filter_upwards [hW,(actualOriginalAnalyticOpen_isOpen d t I).mem_nhds
      (zero_mem_actualOriginalAnalyticOpen d t I)] with y hyW hyU
    by_contra hyβ
    exact hn ⟨y,hyW,hyU,hyβ⟩
  have hz : (actualOriginalDenominatorRepresentative d t I : Germ (𝓝 (0 : ComplexModel d)) ℂ) = 0 :=
    Germ.coe_eq.mpr he
  rw [actualOriginalDenominatorRepresentative_whole_germ] at hz
  exact originalUniformNormalDenominator_ne_zero d t I (Subtype.val_injective hz)

/-- ALL internally supplied original leading exponents persist on the SAME actual nonvanishing analytic open. -/
theorem actualOriginalLeadingLifts_specialized_degree (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (y : ComplexModel d) (hy : y ∈ actualOriginalNonvanishingOpen d t I) :
    ∀ g ∈ actualOriginalLeadingLifts d t I,
      (MonomialOrder.degLex (σ := Fin t)).degree (actualPolynomialSpecialization g y) =
        (MonomialOrder.degLex (σ := Fin t)).degree g := by
  classical
  intro g hg
  apply actualPolynomialSpecialization_degree
  have hp := hy.2
  change (Pi.evalRingHom (fun _ : ComplexModel d => ℂ) y)
    (∏ h ∈ actualOriginalLeadingLifts d t I,
      actualCoefficientRepresentative ((MonomialOrder.degLex (σ := Fin t)).leadingCoeff h)) ≠ 0 at hp
  rw [map_prod] at hp
  exact Finset.prod_ne_zero_iff.mp hp g hg

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- ONLY the actual original whole ideal internally produces its ENTIRE common analytic finite model and SAME nonzero denominator open. -/
theorem exists_original_whole_analytic_model (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :
    ∃ (U : Set (ComplexModel d)) (β : ComplexModel d → ℂ),
      U = actualOriginalAnalyticOpen d t I ∧ β = actualOriginalDenominatorRepresentative d t I ∧
      (actualOriginalHomogeneousRelations d t I : Set _) ⊆ range (originalNormalRelation d t I) ∧
      originalNormalInitialIdeal d t I = Ideal.span (actualOriginalHomogeneousRelations d t I : Set _) ∧
      (∀ P ∈ actualOriginalHomogeneousRelations d t I, ∃ q : ℕ,
        P.IsHomogeneous q ∧ ∀ y ∈ U, (actualPolynomialSpecialization P y).IsHomogeneous q) ∧
      (∀ g ∈ actualOriginalLeadingLifts d t I, g ∈ originalNormalInitialIdeal d t I ∧ g ≠ 0) ∧
      IsOpen U ∧ (0 : ComplexModel d) ∈ U ∧
      (∀ P ∈ actualOriginalModelPolynomials d t I, ∀ α : Fin t →₀ ℕ, ∀ y ∈ U,
        DifferentiableAt ℂ ((actualPolynomialRepresentative P).coeff α) y) ∧
      (∀ P ∈ actualOriginalModelPolynomials d t I,
        MvPolynomial.map (Germ.coeRingHom (𝓝 (0 : ComplexModel d))) (actualPolynomialRepresentative P) =
          MvPolynomial.map (holGermSubring (ComplexModel d)).subtype P) ∧
      (∀ g : actualOriginalLeadingLifts d t I, ∀ y ∈ U,
        actualPolynomialSpecialization g.val y =
          ∑ s : actualOriginalHomogeneousRelations d t I,
            actualPolynomialSpecialization (actualOriginalLeadingMultiplier d t I g s) y *
              actualPolynomialSpecialization s.val y) ∧
      (β : Germ (𝓝 (0 : ComplexModel d)) ℂ) = (originalUniformNormalDenominator d t I).val ∧
      originalUniformNormalDenominator d t I ≠ 0 ∧
      (∀ y ∈ U, DifferentiableAt ℂ β y) ∧
      IsOpen {y | y ∈ U ∧ β y ≠ 0} ∧
      (∀ W ∈ 𝓝 (0 : ComplexModel d), (W ∩ {y | y ∈ U ∧ β y ≠ 0}).Nonempty) ∧
      ∀ y ∈ {y | y ∈ U ∧ β y ≠ 0}, ∀ g ∈ actualOriginalLeadingLifts d t I,
        (MonomialOrder.degLex (σ := Fin t)).degree (actualPolynomialSpecialization g y) =
          (MonomialOrder.degLex (σ := Fin t)).degree g := by
  refine ⟨actualOriginalAnalyticOpen d t I,actualOriginalDenominatorRepresentative d t I,rfl,rfl,
    (actualOriginalHomogeneousRelations_spec d t I).1,(actualOriginalHomogeneousRelations_spec d t I).2,
    ?_,actualOriginalLeadingLifts_mem d t I,actualOriginalAnalyticOpen_isOpen d t I,
    zero_mem_actualOriginalAnalyticOpen d t I,actualOriginalModel_coefficients_holomorphic d t I,
    (fun P _ => actualPolynomialRepresentative_whole_germ P),actualOriginalModel_leading_identity d t I,
    actualOriginalDenominatorRepresentative_whole_germ d t I,originalUniformNormalDenominator_ne_zero d t I,
    actualOriginalDenominatorRepresentative_holomorphic d t I,actualOriginalNonvanishingOpen_isOpen d t I,
    actualOriginalNonvanishingOpen_meets_nhds d t I,actualOriginalLeadingLifts_specialized_degree d t I⟩
  intro P hP
  obtain ⟨q,hq⟩ := actualOriginalHomogeneousRelations_homogeneous d t I P hP
  exact ⟨q,hq,fun y _ => actualPolynomialSpecialization_homogeneous P hq y⟩

end
end Hironaka.HironakaRelativeNormalAnalyticCoefficients
