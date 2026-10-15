/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalAffineDNCDictionary

/-! # A common algebra of actual holomorphic coefficient functions

The honest nearby homomorphisms have actual functions as their domain. Finite
original homogeneous relations lift to this algebra on a common open set. Their
mapped ideals are the entire nearby original initial ideals. This does not yet
prove a single all-degree generic free open for the nearby normal cones.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaRelativeNormalCoefficientFunctionAlgebra

noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalCoherentSaturation HironakaRelativeNormalAnalyticCoefficients
  HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalDeformationFiniteRelationsSpread
  HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalNearbyPolynomialCoefficientGerms
  HironakaRelativeNormalAffineDNCDictionary

/-- Actual functions holomorphic near every point of the fixed base set. -/
def coefficientFunctionAlgebra (d : ℕ) (B : Set (ComplexModel d)) :
    Subalgebra ℂ (ComplexModel d → ℂ) where
  carrier := {f | ∀ a ∈ B, HolAt f a}
  zero_mem' := fun _ _ => Eventually.of_forall fun _ => differentiableAt_const (0 : ℂ)
  one_mem' := fun _ _ => Eventually.of_forall fun _ => differentiableAt_const (1 : ℂ)
  add_mem' := fun hf hg a ha => (hf a ha).add (hg a ha)
  mul_mem' := fun hf hg a ha => (hf a ha).mul (hg a ha)
  algebraMap_mem' := fun c _ _ => Eventually.of_forall fun _ => differentiableAt_const c

/-- The whole translated germ map is defined on actual holomorphic functions. -/
def coefficientGermHom (d : ℕ) (B : Set (ComplexModel d))
    (a : ComplexModel d) (ha : a ∈ B) :
    coefficientFunctionAlgebra d B →ₐ[ℂ] HolGerm (ComplexModel d) where
  toFun f := HolGerm.mk (f.val ∘ actualAffineTranslation d a)
    (actualCoefficientFunctionTranslation_holomorphic d a f.val (f.property a ha))
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The chosen original coefficient is an actual function in the common algebra. -/
def coefficientFunction (d : ℕ) (B : Set (ComplexModel d))
    (c : HolGerm (ComplexModel d))
    (hc : ∀ a ∈ B, HolAt (actualCoefficientRepresentative c) a) :
    coefficientFunctionAlgebra d B := ⟨actualCoefficientRepresentative c, hc⟩

/-- A finite whole polynomial lifted through actual coefficient functions. -/
def coefficientPolynomialLift (d t : ℕ) (B : Set (ComplexModel d))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hc : ∀ α, ∀ a ∈ B, HolAt (actualCoefficientRepresentative (P.coeff α)) a) :
    MvPolynomial (Fin t) (coefficientFunctionAlgebra d B) :=
  ∑ α ∈ P.support, MvPolynomial.monomial α (coefficientFunction d B (P.coeff α) (hc α))

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
theorem coefficientPolynomialLift_coeff (d t : ℕ) (B : Set (ComplexModel d))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hc : ∀ α, ∀ a ∈ B, HolAt (actualCoefficientRepresentative (P.coeff α)) a)
    (α : Fin t →₀ ℕ) :
    (coefficientPolynomialLift d t B P hc).coeff α = coefficientFunction d B (P.coeff α) (hc α) := by
  classical
  by_cases hα : α ∈ P.support
  · simp [coefficientPolynomialLift, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hα]
  · have hz : coefficientFunction d B (P.coeff α) (hc α) = 0 := by
      apply Subtype.ext
      change actualCoefficientRepresentative (P.coeff α) = 0
      rw [MvPolynomial.notMem_support_iff.mp hα, actualCoefficientRepresentative_zero]
    simp [coefficientPolynomialLift, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hα, hz]

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
theorem coefficientPolynomialLift_homogeneous (d t : ℕ) (B : Set (ComplexModel d))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hc : ∀ α, ∀ a ∈ B, HolAt (actualCoefficientRepresentative (P.coeff α)) a)
    {q : ℕ} (hP : P.IsHomogeneous q) :
    (coefficientPolynomialLift d t B P hc).IsHomogeneous q := by
  intro α hα
  apply hP
  intro hz
  apply hα
  rw [coefficientPolynomialLift_coeff]
  apply Subtype.ext
  change actualCoefficientRepresentative (P.coeff α) = 0
  rw [hz, actualCoefficientRepresentative_zero]

theorem coefficientPolynomialLift_nearby (d t : ℕ) (B : Set (ComplexModel d))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hc : ∀ α, ∀ a ∈ B, HolAt (actualCoefficientRepresentative (P.coeff α)) a)
    (a : ComplexModel d) (ha : a ∈ B) :
    MvPolynomial.map (coefficientGermHom d B a ha).toRingHom (coefficientPolynomialLift d t B P hc) =
      actualNearbyCoefficientPolynomial d t P a (fun α => hc α a ha) := by
  apply MvPolynomial.ext
  intro α
  rw [MvPolynomial.coeff_map, coefficientPolynomialLift_coeff, actualNearbyCoefficientPolynomial_coeff]
  rfl

theorem coefficientPolynomialLift_origin (d t : ℕ) (B : Set (ComplexModel d))
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hc : ∀ α, ∀ a ∈ B, HolAt (actualCoefficientRepresentative (P.coeff α)) a)
    (h0 : (0 : ComplexModel d) ∈ B) :
    MvPolynomial.map (coefficientGermHom d B 0 h0).toRingHom (coefficientPolynomialLift d t B P hc) = P := by
  apply MvPolynomial.ext
  intro α
  rw [MvPolynomial.coeff_map, coefficientPolynomialLift_coeff]
  apply Subtype.ext
  change (actualCoefficientRepresentative (P.coeff α) ∘ actualAffineTranslation d 0 :
    Germ (𝓝 (0 : ComplexModel d)) ℂ) = (P.coeff α).val
  have he : actualCoefficientRepresentative (P.coeff α) ∘ actualAffineTranslation d 0 =
      actualCoefficientRepresentative (P.coeff α) := by
    funext z
    simp only [Function.comp_apply, actualAffineTranslation, zero_add]
  rw [he]
  exact actualCoefficientRepresentative_germ (P.coeff α)

private theorem map_span_range {R S ι : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (Q : ι → R) :
    Ideal.map f (Ideal.span (range Q)) = Ideal.span (range (fun i => f (Q i))) := by
  rw [Ideal.map_span]
  apply congrArg Ideal.span
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨Q i, ⟨i, rfl⟩, rfl⟩

/-- A single internally produced function algebra presents every whole nearby initial ideal. -/
theorem exists_original_coefficient_algebra_initial_family (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ B : Set (ComplexModel d), IsOpen B ∧
      ∃ h0 : (0 : ComplexModel d) ∈ B,
      ∃ Q : ↥(actualOriginalRelationFamily d t I) →
        MvPolynomial (Fin t) (coefficientFunctionAlgebra d B),
        (∀ P, ∃ q : ℕ, (Q P).IsHomogeneous q) ∧
        (∀ P, MvPolynomial.map (coefficientGermHom d B 0 h0).toRingHom (Q P) = P.val) ∧
        Ideal.map (MvPolynomial.map (coefficientGermHom d B 0 h0).toRingHom)
          (Ideal.span (range Q)) = originalNormalInitialIdeal d t (originalCoherentOriginIdeal I) ∧
        ∀ a (ha : a ∈ B),
          Ideal.map (MvPolynomial.map (coefficientGermHom d B a ha).toRingHom)
            (Ideal.span (range Q)) = originalNormalInitialIdeal d t
              (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) := by
  classical
  let := tangentAlgebra d t
  obtain ⟨_N, B, hB, h0, _hcent, _hchain, hc, hmodels⟩ :=
    exists_original_whole_nearby_normal_initial_ideal d t I hI
  let Q := fun P : ↥(actualOriginalRelationFamily d t I) =>
    coefficientPolynomialLift d t B P.val (fun α a ha => hc a ha P α)
  have hQ0 (P : ↥(actualOriginalRelationFamily d t I)) :
      MvPolynomial.map (coefficientGermHom d B 0 h0).toRingHom (Q P) = P.val :=
    coefficientPolynomialLift_origin d t B P.val (fun α a ha => hc a ha P α) h0
  refine ⟨B, hB, h0, Q, ?_, hQ0, ?_, ?_⟩
  · intro P
    obtain ⟨q, hq⟩ := actualOriginalHomogeneousRelations_homogeneous d t
      (originalCoherentOriginIdeal I) P.val P.property
    exact ⟨q, coefficientPolynomialLift_homogeneous d t B P.val _ hq⟩
  · rw [map_span_range (MvPolynomial.map (coefficientGermHom d B 0 h0).toRingHom) Q]
    have he : (fun P => MvPolynomial.map (coefficientGermHom d B 0 h0).toRingHom (Q P)) =
        fun P : ↥(actualOriginalRelationFamily d t I) => P.val := funext hQ0
    rw [he]
    have hr : range (fun P : ↥(actualOriginalRelationFamily d t I) => P.val) =
        (actualOriginalRelationFamily d t I : Set _) := by
      ext P
      exact ⟨fun ⟨Q, hQ⟩ => hQ ▸ Q.property, fun hP => ⟨⟨P, hP⟩, rfl⟩⟩
    rw [hr]
    exact (actualOriginalHomogeneousRelations_spec d t (originalCoherentOriginIdeal I)).2.symm
  · intro a ha
    rw [map_span_range (MvPolynomial.map (coefficientGermHom d B a ha).toRingHom) Q]
    have he : (fun P => MvPolynomial.map (coefficientGermHom d B a ha).toRingHom (Q P)) =
        fun P : ↥(actualOriginalRelationFamily d t I) =>
          actualNearbyCoefficientPolynomial d t P.val a (hc a ha P) := by
      funext P
      exact coefficientPolynomialLift_nearby d t B P.val _ a ha
    rw [he]
    exact (hmodels a ha).2.2.1

section FiniteCoefficients

variable {A : Type*} [CommRing A] [Algebra ℂ A] {t : ℕ}

/-- The actual finite coefficient set of a finite polynomial family. -/
def finitePolynomialCoefficients (Ps : Finset (MvPolynomial (Fin t) A)) : Finset A := by
  classical
  exact Ps.biUnion fun P => P.support.image P.coeff

/-- The finitely generated complex subalgebra of all supported coefficients. -/
def finitePolynomialCoefficientAlgebra (Ps : Finset (MvPolynomial (Fin t) A)) : Subalgebra ℂ A :=
  Algebra.adjoin ℂ (finitePolynomialCoefficients Ps : Set A)

theorem finitePolynomialCoefficientAlgebra_finiteType (Ps : Finset (MvPolynomial (Fin t) A)) :
    Algebra.FiniteType ℂ (finitePolynomialCoefficientAlgebra Ps) :=
  Algebra.FiniteType.adjoin_of_finite (finitePolynomialCoefficients Ps).finite_toSet

theorem finitePolynomialCoefficientAlgebra_isNoetherianRing (Ps : Finset (MvPolynomial (Fin t) A)) :
    IsNoetherianRing (finitePolynomialCoefficientAlgebra Ps) := by
  let := finitePolynomialCoefficientAlgebra_finiteType Ps
  exact Algebra.FiniteType.isNoetherianRing ℂ _

theorem coefficient_mem_finitePolynomialCoefficientAlgebra
    (Ps : Finset (MvPolynomial (Fin t) A)) (P : MvPolynomial (Fin t) A) (hP : P ∈ Ps)
    (α : Fin t →₀ ℕ) : P.coeff α ∈ finitePolynomialCoefficientAlgebra Ps := by
  classical
  by_cases hα : α ∈ P.support
  · apply Algebra.subset_adjoin
    exact Finset.mem_biUnion.mpr ⟨P, hP, Finset.mem_image.mpr ⟨α, hα, rfl⟩⟩
  · rw [MvPolynomial.notMem_support_iff.mp hα]
    exact (finitePolynomialCoefficientAlgebra Ps).zero_mem

/-- A whole polynomial with all coefficients in the finite generated subalgebra. -/
def finiteCoefficientPolynomialLift (Ps : Finset (MvPolynomial (Fin t) A))
    (P : MvPolynomial (Fin t) A) (hP : P ∈ Ps) :
    MvPolynomial (Fin t) (finitePolynomialCoefficientAlgebra Ps) :=
  ∑ α ∈ P.support, MvPolynomial.monomial α
    ⟨P.coeff α, coefficient_mem_finitePolynomialCoefficientAlgebra Ps P hP α⟩

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
theorem finiteCoefficientPolynomialLift_coeff (Ps : Finset (MvPolynomial (Fin t) A))
    (P : MvPolynomial (Fin t) A) (hP : P ∈ Ps) (α : Fin t →₀ ℕ) :
    (finiteCoefficientPolynomialLift Ps P hP).coeff α =
      ⟨P.coeff α, coefficient_mem_finitePolynomialCoefficientAlgebra Ps P hP α⟩ := by
  classical
  by_cases hα : α ∈ P.support
  · simp [finiteCoefficientPolynomialLift, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hα]
  · have hz : (⟨P.coeff α, coefficient_mem_finitePolynomialCoefficientAlgebra Ps P hP α⟩ :
        finitePolynomialCoefficientAlgebra Ps) = 0 :=
      Subtype.ext (MvPolynomial.notMem_support_iff.mp hα)
    simp [finiteCoefficientPolynomialLift, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, hα, hz]

theorem finiteCoefficientPolynomialLift_map (Ps : Finset (MvPolynomial (Fin t) A))
    (P : MvPolynomial (Fin t) A) (hP : P ∈ Ps) :
    MvPolynomial.map (finitePolynomialCoefficientAlgebra Ps).val.toRingHom
      (finiteCoefficientPolynomialLift Ps P hP) = P := by
  apply MvPolynomial.ext
  intro α
  rw [MvPolynomial.coeff_map, finiteCoefficientPolynomialLift_coeff]
  rfl

theorem finiteCoefficientPolynomialLift_homogeneous (Ps : Finset (MvPolynomial (Fin t) A))
    (P : MvPolynomial (Fin t) A) (hP : P ∈ Ps) {q : ℕ} (hq : P.IsHomogeneous q) :
    (finiteCoefficientPolynomialLift Ps P hP).IsHomogeneous q := by
  intro α hα
  apply hq
  intro hz
  apply hα
  rw [finiteCoefficientPolynomialLift_coeff]
  exact Subtype.ext hz

end FiniteCoefficients

/-- Capture the commutative ring structure of a coefficient subalgebra before forming quotients. -/
@[instance_reducible] def coefficientSubalgebraRing (d : ℕ) (B : Set (ComplexModel d))
    (C : Subalgebra ℂ (coefficientFunctionAlgebra d B)) : CommRing C := C.toCommRing

attribute [local instance] coefficientSubalgebraRing

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Noetherianity spreads the complete coefficient kernel, not only finitely many chosen identities. -/
theorem exists_common_coefficient_kernel_open (d : ℕ) (B : Set (ComplexModel d))
    (hB : IsOpen B) (h0 : (0 : ComplexModel d) ∈ B)
    (C : Subalgebra ℂ (coefficientFunctionAlgebra d B)) [IsNoetherianRing C] :
    ∃ W : Set (ComplexModel d), IsOpen W ∧ (0 : ComplexModel d) ∈ W ∧
      ∃ hWB : W ⊆ B, ∀ a (ha : a ∈ W),
        RingHom.ker ((coefficientGermHom d B 0 h0).comp C.val) ≤
          RingHom.ker ((coefficientGermHom d B a (hWB ha)).comp C.val) := by
  classical
  let J := RingHom.ker ((coefficientGermHom d B 0 h0).comp C.val)
  have hfg : J.FG := IsNoetherian.noetherian J
  obtain ⟨S, hS⟩ := hfg
  have he (f : C) (hf : f ∈ S) : (C.val f).val =ᶠ[𝓝 (0 : ComplexModel d)] 0 := by
    have hj : f ∈ J := by
      rw [← hS]
      exact Ideal.subset_span hf
    have hg : ((coefficientGermHom d B 0 h0).comp C.val) f = 0 := hj
    apply Germ.coe_eq.mp
    have hg' := congrArg Subtype.val hg
    change (Germ.coeRingHom (𝓝 (0 : ComplexModel d)))
      ((C.val f).val ∘ actualAffineTranslation d 0) = 0 at hg'
    have hid : (C.val f).val ∘ actualAffineTranslation d 0 = (C.val f).val := by
      funext z
      simp only [Function.comp_apply, actualAffineTranslation, zero_add]
    rw [hid] at hg'
    exact hg'
  have hall : ∀ᶠ z in 𝓝 (0 : ComplexModel d), ∀ f ∈ S, (C.val f).val z = 0 :=
    (eventually_all_finset S).mpr fun f hf => he f hf
  obtain ⟨U, hUsub, hU, h0U⟩ := mem_nhds_iff.mp hall
  let W := U ∩ B
  have hW : IsOpen W := hU.inter hB
  have hWB : W ⊆ B := fun _ hx => hx.2
  refine ⟨W, hW, ⟨h0U, h0⟩, hWB, ?_⟩
  intro a ha
  change J ≤ _
  rw [← hS]
  apply Ideal.span_le.mpr
  intro f hf
  change ((coefficientGermHom d B a (hWB ha)).comp C.val) f = 0
  apply Subtype.ext
  change (Germ.coeRingHom (𝓝 (0 : ComplexModel d)))
    ((C.val f).val ∘ actualAffineTranslation d a) = 0
  apply Germ.coe_eq.mpr
  have ht : Tendsto (actualAffineTranslation d a) (𝓝 0) (𝓝 a) := by
    simpa only [actualAffineTranslation_zero] using
      (actualAffineTranslation_contMDiff d a).continuous.tendsto (0 : ComplexModel d)
  exact (ht.eventually (hW.mem_nhds ha)).mono fun z hz => hUsub hz.1 f hf

/-- The internally determined full origin-germ kernel of a coefficient subalgebra. -/
def coefficientOriginKernel (d : ℕ) (B : Set (ComplexModel d))
    (h0 : (0 : ComplexModel d) ∈ B) (C : Subalgebra ℂ (coefficientFunctionAlgebra d B)) : Ideal C :=
  RingHom.ker ((coefficientGermHom d B 0 h0).comp C.val)

/-- The common algebra of actual coefficients modulo their complete origin kernel. -/
abbrev coefficientOriginAlgebra (d : ℕ) (B : Set (ComplexModel d))
    (h0 : (0 : ComplexModel d) ∈ B) (C : Subalgebra ℂ (coefficientFunctionAlgebra d B)) :=
  C ⧸ coefficientOriginKernel d B h0 C

theorem coefficientOriginAlgebra_isDomain (d : ℕ) (B : Set (ComplexModel d))
    (h0 : (0 : ComplexModel d) ∈ B) (C : Subalgebra ℂ (coefficientFunctionAlgebra d B)) :
    IsDomain (coefficientOriginAlgebra d B h0 C) := by
  let : (coefficientOriginKernel d B h0 C).IsPrime :=
    RingHom.ker_isPrime ((coefficientGermHom d B 0 h0).comp C.val)
  infer_instance

theorem coefficientOriginAlgebra_finiteType (d : ℕ) (B : Set (ComplexModel d))
    (h0 : (0 : ComplexModel d) ∈ B) (C : Subalgebra ℂ (coefficientFunctionAlgebra d B))
    [Algebra.FiniteType ℂ C] : Algebra.FiniteType ℂ (coefficientOriginAlgebra d B h0 C) :=
  inferInstance

/-- One genuine open supports all nearby maps out of the common coefficient domain. -/
theorem exists_common_coefficient_origin_quotient_homs (d : ℕ) (B : Set (ComplexModel d))
    (hB : IsOpen B) (h0 : (0 : ComplexModel d) ∈ B)
    (C : Subalgebra ℂ (coefficientFunctionAlgebra d B)) [IsNoetherianRing C] :
    ∃ W : Set (ComplexModel d), IsOpen W ∧ (0 : ComplexModel d) ∈ W ∧
      ∃ hWB : W ⊆ B,
      ∃ ρ : ∀ a : ComplexModel d, a ∈ W →
          coefficientOriginAlgebra d B h0 C →ₐ[ℂ] HolGerm (ComplexModel d),
      ∀ a (ha : a ∈ W),
        (ρ a ha).comp (Ideal.Quotient.mkₐ ℂ (coefficientOriginKernel d B h0 C)) =
          (coefficientGermHom d B a (hWB ha)).comp C.val := by
  obtain ⟨W, hW, h0W, hWB, hker⟩ := exists_common_coefficient_kernel_open d B hB h0 C
  let ρ := fun a (ha : a ∈ W) => Ideal.Quotient.liftₐ (coefficientOriginKernel d B h0 C)
    ((coefficientGermHom d B a (hWB ha)).comp C.val) (fun f hf => hker a ha hf)
  exact ⟨W, hW, h0W, hWB, ρ, fun a ha => Ideal.Quotient.liftₐ_comp _ _ _⟩

/-- Original coherent input supplies a finite type actual coefficient algebra for all nearby initial ideals. -/
theorem exists_original_finiteType_coefficient_algebra_initial_family (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ B : Set (ComplexModel d), IsOpen B ∧ ∃ h0 : (0 : ComplexModel d) ∈ B,
      ∃ C : Subalgebra ℂ (coefficientFunctionAlgebra d B), Algebra.FiniteType ℂ C ∧
      ∃ Q : ↥(actualOriginalRelationFamily d t I) → MvPolynomial (Fin t) C,
        (∀ P, ∃ q : ℕ, (Q P).IsHomogeneous q) ∧
        Ideal.map (MvPolynomial.map ((coefficientGermHom d B 0 h0).comp C.val).toRingHom)
          (Ideal.span (range Q)) = originalNormalInitialIdeal d t (originalCoherentOriginIdeal I) ∧
        ∀ a (ha : a ∈ B),
          Ideal.map (MvPolynomial.map ((coefficientGermHom d B a ha).comp C.val).toRingHom)
            (Ideal.span (range Q)) = originalNormalInitialIdeal d t
              (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) := by
  classical
  obtain ⟨B, hB, h0, Q, hhom, _hQ0, horigin, hnearby⟩ :=
    exists_original_coefficient_algebra_initial_family d t I hI
  let Ps : Finset (MvPolynomial (Fin t) (coefficientFunctionAlgebra d B)) := Finset.univ.image Q
  have hPs (P : ↥(actualOriginalRelationFamily d t I)) : Q P ∈ Ps :=
    Finset.mem_image.mpr ⟨P, Finset.mem_univ _, rfl⟩
  let C : Subalgebra ℂ (coefficientFunctionAlgebra d B) := finitePolynomialCoefficientAlgebra Ps
  let L : ↥(actualOriginalRelationFamily d t I) → MvPolynomial (Fin t) C :=
    fun P => finiteCoefficientPolynomialLift Ps (Q P) (hPs P)
  have hL (a : ComplexModel d) (ha : a ∈ B) (P : ↥(actualOriginalRelationFamily d t I)) :
      MvPolynomial.map ((coefficientGermHom d B a ha).comp C.val).toRingHom (L P) =
        MvPolynomial.map (coefficientGermHom d B a ha).toRingHom (Q P) := by
    rw [← finiteCoefficientPolynomialLift_map Ps (Q P) (hPs P)]
    rw [MvPolynomial.map_map]
    rfl
  have himage (a : ComplexModel d) (ha : a ∈ B) :
      Ideal.map (MvPolynomial.map ((coefficientGermHom d B a ha).comp C.val).toRingHom)
        (Ideal.span (range L)) =
      Ideal.map (MvPolynomial.map (coefficientGermHom d B a ha).toRingHom) (Ideal.span (range Q)) := by
    let : CommRing C := C.toCommRing
    rw [map_span_range (MvPolynomial.map ((coefficientGermHom d B a ha).comp C.val).toRingHom) L,
      map_span_range (MvPolynomial.map (coefficientGermHom d B a ha).toRingHom) Q]
    exact congrArg (fun F => Ideal.span (range F)) (funext (hL a ha))
  refine ⟨B, hB, h0, C, finitePolynomialCoefficientAlgebra_finiteType Ps, L, ?_, ?_, ?_⟩
  · intro P
    obtain ⟨q, hq⟩ := hhom P
    exact ⟨q, finiteCoefficientPolynomialLift_homogeneous Ps (Q P) (hPs P) hq⟩
  · exact (himage 0 h0).trans horigin
  · exact fun a ha => (himage a ha).trans (hnearby a ha)

/-- Every whole nearby initial ideal is an actual coefficient image of one homogeneous ideal over a domain. -/
theorem exists_original_common_domain_coefficient_initial_family (d t : ℕ)
    (I : GermIdeal (d+t) (ComplexModel (d+t))) (hI : I.IsCoherent) :
    ∃ B : Set (ComplexModel d), IsOpen B ∧ ∃ h0 : (0 : ComplexModel d) ∈ B,
      ∃ C : Subalgebra ℂ (coefficientFunctionAlgebra d B), Algebra.FiniteType ℂ C ∧
        IsDomain (coefficientOriginAlgebra d B h0 C) ∧
        Algebra.FiniteType ℂ (coefficientOriginAlgebra d B h0 C) ∧
      ∃ W : Set (ComplexModel d), IsOpen W ∧ (0 : ComplexModel d) ∈ W ∧
      ∃ hWB : W ⊆ B,
      ∃ ρ : ∀ a : ComplexModel d, a ∈ W →
          coefficientOriginAlgebra d B h0 C →ₐ[ℂ] HolGerm (ComplexModel d),
      ∃ Q : ↥(actualOriginalRelationFamily d t I) →
          MvPolynomial (Fin t) (coefficientOriginAlgebra d B h0 C),
        (∀ P, ∃ q : ℕ, (Q P).IsHomogeneous q) ∧
        (∀ a (ha : a ∈ W),
          (ρ a ha).comp (Ideal.Quotient.mkₐ ℂ (coefficientOriginKernel d B h0 C)) =
            (coefficientGermHom d B a (hWB ha)).comp C.val) ∧
        ∀ a (ha : a ∈ W), Ideal.map (MvPolynomial.map (ρ a ha).toRingHom)
          (Ideal.span (range Q)) = originalNormalInitialIdeal d t
            (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf I (tangentInclusion d t a))) := by
  classical
  obtain ⟨B, hB, h0, C, hC, L, hhom, _horigin, hnearby⟩ :=
    exists_original_finiteType_coefficient_algebra_initial_family d t I hI
  let : Algebra.FiniteType ℂ C := hC
  let : IsNoetherianRing C := Algebra.FiniteType.isNoetherianRing ℂ C
  obtain ⟨W, hW, h0W, hWB, ρ, hρ⟩ := exists_common_coefficient_origin_quotient_homs d B hB h0 C
  let q := Ideal.Quotient.mkₐ ℂ (coefficientOriginKernel d B h0 C)
  let Q := fun P => MvPolynomial.map q.toRingHom (L P)
  refine ⟨B, hB, h0, C, hC, coefficientOriginAlgebra_isDomain d B h0 C,
    coefficientOriginAlgebra_finiteType d B h0 C, W, hW, h0W, hWB, ρ, Q, ?_, hρ, ?_⟩
  · intro P
    obtain ⟨k, hk⟩ := hhom P
    exact ⟨k, hk.map q.toRingHom⟩
  · intro a ha
    have hmap (P : ↥(actualOriginalRelationFamily d t I)) :
        MvPolynomial.map (ρ a ha).toRingHom (Q P) =
          MvPolynomial.map ((coefficientGermHom d B a (hWB ha)).comp C.val).toRingHom (L P) := by
      change MvPolynomial.map (ρ a ha).toRingHom (MvPolynomial.map q.toRingHom (L P)) = _
      rw [MvPolynomial.map_map]
      change MvPolynomial.map ((ρ a ha).comp q).toRingHom (L P) = _
      exact congrArg (fun f : C →ₐ[ℂ] HolGerm (ComplexModel d) =>
        MvPolynomial.map f.toRingHom (L P)) (hρ a ha)
    rw [map_span_range (MvPolynomial.map (ρ a ha).toRingHom) Q]
    apply Eq.trans (congrArg
      (fun F : ↥(actualOriginalRelationFamily d t I) → MvPolynomial (Fin t) (HolGerm (ComplexModel d)) =>
        Ideal.span (range F)) (funext hmap))
    exact (map_span_range
      (MvPolynomial.map ((coefficientGermHom d B a (hWB ha)).comp C.val).toRingHom) L).symm.trans
      (hnearby a (hWB ha))

end
end Hironaka.HironakaRelativeNormalCoefficientFunctionAlgebra
