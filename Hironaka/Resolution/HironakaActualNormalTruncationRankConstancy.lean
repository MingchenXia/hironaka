import Hironaka.Resolution.HironakaRelativeNormalFibreHilbertSamuel
import Hironaka.Resolution.HironakaSmoothCentreRealDomainCoefficientAlgebra
import Hironaka.Resolution.HironakaActualNearbyTangentParameters
import Hironaka.Resolution.HironakaActualFixedFlatteningTangentClosure
import Hironaka.Resolution.HironakaActualRelativeStandardnessLocalBasis
/-! # Generic ranks from one fixed original nearby normal fibre family

The same coefficient-domain standard exponents are transported to the actual
generic original normal associated graded and to the nearby original fibres.
The actual original short exact filtration then gives equal all-order generic
and nearby truncation dimensions. Constant whole original fibre profiles turn
this into numerical generic/origin residue dimension equality.
-/

set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff DirectSum TensorProduct

namespace Hironaka.HironakaActualNormalTruncationRankConstancy
noncomputable section

open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf
  HironakaRelativeNormalIdeal HironakaRelativeNormalAssociatedGraded
  HironakaRelativeNormalLocalizedAssociatedGraded HironakaRelativeNormalUniformLocalization
  HironakaRelativeNormalNearbyUniformRanks HironakaRelativeNormalUniformTruncations
  HironakaRelativeNormalCoherentTranslatedJets HironakaRelativeNormalCoefficientFunctionAlgebra
  HironakaRelativeNormalFibreHilbertSamuel HironakaRelativeNormalCoefficientAlgebraNearbyFreeness
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreRealDomainCoefficientAlgebra
  HironakaActualNearbyTangentParameters HironakaActualFixedFlatteningTangentClosure
  HironakaActualHomogeneousInitialHS HironakaActualOriginalFormalTaylor
  HironakaSmoothCentreRealDomainActualAmbientHS
  HironakaActualRelativeStandardnessLocalBasis
  HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalDeformationInitialRelations
  HironakaActualCoefficientPresentationCentrePower

attribute [local instance] baseGermResidueAlgebra coefficientSubalgebraRing

private def polynomialQuotientAllLocalizationEquiv {B : Type*} [CommRing B]
    (S : Submonoid B) (t : ℕ) (H : Ideal (MvPolynomial (Fin t) B)) :
    LocalizedModule S (MvPolynomial (Fin t) B ⧸ H) ≃ₗ[Localization S]
      (MvPolynomial (Fin t) (Localization S) ⧸
        Ideal.map (MvPolynomial.map (algebraMap B (Localization S))) H) :=
  (LocalizedModule.equivTensorProduct S (MvPolynomial (Fin t) B ⧸ H)).trans
    (polynomialQuotientCoefficientAlgEquiv B (Localization S) t H).toLinearEquiv

private theorem polynomialQuotientAllLocalizationEquiv_mk_one {B : Type*} [CommRing B]
    (S : Submonoid B) (t : ℕ) (H : Ideal (MvPolynomial (Fin t) B))
    (P : MvPolynomial (Fin t) B) :
    polynomialQuotientAllLocalizationEquiv S t H
        (LocalizedModule.mk (Ideal.Quotient.mk H P) 1) =
      Ideal.Quotient.mk (Ideal.map (MvPolynomial.map (algebraMap B (Localization S))) H)
        (MvPolynomial.map (algebraMap B (Localization S)) P) := by
  simp only [polynomialQuotientAllLocalizationEquiv, LinearEquiv.trans_apply,
    LocalizedModule.equivTensorProduct_apply_mk, Localization.mk_one]
  exact polynomialQuotientCoefficientAlgEquiv_tmul_mk B (Localization S) t H P

section GenericCoefficientDomain

variable {D KD : Type*} [CommRing D] [IsDomain D] [Field KD]
  [Algebra D KD] [IsFractionRing D KD]

omit [IsDomain D] in
private theorem genericCoefficientImageIdeal (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (H : Ideal (MvPolynomial (Fin t) D)) (f : D →+* HolGerm (ComplexModel d))
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I) :
    Ideal.map (MvPolynomial.map (algebraMap (HolGerm (ComplexModel d))
        (FractionRing (HolGerm (ComplexModel d))))) (originalNormalInitialIdeal d t I) =
      Ideal.map (MvPolynomial.map
        ((algebraMap (HolGerm (ComplexModel d))
          (FractionRing (HolGerm (ComplexModel d)))).comp f)) H := by
  rw [← hH, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro P
  exact MvPolynomial.map_map _ _ P

/-- The genuine generic original associated graded quotient, with the entire coefficient-image ideal retained. -/
def genericOriginalAssociatedQuotientEquiv (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (H : Ideal (MvPolynomial (Fin t) D)) (f : D →+* HolGerm (ComplexModel d))
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I) :
    letI := tangentAlgebra d t
    (MvPolynomial (Fin t) (FractionRing (HolGerm (ComplexModel d))) ⧸
      Ideal.map (MvPolynomial.map
        ((algebraMap (HolGerm (ComplexModel d))
          (FractionRing (HolGerm (ComplexModel d)))).comp f)) H) ≃ₗ[FractionRing (HolGerm (ComplexModel d))]
        LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
          (originalNormalAssociatedGraded d t I) :=
  letI := tangentAlgebra d t
  ((Ideal.quotientEquivAlgOfEq (FractionRing (HolGerm (ComplexModel d)))
    (genericCoefficientImageIdeal d t I H f hH).symm).toLinearEquiv.trans
      (polynomialQuotientAllLocalizationEquiv (nonZeroDivisors (HolGerm (ComplexModel d)))
        t (originalNormalInitialIdeal d t I)).symm).trans
    (actualLocalizedLinearEquiv (nonZeroDivisors (HolGerm (ComplexModel d)))
      (originalNormalAssociatedGradedQuotientEquiv d t I))

set_option maxHeartbeats 800000 in
omit [IsDomain D] in
private theorem genericOriginalAssociatedQuotientEquiv_monomial (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (H : Ideal (MvPolynomial (Fin t) D)) (f : D →+* HolGerm (ComplexModel d))
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I)
    (α : Fin t →₀ ℕ) :
    letI := tangentAlgebra d t
    genericOriginalAssociatedQuotientEquiv d t I H f hH
      (Ideal.Quotient.mk (Ideal.map (MvPolynomial.map
        ((algebraMap (HolGerm (ComplexModel d))
          (FractionRing (HolGerm (ComplexModel d)))).comp f)) H)
        (MvPolynomial.monomial α 1)) =
      LocalizedModule.mk (normalAssociatedSymbolMap d t I (MvPolynomial.monomial α 1)) 1 := by
  let := tangentAlgebra d t
  let S := nonZeroDivisors (HolGerm (ComplexModel d))
  let P : MvPolynomial (Fin t) (HolGerm (ComplexModel d)) := MvPolynomial.monomial α 1
  have hn := polynomialQuotientAllLocalizationEquiv_mk_one S t
    (originalNormalInitialIdeal d t I) P
  simp only [P, MvPolynomial.map_monomial, map_one] at hn
  simp only [genericOriginalAssociatedQuotientEquiv, LinearEquiv.trans_apply,
    AlgEquiv.coe_toLinearEquiv, Ideal.quotientEquivAlgOfEq_mk]
  rw [← hn, LinearEquiv.symm_apply_apply, actualLocalizedLinearEquiv_mk_one,
    originalNormalAssociatedGradedQuotientEquiv_mk]

private theorem genericDenominator_isUnit (d t : ℕ) (m : MonomialOrder (Fin t))
    (H : Ideal (MvPolynomial (Fin t) D)) (f : D →+* HolGerm (ComplexModel d))
    (hf : Function.Injective f) :
    IsUnit (((algebraMap (HolGerm (ComplexModel d))
      (FractionRing (HolGerm (ComplexModel d)))).comp f)
        (uniformLeadingDenominator (K := KD) t m H)) := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  apply uniformLeadingDenominator_ne_zero (K := KD) t m H
  apply hf
  apply IsFractionRing.injective (HolGerm (ComplexModel d)) (FractionRing (HolGerm (ComplexModel d)))
  simpa only [RingHom.comp_apply, map_zero] using hz

/-- The fixed coefficient-domain monomials form an actual basis of the generic original associated graded. -/
def genericOriginalAssociatedMonomialBasis (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* HolGerm (ComplexModel d)) (hf : Function.Injective f)
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I) :
    letI := tangentAlgebra d t
    Module.Basis (uniformStandardExponentIndex (K := KD) t m H)
      (FractionRing (HolGerm (ComplexModel d)))
      (LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
        (originalNormalAssociatedGraded d t I)) :=
  letI := tangentAlgebra d t
  (coefficientImageStandardMonomialBasis (K := KD) t m H
    ((algebraMap (HolGerm (ComplexModel d))
      (FractionRing (HolGerm (ComplexModel d)))).comp f)
    (genericDenominator_isUnit (KD := KD) d t m H f hf)).map
      (genericOriginalAssociatedQuotientEquiv d t I H f hH)

set_option maxHeartbeats 800000 in
private theorem genericOriginalAssociatedMonomialBasis_apply (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* HolGerm (ComplexModel d)) (hf : Function.Injective f)
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I)
    (α : uniformStandardExponentIndex (K := KD) t m H) :
    letI := tangentAlgebra d t
    genericOriginalAssociatedMonomialBasis (KD := KD) d t I m H f hf hH α =
      LocalizedModule.mk (normalAssociatedSymbolMap d t I (MvPolynomial.monomial α.val 1)) 1 := by
  let := tangentAlgebra d t
  rw [genericOriginalAssociatedMonomialBasis, Module.Basis.map_apply,
    coefficientImageStandardMonomialBasis_apply, genericOriginalAssociatedQuotientEquiv_monomial]

private def genericOriginalDirectSumMonomialBasis (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* HolGerm (ComplexModel d)) (hf : Function.Injective f)
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I) :
    letI := tangentAlgebra d t
    Module.Basis (uniformStandardExponentIndex (K := KD) t m H)
      (FractionRing (HolGerm (ComplexModel d)))
      (⨁ q, LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
        (originalNormalGradedPiece d t I q : Type)) :=
  letI := tangentAlgebra d t
  (genericOriginalAssociatedMonomialBasis (KD := KD) d t I m H f hf hH).map
    (localizedDirectSumEquiv (nonZeroDivisors (HolGerm (ComplexModel d)))
      (fun q => (originalNormalGradedPiece d t I q : Type)))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2000 in
private theorem genericOriginalDirectSumMonomialBasis_supported (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* HolGerm (ComplexModel d)) (hf : Function.Injective f)
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I)
    (α : uniformStandardExponentIndex (K := KD) t m H) :
    letI := tangentAlgebra d t
    let v := genericOriginalDirectSumMonomialBasis (KD := KD) d t I m H f hf hH
    v α = DirectSum.lof (FractionRing (HolGerm (ComplexModel d))) ℕ
      (fun q => LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
        (originalNormalGradedPiece d t I q : Type)) α.val.degree (v α α.val.degree) := by
  let := tangentAlgebra d t
  dsimp only
  let v := genericOriginalDirectSumMonomialBasis (KD := KD) d t I m H f hf hH
  let g := localizedDirectSumEquiv (nonZeroDivisors (HolGerm (ComplexModel d)))
    (fun q => (originalNormalGradedPiece d t I q : Type))
  have h : v α = DirectSum.lof (FractionRing (HolGerm (ComplexModel d))) ℕ
      (fun q => LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
        (originalNormalGradedPiece d t I q : Type)) α.val.degree
          (LocalizedModule.mk (originalNormalMonomialSymbol d t I α.val) 1) := by
    calc
      v α = g (genericOriginalAssociatedMonomialBasis (KD := KD) d t I m H f hf hH α) :=
        Module.Basis.map_apply
          (genericOriginalAssociatedMonomialBasis (KD := KD) d t I m H f hf hH) g α
      _ = g (LocalizedModule.mk
          (normalAssociatedSymbolMap d t I (MvPolynomial.monomial α.val 1)) 1) :=
        congrArg g (genericOriginalAssociatedMonomialBasis_apply (KD := KD) d t I m H f hf hH α)
      _ = g (LocalizedModule.mk
          (DirectSum.lof (HolGerm (ComplexModel d)) ℕ
            (fun q => (originalNormalGradedPiece d t I q : Type)) α.val.degree
            (originalNormalMonomialSymbol d t I α.val)) 1) :=
        congrArg (fun z => g (LocalizedModule.mk z 1))
          (normalAssociatedSymbolMap_monomial d t I α.val)
      _ = _ := localizedDirectSumEquiv_mk_one_lof
        (nonZeroDivisors (HolGerm (ComplexModel d)))
        (fun q => (originalNormalGradedPiece d t I q : Type))
        α.val.degree (originalNormalMonomialSymbol d t I α.val)
  have hc := congrArg (fun z => z α.val.degree) h
  simp only [DirectSum.lof_eq_of, DirectSum.of_eq_same] at hc
  exact h.trans (congrArg (DirectSum.lof (FractionRing (HolGerm (ComplexModel d))) ℕ
    (fun q => LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
      (originalNormalGradedPiece d t I q : Type)) α.val.degree) hc.symm)

/-- Every generic original degree has the same literal finite standard exponent indexing set. -/
def genericOriginalDegreeMonomialBasis (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (m : MonomialOrder (Fin t)) (H : Ideal (MvPolynomial (Fin t) D))
    (f : D →+* HolGerm (ComplexModel d)) (hf : Function.Injective f)
    (hH : Ideal.map (MvPolynomial.map f) H = originalNormalInitialIdeal d t I) (q : ℕ) :
    letI := tangentAlgebra d t
    Module.Basis (uniformDegreeStandardExponentIndex (K := KD) t m H q)
      (FractionRing (HolGerm (ComplexModel d)))
      (LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
        (originalNormalGradedPiece d t I q : Type)) := by
  letI := tangentAlgebra d t
  let v := genericOriginalDirectSumMonomialBasis (KD := KD) d t I m H f hf hH
  exact Finsupp.basisSingleOne.map
    (homogeneousBasisDegreeLinearEquiv
      (fun α : uniformStandardExponentIndex (K := KD) t m H => α.val.degree)
      (fun q => LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
        (originalNormalGradedPiece d t I q : Type)) v.repr.symm
      (fun α => by simpa only [Module.Basis.repr_symm_single_one] using
        genericOriginalDirectSumMonomialBasis_supported (KD := KD) d t I m H f hf hH α) q)

end GenericCoefficientDomain

private theorem shortExact_finrank {K L M N : Type} [Field K]
    [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
    [Module K L] [Module K M] [Module K N]
    [Module.Finite K L] [Module.Finite K N]
    (g : L →ₗ[K] M) (h : M →ₗ[K] N) (hg : Function.Injective g)
    (hh : Function.Surjective h) (ex : Function.Exact g h) :
    Module.finrank K M = Module.finrank K L + Module.finrank K N := by
  let S := ModuleCat.shortComplexOfCompEqZero g h ex.linearMap_comp_eq_zero
  have hs := ModuleCat.shortComplex_shortExact S ex hg hh
  exact ModuleCat.free_shortExact_finrank_add hs rfl rfl

/-- Genuine localization of the entire original normal-power filtration determines every generic truncation rank. -/
theorem genericOriginalTruncation_finrank_of_graded (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (r : ℕ → ℕ) :
    letI := tangentAlgebra d t
    (∀ q, Module.Finite (FractionRing (HolGerm (ComplexModel d)))
      (LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
        (originalNormalGradedPiece d t I q : Type)) ∧
      Module.finrank (FractionRing (HolGerm (ComplexModel d)))
        (LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
          (originalNormalGradedPiece d t I q : Type)) = r q) →
    ∀ q, Module.finrank (FractionRing (HolGerm (ComplexModel d)))
      (LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
        (originalNormalTruncation d t I q)) = ∑ i ∈ Finset.range q, r i := by
  let := tangentAlgebra d t
  intro hdegree q
  let S := nonZeroDivisors (HolGerm (ComplexModel d))
  induction q with
  | zero =>
    let := originalNormalTruncation_zero_subsingleton d t I
    let : Subsingleton (LocalizedModule S (originalNormalTruncation d t I 0)) := inferInstance
    simp only [Finset.range_zero, Finset.sum_empty]
    exact Module.finrank_zero_of_subsingleton
  | succ q ih =>
    let := (hdegree q).1
    let := finite_quotient_sup_normalIdeal_pow d t q I
    let : Module.Finite (FractionRing (HolGerm (ComplexModel d)))
        (LocalizedModule S (originalNormalTruncation d t I q)) := inferInstance
    let g := originalNormalTruncationPieceInclusion d t I q
    let h := (originalNormalTruncationMap d t I q).toLinearMap
    have hr := shortExact_finrank (LocalizedModule.map S g) (LocalizedModule.map S h)
      (LocalizedModule.map_injective S g (originalNormalTruncationPieceInclusion_injective d t I q))
      (LocalizedModule.map_surjective S h (originalNormalTruncationMap_surjective d t I q))
      (LocalizedModule.map_exact S g h (originalNormalTruncation_exact d t I q))
    rw [hr, (hdegree q).2, ih, Finset.sum_range_succ]
    exact Nat.add_comm _ _

private theorem coefficientOriginMap_injective (d : ℕ) (B : Set (ComplexModel d))
    (h0 : (0 : ComplexModel d) ∈ B)
    (C : Subalgebra ℂ (coefficientFunctionAlgebra d B))
    (ρ : coefficientOriginAlgebra d B h0 C →ₐ[ℂ] HolGerm (ComplexModel d))
    (hρ : ρ.comp (Ideal.Quotient.mkₐ ℂ (coefficientOriginKernel d B h0 C)) =
      (coefficientGermHom d B 0 h0).comp C.val) : Function.Injective ρ := by
  intro u v huv
  obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective u
  obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
  apply Ideal.Quotient.eq.mpr
  change ((coefficientGermHom d B 0 h0).comp C.val) (u-v) = 0
  have hu := congrArg (fun f : C →ₐ[ℂ] HolGerm (ComplexModel d) => f u) hρ
  have hv := congrArg (fun f : C →ₐ[ℂ] HolGerm (ComplexModel d) => f v) hρ
  rw [map_sub, ← hu, ← hv]
  exact sub_eq_zero.mpr huv

/-- One actual coefficient-domain family supplies both generic origin dimensions and the identical nearby residue dimensions. -/
theorem exists_coefficient_family_generic_and_nearby_truncation_dimensions
    (d t : ℕ) (B : Set (ComplexModel d)) (h0 : (0 : ComplexModel d) ∈ B)
    (C : Subalgebra ℂ (coefficientFunctionAlgebra d B))
    [IsDomain (coefficientOriginAlgebra d B h0 C)]
    (W : Set (ComplexModel d)) (hW : IsOpen W) (h0W : (0 : ComplexModel d) ∈ W)
    (hWB : W ⊆ B)
    (ρ : ∀ a, a ∈ W → coefficientOriginAlgebra d B h0 C →ₐ[ℂ] HolGerm (ComplexModel d))
    (hρ : ∀ a (ha : a ∈ W),
      (ρ a ha).comp (Ideal.Quotient.mkₐ ℂ (coefficientOriginKernel d B h0 C)) =
        (coefficientGermHom d B a (hWB ha)).comp C.val)
    (H : Ideal (MvPolynomial (Fin t) (coefficientOriginAlgebra d B h0 C)))
    (I : ComplexModel d → Ideal (HolGerm (ComplexModel (d+t))))
    (hH : ∀ a (ha : a ∈ W),
      Ideal.map (MvPolynomial.map (ρ a ha).toRingHom) H = originalNormalInitialIdeal d t (I a)) :
    letI := tangentAlgebra d t
    ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧ U ⊆ W ∧
      (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
      (∀ q, Module.finrank (FractionRing (HolGerm (ComplexModel d)))
        (FractionRing (HolGerm (ComplexModel d)) ⊗[HolGerm (ComplexModel d)]
          originalNormalTruncation d t (I 0) q) = ∑ i ∈ Finset.range q, r i) ∧
      ∀ a ∈ U, ∀ q,
        Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t (I a) q) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t (I a) q) ∧
        Module.finrank ℂ (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t (I a) q) =
          ∑ i ∈ Finset.range q, r i := by
  classical
  let := tangentAlgebra d t
  let D := coefficientOriginAlgebra d B h0 C
  let b := uniformLeadingDenominator (K := FractionRing D) t
    (MonomialOrder.degLex (σ := Fin t)) H
  have hb : b ≠ 0 := uniformLeadingDenominator_ne_zero _ _ _
  have hρ0 : Function.Injective (ρ 0 h0W) :=
    coefficientOriginMap_injective d B h0 C (ρ 0 h0W) (hρ 0 h0W)
  obtain ⟨c, hcb⟩ := Ideal.Quotient.mk_surjective b
  let g : ComplexModel d → ℂ := (C.val c).val
  have hc0 : ((coefficientGermHom d B 0 h0).comp C.val) c ≠ 0 := by
    intro hz
    have hc : c ∈ coefficientOriginKernel d B h0 C := hz
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr hc
    rw [hcb] at he
    exact hb he
  have hg0 : (g : Germ (𝓝 (0 : ComplexModel d)) ℂ) ≠ 0 := by
    intro hz
    apply hc0
    apply Subtype.ext
    change (Germ.coeRingHom (𝓝 (0 : ComplexModel d))) (g ∘ actualAffineTranslation d 0) = 0
    have hid : g ∘ actualAffineTranslation d 0 = g := by
      funext z
      simp only [Function.comp_apply, actualAffineTranslation, zero_add]
    rw [hid]
    exact hz
  let U := {a : ComplexModel d | a ∈ W ∧ g a ≠ 0}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    have hcont : ContinuousAt g a := ((C.val c).property a (hWB ha.1)).self_of_nhds.continuousAt
    filter_upwards [hW.mem_nhds ha.1, hcont.eventually_ne ha.2] with z hz hgz
    exact ⟨hz, hgz⟩
  have hmeet : ∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty := by
    intro V hV
    by_contra hn
    apply hg0
    apply Germ.coe_eq.mpr
    filter_upwards [hV, hW.mem_nhds h0W] with a haV haW
    by_contra hga
    exact hn ⟨a, haV, haW, hga⟩
  let r : ℕ → ℕ := fun q => Nat.card
    (uniformDegreeStandardExponentIndex (K := FractionRing D) t
      (MonomialOrder.degLex (σ := Fin t)) H q)
  have hgeneric : ∀ q, Module.finrank (FractionRing (HolGerm (ComplexModel d)))
      (LocalizedModule (nonZeroDivisors (HolGerm (ComplexModel d)))
        (originalNormalTruncation d t (I 0) q)) = ∑ i ∈ Finset.range q, r i := by
    apply genericOriginalTruncation_finrank_of_graded d t (I 0) r
    intro q
    let := uniformDegreeStandardExponentFintype (K := FractionRing D) t
      (MonomialOrder.degLex (σ := Fin t)) H q
    let v := genericOriginalDegreeMonomialBasis (KD := FractionRing D) d t (I 0)
      (MonomialOrder.degLex (σ := Fin t)) H (ρ 0 h0W).toRingHom hρ0 (hH 0 h0W) q
    exact ⟨Module.Finite.of_basis v, Module.finrank_eq_nat_card_basis v⟩
  refine ⟨U, r, hU, fun _ ha => ha.1, hmeet, ?_, ?_⟩
  · intro q
    exact ((LocalizedModule.equivTensorProduct (nonZeroDivisors (HolGerm (ComplexModel d)))
      (originalNormalTruncation d t (I 0) q)).finrank_eq).symm.trans (hgeneric q)
  · intro a ha q
    have hvalue : (ρ a ha.1) b = coefficientGermHom d B a (hWB ha.1) (C.val c) := by
      rw [← hcb]
      exact congrArg (fun f : C →ₐ[ℂ] HolGerm (ComplexModel d) => f c) (hρ a ha.1)
    have hunit : IsUnit ((ρ a ha.1) b) := by
      apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
      rw [hvalue]
      change g (actualAffineTranslation d a 0) ≠ 0
      simpa only [actualAffineTranslation_zero] using ha.2
    have hdegree : ∀ k, Module.Free (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t (I a) k) ∧
        Module.Finite (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t (I a) k) ∧
        Module.finrank (HolGerm (ComplexModel d)) (originalNormalGradedPiece d t (I a) k) = r k := by
      intro k
      let := uniformDegreeStandardExponentFintype (K := FractionRing D) t
        (MonomialOrder.degLex (σ := Fin t)) H k
      let v := originalDegreeCoefficientImageMonomialBasis (K := FractionRing D) d t (I a)
        (MonomialOrder.degLex (σ := Fin t)) H (ρ a ha.1).toRingHom hunit (hH a ha.1) k
      exact ⟨Module.Free.of_basis v, Module.Finite.of_basis v, Module.finrank_eq_nat_card_basis v⟩
    have hff := all_originalNormalTruncation_finite_free_of_graded_free d t (I a)
      (fun k => ⟨(hdegree k).1, (hdegree k).2.1⟩) q
    refine ⟨hff.1, hff.2, ?_⟩
    exact (originalNormalFibreTruncation_finrank d t (I a) q hff.1).trans
      (all_originalNormalTruncation_finrank_of_graded d t (I a) r hdegree q)

/-- The actual whole fibre quotient supplies the complex dimension, including original degree zero. -/
theorem originalResidueTruncation_finrank_succ (d t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (q : ℕ) :
    letI := tangentAlgebra d t
    Module.finrank ℂ (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I (q+1)) =
      hilbertSamuelValue (I ⊔ originalBaseMaximalIdeal d t) q := by
  let := tangentAlgebra d t
  calc
    _ = Module.finrank ℂ (originalFibrePowerQuotient d t I (q+1)) :=
      (originalNormalFibreTruncationAlgEquiv d t I (q+1)).toLinearEquiv.finrank_eq
    _ = _ := by
      unfold hilbertSamuelValue
      rw [fibreMaximalIdeal_power_eq]

/-- Whole original fibre-profile equality gives every literal residue truncation dimension, including the zero truncation. -/
theorem originalResidueTruncation_finrank_eq_of_hilbertSamuel_eq (d t : ℕ)
    (I J : Ideal (HolGerm (ComplexModel (d+t))))
    (h : ∀ q, hilbertSamuelValue (I ⊔ originalBaseMaximalIdeal d t) q =
      hilbertSamuelValue (J ⊔ originalBaseMaximalIdeal d t) q) (q : ℕ) :
    letI := tangentAlgebra d t
    Module.finrank ℂ (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I q) =
      Module.finrank ℂ (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t J q) := by
  let := tangentAlgebra d t
  cases q with
  | zero =>
    let := originalNormalTruncation_zero_subsingleton d t I
    let := originalNormalTruncation_zero_subsingleton d t J
    exact (Module.finrank_zero_of_subsingleton (R := ℂ)).trans
      (Module.finrank_zero_of_subsingleton (R := ℂ)).symm
  | succ q =>
    rw [originalResidueTruncation_finrank_succ, originalResidueTruncation_finrank_succ, h q]

section OriginalCentre

variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- Original real-domain geometry supplies SAME-flattening generic and nearby dimensions without global flattened coherence. -/
theorem exists_original_generic_and_nearby_truncation_dimensions
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent) :
    letI := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0 ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈
          complexCoordinatePlane (d+t) d)) ∧
      ∃ U : Set (ComplexModel d), ∃ r : ℕ → ℕ, IsOpen U ∧
        (∀ a ∈ U, tangentInclusion d t a ∈ Φ.target) ∧
        (∀ V ∈ 𝓝 (0 : ComplexModel d), (V ∩ U).Nonempty) ∧
        let F := actualFlattenedOriginalSheaf A x Φ
        let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F 0)
        (∀ q, Module.finrank (FractionRing (HolGerm (ComplexModel d)))
          (FractionRing (HolGerm (ComplexModel d)) ⊗[HolGerm (ComplexModel d)]
            originalNormalTruncation d t I0 q) = ∑ i ∈ Finset.range q, r i) ∧
        ∀ a ∈ U, ∀ q,
          let Ia := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a))
          Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t Ia q) ∧
          Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t Ia q) ∧
          Module.finrank ℂ (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t Ia q) =
            ∑ i ∈ Finset.range q, r i := by
  let := tangentAlgebra d t
  obtain ⟨Φ, hsrc, h0, hflat, B, _hB, h0B, hpoint, C0, _hC0, hD, _hDf,
      W, hW, h0W, hWB, ρ, Q, _hhom, hρ, hideal⟩ :=
    exists_original_regular_real_common_domain_initial_family C x hreg A hA
  let := hD
  let F := actualFlattenedOriginalSheaf A x Φ
  let I : ComplexModel d → Ideal (HolGerm (ComplexModel (d+t))) := fun a =>
    originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F (tangentInclusion d t a))
  obtain ⟨U, r, hU, hUW, hmeet, hgeneric, hnearby⟩ :=
    exists_coefficient_family_generic_and_nearby_truncation_dimensions d t B h0B C0
      W hW h0W hWB ρ hρ (Ideal.span (range Q)) I hideal
  refine ⟨Φ, hsrc, h0, hflat, U, r, hU, ?_, hmeet, ?_, hnearby⟩
  · intro a ha
    exact (hpoint a (hWB (hUW ha))).1
  · intro q
    have hz : tangentInclusion d t (0 : ComplexModel d) = 0 := map_zero _
    have htransport := congrArg (fun z : ComplexModel (d+t) =>
      Module.finrank (FractionRing (HolGerm (ComplexModel d)))
        (FractionRing (HolGerm (ComplexModel d)) ⊗[HolGerm (ComplexModel d)]
          originalNormalTruncation d t
            (originalCoherentOriginIdeal (actualTranslatedOriginalSheaf F z)) q)) hz
    exact htransport.symm.trans (hgeneric q)

/-- In a prescribed original flattening, whole initial stability and whole fibre profiles retain one domain. -/
theorem fixed_flattening_original_nearby_fibre_profiles
    (C : Set M) (x : M) (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ q, hilbertSamuelAt A y q = hilbertSamuelAt A x q)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x))
    (hsrc : Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target)
    (h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0)
    (hflat : ∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
      chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
      (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) :
    ∃ U : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧ U ⊆ Φ.target ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      ∀ c : ComplexModel d, tangentInclusion d t c ∈ U →
        let Ic := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t c))
        let Kc := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom Ic
        (∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
          F ∈ actualHomogeneousInitialIdeal Kc →
          MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal Kc) ∧
        (∀ q, hilbertSamuelValue (Ic ⊔ originalBaseMaximalIdeal d t) q =
          hilbertSamuelValue (I0 ⊔ originalBaseMaximalIdeal d t) q) := by
  obtain ⟨U, hU, h0U, hUT, hInitial⟩ :=
    fixed_flattening_original_hs_constant_centre_initial_tangent_pderiv C x A hA hhs Φ hsrc h0 hflat
  refine ⟨U, hU, h0U, hUT, ?_⟩
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) 0)
  dsimp only
  intro c hc
  let Ic := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t c))
  have hc0 : tangentInclusion d t (0 : ComplexModel d) ∈ U := by
    simpa only [map_zero] using h0U
  have hDc (j : Fin (d+t)) (hj : j.val < d) :
      ∀ F ∈ actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom Ic),
        MvPowerSeries.pderiv ℂ j F ∈
          actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom Ic) := by
    let k : Fin d := ⟨j.val, hj⟩
    have he : k.castAdd t = j := Fin.ext rfl
    intro F hF
    simpa only [he] using hInitial c hc k F hF
  have hD0 (j : Fin (d+t)) (hj : j.val < d) :
      ∀ F ∈ actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0),
        MvPowerSeries.pderiv ℂ j F ∈
          actualHomogeneousInitialIdeal (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0) := by
    let k : Fin d := ⟨j.val, hj⟩
    have he : k.castAdd t = j := Fin.ext rfl
    intro F hF
    have hInit0 := hInitial (0 : ComplexModel d) hc0 k
    simp only [map_zero] at hInit0
    simpa only [he] using hInit0 F hF
  have hvalue : ∀ q, hilbertSamuelValue Ic q = hilbertSamuelValue I0 q := by
    intro q
    have hPlane0 : (0 : ComplexModel (d+t)) ∈ complexCoordinatePlane (d+t) d := by
      simpa only [map_zero] using tangentInclusion_mem_plane d t (0 : ComplexModel d)
    exact (hilbertSamuelValue_original_translated_plane_eq C x A hA hhs Φ hsrc hflat
      (tangentInclusion d t c) (hUT hc) (tangentInclusion_mem_plane d t c) q).trans
        (hilbertSamuelValue_original_translated_plane_eq C x A hA hhs Φ hsrc hflat
          0 (hUT h0U) hPlane0 q).symm
  refine ⟨hInitial c hc, ?_⟩
  intro q
  have hEq := hilbertSamuelValue_coordinate_cuts_eq_of_eq (d+t) Ic I0
    (Finset.univ.filter (fun j : Fin (d+t) => j.val < d))
    (fun j hj => hDc j (Finset.mem_filter.mp hj).2)
    (fun j hj => hD0 j (Finset.mem_filter.mp hj).2) hvalue q
  simpa only [originalCoordinateCutIdeal_all_tangent] using hEq

/-- Original ambient HS constancy produces actual numerical generic/origin residue equality on the SAME flattening as all nearby initial and fibre profiles. -/
theorem exists_original_hs_constant_centre_normal_truncation_rank_eq
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ q, hilbertSamuelAt A y q = hilbertSamuelAt A x q) :
    letI := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0 ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ U : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧ U ⊆ Φ.target ∧
        let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf A x Φ) 0)
        (∀ c : ComplexModel d, tangentInclusion d t c ∈ U →
          let Ic := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t c))
          let Kc := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom Ic
          (∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
            F ∈ actualHomogeneousInitialIdeal Kc →
            MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal Kc) ∧
          (∀ q, hilbertSamuelValue (Ic ⊔ originalBaseMaximalIdeal d t) q =
            hilbertSamuelValue (I0 ⊔ originalBaseMaximalIdeal d t) q)) ∧
        ∀ q, Module.finrank (FractionRing (HolGerm (ComplexModel d)))
          (FractionRing (HolGerm (ComplexModel d)) ⊗[HolGerm (ComplexModel d)]
            originalNormalTruncation d t I0 q) =
          Module.finrank ℂ (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I0 q) := by
  let := tangentAlgebra d t
  obtain ⟨Φ, hsrc, h0, hflat, W, r, _hW, _hWT, hmeet, hgeneric, hnearby⟩ :=
    exists_original_generic_and_nearby_truncation_dimensions C x hreg A hA
  obtain ⟨U, hU, h0U, hUT, hProfiles⟩ :=
    fixed_flattening_original_nearby_fibre_profiles C x A hA hhs Φ hsrc h0 hflat
  refine ⟨Φ, hsrc, h0, hflat, U, hU, h0U, hUT, hProfiles, ?_⟩
  have hBase : (tangentInclusion d t) ⁻¹' U ∈ 𝓝 (0 : ComplexModel d) :=
    (hU.preimage (tangentInclusion d t).continuous).mem_nhds (by
      change tangentInclusion d t (0 : ComplexModel d) ∈ U
      rw [map_zero]
      exact h0U)
  obtain ⟨a, haU, haW⟩ := hmeet _ hBase
  intro q
  exact (hgeneric q).trans (((hnearby a haW q).2.2).symm.trans
    (originalResidueTruncation_finrank_eq_of_hilbertSamuel_eq d t _ _ (hProfiles a haU).2 q))

/-- Only original regularity, coherence and ambient profile constancy produce all actual original normal truncations finite free, on the SAME chosen flattening and initial-stability domain. -/
theorem exists_original_hs_constant_centre_normal_truncations_free
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y ∈ C, ∀ q, hilbertSamuelAt A y q = hilbertSamuelAt A x q) :
    letI := tangentAlgebra d t
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      Φ.source ⊆ (chartAt (ComplexModel (d+t)) x).target ∧
      Φ.toFun (chartAt (ComplexModel (d+t)) x x) = 0 ∧
      (∀ {y : M}, y ∈ (chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y ∈ Φ.source →
        (y ∈ C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y) ∈ complexCoordinatePlane (d+t) d)) ∧
      ∃ U : Set (ComplexModel (d+t)), IsOpen U ∧ 0 ∈ U ∧ U ⊆ Φ.target ∧
        let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf A x Φ) 0)
        (∀ c : ComplexModel d, tangentInclusion d t c ∈ U →
          let Ic := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
            (actualFlattenedOriginalSheaf A x Φ) (tangentInclusion d t c))
          let Kc := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom Ic
          (∀ (i : Fin d) (F : MvPowerSeries (Fin (d+t)) ℂ),
            F ∈ actualHomogeneousInitialIdeal Kc →
            MvPowerSeries.pderiv ℂ (i.castAdd t) F ∈ actualHomogeneousInitialIdeal Kc) ∧
          (∀ q, hilbertSamuelValue (Ic ⊔ originalBaseMaximalIdeal d t) q =
            hilbertSamuelValue (I0 ⊔ originalBaseMaximalIdeal d t) q)) ∧
        (∀ q, Module.finrank (FractionRing (HolGerm (ComplexModel d)))
          (FractionRing (HolGerm (ComplexModel d)) ⊗[HolGerm (ComplexModel d)]
            originalNormalTruncation d t I0 q) =
          Module.finrank ℂ (ℂ ⊗[HolGerm (ComplexModel d)] originalNormalTruncation d t I0 q)) ∧
        ∀ q, Module.Free (HolGerm (ComplexModel d)) (originalNormalTruncation d t I0 q) ∧
          Module.Finite (HolGerm (ComplexModel d)) (originalNormalTruncation d t I0 q) := by
  let := tangentAlgebra d t
  obtain ⟨Φ, hsrc, h0, hflat, U, hU, h0U, hUT, hProfiles, hRank⟩ :=
    exists_original_hs_constant_centre_normal_truncation_rank_eq C x hreg A hA hhs
  refine ⟨Φ, hsrc, h0, hflat, U, hU, h0U, hUT, hProfiles, hRank, ?_⟩
  intro q
  let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
    (actualFlattenedOriginalSheaf A x Φ) 0)
  let := finite_quotient_sup_normalIdeal_pow d t q I0
  refine ⟨?_, inferInstance⟩
  apply free_of_generic_rank_eq_field_fibre_dimension
    (B := HolGerm (ComplexModel d)) (L := FractionRing (HolGerm (ComplexModel d)))
    (k := ℂ) (IsFractionRing.injective _ _) ?_ (hRank q)
  intro g hg
  change HolGerm.eval g = 0
  exact (HolGerm.mem_maximalIdeal_iff g).mp hg

end OriginalCentre

end
end Hironaka.HironakaActualNormalTruncationRankConstancy
