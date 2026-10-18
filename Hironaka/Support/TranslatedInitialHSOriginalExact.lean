/- Complete original prerequisites; statements and mathematical proofs are unchanged. -/

import Hironaka.Resolution.HironakaActualFiniteInitialGeneration
import Hironaka.Resolution.HironakaActualCoordinateSpecializationHS
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Actual translated homogeneous initial polynomial ideals and their genuine holomorphic ray family. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualTranslatedInitialHS
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalTaylorPolynomial HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision
  HironakaActualHomogeneousInitialHS HironakaActualFiniteInitialGeneration
  HironakaActualHolomorphicFibreHS HironakaSmoothCentreRealDomainActualAmbientHS
variable {n : ℕ}

/-- True entire polynomial inclusion internally supplies genuine polynomial homogeneity. -/
theorem actualInitialVertexPolynomial_isHomogeneous (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex I) :
    (actualInitialVertexPolynomial I a).IsHomogeneous (normalExponentDegree a.val) := by
  intro b hb
  have hc : MvPowerSeries.coeff b
      (actualHomogeneousInitialForm (actualVertexSeries MonomialOrder.degLex I a)
        (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose) ≠ 0 := by
    rw [← actualInitialVertexPolynomial_coe,MvPolynomial.coeff_coe]
    exact hb
  have hh : (actualHomogeneousInitialForm (actualVertexSeries MonomialOrder.degLex I a)
      (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose).IsHomogeneous (normalExponentDegree a.val) := by
    rw [actualHomogeneousInitialForm,actualHomogeneousInitialDegree,
      (actualVertexSeries_spec MonomialOrder.degLex I a).2.choose_spec.1]
    intro c hcc
    exact MvPowerSeries.isHomogeneous_homogeneousComponent _ _ hcc
  exact hh hc

-- Same finite-monomial argument as BingWangEntropy.homogeneousPolynomial_eval₂_scaled;
-- projects have separate Lean libraries, so retain the needed complex-algebra form here.
private theorem homogeneous_aeval_scaled {S : Type*} [CommSemiring S] [Algebra ℂ S]
    (P : MvPolynomial (Fin n) ℂ) (d : ℕ) (hP : P.IsHomogeneous d) (x : Fin n → S) (c : S) :
    MvPolynomial.aeval (fun i => c*x i) P=c^d*MvPolynomial.aeval x P := by
  rw [← P.support_sum_monomial_coeff,map_sum,map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [MvPolynomial.aeval_monomial,Finsupp.prod,mul_pow,
    Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  rw [← hP.degree_eq_sum_deg_support he]
  ac_rfl

private theorem polynomial_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P : MvPolynomial (Fin n) ℂ) (x : Fin n → E → ℂ) (hx : ∀ i, ContDiff ℂ ∞ (x i)) :
    ContDiff ℂ ∞ (fun z => MvPolynomial.eval (fun i => x i z) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using (contDiff_const : ContDiff ℂ ∞ (fun _ : E => c))
  | add P Q hP hQ => simpa only [MvPolynomial.eval_add] using hP.add hQ
  | mul_X P i hP => simpa only [MvPolynomial.eval_mul,MvPolynomial.eval_X] using hP.mul (hx i)

/-- Literal translation is polynomial evaluation at the SAME actual original coordinate germs. -/
def actualTranslatedPolynomialEval (n : ℕ) (p : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] HolGerm (ComplexModel (0+n)) :=
  MvPolynomial.aeval (fun i => normalCoordinate 0 n i+algebraMap ℂ _ (p i))

private theorem translated_polynomial_holomorphic (p : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ) :
    ∀ᶠ z in 𝓝 (0 : ComplexModel (0+n)),
      DifferentiableAt ℂ (fun w : ComplexModel (0+n) => MvPolynomial.eval (fun i => w (i.natAdd 0)+p i) P) z := by
  have h := polynomial_contDiff P (fun i (z : ComplexModel (0+n)) => z (i.natAdd 0)+p i)
    (fun i => (EuclideanSpace.proj (i.natAdd 0) : ComplexModel (0+n) →L[ℂ] ℂ).contDiff.add contDiff_const)
  exact Eventually.of_forall fun _ => (h.differentiable (by simp)).differentiableAt

private theorem translated_polynomial_mk (p : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ) :
    actualTranslatedPolynomialEval n p P=
      HolGerm.mk (fun z : ComplexModel (0+n) => MvPolynomial.eval (fun i => z (i.natAdd 0)+p i) P)
        (translated_polynomial_holomorphic p P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp only [actualTranslatedPolynomialEval,MvPolynomial.aeval_C,MvPolynomial.eval_C]
      rfl
  | add P Q hP hQ =>
      rw [map_add,hP,hQ]
      rw [← HolGerm.mk_add]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => MvPolynomial.eval_add.symm
  | mul_X P i hP =>
      rw [map_mul,hP,actualTranslatedPolynomialEval,MvPolynomial.aeval_X]
      let hx : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+n)),
          DifferentiableAt ℂ (fun w : ComplexModel (0+n) => w (i.natAdd 0)) z :=
        Eventually.of_forall fun _ => (EuclideanSpace.proj (i.natAdd 0) : ComplexModel (0+n) →L[ℂ] ℂ).differentiableAt
      change HolGerm.mk (fun z : ComplexModel (0+n) => MvPolynomial.eval (fun j => z (j.natAdd 0)+p j) P)
        (translated_polynomial_holomorphic p P)*
          (HolGerm.mk (fun z : ComplexModel (0+n) => z (i.natAdd 0)) hx+
            HolGerm.mk (fun _ : ComplexModel (0+n) => p i) (eventually_differentiableAt_const (p i)))=_
      rw [← HolGerm.mk_add,← HolGerm.mk_mul]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => by simp [MvPolynomial.eval_mul,MvPolynomial.eval_X]

/-- The actual ORIGINAL translated homogeneous initial ideal, without an analytic-model premise. -/
def actualTranslatedInitialIdeal (I : Ideal (MvPowerSeries (Fin n) ℂ)) (p : Fin n → ℂ) :
    Ideal (HolGerm (ComplexModel (0+n))) :=
  Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex I =>
    actualTranslatedPolynomialEval n p (actualInitialVertexPolynomial I a))

/-- Only genuine finite polynomials are translated in the actual formal ring. -/
def actualTranslatedInitialFormalIdeal (I : Ideal (MvPowerSeries (Fin n) ℂ)) (p : Fin n → ℂ) :
    Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.span (range fun a : actualInitialVertices MonomialOrder.degLex I =>
    MvPolynomial.aeval (fun i => MvPowerSeries.X i+algebraMap ℂ _ (p i)) (actualInitialVertexPolynomial I a))

/-- Genuine Taylor coordinates and true polynomial extensionality supply BOTH whole translated ideal directions. -/
theorem actualTranslatedInitialIdeal_formal_extension (I : Ideal (MvPowerSeries (Fin n) ℂ)) (p : Fin n → ℂ) :
    Ideal.map (originalTaylorAlgHom n).toRingHom (actualTranslatedInitialIdeal I p)=
      actualTranslatedInitialFormalIdeal I p := by
  have hm : (originalTaylorAlgHom n).comp (actualTranslatedPolynomialEval n p)=
      MvPolynomial.aeval (fun i => MvPowerSeries.X i+algebraMap ℂ _ (p i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    change originalTaylorAlgHom n (actualTranslatedPolynomialEval n p (MvPolynomial.X i))=_
    simp only [actualTranslatedPolynomialEval,MvPolynomial.aeval_X,map_add,
      originalTaylorAlgHom_coordinate,AlgHom.commutes]
  rw [actualTranslatedInitialIdeal,Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact DFunLike.congr_fun hm (actualInitialVertexPolynomial I a)

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
private theorem translated_initial_zero (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    actualTranslatedInitialIdeal I 0=actualOriginalInitialVertexIdeal I := by
  have he : actualTranslatedPolynomialEval n (0 : Fin n → ℂ)=originalPolynomialEval n := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [actualTranslatedPolynomialEval,originalPolynomialEval]
  unfold actualTranslatedInitialIdeal actualOriginalInitialVertexIdeal
  rw [he]

private def scalarLinearEquiv (k : ℕ) (c : ℂ) (hc : c ≠ 0) : ComplexModel k ≃L[ℂ] ComplexModel k where
  toFun z := c • z
  invFun z := c⁻¹ • z
  map_add' z w := smul_add _ _ _
  map_smul' r z := by simp only [RingHom.id_apply,smul_smul]; rw [mul_comm]
  left_inv z := by simp [smul_smul,hc]
  right_inv z := by simp [smul_smul,hc]
  continuous_toFun := (continuous_const : Continuous (fun _ : ComplexModel k => c)).smul
    (continuous_id : Continuous (fun z : ComplexModel k => z))
  continuous_invFun := (continuous_const : Continuous (fun _ : ComplexModel k => (c⁻¹ : ℂ))).smul
    (continuous_id : Continuous (fun z : ComplexModel k => z))

/-- The ACTUAL continuous scalar isomorphism induces a genuine original COMPLEX germ algebra equivalence. -/
def actualScalarGermAlgEquiv (n : ℕ) (c : ℂ) (hc : c ≠ 0) :
    HolGerm (ComplexModel (0+n)) ≃ₐ[ℂ] HolGerm (ComplexModel (0+n)) where
  toRingEquiv := HolGerm.comapEquiv (scalarLinearEquiv (0+n) c hc)
  commutes' _ := rfl

private theorem scalarGerm_coordinate (c : ℂ) (hc : c ≠ 0) (i : Fin n) :
    actualScalarGermAlgEquiv n c hc (normalCoordinate 0 n i)=
      algebraMap ℂ _ c*normalCoordinate 0 n i := by
  let hx : ∀ᶠ z in 𝓝 (0 : ComplexModel (0+n)),
      DifferentiableAt ℂ (fun w : ComplexModel (0+n) => w (i.natAdd 0)) z :=
    Eventually.of_forall fun _ => (EuclideanSpace.proj (i.natAdd 0) : ComplexModel (0+n) →L[ℂ] ℂ).differentiableAt
  change HolGerm.comapEquiv (scalarLinearEquiv (0+n) c hc)
    (HolGerm.mk (fun z : ComplexModel (0+n) => z (i.natAdd 0)) hx)=
      HolGerm.mk (fun _ : ComplexModel (0+n) => c) (eventually_differentiableAt_const c)*
        HolGerm.mk (fun z : ComplexModel (0+n) => z (i.natAdd 0)) hx
  rw [HolGerm.comapEquiv_mk,← HolGerm.mk_mul]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by simp [scalarLinearEquiv]

private theorem scalarGerm_translated_initial (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (p : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0) (a : actualInitialVertices MonomialOrder.degLex I) :
    actualScalarGermAlgEquiv n c hc (actualTranslatedPolynomialEval n (c • p) (actualInitialVertexPolynomial I a))=
      algebraMap ℂ _ (c^normalExponentDegree a.val)*actualTranslatedPolynomialEval n p (actualInitialVertexPolynomial I a) := by
  have he : (actualScalarGermAlgEquiv n c hc).toAlgHom.comp (actualTranslatedPolynomialEval n (c • p))=
      MvPolynomial.aeval (fun i => algebraMap ℂ (HolGerm (ComplexModel (0+n))) c*
        (normalCoordinate 0 n i+algebraMap ℂ _ (p i))) := by
    apply MvPolynomial.algHom_ext
    intro i
    change actualScalarGermAlgEquiv n c hc (actualTranslatedPolynomialEval n (c • p) (MvPolynomial.X i))=_
    simp only [actualTranslatedPolynomialEval,MvPolynomial.aeval_X,map_add,
      scalarGerm_coordinate,AlgEquiv.commutes,Pi.smul_apply,smul_eq_mul,map_mul]
    ring
  have h := DFunLike.congr_fun he (actualInitialVertexPolynomial I a)
  change actualScalarGermAlgEquiv n c hc
    (actualTranslatedPolynomialEval n (c • p) (actualInitialVertexPolynomial I a))=_ at h
  rw [h,homogeneous_aeval_scaled _ _ (actualInitialVertexPolynomial_isHomogeneous I a)]
  rw [← map_pow]
  rfl


private theorem map_scalar_translated_initial (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (p : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0) :
    Ideal.map (actualScalarGermAlgEquiv n c hc).toRingEquiv.toRingHom
      (actualTranslatedInitialIdeal I (c • p))=actualTranslatedInitialIdeal I p := by
  rw [actualTranslatedInitialIdeal,Ideal.map_span,← Set.range_comp]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro g ⟨a,rfl⟩
    change actualScalarGermAlgEquiv n c hc
      (actualTranslatedPolynomialEval n (c • p) (actualInitialVertexPolynomial I a)) ∈ actualTranslatedInitialIdeal I p
    rw [scalarGerm_translated_initial]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨a,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro g ⟨a,rfl⟩
    have hg : actualScalarGermAlgEquiv n c hc
        (actualTranslatedPolynomialEval n (c • p) (actualInitialVertexPolynomial I a)) ∈
          Ideal.span (range fun b : actualInitialVertices MonomialOrder.degLex I =>
            actualScalarGermAlgEquiv n c hc
              (actualTranslatedPolynomialEval n (c • p) (actualInitialVertexPolynomial I b))) :=
      Ideal.subset_span ⟨a,rfl⟩
    rw [scalarGerm_translated_initial] at hg
    have hh := Ideal.mul_mem_left _ (algebraMap ℂ (HolGerm (ComplexModel (0+n))) ((c^normalExponentDegree a.val)⁻¹)) hg
    rw [← mul_assoc,← map_mul,inv_mul_cancel₀ (pow_ne_zero _ hc),map_one,one_mul] at hh
    exact hh

/-- Every true nonzero ray parameter preserves the SAME actual original translated ideal HS values. -/
theorem actualTranslatedInitialIdeal_nonzero_ray_hs (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (p : Fin n → ℂ) (c : ℂ) (hc : c ≠ 0) (ℓ : ℕ) :
    hilbertSamuelValue (actualTranslatedInitialIdeal I (c • p)) ℓ=
      hilbertSamuelValue (actualTranslatedInitialIdeal I p) ℓ := by
  have h := actualAmbientHS_eq_of_genuineAlgEquiv (actualScalarGermAlgEquiv n c hc)
    (actualTranslatedInitialIdeal I (c • p)) ℓ
  rw [map_scalar_translated_initial I p c hc] at h
  exact h.symm

private def vertexEnumeration (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Fin (Fintype.card (actualInitialVertices MonomialOrder.degLex I)) ≃
      actualInitialVertices MonomialOrder.degLex I :=
  (Fintype.equivFin _).symm

/-- The genuine jointly polynomial family is internally constructed from the actual finite original vertex family. -/
def actualRayInitialFamily (I : Ideal (MvPowerSeries (Fin n) ℂ)) (p : Fin n → ℂ)
    (i : Fin (Fintype.card (actualInitialVertices MonomialOrder.degLex I)))
    (u : ComplexModel 1 × ComplexModel (0+n)) : ℂ :=
  MvPolynomial.eval (fun j => u.2 (j.natAdd 0)+u.1 0*p j)
    (actualInitialVertexPolynomial I (vertexEnumeration I i))

/-- Literal polynomial coordinates prove genuine joint holomorphicity on the entire actual product domain. -/
theorem actualRayInitialFamily_holomorphic (I : Ideal (MvPowerSeries (Fin n) ℂ)) (p : Fin n → ℂ)
    (i : Fin (Fintype.card (actualInitialVertices MonomialOrder.degLex I))) :
    DifferentiableOn ℂ (actualRayInitialFamily I p i) Set.univ := by
  have ht : ContDiff ℂ ∞ (fun u : ComplexModel 1 × ComplexModel (0+n) => u.1 0) :=
    (EuclideanSpace.proj (0 : Fin 1) : ComplexModel 1 →L[ℂ] ℂ).contDiff.comp contDiff_fst
  have hx (j : Fin n) : ContDiff ℂ ∞ (fun u : ComplexModel 1 × ComplexModel (0+n) =>
      u.2 (j.natAdd 0)+u.1 0*p j) :=
    ((EuclideanSpace.proj (j.natAdd 0) : ComplexModel (0+n) →L[ℂ] ℂ).contDiff.comp contDiff_snd).add
      (ht.mul contDiff_const)
  exact ((polynomial_contDiff (actualInitialVertexPolynomial I (vertexEnumeration I i)) _ hx).differentiable
    (by simp)).differentiableOn

/-- BOTH whole actual original fibre-ideal directions retain the SAME literal translated generators. -/
theorem actualRayInitialFibreIdeal_eq (I : Ideal (MvPowerSeries (Fin n) ℂ)) (p : Fin n → ℂ)
    (t : ComplexModel 1) :
    actualFibreIdeal isOpen_univ (actualRayInitialFamily I p) (actualRayInitialFamily_holomorphic I p)
      t (mem_univ _)=actualTranslatedInitialIdeal I ((t 0) • p) := by
  rw [actualFibreIdeal_eq_original_span,actualTranslatedInitialIdeal]
  apply congrArg Ideal.span
  apply Set.Subset.antisymm
  · rintro g ⟨i,rfl⟩
    refine ⟨vertexEnumeration I i,?_⟩
    dsimp only
    rw [translated_polynomial_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by
      simp only [actualRayInitialFamily,Pi.smul_apply,smul_eq_mul]
  · rintro g ⟨a,rfl⟩
    refine ⟨(vertexEnumeration I).symm a,?_⟩
    dsimp only
    rw [translated_polynomial_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun z => by
      simp only [actualRayInitialFamily,Equiv.apply_symm_apply,Pi.smul_apply,smul_eq_mul]

private def complexParameterPoint (c : ℂ) : ComplexModel 1 :=
  c • (EuclideanSpace.basisFun (Fin 1) ℂ) 0

private theorem complexParameterPoint_coordinate (c : ℂ) : complexParameterPoint c 0=c := by
  simp [complexParameterPoint]

private theorem continuous_complexParameterPoint : Continuous complexParameterPoint :=
  continuous_id.smul continuous_const

/-- EVERY actual translated original homogeneous initial ideal has true HS values bounded by the original formal ideal. -/
theorem hilbertSamuelValue_actual_translated_initial_le (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (p : Fin n → ℂ) (ℓ : ℕ) :
    hilbertSamuelValue (actualTranslatedInitialIdeal I p) ℓ ≤ genuineFormalHilbertSamuelValue n I ℓ := by
  let G := actualRayInitialFamily I p
  have hG : ∀ i, DifferentiableOn ℂ (G i) Set.univ := actualRayInitialFamily_holomorphic I p
  let J (c : ℂ) := actualFibreIdeal isOpen_univ G hG (complexParameterPoint c) (mem_univ _)
  have hdict (c : ℂ) : J c=actualTranslatedInitialIdeal I (c • p) := by
    have h := actualRayInitialFibreIdeal_eq I p (complexParameterPoint c)
    rw [complexParameterPoint_coordinate] at h
    exact h
  let P : ℂ → (⊤ : TopologicalSpace.Opens (ComplexModel 1)) :=
    fun c => ⟨complexParameterPoint c,mem_univ _⟩
  have hP : Continuous P := Continuous.subtype_mk continuous_complexParameterPoint _
  have hclosed : IsClosed {c : ℂ |
      hilbertSamuelValue (actualTranslatedInitialIdeal I p) ℓ ≤ hilbertSamuelValue (J c) ℓ} :=
    (isClosed_actualFibreHS_superlevel isOpen_univ G hG ⊤ (fun _ _ => mem_univ _) ℓ
      (hilbertSamuelValue (actualTranslatedInitialIdeal I p) ℓ)).preimage hP
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆ {c : ℂ |
      hilbertSamuelValue (actualTranslatedInitialIdeal I p) ℓ ≤ hilbertSamuelValue (J c) ℓ} := by
    intro c hc
    have hc0 : c ≠ 0 := by simpa using hc
    change hilbertSamuelValue (actualTranslatedInitialIdeal I p) ℓ ≤ hilbertSamuelValue (J c) ℓ
    rw [hdict c,actualTranslatedInitialIdeal_nonzero_ray_hs I p c hc0]
  have hz := closure_minimal hsub hclosed ((dense_compl_singleton (0 : ℂ)) 0)
  change hilbertSamuelValue (actualTranslatedInitialIdeal I p) ℓ ≤ hilbertSamuelValue (J 0) ℓ at hz
  rw [hdict 0,zero_smul,translated_initial_zero,actualOriginalInitialVertexIdeal_hs] at hz
  exact hz

/-- Genuine whole Taylor extension transfers the actual translated-polynomial comparison to EVERY formal HS quotient. -/
theorem genuineFormalHilbertSamuelValue_translated_initial_le (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (p : Fin n → ℂ) (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n (actualTranslatedInitialFormalIdeal I p) ℓ ≤
      genuineFormalHilbertSamuelValue n I ℓ := by
  rw [← actualTranslatedInitialIdeal_formal_extension,
    ← hilbertSamuelValue_eq_genuine_formal_extension]
  exact hilbertSamuelValue_actual_translated_initial_le I p ℓ

end
end Hironaka.HironakaActualTranslatedInitialHS
