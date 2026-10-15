/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalIdealContraction
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! Actual original/formal whole jet quotients, retaining their genuine complex actions. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualOriginalFormalHSTransfer
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaRelativeNormalIdeal
  HironakaRelativeNormalMonomialBasis HironakaRelativeNormalActualBaseJetDimension
  HironakaActualOriginalTaylorPolynomial HironakaActualOriginalFormalTaylor
  HironakaActualFormalIdealContraction

/-- The GENUINE ideal of all original formal variables. -/
def genuineFormalVariables (n : ℕ) : Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.span (range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) ℂ))

/-- Actual polynomial completion internally proves the GENUINE formal variable-power coefficient kernel. -/
theorem mem_genuineFormalVariables_pow_iff_coefficients_zero (n q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    F ∈ genuineFormalVariables n ^ q ↔
      ∀ α : Fin n →₀ ℕ, normalExponentDegree α < q → MvPowerSeries.coeff α F=0 := by
  classical
  let P := MvPolynomial (Fin n) ℂ
  let J := MvPolynomial.idealOfVars (Fin n) ℂ
  let E := MvPowerSeries.toAdicCompletionAlgEquiv (Fin n) ℂ
  have hvars : Ideal.map E.toRingEquiv.toRingHom (genuineFormalVariables n)=
      Ideal.map (algebraMap P (AdicCompletion J P)) J := by
    change Ideal.map E.toRingEquiv.toRingHom (Ideal.span (range (MvPowerSeries.X : Fin n → MvPowerSeries (Fin n) ℂ)))=
      Ideal.map (algebraMap P (AdicCompletion J P)) (Ideal.span (range (MvPolynomial.X : Fin n → P)))
    rw [Ideal.map_span,Ideal.map_span,← Set.range_comp,← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    dsimp only [Function.comp_def,E,P,J]
    simp [← MvPolynomial.coe_X,MvPowerSeries.toAdicCompletion_coe,AdicCompletion.algebraMap_apply]
  have hpow : Ideal.map E.toRingEquiv.toRingHom (genuineFormalVariables n ^ q)=
      Ideal.map (algebraMap P (AdicCompletion J P)) (J^q) := by
    rw [Ideal.map_pow,hvars,Ideal.map_pow]
  have hm : F ∈ genuineFormalVariables n ^ q ↔
      E F ∈ Ideal.map (algebraMap P (AdicCompletion J P)) (J^q) := by
    rw [← hpow]
    constructor
    · exact Ideal.mem_map_of_mem _
    · intro h
      obtain ⟨f,hf,he⟩ := (Ideal.mem_map_iff_of_surjective _ E.surjective).mp h
      have he' : f=F := E.injective he
      rwa [he'] at hf
  have hker : (J^q • (⊤ : Submodule P (AdicCompletion J P)))=(AdicCompletion.eval J P q).ker :=
    AdicCompletion.pow_smul_top_eq_ker_eval (I := J) (M := P) (MvPolynomial.idealOfVars_fg (Fin n) ℂ)
  have heval : E F ∈ Ideal.map (algebraMap P (AdicCompletion J P)) (J^q) ↔ (E F).val q=0 := by
    change E F ∈ (Ideal.map (algebraMap P (AdicCompletion J P)) (J^q)).restrictScalars P ↔ _
    rw [← Ideal.smul_top_eq_map,hker,LinearMap.mem_ker,AdicCompletion.eval_apply]
  have hcoeff : (E F).val q=0 ↔
      ∀ α : Fin n →₀ ℕ, normalExponentDegree α < q → MvPowerSeries.coeff α F=0 := by
    change Ideal.Quotient.mk (J^q • (⊤ : Ideal P)) (MvPowerSeries.truncTotal q F)=0 ↔ _
    rw [smul_eq_mul,Ideal.mul_top,Ideal.Quotient.eq_zero_iff_mem]
    change MvPowerSeries.truncTotal q F ∈ MvPolynomial.idealOfVars (Fin n) ℂ ^ q ↔ _
    rw [MvPolynomial.mem_pow_idealOfVars_iff']
    constructor
    · intro h α hα
      have hd : Finsupp.degree α < q := by rwa [Finsupp.degree_eq_sum]
      have hc := h α hd
      rwa [MvPowerSeries.coeff_truncTotal F hd] at hc
    · intro h α hα
      rw [MvPowerSeries.coeff_truncTotal F hα]
      apply h α
      rwa [Finsupp.degree_eq_sum] at hα
  exact hm.trans (heval.trans hcoeff)

/-- The ENTIRE actual formal extension plus the true formal variable power. -/
def actualFormalThickening (n : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) (q : ℕ) :
    Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.map (originalTaylorAlgHom n).toRingHom I ⊔ genuineFormalVariables n ^ q

/-- The canonical actual ORIGINAL complex quotient map, internally well defined on the whole ideal. -/
def originalFormalWholeJetMap (n : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) (q : ℕ) :
    (HolGerm (ComplexModel (0+n)) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q)) →ₐ[ℂ]
        (MvPowerSeries (Fin n) ℂ ⧸ actualFormalThickening n I q) :=
  Ideal.quotientMapₐ (actualFormalThickening n I q) (originalTaylorAlgHom n) (by
    intro g hg
    change originalTaylorAlgHom n g ∈ actualFormalThickening n I q
    have he : Ideal.map (originalTaylorAlgHom n).toRingHom
        (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q)=actualFormalThickening n I q :=
      map_original_thickening_eq_formal_thickening n q I
    rw [← he]
    exact Ideal.mem_map_of_mem _ hg)

/-- EVERY actual original numerator keeps its literal genuine Taylor numerator class. -/
theorem originalFormalWholeJetMap_mk (n : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) (q : ℕ)
    (g : HolGerm (ComplexModel (0+n))) :
    originalFormalWholeJetMap n I q
      (Ideal.Quotient.mk (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q) g)=
      Ideal.Quotient.mk (actualFormalThickening n I q) (originalTaylorAlgHom n g) := rfl

/-- Actual WHOLE original ideal contraction supplies injectivity of the genuine quotient map. -/
theorem originalFormalWholeJetMap_injective (n : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) (q : ℕ) :
    Function.Injective (originalFormalWholeJetMap n I q) := by
  intro a b hab
  obtain ⟨g,rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨h,rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [originalFormalWholeJetMap_mk,originalFormalWholeJetMap_mk] at hab
  have hc := Ideal.Quotient.eq.mp hab
  have hsub : originalTaylorAlgHom n (g-h)=originalTaylorAlgHom n g-originalTaylorAlgHom n h := map_sub _ _ _
  rw [← hsub] at hc
  have he : Ideal.map (originalTaylorAlgHom n).toRingHom
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q)=actualFormalThickening n I q :=
    map_original_thickening_eq_formal_thickening n q I
  rw [← he] at hc
  apply Ideal.Quotient.eq.mpr
  exact (mem_original_ideal_iff_formal_extension n _ (g-h)).mpr hc

/-- Actual original polynomial truncations reach EVERY genuine formal quotient class. -/
theorem originalFormalWholeJetMap_surjective (n : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) (q : ℕ) :
    Function.Surjective (originalFormalWholeJetMap n I q) := by
  intro z
  obtain ⟨F,rfl⟩ := Ideal.Quotient.mk_surjective z
  let g := originalPolynomialEval n (MvPowerSeries.truncTotal q F)
  refine ⟨Ideal.Quotient.mk (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q) g,?_⟩
  rw [originalFormalWholeJetMap_mk]
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_sup_right
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
  intro α hα
  rw [map_sub]
  change MvPowerSeries.coeff α (originalTaylorAlgHom n (originalPolynomialEval n (MvPowerSeries.truncTotal q F)))-
      MvPowerSeries.coeff α F=0
  rw [originalTaylorAlgHom_polynomialEval,MvPolynomial.coeff_coe,
    MvPowerSeries.coeff_truncTotal F (by rwa [Finsupp.degree_eq_sum]),sub_self]

/-- The internally proved ACTUAL quotient bijection gives a genuine ORIGINAL complex algebra equivalence. -/
def originalFormalWholeJetAlgEquiv (n : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) (q : ℕ) :
    (HolGerm (ComplexModel (0+n)) ⧸
      (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q)) ≃ₐ[ℂ]
        (MvPowerSeries (Fin n) ℂ ⧸ actualFormalThickening n I q) :=
  AlgEquiv.ofBijective (originalFormalWholeJetMap n I q)
    ⟨originalFormalWholeJetMap_injective n I q,originalFormalWholeJetMap_surjective n I q⟩

/-- Every SAME original class is retained by the actual inverse-derived quotient equivalence. -/
theorem originalFormalWholeJetAlgEquiv_mk (n : ℕ) (I : Ideal (HolGerm (ComplexModel (0+n)))) (q : ℕ)
    (g : HolGerm (ComplexModel (0+n))) :
    originalFormalWholeJetAlgEquiv n I q
      (Ideal.Quotient.mk (I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n))) ^ q) g)=
      Ideal.Quotient.mk (actualFormalThickening n I q) (originalTaylorAlgHom n g) := rfl

/-- EVERY genuine formal ideal has finite actual complex jet quotients, internally from genuine original jets. -/
theorem finiteDimensional_formal_quotient_sup_variables_pow (n q : ℕ)
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    FiniteDimensional ℂ (MvPowerSeries (Fin n) ℂ ⧸ (K ⊔ genuineFormalVariables n ^ q)) := by
  let := finiteDimensional_quotient_sup_maximalIdeal_pow (0+n) q ⊥
  let e := originalFormalWholeJetAlgEquiv n ⊥ q
  have hf : FiniteDimensional ℂ (MvPowerSeries (Fin n) ℂ ⧸ actualFormalThickening n ⊥ q) :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  have hbase : FiniteDimensional ℂ (MvPowerSeries (Fin n) ℂ ⧸ genuineFormalVariables n ^ q) := by
    have hbot : actualFormalThickening n ⊥ q=genuineFormalVariables n ^ q := by
      change Ideal.map (originalTaylorAlgHom n).toRingHom (⊥ : Ideal (HolGerm (ComplexModel (0+n)))) ⊔ genuineFormalVariables n ^ q=_
      have hb : Ideal.map (originalTaylorAlgHom n).toRingHom (⊥ : Ideal (HolGerm (ComplexModel (0+n))))=⊥ := Ideal.map_bot
      rw [hb,bot_sup_eq]
    rw [hbot] at hf
    exact hf
  let := hbase
  have hle : genuineFormalVariables n ^ q ≤ K ⊔ genuineFormalVariables n ^ q := le_sup_right
  let f := Ideal.Quotient.factorₐ ℂ hle
  exact FiniteDimensional.of_surjective f.toLinearMap
    (show Function.Surjective f from Ideal.Quotient.factor_surjective hle)

/-- The actual whole formal Hilbert--Samuel quotient uses the GENUINE existing complex scalar action. -/
def genuineFormalHilbertSamuelValue (n : ℕ) (K : Ideal (MvPowerSeries (Fin n) ℂ)) (ℓ : ℕ) : ℕ :=
  Module.finrank ℂ (MvPowerSeries (Fin n) ℂ ⧸ (K ⊔ genuineFormalVariables n ^ (ℓ+1)))

/-- EVERY EXISTING original HS value equals the true formal extension value, through the entire actual quotient. -/
theorem hilbertSamuelValue_eq_genuine_formal_extension (n : ℕ)
    (I : Ideal (HolGerm (ComplexModel (0+n)))) (ℓ : ℕ) :
    hilbertSamuelValue I ℓ = genuineFormalHilbertSamuelValue n (Ideal.map (originalTaylorAlgHom n).toRingHom I) ℓ :=
  (originalFormalWholeJetAlgEquiv n I (ℓ+1)).toLinearEquiv.finrank_eq

end
end Hironaka.HironakaActualOriginalFormalHSTransfer
