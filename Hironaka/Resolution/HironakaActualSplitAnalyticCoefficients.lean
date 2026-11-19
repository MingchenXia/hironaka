import Hironaka.Resolution.HironakaActualRelativeCoefficientGerms
import Hironaka.Analytic.HolomorphicZeroSetThin

/-! Canonical actual normal coefficients of genuine split holomorphic maps.
The existing whole normal-power polynomial remainder and uniqueness produce
the coefficient identity, including zero scalar and zero dimensions. The
normalization corollary is an intermediate analytic product dictionary only.
It does not construct blowup charts or close the whole constant-HS phase.
Mathematics/API first: work/hironaka-g8-constant-hs-phase-20261024/
split-analytic-coefficient-source/. Initial SOURCE ONLY; no Lean acceptance.
-/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaActualSplitAnalyticCoefficients
noncomputable section

open HolGerm HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualRelativeCoefficientGerms HironakaHolomorphicJetChartInvariance

/-- The actual split function uses genuine free composition and normal scalar
multiplication. No reciprocal or nonzero scalar is part of its definition. -/
def actualSplitMap (d t : ℕ) (φ : ComplexModel d → ComplexModel d)
    (u : ComplexModel d → ℂ) (w : ComplexModel (d+t)) : ComplexModel (d+t) :=
  tangentInclusion d t (φ (tangentProjection d t w)) +
    u (tangentProjection d t w) • (w-tangentInclusion d t (tangentProjection d t w))

theorem tangentProjection_actualSplitMap (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d) (u : ComplexModel d → ℂ)
    (w : ComplexModel (d+t)) :
    tangentProjection d t (actualSplitMap d t φ u w) = φ (tangentProjection d t w) := by
  simp only [actualSplitMap,map_add,map_smul,map_sub,tangentProjection_tangentInclusion,
    sub_self,smul_zero,add_zero]

theorem actualSplitMap_normal (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d) (u : ComplexModel d → ℂ)
    (w : ComplexModel (d+t)) (i : Fin t) :
    actualSplitMap d t φ u w (i.natAdd d) = u (tangentProjection d t w) * w (i.natAdd d) := by
  simp only [actualSplitMap,PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,
    tangentInclusion_normal,zero_add,sub_zero,smul_eq_mul]

/-- The actual vector-valued map is holomorphic on a genuine neighborhood.
Only the free projection is used to pull back the two input neighborhoods. -/
theorem holomorphic_actualSplitMap (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x) :
    ∀ᶠ w in 𝓝 (0 : ComplexModel (d+t)), DifferentiableAt ℂ (actualSplitMap d t φ u) w := by
  have hp : Tendsto (tangentProjection d t)
      (𝓝 (0 : ComplexModel (d+t))) (𝓝 (0 : ComplexModel d)) := by
    simpa only [map_zero] using (tangentProjection d t).continuous.tendsto 0
  filter_upwards [hp.eventually hφ,hp.eventually hu] with w hφw huw
  have hpr := (tangentProjection d t).differentiableAt (x := w)
  have hfree := (tangentInclusion d t).differentiableAt.comp w (hφw.comp w hpr)
  have hnormal := differentiableAt_id.sub ((tangentInclusion d t).differentiableAt.comp w hpr)
  exact hfree.add ((huw.comp w hpr).smul hnormal)

/-- The scalar may have any value at zero, including zero. -/
theorem actualSplitMap_zero (d t : ℕ) (φ : ComplexModel d → ComplexModel d)
    (hφ0 : φ 0 = 0) (u : ComplexModel d → ℂ) : actualSplitMap d t φ u 0 = 0 := by
  simp only [actualSplitMap,map_zero,hφ0,sub_self,smul_zero,add_zero]

/-- The actual entire germ homomorphism is induced by genuine composition. -/
def actualSplitPullback (d t : ℕ) (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x) :
    HolGerm (ComplexModel (d+t)) →ₐ[ℂ] HolGerm (ComplexModel (d+t)) :=
  compAlgHom (actualSplitMap d t φ u) (holomorphic_actualSplitMap d t φ hφ u hu)
    (actualSplitMap_zero d t φ hφ0 u)

theorem actualSplitPullback_tangentPullback (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x)
    (a : HolGerm (ComplexModel d)) :
    actualSplitPullback d t φ hφ hφ0 u hu (tangentPullback d t a) =
      tangentPullback d t (compAlgHom φ hφ hφ0 a) := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    unfold actualSplitPullback tangentPullback
    rw [compAlgHom_mk,compAlgHom_mk,compAlgHom_mk,compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun w => congrArg f (tangentProjection_actualSplitMap d t φ u w)

theorem actualSplitPullback_normalCoordinate (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x) (i : Fin t) :
    actualSplitPullback d t φ hφ hφ0 u hu (normalCoordinate d t i) =
      tangentPullback d t (HolGerm.mk u hu) * normalCoordinate d t i := by
  unfold actualSplitPullback normalCoordinate tangentPullback HironakaHolomorphicJetMonomialSpan.coordinateGerm
  rw [compAlgHom_mk,compAlgHom_mk]
  rw [← HolGerm.mk_mul]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun w => actualSplitMap_normal d t φ u w i

/-- The actual map preserves the WHOLE normal ideal without scalar invertibility. -/
theorem actualSplitPullback_map_normalIdeal_le (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x) :
    Ideal.map (actualSplitPullback d t φ hφ hφ0 u hu).toRingHom (normalIdeal d t) ≤
      normalIdeal d t := by
  apply Ideal.map_le_iff_le_comap.mpr
  apply Ideal.span_le.mpr
  rintro g ⟨i,rfl⟩
  change actualSplitPullback d t φ hφ hφ0 u hu (normalCoordinate d t i) ∈ normalIdeal d t
  rw [actualSplitPullback_normalCoordinate]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)

theorem actualSplitPullback_mem_normalIdeal_pow (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x)
    (q : ℕ) (F : HolGerm (ComplexModel (d+t))) (hF : F ∈ normalIdeal d t ^ q) :
    actualSplitPullback d t φ hφ hφ0 u hu F ∈ normalIdeal d t ^ q := by
  have hm := Ideal.mem_map_of_mem (actualSplitPullback d t φ hφ hφ0 u hu).toRingHom hF
  rw [Ideal.map_pow] at hm
  exact (pow_le_pow_left' (actualSplitPullback_map_normalIdeal_le d t φ hφ hφ0 u hu) q) hm

theorem actualSplitPullback_normalPolynomialEval_monomial (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x)
    (α : Fin t →₀ ℕ) (a : HolGerm (ComplexModel d)) :
    actualSplitPullback d t φ hφ hφ0 u hu
        (normalPolynomialEval d t (MvPolynomial.monomial α a)) =
      normalPolynomialEval d t (MvPolynomial.monomial α
        ((HolGerm.mk u hu)^normalExponentDegree α * compAlgHom φ hφ hφ0 a)) := by
  rw [normalPolynomialEval_monomial,map_mul,actualSplitPullback_tangentPullback]
  have hmono : actualSplitPullback d t φ hφ hφ0 u hu (normalExponentMonomial d t α) =
      tangentPullback d t (HolGerm.mk u hu)^normalExponentDegree α * normalExponentMonomial d t α := by
    simp only [normalExponentMonomial,map_prod,map_pow,actualSplitPullback_normalCoordinate,
      mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,normalExponentDegree]
  rw [hmono,normalPolynomialEval_monomial,map_mul,map_pow]
  ring

/-- This finite polynomial uses the SAME genuine original quotient coordinates. -/
def actualSplitNormalPolynomial (d t : ℕ) (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x)
    (q : ℕ) (F : HolGerm (ComplexModel (d+t))) :
    MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  let := normalExponentFintype t q
  ∑ α : normalExponentIndex t q, MvPolynomial.monomial α.val
    ((HolGerm.mk u hu)^normalExponentDegree α.val *
      compAlgHom φ hφ hφ0 (actualNormalJetCoordinates d t q F α))

private theorem splitPolynomial_high (d t : ℕ) (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x)
    (q : ℕ) (F : HolGerm (ComplexModel (d+t))) (γ : Fin t →₀ ℕ)
    (hγ : q ≤ normalExponentDegree γ) :
    MvPolynomial.coeff γ (actualSplitNormalPolynomial d t φ hφ hφ0 u hu q F) = 0 := by
  let := normalExponentFintype t q
  have hne (α : normalExponentIndex t q) : α.val ≠ γ := by
    intro he
    have hα := α.property
    rw [he] at hα
    omega
  simp [actualSplitNormalPolynomial,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,hne]

private theorem splitPolynomial_coefficient (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x)
    (q : ℕ) (F : HolGerm (ComplexModel (d+t))) (γ : normalExponentIndex t q) :
    MvPolynomial.coeff γ.val (actualSplitNormalPolynomial d t φ hφ hφ0 u hu q F) =
      (HolGerm.mk u hu)^normalExponentDegree γ.val *
        compAlgHom φ hφ hφ0 (actualNormalJetCoordinates d t q F γ) := by
  let := normalExponentFintype t q
  exact coefficient_normalMonomialCombination_polynomial d t q _ γ

/-- The genuine ENTIRE normal-power remainder identifies the transformed
finite polynomial with the canonical actual polynomial. This also covers q=0. -/
theorem actualSplitNormalPolynomial_eq_actualNormalTaylorPolynomial (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x)
    (q : ℕ) (F : HolGerm (ComplexModel (d+t))) :
    actualSplitNormalPolynomial d t φ hφ hφ0 u hu q F =
      actualNormalTaylorPolynomial d t q (actualSplitPullback d t φ hφ hφ0 u hu F) := by
  let := normalExponentFintype t q
  have heval : normalPolynomialEval d t (actualSplitNormalPolynomial d t φ hφ hφ0 u hu q F) =
      actualSplitPullback d t φ hφ hφ0 u hu
        (normalPolynomialEval d t (actualNormalTaylorPolynomial d t q F)) := by
    unfold actualSplitNormalPolynomial actualNormalTaylorPolynomial
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro α _
    exact (actualSplitPullback_normalPolynomialEval_monomial d t φ hφ hφ0 u hu α.val
      (actualNormalJetCoordinates d t q F α)).symm
  apply actualNormalTaylorPolynomial_unique d t q
    (actualSplitPullback d t φ hφ hφ0 u hu F)
    (actualSplitNormalPolynomial d t φ hφ hφ0 u hu q F)
    (splitPolynomial_high d t φ hφ hφ0 u hu q F)
  have hm := actualSplitPullback_mem_normalIdeal_pow d t φ hφ hφ0 u hu q _
    (actualNormalTaylorPolynomial_remainder d t q F)
  rwa [map_sub,← heval] at hm

/-- Every canonical entire analytic coefficient has the actual split
pullback formula. The scalar can be zero and gamma is arbitrary. -/
theorem actualNormalAnalyticCoefficientGerm_actualSplitPullback (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x)
    (F : HolGerm (ComplexModel (d+t))) (γ : Fin t →₀ ℕ) :
    actualNormalAnalyticCoefficientGerm d t (actualSplitPullback d t φ hφ hφ0 u hu F) γ =
      (HolGerm.mk u hu)^normalExponentDegree γ *
        compAlgHom φ hφ hφ0 (actualNormalAnalyticCoefficientGerm d t F γ) := by
  let q := normalExponentDegree γ+1
  have hγ : normalExponentDegree γ < q := by dsimp only [q]; omega
  let α : normalExponentIndex t q := ⟨γ,hγ⟩
  have hcoord : actualNormalJetCoordinates d t q F α = actualNormalAnalyticCoefficientGerm d t F γ :=
    (actualNormalTaylorPolynomial_coefficient d t q F α).symm.trans
      (actualNormalTaylorPolynomial_coefficient_eq_germ d t q F γ hγ)
  calc
    _ = MvPolynomial.coeff γ
        (actualNormalTaylorPolynomial d t q (actualSplitPullback d t φ hφ hφ0 u hu F)) :=
      (actualNormalTaylorPolynomial_coefficient_eq_germ d t q _ γ hγ).symm
    _ = MvPolynomial.coeff γ (actualSplitNormalPolynomial d t φ hφ hφ0 u hu q F) :=
      congrArg (MvPolynomial.coeff γ)
        (actualSplitNormalPolynomial_eq_actualNormalTaylorPolynomial d t φ hφ hφ0 u hu q F).symm
    _ = (HolGerm.mk u hu)^normalExponentDegree γ *
        compAlgHom φ hφ hφ0 (actualNormalJetCoordinates d t q F α) :=
      splitPolynomial_coefficient d t φ hφ hφ0 u hu q F α
    _ = _ := by rw [hcoord]

/-- True base-scalar linearity follows from the SAME whole polynomial
uniqueness, without any normal derivative/factorial convention. -/
theorem actualNormalAnalyticCoefficientGerm_tangent_mul (d t : ℕ)
    (v : HolGerm (ComplexModel d)) (F : HolGerm (ComplexModel (d+t))) (γ : Fin t →₀ ℕ) :
    actualNormalAnalyticCoefficientGerm d t (tangentPullback d t v * F) γ =
      v * actualNormalAnalyticCoefficientGerm d t F γ := by
  let := tangentAlgebra d t
  let q := normalExponentDegree γ+1
  have hγ : normalExponentDegree γ < q := by dsimp only [q]; omega
  let P := MvPolynomial.C v * actualNormalTaylorPolynomial d t q F
  have heval : normalPolynomialEval d t P =
      tangentPullback d t v * normalPolynomialEval d t (actualNormalTaylorPolynomial d t q F) := by
    change normalPolynomialEval d t (MvPolynomial.C v * _) = _
    have hC : normalPolynomialEval d t (MvPolynomial.C v) = tangentPullback d t v := by
      change MvPolynomial.aeval (normalCoordinate d t) (MvPolynomial.C v) = tangentPullback d t v
      rw [MvPolynomial.aeval_C]
      rfl
    rw [map_mul,hC]
  have hhigh (α : Fin t →₀ ℕ) (hα : q ≤ normalExponentDegree α) : MvPolynomial.coeff α P = 0 := by
    change MvPolynomial.coeff α (MvPolynomial.C v * _) = 0
    rw [MvPolynomial.coeff_C_mul,actualNormalTaylorPolynomial_coefficient_high d t q F α hα,mul_zero]
  have hrem : tangentPullback d t v * F - normalPolynomialEval d t P ∈ normalIdeal d t ^ q := by
    rw [heval,← mul_sub]
    exact Ideal.mul_mem_left _ _ (actualNormalTaylorPolynomial_remainder d t q F)
  have he := actualNormalTaylorPolynomial_unique d t q (tangentPullback d t v * F) P hhigh hrem
  calc
    _ = MvPolynomial.coeff γ (actualNormalTaylorPolynomial d t q (tangentPullback d t v * F)) :=
      (actualNormalTaylorPolynomial_coefficient_eq_germ d t q _ γ hγ).symm
    _ = MvPolynomial.coeff γ P := congrArg (MvPolynomial.coeff γ) he.symm
    _ = v * MvPolynomial.coeff γ (actualNormalTaylorPolynomial d t q F) :=
      MvPolynomial.coeff_C_mul _ _ _
    _ = _ := by rw [actualNormalTaylorPolynomial_coefficient_eq_germ d t q F γ hγ]

/-- An actual normalization PRODUCT gives the exact lower-mark coefficient
PRODUCT. The only nonzero input is the scalar GERM, not its value at zero.
This intermediate dictionary does not construct the normalization itself. -/
theorem actual_normalized_split_coefficient_product (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x)
    (huG : HolGerm.mk u hu ≠ 0) (μ : ℕ)
    (F H' : HolGerm (ComplexModel (d+t)))
    (hNorm : tangentPullback d t ((HolGerm.mk u hu)^μ) * H' =
      actualSplitPullback d t φ hφ hφ0 u hu F)
    (γ : Fin t →₀ ℕ) (hγ : normalExponentDegree γ ≤ μ) :
    (HolGerm.mk u hu)^(μ-normalExponentDegree γ) * actualNormalAnalyticCoefficientGerm d t H' γ =
      compAlgHom φ hφ hφ0 (actualNormalAnalyticCoefficientGerm d t F γ) := by
  apply mul_left_cancel₀ (pow_ne_zero (normalExponentDegree γ) huG)
  calc
    _ = (HolGerm.mk u hu)^μ * actualNormalAnalyticCoefficientGerm d t H' γ := by
      rw [← mul_assoc,← pow_add,Nat.add_sub_of_le hγ]
    _ = actualNormalAnalyticCoefficientGerm d t (tangentPullback d t ((HolGerm.mk u hu)^μ) * H') γ :=
      (actualNormalAnalyticCoefficientGerm_tangent_mul d t _ H' γ).symm
    _ = actualNormalAnalyticCoefficientGerm d t (actualSplitPullback d t φ hφ hφ0 u hu F) γ :=
      congrArg (fun G => actualNormalAnalyticCoefficientGerm d t G γ) hNorm
    _ = _ := actualNormalAnalyticCoefficientGerm_actualSplitPullback d t φ hφ hφ0 u hu F γ

/-- The canonical actual coefficient is the UNIQUE genuine lower-mark
holomorphic quotient, including lower mark zero. -/
theorem actual_normalized_split_coefficient_unique (d t : ℕ)
    (φ : ComplexModel d → ComplexModel d)
    (hφ : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ φ x) (hφ0 : φ 0 = 0)
    (u : ComplexModel d → ℂ)
    (hu : ∀ᶠ x in 𝓝 (0 : ComplexModel d), DifferentiableAt ℂ u x)
    (huG : HolGerm.mk u hu ≠ 0) (μ : ℕ)
    (F H' : HolGerm (ComplexModel (d+t)))
    (hNorm : tangentPullback d t ((HolGerm.mk u hu)^μ) * H' =
      actualSplitPullback d t φ hφ hφ0 u hu F)
    (γ : Fin t →₀ ℕ) (hγ : normalExponentDegree γ ≤ μ)
    (c : HolGerm (ComplexModel d)) :
    (HolGerm.mk u hu)^(μ-normalExponentDegree γ) * c =
        compAlgHom φ hφ hφ0 (actualNormalAnalyticCoefficientGerm d t F γ) ↔
      c = actualNormalAnalyticCoefficientGerm d t H' γ := by
  have hcanonical := actual_normalized_split_coefficient_product d t φ hφ hφ0 u hu huG μ F H' hNorm γ hγ
  constructor
  · intro hc
    exact mul_left_cancel₀ (pow_ne_zero (μ-normalExponentDegree γ) huG) (hc.trans hcanonical.symm)
  · intro hc
    rw [hc]
    exact hcanonical

end
end Hironaka.HironakaActualSplitAnalyticCoefficients
