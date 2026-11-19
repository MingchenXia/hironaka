import Hironaka.Resolution.HironakaActualInheritedTranslatedAnalyticDivision
import Hironaka.Resolution.HironakaActualCauchyFilteredNeumannDivision
import Hironaka.Resolution.HironakaActualFormalStandardMonomialHS
import Hironaka.Resolution.HironakaActualNormalZeroAnalyticSaturation
import Mathlib.RingTheory.MvPowerSeries.Trunc

/-! The literal OLD-standard monomial map into the WHOLE actual nearby
analytic jet quotient. ONE inherited BP3 domain works for all p and all q.
Arbitrary germs and ideal coefficients are replaced by actual finite Taylor
polynomials, not extended to the fixed ball. Marked injectivity uses the SAME
actual Neumann remainder and weight one only as a coefficient filtration.
SOURCE ONLY: no elaboration, kernel acceptance, BP5/6 or G8 closure claimed.
The complete mathematical/API design precedes this source in work/
hironaka-inherited-neighborhood-standard-jets-20261023/. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualInheritedNeighborhoodStandardJets
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm OkaRelationSheaf HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalInitialDiagram HironakaActualFormalCoordinatePowerDivision
  HironakaActualOriginalFormalHSTransfer HironakaActualFormalStandardMonomialHS
  HironakaActualUnshiftedInitialHSTransfer HironakaActualNormalZeroAnalyticSaturation
  HironakaActualCauchyCoordinateDivision HironakaActualCauchyTaylorSupport
  HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition
  HironakaActualCauchyEnumeratedPartition HironakaActualCauchyNeumannDivision
  HironakaActualCauchyFilteredNeumannDivision HironakaActualCauchyNeumannSameBallBounds
  HironakaActualBoundedSupportedNeumannUniqueness HironakaActualTranslatedCauchyOwnerSupport
  HironakaActualRelativeNormalJetDivision HironakaActualInheritedSmallTails
  HironakaActualOriginalScaledAnalyticDivision HironakaActualInheritedSourceCauchyRemainder
  HironakaActualInheritedUniformTranslatedTails HironakaActualInheritedTranslatedAnalyticDivision

variable {n : ℕ}

private def polynomialGerm (n : ℕ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] HolGerm (ComplexModel n) :=
  MvPolynomial.aeval (coordinateGerm : Fin n → HolGerm (ComplexModel n))

private theorem Taylor_polynomialGerm (A : MvPolynomial (Fin n) ℂ) :
    actualUnshiftedTaylorAlgHom n (polynomialGerm n A) = (A : MvPowerSeries (Fin n) ℂ) := by
  induction A using MvPolynomial.induction_on with
  | C c =>
      simp only [polynomialGerm, MvPolynomial.aeval_C, AlgHom.commutes,
        MvPolynomial.coe_C, MvPowerSeries.c_eq_algebraMap]
  | add A B hA hB => rw [map_add, map_add, hA, hB, MvPolynomial.coe_add]
  | mul_X A i hA =>
      rw [map_mul, map_mul, hA, polynomialGerm, MvPolynomial.aeval_X,
        actualUnshiftedTaylor_coordinate, MvPolynomial.coe_mul, MvPolynomial.coe_X]

private theorem mem_maximal_pow_iff_coefficients (q : ℕ)
    (F : HolGerm (ComplexModel n)) :
    F ∈ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q ↔
      ∀ a : Fin n →₀ ℕ, normalExponentDegree a < q →
        MvPowerSeries.coeff a (actualUnshiftedTaylorAlgHom n F) = 0 := by
  rw [mem_analytic_ideal_iff_actualUnshifted_extension n,
    map_actualUnshifted_maximal_pow,
    mem_genuineFormalVariables_pow_iff_coefficients_zero]

private def finitePolynomial (q : ℕ) (F : HolGerm (ComplexModel n)) :
    MvPolynomial (Fin n) ℂ :=
  MvPowerSeries.truncTotal q (actualUnshiftedTaylorAlgHom n F)

private theorem finitePolynomial_remainder (q : ℕ) (F : HolGerm (ComplexModel n)) :
    F - polynomialGerm n (finitePolynomial q F) ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
  apply (mem_maximal_pow_iff_coefficients q _).mpr
  intro a ha
  rw [map_sub, map_sub, Taylor_polynomialGerm, MvPolynomial.coeff_coe]
  apply sub_eq_zero.mpr
  symm
  apply MvPowerSeries.coeff_truncTotal
  simpa only [Finsupp.degree_eq_sum, normalExponentDegree] using ha

/-- Literal finite OLD-standard polynomial with the SOURCE diagram labels. -/
def actualOldStandardPolynomial (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) (q : ℕ) :
    (actualStandardIndex n (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) q → ℂ)
      →ₗ[ℂ] MvPolynomial (Fin n) ℂ where
  toFun c := ∑ a, MvPolynomial.monomial a.val.val (c a)
  map_add' c d := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c d := by simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]

private theorem Taylor_oldStandard (I : Ideal (HolGerm (ComplexModel n))) (q : ℕ)
    (c : actualStandardIndex n (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) q → ℂ) :
    actualUnshiftedTaylorAlgHom n (polynomialGerm n (actualOldStandardPolynomial n I q c)) =
      actualStandardLift n (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) q c := by
  rw [Taylor_polynomialGerm]
  apply MvPowerSeries.ext
  intro β
  change MvPolynomial.coeff β
      (∑ a, MvPolynomial.monomial a.val.val (c a)) =
    MvPowerSeries.coeff β (∑ a, MvPowerSeries.monomial a.val.val (c a))
  rw [MvPolynomial.coeff_sum, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [MvPolynomial.coeff_monomial, MvPowerSeries.coeff_monomial, eq_comm]

/-- The concrete map is the literal monomial numerator class in the genuine
analytic quotient, with its existing complex scalar action. -/
def actualOldStandardClassMap (n : ℕ) (I J : Ideal (HolGerm (ComplexModel n))) (q : ℕ) :
    (actualStandardIndex n (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) q → ℂ)
      →ₗ[ℂ] (HolGerm (ComplexModel n) ⧸
        (J ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q)) :=
  (Ideal.Quotient.mkₐ ℂ _).toLinearMap.comp
    ((polynomialGerm n).toLinearMap.comp (actualOldStandardPolynomial n I q))

private theorem modelGerm_sum {ι : Type*} [Fintype ι] {r : ℝ} (hr : 0 < r)
    (f : ι → CoordinateSpace n → ℂ) (hf : ∀ j, DifferentiableOn ℂ (f j) (ball 0 r)) :
    modelGerm hr (DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) => hf j) =
      ∑ j, modelGerm hr (hf j) := by
  change HolGerm.mk (fun z : ComplexModel n => ∑ j, modelFunction (f j) z) _ = _
  exact HolGerm.mk_sum Finset.univ _ (fun j => modelFunction_holAt hr (hf j))

private theorem modelGerm_mul {r : ℝ} (hr : 0 < r)
    {f g : CoordinateSpace n → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 r)) (hg : DifferentiableOn ℂ g (ball 0 r)) :
    modelGerm hr (hf.mul hg) = modelGerm hr hf * modelGerm hr hg := by
  change HolGerm.mk (fun z : ComplexModel n => modelFunction f z * modelFunction g z) _ = _
  exact HolGerm.mk_mul _ _ _ _

private theorem modelGerm_sub {r : ℝ} (hr : 0 < r)
    {f g : CoordinateSpace n → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 r)) (hg : DifferentiableOn ℂ g (ball 0 r)) :
    modelGerm hr (hf.sub hg) = modelGerm hr hf - modelGerm hr hg := by
  change HolGerm.mk (fun z : ComplexModel n => modelFunction f z - modelFunction g z) _ = _
  exact HolGerm.mk_sub _ _ _ _

private theorem modelGerm_neg {r : ℝ} (hr : 0 < r)
    {f : CoordinateSpace n → ℂ} (hf : DifferentiableOn ℂ f (ball 0 r)) :
    modelGerm hr hf.neg = -modelGerm hr hf := by
  change HolGerm.mk (fun z : ComplexModel n => -modelFunction f z) _ = _
  exact HolGerm.mk_neg _ _

private theorem modelGerm_eqOn {r : ℝ} (hr : 0 < r)
    {f g : CoordinateSpace n → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 r)) (hg : DifferentiableOn ℂ g (ball 0 r))
    (he : EqOn f g (ball 0 r)) : modelGerm hr hf = modelGerm hr hg := by
  apply HolGerm.mk_eq_mk_iff.mpr
  let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
  have ht : Tendsto e (𝓝 (0 : ComplexModel n)) (𝓝 (0 : CoordinateSpace n)) := by
    simpa only [map_zero] using e.continuous.tendsto (0 : ComplexModel n)
  filter_upwards [ht.eventually (isOpen_ball.mem_nhds (mem_ball_self hr))] with z hz
  exact he hz

private theorem modelGerm_polynomial {r : ℝ} (hr : 0 < r)
    (A : MvPolynomial (Fin n) ℂ) :
    modelGerm hr (actualCoordinatePolynomialFunction_differentiable A).differentiableOn =
      polynomialGerm n A := by
  induction A using MvPolynomial.induction_on with
  | C c =>
      change HolGerm.mk (modelFunction
        (actualCoordinatePolynomialFunction (MvPolynomial.C c))) _ = _
      rw [polynomialGerm, MvPolynomial.aeval_C]
      change HolGerm.mk (modelFunction
        (actualCoordinatePolynomialFunction (MvPolynomial.C c))) _ = HolGerm.constHom c
      rw [← HolGerm.mk_const]
      apply HolGerm.mk_eq_mk_iff.mpr
      exact Eventually.of_forall fun z => by
        simp [modelFunction, actualCoordinatePolynomialFunction]
  | add A B hA hB =>
      have hdA : DifferentiableOn ℂ (actualCoordinatePolynomialFunction A) (ball 0 r) :=
        (actualCoordinatePolynomialFunction_differentiable A).differentiableOn
      have hdB : DifferentiableOn ℂ (actualCoordinatePolynomialFunction B) (ball 0 r) :=
        (actualCoordinatePolynomialFunction_differentiable B).differentiableOn
      have he : modelGerm hr (hdA.add hdB) = modelGerm hr hdA + modelGerm hr hdB := by
        change HolGerm.mk (fun z : ComplexModel n =>
          modelFunction (actualCoordinatePolynomialFunction A) z +
          modelFunction (actualCoordinatePolynomialFunction B) z) _ = _
        exact HolGerm.mk_add _ _ _ _
      have hdSum : DifferentiableOn ℂ (actualCoordinatePolynomialFunction (A+B))
          (ball 0 r) :=
        (actualCoordinatePolynomialFunction_differentiable (A+B)).differentiableOn
      have hEq := modelGerm_eqOn hr hdSum (hdA.add hdB) (by
        intro z _
        exact map_add (MvPolynomial.aeval z) A B)
      exact hEq.trans (he.trans ((congrArg₂
        (fun x y : HolGerm (ComplexModel n) => x+y) hA hB).trans
          (map_add (polynomialGerm n) A B).symm))
  | mul_X A i hA =>
      have hi : modelGerm hr
          (actualCoordinatePolynomialFunction_differentiable (MvPolynomial.X i)).differentiableOn =
          coordinateGerm i := by
        apply HolGerm.mk_eq_mk_iff.mpr
        exact Eventually.of_forall fun z => by
          change actualCoordinatePolynomialFunction (MvPolynomial.X i)
            (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) z) = z i
          rw [actualCoordinatePolynomialFunction, MvPolynomial.aeval_X]
          rfl
      have hdA : DifferentiableOn ℂ (actualCoordinatePolynomialFunction A) (ball 0 r) :=
        (actualCoordinatePolynomialFunction_differentiable A).differentiableOn
      have hdX : DifferentiableOn ℂ (actualCoordinatePolynomialFunction (MvPolynomial.X i))
          (ball 0 r) :=
        (actualCoordinatePolynomialFunction_differentiable (MvPolynomial.X i)).differentiableOn
      have hprod : DifferentiableOn ℂ
          (actualCoordinatePolynomialFunction (A * MvPolynomial.X i)) (ball 0 r) :=
        (actualCoordinatePolynomialFunction_differentiable (A * MvPolynomial.X i)).differentiableOn
      have he := modelGerm_eqOn hr hprod (hdA.mul hdX) (by
        intro z _
        exact map_mul (MvPolynomial.aeval z) A (MvPolynomial.X i))
      have hm := modelGerm_mul hr hdA hdX
      rw [hA, hi] at hm
      exact he.trans (hm.trans (by rw [map_mul, polynomialGerm, MvPolynomial.aeval_X]))

private theorem polynomial_bound {r : ℝ} (A : MvPolynomial (Fin n) ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ ball (0 : CoordinateSpace n) r,
      ‖actualCoordinatePolynomialFunction A z‖ ≤ M := by
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0 : CoordinateSpace n) r).exists_bound_of_continuousOn
      (actualCoordinatePolynomialFunction_differentiable A).continuous.continuousOn
  exact ⟨max 0 B, le_max_left _ _, fun z hz =>
    (hB z (ball_subset_closedBall hz)).trans (le_max_right _ _)⟩

variable {I : Ideal (HolGerm (ComplexModel n))}
variable {G : ActualAnalyticInheritedFamily n 0
  (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)}

/-- The genuine original zero germ of the SAME literal scaled member at p.
The actual ball inclusion and source holomorphicity provide the witness. -/
def actualInheritedTranslatedGerm (P : ActualInheritedWeightedTailData G)
    {s : ℂ} (hs : s ∈ ball 0 P.radius) (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius))
    (j : Fin (actualVertexCount n I)) : HolGerm (ComplexModel n) :=
  modelGerm (half_pos P.radius_pos) (actual_coordinate_translation_differentiableOn
    (actualInheritedSourceScaledFamily_differentiableOn P hs j) p hdom)

/-- The WHOLE actual nearby analytic ideal is spanned by those SAME actual
translated germs; no target monic family or target diagram is selected. -/
def actualInheritedTranslatedIdeal (P : ActualInheritedWeightedTailData G)
    {s : ℂ} (hs : s ∈ ball 0 P.radius) (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius)) :
    Ideal (HolGerm (ComplexModel n)) :=
  Ideal.span (range (actualInheritedTranslatedGerm P hs p hdom))

private theorem combination_hol (P : ActualInheritedWeightedTailData G)
    {s : ℂ} (hs : s ∈ ball 0 P.radius) (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius))
    (A : Fin (actualVertexCount n I) → MvPolynomial (Fin n) ℂ) :
    DifferentiableOn ℂ (actualInheritedTranslatedCombination P s p
      (fun j => actualCoordinatePolynomialFunction (A j))) (ball 0 (P.radius/2)) :=
  DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) =>
    (actualCoordinatePolynomialFunction_differentiable (A j)).differentiableOn.mul
      (actual_coordinate_translation_differentiableOn
        (actualInheritedSourceScaledFamily_differentiableOn P hs j) p hdom)

private theorem combination_modelGerm (P : ActualInheritedWeightedTailData G)
    {s : ℂ} (hs : s ∈ ball 0 P.radius) (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius))
    (A : Fin (actualVertexCount n I) → MvPolynomial (Fin n) ℂ) :
    modelGerm (half_pos P.radius_pos) (combination_hol P hs p hdom A) =
      ∑ j, polynomialGerm n (A j) * actualInheritedTranslatedGerm P hs p hdom j := by
  let hp (j : Fin (actualVertexCount n I)) :
      DifferentiableOn ℂ (actualCoordinatePolynomialFunction (A j)) (ball 0 (P.radius/2)) :=
    (actualCoordinatePolynomialFunction_differentiable (A j)).differentiableOn
  let hg (j : Fin (actualVertexCount n I)) := actual_coordinate_translation_differentiableOn
    (actualInheritedSourceScaledFamily_differentiableOn P hs j) p hdom
  let hm (j : Fin (actualVertexCount n I)) : DifferentiableOn ℂ
      (fun z => actualCoordinatePolynomialFunction (A j) z *
        actualInheritedSourceScaledFamily P s j (p+z)) (ball 0 (P.radius/2)) :=
    (hp j).mul (hg j)
  have hsum := modelGerm_sum (half_pos P.radius_pos)
    (fun j z => actualCoordinatePolynomialFunction (A j) z *
      actualInheritedSourceScaledFamily P s j (p+z)) hm
  refine hsum.trans (Finset.sum_congr rfl ?_)
  intro j _
  exact (modelGerm_mul (half_pos P.radius_pos) (hp j) (hg j)).trans
    (congrArg (fun v : HolGerm (ComplexModel n) =>
      v * actualInheritedTranslatedGerm P hs p hdom j)
        (modelGerm_polynomial (half_pos P.radius_pos) (A j)))

private theorem combination_bound (P : ActualInheritedWeightedTailData G)
    {s : ℂ} (p : CoordinateSpace n)
    (D : ConcreteNeumannData (P.radius/2) (actualVertexWords n I))
    (hb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
      ‖actualInheritedTranslatedTail P s p j z‖ ≤ D.epsilon)
    (A : Fin (actualVertexCount n I) → MvPolynomial (Fin n) ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
      ‖actualInheritedTranslatedCombination P s p
        (fun j => actualCoordinatePolynomialFunction (A j)) z‖ ≤ M := by
  choose B hB0 hB using fun j => polynomial_bound (r := P.radius/2) (A j)
  let M := ∑ j, B j * ((P.radius/2)^wordDegree (actualVertexWords n I j) + D.epsilon)
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => mul_nonneg (hB0 j)
    (add_nonneg (pow_nonneg (half_pos P.radius_pos).le _) D.epsilon_pos.le)
  refine ⟨M,hM,?_⟩
  intro z hz
  have hgb (j : Fin (actualVertexCount n I)) :
      ‖actualInheritedSourceScaledFamily P s j (p+z)‖ ≤
        (P.radius/2)^wordDegree (actualVertexWords n I j) + D.epsilon := by
    have he : actualInheritedSourceScaledFamily P s j (p+z) =
        wordMonomial (actualVertexWords n I j) z + actualInheritedTranslatedTail P s p j z := by
      unfold actualInheritedTranslatedTail
      ring
    rw [he]
    exact (norm_add_le _ _).trans
      (add_le_add (wordMonomial_norm_le _ (half_pos P.radius_pos) hz) (hb j z hz))
  change ‖∑ j, actualCoordinatePolynomialFunction (A j) z *
    actualInheritedSourceScaledFamily P s j (p+z)‖ ≤ _
  calc
    _ ≤ ∑ j, ‖actualCoordinatePolynomialFunction (A j) z *
      actualInheritedSourceScaledFamily P s j (p+z)‖ := norm_sum_le _ _
    _ ≤ M := Finset.sum_le_sum fun j _ => by
      rw [norm_mul]
      exact mul_le_mul (hB j z hz) (hgb j) (norm_nonneg _) (hB0 j)

private theorem division_germ_relation (P : ActualInheritedWeightedTailData G)
    {s : ℂ} (hs : s ∈ ball 0 P.radius) (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius))
    (F : CoordinateSpace n → ℂ)
    (qf : Fin (actualVertexCount n I) → CoordinateSpace n → ℂ) (rf : CoordinateSpace n → ℂ)
    (hF : DifferentiableOn ℂ F (ball 0 (P.radius/2)))
    (hQ : ∀ j, DifferentiableOn ℂ (qf j) (ball 0 (P.radius/2)))
    (hR : DifferentiableOn ℂ rf (ball 0 (P.radius/2)))
    (he : ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
      F z = (∑ j, qf j z * (wordMonomial (actualVertexWords n I j) z +
        actualInheritedTranslatedTail P s p j z)) + rf z) :
    modelGerm (half_pos P.radius_pos) hF - modelGerm (half_pos P.radius_pos) hR ∈
      actualInheritedTranslatedIdeal P hs p hdom := by
  let hg (j : Fin (actualVertexCount n I)) := actual_coordinate_translation_differentiableOn
    (actualInheritedSourceScaledFamily_differentiableOn P hs j) p hdom
  have hprod (j : Fin (actualVertexCount n I)) : DifferentiableOn ℂ
      (fun z => qf j z * actualInheritedSourceScaledFamily P s j (p+z))
      (ball 0 (P.radius/2)) := (hQ j).mul (hg j)
  have hsum : DifferentiableOn ℂ (fun z =>
      ∑ j, qf j z * actualInheritedSourceScaledFamily P s j (p+z))
      (ball 0 (P.radius/2)) := DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) => hprod j
  have hf : DifferentiableOn ℂ (fun z =>
      (∑ j, qf j z * actualInheritedSourceScaledFamily P s j (p+z)) + rf z)
      (ball 0 (P.radius/2)) := hsum.add hR
  have heG : modelGerm (half_pos P.radius_pos) hF =
      (∑ j, modelGerm (half_pos P.radius_pos) (hQ j) *
        actualInheritedTranslatedGerm P hs p hdom j) +
          modelGerm (half_pos P.radius_pos) hR := by
    have hEq := modelGerm_eqOn (half_pos P.radius_pos) hF hf (by
      intro z hz
      have hh := he z hz
      simpa only [actualInheritedTranslatedTail, add_sub_cancel] using hh)
    have hsumG : modelGerm (half_pos P.radius_pos) hsum =
        ∑ j, modelGerm (half_pos P.radius_pos) (hQ j) *
          actualInheritedTranslatedGerm P hs p hdom j := by
      rw [modelGerm_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact modelGerm_mul (half_pos P.radius_pos) (hQ j) (hg j)
    have hadd : modelGerm (half_pos P.radius_pos) hf =
        modelGerm (half_pos P.radius_pos) hsum + modelGerm (half_pos P.radius_pos) hR := by
      change HolGerm.mk (fun z : ComplexModel n =>
        modelFunction (fun x => ∑ j, qf j x * actualInheritedSourceScaledFamily P s j (p+x)) z +
        modelFunction rf z) _ = _
      exact HolGerm.mk_add _ _ _ _
    exact hEq.trans (hadd.trans (congrArg
      (fun v : HolGerm (ComplexModel n) => v + modelGerm (half_pos P.radius_pos) hR) hsumG))
  rw [heG, add_sub_cancel_right]
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)

private theorem remainder_standard_approximation (I : Ideal (HolGerm (ComplexModel n)))
    (q : ℕ) (R : HolGerm (ComplexModel n))
    (hsupport : ∀ β ∈ actualInitialDiagram MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I),
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n R) = 0) :
    ∃ c : actualStandardIndex n (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) q → ℂ,
      R - polynomialGerm n (actualOldStandardPolynomial n I q c) ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
  let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  let c : actualStandardIndex n K q → ℂ := fun a =>
    MvPowerSeries.coeff a.val.val (actualUnshiftedTaylorAlgHom n R)
  refine ⟨c, (mem_maximal_pow_iff_coefficients q _).mpr ?_⟩
  intro β hβ
  rw [map_sub, map_sub, Taylor_oldStandard]
  apply sub_eq_zero.mpr
  by_cases hi : β ∈ actualInitialDiagram MonomialOrder.degLex K
  · rw [hsupport β hi, actualStandardLift_coefficient_outside K q c β (Or.inr hi)]
  · exact (actualStandardLift_coefficient K q c ⟨⟨β,hβ⟩,hi⟩).symm

private theorem oldStandard_surjective (P : ActualInheritedWeightedTailData G)
    {s : ℂ} (hs : s ∈ ball 0 P.radius) (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius))
    (D : ConcreteNeumannData (P.radius/2) (actualVertexWords n I))
    (hHd : ∀ j, DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j)
      (ball 0 (P.radius/2)))
    (hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
      ‖actualInheritedTranslatedTail P s p j z‖ ≤ D.epsilon) (q : ℕ) :
    Function.Surjective (actualOldStandardClassMap n I
      (actualInheritedTranslatedIdeal P hs p hdom) q) := by
  intro v
  obtain ⟨F,rfl⟩ := Ideal.Quotient.mk_surjective v
  let A := finitePolynomial q F
  let f := actualCoordinatePolynomialFunction A
  have hfd : DifferentiableOn ℂ f (ball 0 (P.radius/2)) :=
    (actualCoordinatePolynomialFunction_differentiable A).differentiableOn
  obtain ⟨M,hM,hfb⟩ := polynomial_bound (r := P.radius/2) A
  let H := actualInheritedTranslatedTail P s p
  let heads := actualVertexWords n I
  have hd := neumannSums_differentiableOn (half_pos P.radius_pos) D hHd hHb hM hfd hfb
  have hsupp := neumannSums_whole_support (half_pos P.radius_pos) D hHd hHb hM hfd hfb
  let RG := modelGerm (half_pos P.radius_pos) hd.2
  have hFR : polynomialGerm n A - RG ∈ actualInheritedTranslatedIdeal P hs p hdom := by
    rw [← modelGerm_polynomial (half_pos P.radius_pos) A]
    exact division_germ_relation P hs p hdom f
      (neumannQuotientSum (P.radius/2) heads H f)
      (neumannRemainderSum (P.radius/2) heads H f) hfd hd.1 hd.2
      (fun z hz => neumannSums_division (half_pos P.radius_pos) D hHd hHb hM hfd hfb hz)
  have hRsupp : ∀ β ∈ actualInitialDiagram MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I),
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n RG) = 0 := by
    intro β hβ
    apply hsupp.2 β
    intro hav
    exact (actualVertexWords_avoids_iff n I β).mp hav hβ
  obtain ⟨c,hRc⟩ := remainder_standard_approximation I q RG hRsupp
  have htotal : F - polynomialGerm n (actualOldStandardPolynomial n I q c) ∈
      actualInheritedTranslatedIdeal P hs p hdom ⊔
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q := by
    have he : F - polynomialGerm n (actualOldStandardPolynomial n I q c) =
        (F - polynomialGerm n A) + (polynomialGerm n A - RG) +
          (RG - polynomialGerm n (actualOldStandardPolynomial n I q c)) := by abel
    rw [he]
    exact Ideal.add_mem _
      (Ideal.add_mem _ (Ideal.mem_sup_right (finitePolynomial_remainder q F))
        (Ideal.mem_sup_left hFR)) (Ideal.mem_sup_right hRc)
  refine ⟨c,?_⟩
  change Ideal.Quotient.mk _ (polynomialGerm n (actualOldStandardPolynomial n I q c)) =
    Ideal.Quotient.mk _ F
  apply Ideal.Quotient.eq.mpr
  rw [show polynomialGerm n (actualOldStandardPolynomial n I q c) - F =
    -(F - polynomialGerm n (actualOldStandardPolynomial n I q c)) by abel]
  exact (actualInheritedTranslatedIdeal P hs p hdom ⊔
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ q).neg_mem htotal

private theorem one_weight_degree (β : Fin n →₀ ℕ) :
    Finsupp.weight (fun _ : Fin n => (1 : ℕ)) β = normalExponentDegree β := by
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum]
  rfl

private theorem tails_weight_one (P : ActualInheritedWeightedTailData G)
    {s : ℂ} (hs : s ∈ ball 0 P.radius) (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius))
    (hHd : ∀ j, DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j)
      (ball 0 (P.radius/2)))
    (hmarked : ∀ j, actualInheritedTranslatedGerm P hs p hdom j ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^
        normalExponentDegree (wordExponent (actualVertexWords n I j))) :
    ∀ j, actualUnshiftedTaylorAlgHom n
      (modelGerm (half_pos P.radius_pos) (hHd j)) ∈
        actualFormalWeightVanishing (fun _ => 1)
          (Finsupp.weight (fun _ => 1) (wordExponent (actualVertexWords n I j))) := by
  intro j β hβ
  rw [one_weight_degree] at hβ
  have hg := actual_coordinate_translation_differentiableOn
    (actualInheritedSourceScaledFamily_differentiableOn P hs j) p hdom
  have hw : DifferentiableOn ℂ (wordMonomial (actualVertexWords n I j))
      (ball 0 (P.radius/2)) :=
    (wordMonomial_differentiable (actualVertexWords n I j)).differentiableOn
  change MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n
    (modelGerm (half_pos P.radius_pos) (hg.sub hw))) = 0
  rw [modelGerm_sub (half_pos P.radius_pos) hg hw, map_sub, map_sub,
    actualTaylor_wordMonomial (half_pos P.radius_pos) (actualVertexWords n I j)]
  have hlow : normalExponentDegree β < normalExponentDegree
      (wordExponent (actualVertexWords n I j)) := by simpa only [one_weight_degree] using hβ
  have hzero := (mem_maximal_pow_iff_coefficients _ _).mp (hmarked j) β hlow
  change MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n
    (modelGerm (half_pos P.radius_pos) hg)) = 0 at hzero
  have hne : β ≠ wordExponent (actualVertexWords n I j) := by
    intro he
    rw [he] at hlow
    exact (lt_irrefl _ hlow)
  rw [hzero, MvPowerSeries.coeff_monomial, if_neg hne, sub_self]

private theorem oldStandard_injective (P : ActualInheritedWeightedTailData G)
    {s : ℂ} (hs : s ∈ ball 0 P.radius) (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius))
    (D : ConcreteNeumannData (P.radius/2) (actualVertexWords n I))
    (hHd : ∀ j, DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j)
      (ball 0 (P.radius/2)))
    (hHb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
      ‖actualInheritedTranslatedTail P s p j z‖ ≤ D.epsilon)
    (hpoly : ∀ A : Fin (actualVertexCount n I) → MvPolynomial (Fin n) ℂ,
      ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
        neumannRemainderSum (P.radius/2) (actualVertexWords n I)
          (actualInheritedTranslatedTail P s p)
          (actualInheritedTranslatedCombination P s p
            (fun j => actualCoordinatePolynomialFunction (A j))) z = 0)
    (hmarked : ∀ j, actualInheritedTranslatedGerm P hs p hdom j ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^
        normalExponentDegree (wordExponent (actualVertexWords n I j))) (q : ℕ) :
    Function.Injective (actualOldStandardClassMap n I
      (actualInheritedTranslatedIdeal P hs p hdom) q) := by
  let r := P.radius/2
  have hr : 0 < r := half_pos P.radius_pos
  let heads := actualVertexWords n I
  let H := actualInheritedTranslatedTail P s p
  let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  let γ := actualInheritedTranslatedGerm P hs p hdom
  let m := IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))
  have hker (c : actualStandardIndex n K q → ℂ)
      (hc : polynomialGerm n (actualOldStandardPolynomial n I q c) ∈
        actualInheritedTranslatedIdeal P hs p hdom ⊔ m^q) : c=0 := by
    let A := actualOldStandardPolynomial n I q c
    let f := actualCoordinatePolynomialFunction A
    have hfd : DifferentiableOn ℂ f (ball 0 r) :=
      (actualCoordinatePolynomialFunction_differentiable A).differentiableOn
    obtain ⟨v,hv,z,hz,hvz⟩ := Submodule.mem_sup.mp hc
    obtain ⟨a,ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp hv
    let Q (j : Fin (actualVertexCount n I)) := finitePolynomial q (a j)
    let B := actualInheritedTranslatedCombination P s p
      (fun j => actualCoordinatePolynomialFunction (Q j))
    have hBd := combination_hol P hs p hdom Q
    obtain ⟨MB,hMB,hBb⟩ := combination_bound P p D hHb Q
    obtain ⟨MP,hMP,hPb⟩ := polynomial_bound (r := r) A
    let Z : CoordinateSpace n → ℂ := fun x => f x - B x
    have hZd : DifferentiableOn ℂ Z (ball 0 r) := hfd.sub hBd
    have hZb : ∀ x ∈ ball (0 : CoordinateSpace n) r, ‖Z x‖ ≤ MP+MB :=
      fun x hx => (norm_sub_le _ _).trans (add_le_add (hPb x hx) (hBb x hx))
    have hZg : modelGerm hr hZd ∈ m^q := by
      rw [modelGerm_sub hr hfd hBd, modelGerm_polynomial hr A,
        combination_modelGerm P hs p hdom Q]
      have he : polynomialGerm n A - (∑ j, polynomialGerm n (Q j) * γ j) =
          z + ∑ j, (a j - polynomialGerm n (Q j)) * γ j := by
        rw [← hvz]
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib, ha]
        ring
      rw [he]
      exact Ideal.add_mem _ hz (Ideal.sum_mem _ (fun j _ =>
        Ideal.mul_mem_right _ _ (finitePolynomial_remainder q (a j))))
    have hdB := neumannSums_differentiableOn hr D hHd hHb hMB hBd hBb
    have hsB := neumannSums_whole_support hr D hHd hHb hMB hBd hBb
    have hbB := neumannSums_same_ball_norm_bounds hr D hHd hHb hMB hBd hBb
    have hdZ := neumannSums_differentiableOn hr D hHd hHb
      (add_nonneg hMP hMB) hZd hZb
    have hsZ := neumannSums_whole_support hr D hHd hHb
      (add_nonneg hMP hMB) hZd hZb
    have hbZ := neumannSums_same_ball_norm_bounds hr D hHd hHb
      (add_nonneg hMP hMB) hZd hZb
    let QB := neumannQuotientSum r heads H B
    let QZ := neumannQuotientSum r heads H Z
    let RZ := neumannRemainderSum r heads H Z
    have hQminus (j : Fin (actualVertexCount n I)) :
        DifferentiableOn ℂ (fun x => -QB j x) (ball 0 r) := (hdB.1 j).neg
    have hQms : ∀ j β, ¬ AvoidsCones ((List.ofFn heads).take j.val)
        (β + wordExponent (heads j)) → MvPowerSeries.coeff β
          (actualUnshiftedTaylorAlgHom n (modelGerm hr (hQminus j))) = 0 := by
      intro j β hβ
      rw [modelGerm_neg hr (hdB.1 j), map_neg, map_neg, hsB.1 j β hβ, neg_zero]
    have hPs : ∀ β, ¬ AvoidsCones (List.ofFn heads) β → MvPowerSeries.coeff β
        (actualUnshiftedTaylorAlgHom n (modelGerm hr hfd)) = 0 := by
      intro β hβ
      rw [modelGerm_polynomial, Taylor_oldStandard]
      apply actualStandardLift_coefficient_outside K q c β
      right
      by_contra hnot
      exact hβ ((actualVertexWords_avoids_iff n I β).mpr hnot)
    let CB := (2 * ∑ j, D.quotientConstant j) * MB
    let CZ := (2 * ∑ j, D.quotientConstant j) * (MP+MB)
    have hCB : 0 ≤ CB := mul_nonneg
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => D.quotientConstant_nonneg j)) hMB
    have hCZ : 0 ≤ CZ := mul_nonneg
      (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => D.quotientConstant_nonneg j))
      (add_nonneg hMP hMB)
    have hQmb : ∀ x ∈ ball (0 : CoordinateSpace n) r,
        ∑ j, ‖-QB j x‖ ≤ CB := by
      intro x hx
      simpa only [norm_neg] using hbB.2.1 x hx
    have hdivm : ∀ x ∈ ball (0 : CoordinateSpace n) r,
        Z x = (∑ j, (-QB j x) * (wordMonomial (heads j) x + H j x)) + f x := by
      intro x hx
      have he := neumannSums_division hr D hHd hHb hMB hBd hBb hx
      rw [hpoly Q x hx, add_zero] at he
      change B x = ∑ j, QB j x * (wordMonomial (heads j) x + H j x) at he
      change f x - B x = _
      rw [he]
      simp only [neg_mul, Finset.sum_neg_distrib]
      ring
    have hdivZ : ∀ x ∈ ball (0 : CoordinateSpace n) r,
        Z x = (∑ j, QZ j x * (wordMonomial (heads j) x + H j x)) + RZ x :=
      fun x hx => neumannSums_division hr D hHd hHb
        (add_nonneg hMP hMB) hZd hZb hx
    have hu := actual_bounded_supported_neumann_division_unique hr heads D H
      QZ (fun j x => -QB j x) RZ f Z hHd hHb hdZ.1 hQminus hdZ.2 hfd
      hsZ.1 hQms hsZ.2 hPs CZ CB hCZ hCB hbZ.2.1 hQmb hdivZ hdivm
    have hREq : modelGerm hr hdZ.2 = polynomialGerm n A :=
      (modelGerm_eqOn hr hdZ.2 hfd (fun x hx => (hu x hx).2)).trans
        (modelGerm_polynomial hr A)
    have hHw := tails_weight_one P hs p hdom hHd hmarked
    have hZw : actualUnshiftedTaylorAlgHom n (modelGerm hr hZd) ∈
        actualFormalWeightVanishing (fun _ => 1) q := by
      intro β hβ
      exact (mem_maximal_pow_iff_coefficients q _).mp hZg β
        (by simpa only [one_weight_degree] using hβ)
    have hfilt := (neumannSums_weight_vanishing hr D hHd hHb
      (add_nonneg hMP hMB) hZd hZb (fun _ => 1) q hHw hZw).2
    funext α
    have he := hfilt α.val.val (by
      simpa only [one_weight_degree] using α.val.property)
    rw [hREq, Taylor_oldStandard, actualStandardLift_coefficient] at he
    exact he
  intro c d hcd
  have hz : actualOldStandardClassMap n I (actualInheritedTranslatedIdeal P hs p hdom) q (c-d)=0 := by
    rw [map_sub,hcd,sub_self]
  have hmem : polynomialGerm n (actualOldStandardPolynomial n I q (c-d)) ∈
      actualInheritedTranslatedIdeal P hs p hdom ⊔ m^q :=
    Ideal.Quotient.eq_zero_iff_mem.mp hz
  exact sub_eq_zero.mp (hker (c-d) hmem)

/-- ONLY the original ideal and SAME full inherited family produce one
actual neighborhood for ALL literal old-standard analytic jet maps.
The map is always surjective; natural SAME-member marked orders give
injectivity and every true native HS value, with q=ell+1. -/
theorem exists_actual_inherited_neighborhood_standard_jets
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I))
    (hspan : Ideal.span (range G.germs) = I) :
    ∃ (P : ActualInheritedWeightedTailData G) (s : ℂ), s ≠ 0 ∧
      ∃ (hs : s ∈ ball 0 P.radius)
        (D₀ : ConcreteNeumannData P.radius (actualVertexWords n I))
        (D₁ : ConcreteNeumannData (P.radius/2) (actualVertexWords n I)) (δ : ℝ),
        0 < δ ∧
        (∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
          ‖actualInheritedSourceScaledTail P s j z‖ ≤ D₀.epsilon) ∧
        ∀ p ∈ ball (0 : CoordinateSpace n) δ,
          ∃ hdom : MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius),
            (∀ j, DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j)
              (ball 0 (P.radius/2))) ∧
            (∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
              ‖actualInheritedTranslatedTail P s p j z‖ ≤ D₁.epsilon) ∧
            let J := actualInheritedTranslatedIdeal P hs p hdom
            (∀ q : ℕ, Function.Surjective (actualOldStandardClassMap n I J q)) ∧
            ((∀ j, actualInheritedTranslatedGerm P hs p hdom j ∈
              IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^
                normalExponentDegree (actualVertexEnumeration n I j).val) →
              (∀ q : ℕ, Function.Injective (actualOldStandardClassMap n I J q)) ∧
              ∀ ℓ : ℕ, hilbertSamuelValue J ℓ = hilbertSamuelValue I ℓ) := by
  obtain ⟨P,s,hs0,hs,D₀,D₁,δ,hδ,hsource,hnear⟩ :=
    exists_actual_inherited_uniform_translated_neumann_division I G hspan
  refine ⟨P,s,hs0,hs,D₀,D₁,δ,hδ,hsource,?_⟩
  intro p hp
  obtain ⟨hdom,hHd,hHb,hpoly⟩ := hnear p hp
  refine ⟨hdom,hHd,hHb,?_,?_⟩
  · exact fun q => oldStandard_surjective P hs p hdom D₁ hHd hHb q
  · intro hmarked
    have hmarked' : ∀ j, actualInheritedTranslatedGerm P hs p hdom j ∈
        IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^
          normalExponentDegree (wordExponent (actualVertexWords n I j)) := by
      simpa only [actualVertexWords, wordExponent_wordOfExponent] using hmarked
    have hinj := fun q => oldStandard_injective P hs p hdom D₁ hHd hHb
      (fun A z hz => (hpoly A z hz).1) hmarked' q
    refine ⟨hinj,?_⟩
    intro ℓ
    let J := actualInheritedTranslatedIdeal P hs p hdom
    let K := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
    let E := LinearEquiv.ofBijective (actualOldStandardClassMap n I J (ℓ+1))
      ⟨hinj (ℓ+1), oldStandard_surjective P hs p hdom D₁ hHd hHb (ℓ+1)⟩
    calc
      hilbertSamuelValue J ℓ = Module.finrank ℂ
          (HolGerm (ComplexModel n) ⧸
            (J ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ (ℓ+1))) := rfl
      _ = Module.finrank ℂ (actualStandardIndex n K (ℓ+1) → ℂ) := E.finrank_eq.symm
      _ = Fintype.card (actualStandardIndex n K (ℓ+1)) := Module.finrank_fintype_fun_eq_card ℂ
      _ = genuineFormalHilbertSamuelValue n K ℓ :=
        (genuineFormalHilbertSamuelValue_eq_card_standardIndex K ℓ).symm
      _ = hilbertSamuelValue I ℓ :=
        (hilbertSamuelValue_eq_actual_unshifted_formal_extension n I ℓ).symm

end
end Hironaka.HironakaActualInheritedNeighborhoodStandardJets
