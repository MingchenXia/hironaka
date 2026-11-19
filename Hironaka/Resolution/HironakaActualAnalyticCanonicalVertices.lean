import Hironaka.Resolution.HironakaActualOriginalScaledAnalyticDivision
import Hironaka.Resolution.HironakaActualDiagonalTaylor

/-!
# Actual analytic preimages of the SAME canonical reduced formal vertices

Actual Cauchy--Neumann division of a finite polynomial, followed by the genuine
inverse diagonal map, produces an original ideal member.  Its entire diagram
coefficients identify its Taylor series with the existing canonical series.
Neither canonical convergence nor a scaled/original ideal identity is an input.
-/

set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualAnalyticCanonicalVertices

noncomputable section
attribute [local instance] Classical.propDecidable

open HolGerm HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalCoordinatePowerDivision
  HironakaActualOriginalFormalTaylor HironakaActualFormalIdealContraction
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFiniteDegLexWeights HironakaActualWeightedScaling
  HironakaActualWeightedVertexSmallTails HironakaActualCauchyCoordinateDivision
  HironakaActualCauchyTaylorSupport HironakaActualCauchyMonomialDivision
  HironakaActualCauchyEnumeratedPartition HironakaActualOriginalScaledAnalyticDivision
  HironakaActualDiagonalTaylor

variable {n : ℕ}

private theorem weighted_joint_eq_diagonal (W : Fin n → ℕ) (s : ℂ) (z : ComplexModel n) :
    actualWeightedScalingMap W
        (jointPoint n (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) z,s)) =
      actualDiagonalMap (fun i => s ^ W i) z := by
  ext i
  let p : CoordinateSpace n × ℂ := (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n) z,s)
  have hp : jointPoint n p (parameterIndex n) = s := by
    change (Fin.addCases (motive := fun _ : Fin (n+1) => CoordinateSpace n × ℂ →L[ℂ] ℂ)
      (fun j : Fin n => (ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
      (fun _ : Fin 1 => ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ) ((0 : Fin 1).natAdd n)) p = s
    rw [Fin.addCases_right]
    rfl
  have hb : jointPoint n p (i.castAdd 1) = z i := by
    change (Fin.addCases (motive := fun _ : Fin (n+1) => CoordinateSpace n × ℂ →L[ℂ] ℂ)
      (fun j : Fin n => (ContinuousLinearMap.proj j).comp
        (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
      (fun _ : Fin 1 => ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ) (i.castAdd 1)) p = z i
    rw [Fin.addCases_left]
    rfl
  change jointPoint n p (parameterIndex n) ^ W i * jointPoint n p (i.castAdd 1) = s ^ W i * z i
  rw [hp,hb]

private theorem normalizedScaledRepresentative_hol
    {I : Ideal (HolGerm (ComplexModel n))} (P : ActualWeightedVertexSmallTailData n I)
    (a : ActualVertexIndex n I) {s : ℂ} (hs : s ∈ ball 0 P.radius) :
    DifferentiableOn ℂ (normalizedScaledRepresentative P a s) (ball 0 P.radius) := by
  have hgraph : Differentiable ℂ (fun z : CoordinateSpace n => (z,s)) :=
    differentiable_id.prodMk (differentiable_const s)
  have hd := (P.scaled_hol a).comp hgraph.differentiableOn (fun z hz => ⟨hz,hs⟩)
  unfold normalizedScaledRepresentative
  simp only [div_eq_mul_inv]
  exact hd.mul_const ((s ^ weightedDegree (degLexWeight n P.germs.degreeBound) a.val)⁻¹)

/-- The normalized actual representative is literally the original germ's
actual diagonal pullback times its normalization constant. -/
private theorem modelGerm_normalizedScaledRepresentative
    {I : Ideal (HolGerm (ComplexModel n))} (P : ActualWeightedVertexSmallTailData n I)
    (a : ActualVertexIndex n I) {s : ℂ} (hs : s ∈ ball 0 P.radius) :
    modelGerm P.radius_pos (normalizedScaledRepresentative_hol P a hs) =
      HolGerm.constHom ((s ^ weightedDegree (degLexWeight n P.germs.degreeBound) a.val)⁻¹) *
        actualDiagonalPullback (fun i => s ^ degLexWeight n P.germs.degreeBound i)
          (P.germs.generator a) := by
  rw [← P.representative_eq a]
  unfold actualDiagonalPullback
  rw [compAlgHom_mk,← HolGerm.mk_const,← HolGerm.mk_mul]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by
    simp only [modelFunction,Function.comp_apply,normalizedScaledRepresentative,
      weighted_joint_eq_diagonal,div_eq_mul_inv,mul_comm]

private theorem modelGerm_eq_sum_mul_add
    {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 < R)
    {h r : CoordinateSpace n → ℂ} {q G : ι → CoordinateSpace n → ℂ}
    (hh : DifferentiableOn ℂ h (ball 0 R))
    (hq : ∀ j, DifferentiableOn ℂ (q j) (ball 0 R))
    (hG : ∀ j, DifferentiableOn ℂ (G j) (ball 0 R))
    (hr : DifferentiableOn ℂ r (ball 0 R))
    (he : ∀ z ∈ ball (0 : CoordinateSpace n) R, h z = ∑ j, q j z * G j z + r z) :
    modelGerm hR hh = ∑ j, modelGerm hR (hq j) * modelGerm hR (hG j) + modelGerm hR hr := by
  have hp (j : ι) := eventually_differentiableAt_mul
    (modelFunction_holAt hR (hq j)) (modelFunction_holAt hR (hG j))
  have hsum := eventually_differentiableAt_sum Finset.univ hp
  have hall := eventually_differentiableAt_add hsum (modelFunction_holAt hR hr)
  change HolGerm.mk (modelFunction h) (modelFunction_holAt hR hh) = _
  calc
    _ = HolGerm.mk (fun z : ComplexModel n =>
        ∑ j, modelFunction (q j) z * modelFunction (G j) z + modelFunction r z) hall := by
      apply HolGerm.mk_eq_mk_iff.mpr
      let e := EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)
      have ht : Tendsto e (nhds (0 : ComplexModel n)) (nhds (0 : CoordinateSpace n)) := by
        simpa only [map_zero] using e.continuous.tendsto (0 : ComplexModel n)
      filter_upwards [ht.eventually (isOpen_ball.mem_nhds (mem_ball_self hR))] with z hz
      exact he (e z) hz
    _ = _ := by
      rw [HolGerm.mk_add _ _ hsum (modelFunction_holAt hR hr),
        HolGerm.mk_sum Finset.univ _ hp]
      congr 1

/-- The original analytic ideal alone produces an actual analytic preimage of
each SAME canonical reduced formal vertex, including its whole Taylor series. -/
theorem exists_actualAnalyticCanonicalVertex (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (a : ActualVertexIndex n I) :
    ∃ B ∈ I, actualUnshiftedTaylorAlgHom n B = actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a := by
  obtain ⟨P,s,hs0,hs,hdivision⟩ := exists_actualOriginal_scaled_analytic_division n I
  let W := degLexWeight n P.germs.degreeBound
  let c : Fin n → ℂ := fun i => s ^ W i
  have hc (i : Fin n) : c i ≠ 0 := pow_ne_zero _ hs0
  let w := wordOfExponent a.val
  have hh : DifferentiableOn ℂ (wordMonomial w) (ball 0 P.radius) :=
    (wordMonomial_differentiable w).differentiableOn
  obtain ⟨q,r,hq,hr,he,_hqSupport,hrSupport⟩ :=
    hdivision (P.radius ^ wordDegree w) (wordMonomial w) hh
      (fun z hz => wordMonomial_norm_le w P.radius_pos hz)
  let Q (j : Fin (actualVertexCount n I)) := modelGerm P.radius_pos (hq j)
  let rG := modelGerm P.radius_pos hr
  let G (j : Fin (actualVertexCount n I)) :=
    normalizedScaledRepresentative P (actualVertexEnumeration n I j) s
  have hG (j : Fin (actualVertexCount n I)) : DifferentiableOn ℂ (G j) (ball 0 P.radius) :=
    normalizedScaledRepresentative_hol P _ hs
  let GG (j : Fin (actualVertexCount n I)) := modelGerm P.radius_pos (hG j)
  have hGG (j : Fin (actualVertexCount n I)) :
      GG j = HolGerm.constHom ((s ^ weightedDegree W (actualVertexEnumeration n I j).val)⁻¹) *
        actualDiagonalPullback c (P.germs.generator (actualVertexEnumeration n I j)) :=
    modelGerm_normalizedScaledRepresentative P _ hs
  let Fs := modelGerm P.radius_pos hh - rG
  have hFs : Fs = ∑ j, Q j * GG j := by
    apply sub_eq_iff_eq_add.mpr
    exact modelGerm_eq_sum_mul_add P.radius_pos hh hq hG hr he
  let B := HolGerm.constHom (s ^ weightedDegree W a.val) *
    actualDiagonalPullback (fun i => (c i)⁻¹) Fs
  have hB : B ∈ I := by
    apply I.mul_mem_left
    rw [hFs,map_sum]
    apply I.sum_mem
    intro j _
    rw [map_mul,hGG,map_mul,actualDiagonalPullback_const,actualDiagonalPullback_inverse c hc]
    exact I.mul_mem_left _ (I.mul_mem_left _ (P.germs.member (actualVertexEnumeration n I j)))
  have hmono : actualUnshiftedTaylorAlgHom n (modelGerm P.radius_pos hh) =
      MvPowerSeries.monomial a.val 1 := by
    simpa only [w,wordExponent_wordOfExponent] using
      actualTaylor_wordMonomial P.radius_pos (wordOfExponent a.val)
  have hFsCoeff (b : Fin n →₀ ℕ)
      (hb : b ∈ actualInitialDiagram MonomialOrder.degLex
        (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)) :
      MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n Fs) = if b = a.val then 1 else 0 := by
    simp only [Fs,rG,map_sub,hmono,hrSupport b hb,sub_zero,MvPowerSeries.coeff_monomial]
  refine ⟨B,hB,?_⟩
  apply actualReducedVertexSeries_unique MonomialOrder.degLex _ a _ (Ideal.mem_map_of_mem _ hB)
  intro b hb
  change MvPowerSeries.coeff b (actualUnshiftedTaylorAlgHom n
    (HolGerm.constHom (s ^ weightedDegree W a.val) *
      actualDiagonalPullback (fun i => (c i)⁻¹) Fs)) = _
  have hconst (u : ℂ) : actualUnshiftedTaylorAlgHom n (HolGerm.constHom u) = MvPowerSeries.C u :=
    (actualUnshiftedTaylorAlgHom n).commutes u
  rw [map_mul,hconst,MvPowerSeries.coeff_C_mul,coeff_actualDiagonalPullback,hFsCoeff b hb]
  by_cases hba : b = a.val
  · subst b
    simp only [ite_true,mul_one]
    exact weighted_inverse_monomial_scalar W s hs0 a.val
  · simp only [if_neg hba,mul_zero]

private theorem unshifted_extension_injective (n : ℕ) :
    Function.Injective (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom) := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    Function.Injective (Ideal.map f.toRingHom)
  have hc {m : ℕ} (hm : m = n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ]
        MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) (original_formal_ideal_extension_injective n)

/-- The actual canonical analytic family has the SAME finite labels and whole
canonical Taylor series, and it generates the WHOLE original analytic ideal. -/
theorem exists_actualAnalyticCanonicalVertexFamily (n : ℕ) (I : Ideal (HolGerm (ComplexModel n))) :
    ∃ B : ActualVertexIndex n I → HolGerm (ComplexModel n),
      (∀ a, B a ∈ I ∧ actualUnshiftedTaylorAlgHom n (B a) = actualReducedVertexSeries MonomialOrder.degLex
          (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a ∧
        ∃ hne : actualUnshiftedTaylorAlgHom n (B a) ≠ 0,
          actualInitialExponent MonomialOrder.degLex (actualUnshiftedTaylorAlgHom n (B a)) hne = a.val ∧
          MvPowerSeries.coeff a.val (actualUnshiftedTaylorAlgHom n (B a)) = 1) ∧
      Ideal.span (range B) = I := by
  choose B hmem hTaylor using exists_actualAnalyticCanonicalVertex n I
  let J := Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I
  refine ⟨B,?_,?_⟩
  · intro a
    have hne : actualUnshiftedTaylorAlgHom n (B a) ≠ 0 := by
      rw [hTaylor a]
      exact actualReducedVertexSeries_ne_zero MonomialOrder.degLex J a
    refine ⟨hmem a,hTaylor a,hne,?_,?_⟩
    · apply actualInitialExponent_eq_of_coefficients
      · rw [hTaylor a,actualReducedVertexSeries_coefficient]
        exact one_ne_zero
      · intro b hb
        rw [hTaylor a]
        exact actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex J a b hb
    · rw [hTaylor a,actualReducedVertexSeries_coefficient]
  · apply unshifted_extension_injective n
    rw [Ideal.map_span,← Set.range_comp]
    change Ideal.span (range (fun a => actualUnshiftedTaylorAlgHom n (B a))) = J
    have he : (fun a => actualUnshiftedTaylorAlgHom n (B a)) =
        actualReducedVertexSeries MonomialOrder.degLex J := funext hTaylor
    rw [he]
    exact (actual_formal_ideal_eq_span_reduced_vertex_series MonomialOrder.degLex J).symm

end

end Hironaka.HironakaActualAnalyticCanonicalVertices
