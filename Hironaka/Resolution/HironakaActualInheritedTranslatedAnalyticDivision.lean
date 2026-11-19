import Hironaka.Resolution.HironakaActualInheritedUniformTranslatedTails
import Hironaka.Resolution.HironakaActualCauchyNeumannSameBallBounds
import Hironaka.Resolution.HironakaActualBoundedSupportedNeumannUniqueness
import Mathlib.Algebra.MvPolynomial.Eval

/-! Literal whole translated division for the SAME inherited original family.
All source/target domains and Cauchy data are chosen before any polynomial
numerator. Original hspan produces source remainder zero internally; real
owner translation and same-ball bounded uniqueness identify BOTH actual
quotient tuples and remainders. No nearby diagram or target-HS certificate.
Initial SOURCE-ONLY draft for BP3; not elaborated or accepted. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology

namespace Hironaka.HironakaActualInheritedTranslatedAnalyticDivision
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaActualCoefficientPresentationCentrePower
  HironakaActualCauchyCoordinateDivision HironakaActualCauchyTaylorSupport
  HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition
  HironakaActualCauchyEnumeratedPartition HironakaActualCauchyNeumannDivision
  HironakaActualCauchyNeumannSameBallBounds HironakaActualRelativeNormalJetDivision
  HironakaActualInheritedSmallTails HironakaActualOriginalScaledAnalyticDivision
  HironakaActualInheritedSourceCauchyRemainder HironakaActualInheritedUniformTranslatedTails
  HironakaActualTranslatedCauchyOwnerSupport HironakaActualBoundedSupportedNeumannUniqueness

variable {n : ℕ} {I : Ideal (HolGerm (ComplexModel n))}
variable {G : ActualAnalyticInheritedFamily n 0
  (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I)}

def actualCoordinatePolynomialFunction (P : MvPolynomial (Fin n) ℂ)
    (z : CoordinateSpace n) : ℂ := MvPolynomial.aeval z P

theorem actualCoordinatePolynomialFunction_differentiable (P : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (actualCoordinatePolynomialFunction P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have hc : actualCoordinatePolynomialFunction (MvPolynomial.C c) =
          (fun _ : CoordinateSpace n => c) := by
        funext z
        simp [actualCoordinatePolynomialFunction]
      rw [hc]
      exact differentiable_const c
  | add p q hp hq =>
      have ha : actualCoordinatePolynomialFunction (p+q) =
          actualCoordinatePolynomialFunction p + actualCoordinatePolynomialFunction q := by
        funext z
        exact map_add (MvPolynomial.aeval z) p q
      rw [ha]
      exact hp.add hq
  | mul_X p i hp =>
      have hm : actualCoordinatePolynomialFunction (p * MvPolynomial.X i) =
          actualCoordinatePolynomialFunction p * (fun z : CoordinateSpace n => z i) := by
        funext z
        simp only [actualCoordinatePolynomialFunction, map_mul, MvPolynomial.aeval_X,
          Pi.mul_apply]
      rw [hm]
      exact hp.mul (ContinuousLinearMap.proj i : CoordinateSpace n →L[ℂ] ℂ).differentiable

def actualInheritedTranslatedCombination (P : ActualInheritedWeightedTailData G)
    (s : ℂ) (p : CoordinateSpace n)
    (A : Fin (actualVertexCount n I) → CoordinateSpace n → ℂ)
    (z : CoordinateSpace n) : ℂ :=
  ∑ j, A j z * actualInheritedSourceScaledFamily P s j (p+z)

private theorem translated_combination_eq_source
    (P : ActualInheritedWeightedTailData G) (s : ℂ) (p : CoordinateSpace n)
    (A : Fin (actualVertexCount n I) → CoordinateSpace n → ℂ) (z : CoordinateSpace n) :
    actualInheritedTranslatedCombination P s p A z =
      actualInheritedSourceCombination P s (fun j x => A j (x-p)) (p+z) := by
  unfold actualInheritedTranslatedCombination actualInheritedSourceCombination
  apply Finset.sum_congr rfl
  intro j _
  have he : (p+z)-p = z := by abel
  dsimp only
  rw [he]

private theorem exists_bounded_source_combination
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs0 : s ≠ 0)
    (hs : s ∈ ball 0 P.radius)
    (D : ConcreteNeumannData P.radius (actualVertexWords n I))
    (hsmall : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
      ‖actualInheritedSourceScaledTail P s j z‖ ≤ D.epsilon)
    (A : Fin (actualVertexCount n I) → CoordinateSpace n → ℂ)
    (hA : ∀ j, Differentiable ℂ (A j)) (p : CoordinateSpace n) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
      ‖actualInheritedSourceCombination P s (fun j x => A j (x-p)) z‖ ≤ M := by
  have hAc (j : Fin (actualVertexCount n I)) :
      Continuous (fun x : CoordinateSpace n => A j (x-p)) :=
    (hA j).continuous.comp (continuous_id.sub continuous_const)
  choose B hB using fun j : Fin (actualVertexCount n I) =>
    (isCompact_closedBall (0 : CoordinateSpace n) P.radius).exists_bound_of_continuousOn
      (hAc j).continuousOn
  let b (j : Fin (actualVertexCount n I)) := max 0 (B j)
  have hb (j : Fin (actualVertexCount n I)) : 0 ≤ b j := le_max_left _ _
  let M := ∑ j, b j * (P.radius ^ wordDegree (actualVertexWords n I j) + D.epsilon)
  have hM : 0 ≤ M := Finset.sum_nonneg fun j _ => mul_nonneg (hb j)
    (add_nonneg (pow_nonneg P.radius_pos.le _) D.epsilon_pos.le)
  refine ⟨M,hM,?_⟩
  intro z hz
  have hAb (j : Fin (actualVertexCount n I)) : ‖A j (z-p)‖ ≤ b j :=
    (hB j z (ball_subset_closedBall hz)).trans (le_max_right _ _)
  have hgb (j : Fin (actualVertexCount n I)) :
      ‖actualInheritedSourceScaledFamily P s j z‖ ≤
        P.radius ^ wordDegree (actualVertexWords n I j) + D.epsilon := by
    rw [actualInheritedSourceScaledFamily_eq_monomial_add_tail P hs0 hs j hz]
    exact (norm_add_le _ _).trans
      (add_le_add (wordMonomial_norm_le _ P.radius_pos hz) (hsmall j z hz))
  change ‖∑ j, A j (z-p) * actualInheritedSourceScaledFamily P s j z‖ ≤ _
  calc
    _ ≤ ∑ j, ‖A j (z-p) * actualInheritedSourceScaledFamily P s j z‖ := norm_sum_le _ _
    _ ≤ ∑ j, b j * (P.radius ^ wordDegree (actualVertexWords n I j) + D.epsilon) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul (hAb j) (hgb j) (norm_nonneg _) (hb j)

private theorem literal_translated_neumann_division
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I))
    (hspan : Ideal.span (range G.germs) = I)
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs0 : s ≠ 0)
    (hs : s ∈ ball 0 P.radius)
    (D₀ : ConcreteNeumannData P.radius (actualVertexWords n I))
    (D₁ : ConcreteNeumannData (P.radius/2) (actualVertexWords n I))
    (hsource : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
      ‖actualInheritedSourceScaledTail P s j z‖ ≤ D₀.epsilon)
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius))
    (htd : ∀ j, DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j)
      (ball 0 (P.radius/2)))
    (htb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
      ‖actualInheritedTranslatedTail P s p j z‖ ≤ D₁.epsilon)
    (A : Fin (actualVertexCount n I) → CoordinateSpace n → ℂ)
    (hA : ∀ j, Differentiable ℂ (A j)) :
    ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
      neumannRemainderSum (P.radius/2) (actualVertexWords n I)
        (actualInheritedTranslatedTail P s p) (actualInheritedTranslatedCombination P s p A) z = 0 ∧
      ∀ j, neumannQuotientSum (P.radius/2) (actualVertexWords n I)
        (actualInheritedTranslatedTail P s p) (actualInheritedTranslatedCombination P s p A) j z =
          neumannQuotientSum P.radius (actualVertexWords n I) (actualInheritedSourceScaledTail P s)
            (actualInheritedSourceCombination P s (fun j x => A j (x-p))) j (p+z) := by
  let w := actualVertexWords n I
  let H₀ := actualInheritedSourceScaledTail P s
  let H₁ := actualInheritedTranslatedTail P s p
  let F₀ := actualInheritedSourceCombination P s (fun j x => A j (x-p))
  let F₁ := actualInheritedTranslatedCombination P s p A
  have hH₀ (j : Fin (actualVertexCount n I)) : DifferentiableOn ℂ (H₀ j) (ball 0 P.radius) :=
    actualInheritedSourceScaledTail_differentiableOn P hs j
  have hAs (j : Fin (actualVertexCount n I)) :
      DifferentiableOn ℂ (fun x => A j (x-p)) (ball 0 P.radius) :=
    ((hA j).comp (differentiable_id.sub_const p)).differentiableOn
  have hF₀ : DifferentiableOn ℂ F₀ (ball 0 P.radius) :=
    DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) =>
      (hAs j).mul (actualInheritedSourceScaledFamily_differentiableOn P hs j)
  obtain ⟨M,hM,hF₀b⟩ := exists_bounded_source_combination P hs0 hs D₀ hsource A hA p
  have hF₁ : DifferentiableOn ℂ F₁ (ball 0 (P.radius/2)) :=
    DifferentiableOn.fun_sum fun j (_hj : j ∈ Finset.univ) => (hA j).differentiableOn.mul
      (actual_coordinate_translation_differentiableOn
        (actualInheritedSourceScaledFamily_differentiableOn P hs j) p hdom)
  have hF₁b : ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2), ‖F₁ z‖ ≤ M := by
    intro z hz
    rw [show F₁ z = F₀ (p+z) from translated_combination_eq_source P s p A z]
    exact hF₀b (p+z) (hdom hz)
  have hd₀ := neumannSums_differentiableOn P.radius_pos D₀ hH₀ hsource hM hF₀ hF₀b
  have hd₁ := neumannSums_differentiableOn (half_pos P.radius_pos) D₁ htd htb hM hF₁ hF₁b
  have hs₀ := neumannSums_whole_support P.radius_pos D₀ hH₀ hsource hM hF₀ hF₀b
  have hs₁ := neumannSums_whole_support (half_pos P.radius_pos) D₁ htd htb hM hF₁ hF₁b
  have hb₀ := neumannSums_same_ball_norm_bounds P.radius_pos D₀ hH₀ hsource hM hF₀ hF₀b
  have hb₁ := neumannSums_same_ball_norm_bounds (half_pos P.radius_pos) D₁ htd htb hM hF₁ hF₁b
  have hr₀ := actual_inherited_source_neumann_remainder_eq_zero I G hspan P hs0 hs D₀
    hsource (fun j x => A j (x-p)) hAs M hM hF₀b
  let q₀ := neumannQuotientSum P.radius w H₀ F₀
  let q₁ := neumannQuotientSum (P.radius/2) w H₁ F₁
  let r₁ := neumannRemainderSum (P.radius/2) w H₁ F₁
  let qt (j : Fin (actualVertexCount n I)) (z : CoordinateSpace n) := q₀ j (p+z)
  have hqt (j : Fin (actualVertexCount n I)) :
      DifferentiableOn ℂ (qt j) (ball 0 (P.radius/2)) :=
    actual_coordinate_translation_differentiableOn (hd₀.1 j) p hdom
  have hqts : ∀ j β, ¬ AvoidsCones ((List.ofFn w).take j.val) (β+wordExponent (w j)) →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n
        (modelGerm (half_pos P.radius_pos) (hqt j))) = 0 := by
    intro j β hβ
    exact actual_translated_cauchy_owner_support P.radius_pos (half_pos P.radius_pos)
      w j (q₀ j) (hd₀.1 j) (hs₀.1 j) p hdom β hβ
  have hzD : DifferentiableOn ℂ (fun _ : CoordinateSpace n => (0 : ℂ))
      (ball 0 (P.radius/2)) := (differentiable_const _).differentiableOn
  have hzG : modelGerm (half_pos P.radius_pos) hzD = 0 := by
    change HolGerm.mk (fun _ : ComplexModel n => (0 : ℂ)) _ = 0
    exact HolGerm.mk_zero
  have hzs : ∀ β : Fin n →₀ ℕ, ¬ AvoidsCones (List.ofFn w) β →
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n
        (modelGerm (half_pos P.radius_pos) hzD)) = 0 := by
    intro β _
    rw [hzG, map_zero, map_zero]
  let M₀ := (2 * ∑ j, D₀.quotientConstant j) * M
  let M₁ := (2 * ∑ j, D₁.quotientConstant j) * M
  have hM₀ : 0 ≤ M₀ := mul_nonneg
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => D₀.quotientConstant_nonneg j)) hM
  have hM₁ : 0 ≤ M₁ := mul_nonneg
    (mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => D₁.quotientConstant_nonneg j)) hM
  have hqtb : ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2), ∑ j, ‖qt j z‖ ≤ M₀ :=
    fun z hz => hb₀.2.1 (p+z) (hdom hz)
  have hdivt : ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
      F₁ z = (∑ j, qt j z * (wordMonomial (w j) z + H₁ j z)) + 0 := by
    intro z hz
    have hpz := hdom hz
    calc
      F₁ z = F₀ (p+z) := translated_combination_eq_source P s p A z
      _ = (∑ j, q₀ j (p+z) * (wordMonomial (w j) (p+z) + H₀ j (p+z))) +
          neumannRemainderSum P.radius w H₀ F₀ (p+z) :=
        neumannSums_division P.radius_pos D₀ hH₀ hsource hM hF₀ hF₀b hpz
      _ = _ := by
        rw [hr₀ (p+z) hpz]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        rw [← actualInheritedSourceScaledFamily_eq_monomial_add_tail P hs0 hs j hpz]
        dsimp only [H₁, actualInheritedTranslatedTail]
        ring
  have hdiv₁ : ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
      F₁ z = (∑ j, q₁ j z * (wordMonomial (w j) z + H₁ j z)) + r₁ z :=
    fun z hz => neumannSums_division (half_pos P.radius_pos) D₁ htd htb hM hF₁ hF₁b hz
  have hu := actual_bounded_supported_neumann_division_unique (half_pos P.radius_pos)
    w D₁ H₁ q₁ qt r₁ (fun _ => 0) F₁ htd htb hd₁.1 hqt hd₁.2 hzD
    hs₁.1 hqts hs₁.2 hzs M₁ M₀ hM₁ hM₀ hb₁.2.1 hqtb hdiv₁ hdivt
  intro z hz
  exact ⟨(hu z hz).2,(hu z hz).1⟩

/-- ORIGINAL I and the SAME inherited full family choose ONE scale, both
fixed Cauchy balls and ONE actual parameter neighborhood before ALL polynomial
numerators. Both literal target Neumann outputs are identified with the real
translated source outputs. No target head, diagram, order or HS premise. -/
theorem exists_actual_inherited_uniform_translated_neumann_division
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I))
    (hspan : Ideal.span (range G.germs) = I) :
    ∃ (P : ActualInheritedWeightedTailData G) (s : ℂ), s ≠ 0 ∧ s ∈ ball 0 P.radius ∧
      ∃ (D₀ : ConcreteNeumannData P.radius (actualVertexWords n I))
        (D₁ : ConcreteNeumannData (P.radius/2) (actualVertexWords n I)) (δ : ℝ),
        0 < δ ∧
        (∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
          ‖actualInheritedSourceScaledTail P s j z‖ ≤ D₀.epsilon) ∧
        ∀ p ∈ ball (0 : CoordinateSpace n) δ,
          MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius) ∧
          (∀ j, DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j)
            (ball 0 (P.radius/2))) ∧
          (∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
            ‖actualInheritedTranslatedTail P s p j z‖ ≤ D₁.epsilon) ∧
          ∀ Q : Fin (actualVertexCount n I) → MvPolynomial (Fin n) ℂ,
            ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
              neumannRemainderSum (P.radius/2) (actualVertexWords n I)
                (actualInheritedTranslatedTail P s p)
                (actualInheritedTranslatedCombination P s p
                  (fun j => actualCoordinatePolynomialFunction (Q j))) z = 0 ∧
              ∀ j, neumannQuotientSum (P.radius/2) (actualVertexWords n I)
                (actualInheritedTranslatedTail P s p)
                (actualInheritedTranslatedCombination P s p
                  (fun j => actualCoordinatePolynomialFunction (Q j))) j z =
                neumannQuotientSum P.radius (actualVertexWords n I)
                  (actualInheritedSourceScaledTail P s)
                  (actualInheritedSourceCombination P s
                    (fun j x => actualCoordinatePolynomialFunction (Q j) (x-p))) j (p+z) := by
  obtain ⟨P,s,hs0,hs,D₀,D₁,δ,hδ,hsource,hnear⟩ :=
    exists_actual_inherited_uniform_translated_tail_domain I G
  refine ⟨P,s,hs0,hs,D₀,D₁,δ,hδ,hsource,?_⟩
  intro p hp
  obtain ⟨hdom,htd,htb⟩ := hnear p hp
  refine ⟨hdom,htd,htb,?_⟩
  intro Q
  exact literal_translated_neumann_division I G hspan P hs0 hs D₀ D₁ hsource p
    hdom htd htb (fun j => actualCoordinatePolynomialFunction (Q j))
      (fun j => actualCoordinatePolynomialFunction_differentiable (Q j))

end
end Hironaka.HironakaActualInheritedTranslatedAnalyticDivision


namespace Hironaka.HironakaActualInheritedTranslatedAnalyticDivision
noncomputable section
open HolGerm HironakaActualCoefficientPresentationCentrePower
  HironakaActualCauchyCoordinateDivision HironakaActualCauchyTaylorSupport
  HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition
  HironakaActualCauchyEnumeratedPartition HironakaActualCauchyNeumannDivision
  HironakaActualCauchyNeumannSameBallBounds HironakaActualRelativeNormalJetDivision
  HironakaActualInheritedSmallTails HironakaActualOriginalScaledAnalyticDivision
  HironakaActualInheritedSourceCauchyRemainder HironakaActualInheritedUniformTranslatedTails
  HironakaActualTranslatedCauchyOwnerSupport HironakaActualBoundedSupportedNeumannUniqueness


variable {n : ℕ}

/-- Public interface to the existing literal whole translated division law.
This alias retains its exact source, domains, hypotheses and conclusion. -/
theorem actual_translated_neumann_division
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I))
    (hspan : Ideal.span (range G.germs) = I)
    (P : ActualInheritedWeightedTailData G) {s : ℂ} (hs0 : s ≠ 0)
    (hs : s ∈ ball 0 P.radius)
    (D₀ : ConcreteNeumannData P.radius (actualVertexWords n I))
    (D₁ : ConcreteNeumannData (P.radius/2) (actualVertexWords n I))
    (hsource : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) P.radius,
      ‖actualInheritedSourceScaledTail P s j z‖ ≤ D₀.epsilon)
    (p : CoordinateSpace n)
    (hdom : MapsTo (fun z => p+z) (ball 0 (P.radius/2)) (ball 0 P.radius))
    (htd : ∀ j, DifferentiableOn ℂ (actualInheritedTranslatedTail P s p j)
      (ball 0 (P.radius/2)))
    (htb : ∀ j, ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
      ‖actualInheritedTranslatedTail P s p j z‖ ≤ D₁.epsilon)
    (A : Fin (actualVertexCount n I) → CoordinateSpace n → ℂ)
    (hA : ∀ j, Differentiable ℂ (A j)) :
    ∀ z ∈ ball (0 : CoordinateSpace n) (P.radius/2),
      neumannRemainderSum (P.radius/2) (actualVertexWords n I)
        (actualInheritedTranslatedTail P s p) (actualInheritedTranslatedCombination P s p A) z = 0 ∧
      ∀ j, neumannQuotientSum (P.radius/2) (actualVertexWords n I)
        (actualInheritedTranslatedTail P s p) (actualInheritedTranslatedCombination P s p A) j z =
          neumannQuotientSum P.radius (actualVertexWords n I) (actualInheritedSourceScaledTail P s)
            (actualInheritedSourceCombination P s (fun j x => A j (x-p))) j (p+z) := by
  exact literal_translated_neumann_division I G hspan P hs0 hs D₀ D₁ hsource p hdom htd htb A hA

end
end Hironaka.HironakaActualInheritedTranslatedAnalyticDivision
