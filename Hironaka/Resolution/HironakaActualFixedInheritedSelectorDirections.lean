import Hironaka.Resolution.HironakaActualFixedInheritedSelector
import Hironaka.Resolution.HironakaActualInheritedHSDirections
import Hironaka.Resolution.HironakaActualInheritedNextBlockCentreGraph

/-! The source contact invariant is consumed for the actual fixed historical
selector. Its Jacobian nonvanishing and HS direction are produced internally;
no fresh selected vertex or target certificate replaces that provenance. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFixedInheritedSelectorDirections
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaActualFixedInheritedSelector HironakaActualInheritedHSDirections
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalInitialDiagram
  HironakaActualRelativeNormalJetDivision HironakaActualCanonicalBlockJacobian
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualInheritedNestedContactFlag
  HironakaActualRelativeStandardnessBlockSupport HironakaActualAnalyticBlockGraphTranslation
  HironakaActualFormalCoordinatePowerDivision HironakaActualReducedBasisDivision
  HironakaActualCanonicalCentreCompatibility HironakaActualCanonicalNormalZeroDirectionOrder
  HironakaActualRelativeStandardnessNormalPointBridge HironakaActualPointDehomogenizedInitial
  HironakaActualAnalyticBlowupTaylor HironakaActualFormalStrictGenerators
  HironakaActualOriginalFormalHSTransfer HironakaActualPointUnitCoordinateChange
  HironakaActualInheritedNextBlockCentreGraph
  HironakaActualHomogeneousInitialHS
variable {n : ℕ} {K : Ideal (MvPowerSeries (Fin n) ℂ)}

private theorem factorial_add_single (α : Fin n →₀ ℕ) (i : Fin n) :
    actualExponentFactorial (α+Finsupp.single i 1) =
      actualExponentFactorial α * ((α i+1 : ℕ) : ℂ) := by
  have h (j : Fin n) :
      ((((α+Finsupp.single i 1 : Fin n →₀ ℕ) j)).factorial : ℂ) =
        ((α j).factorial : ℂ) * (if j=i then ((α i+1 : ℕ) : ℂ) else 1) := by
    by_cases hj : j=i
    · subst j
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, ite_true, Nat.factorial_succ, Nat.cast_mul]
      ring
    · simp [Finsupp.single_eq_of_ne hj, hj]
  simp only [actualExponentFactorial, h, Finset.prod_mul_distrib]
  simp

private theorem degree_add_single (α : Fin n →₀ ℕ) (i : Fin n) :
    Finsupp.degree (α+Finsupp.single i 1) = normalExponentDegree α+1 := by
  simp [Finsupp.degree_eq_sum, normalExponentDegree, Finsupp.add_apply, Finset.sum_add_distrib]

private theorem fixed_linear_direction_zero
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k) (v : Fin n → ℂ)
    (hDir : ∀ F ∈ actualHomogeneousInitialIdeal K,
      (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈ actualHomogeneousInitialIdeal K)
    (j : fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex K)) :
    (∑ i : Fin n, HolGerm.eval (actualAnalyticCoordinateDerivative i
      (actualFixedSelectorDerivative S G.germs j)) * v i) = 0 := by
  let a := S.selected j
  let β := fixedSelectorBeta S j
  have hdegree : normalExponentDegree β+1 = normalExponentDegree a.val := fixedSelector_beta_degree S j
  have hd := actual_inherited_leading_directional_derivative_zero G hmem hred v hDir a
  have hc := congrArg (MvPowerSeries.coeff β) hd
  rw [map_sum, map_zero] at hc
  have he : (∑ i : Fin n, HolGerm.eval (actualAnalyticCoordinateDerivative i
      (actualFixedSelectorDerivative S G.germs j)) * v i) =
      (∑ i : Fin n, MvPowerSeries.coeff β
        (v i • MvPowerSeries.pderiv ℂ i (actualInheritedLeadingHead G a))) * actualExponentFactorial β := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [actualFixedSelectorDerivative_jacobian_coefficient, map_smul,
      MvPowerSeries.coeff_pderiv, factorial_add_single]
    change MvPowerSeries.coeff (β+Finsupp.single i 1)
      (actualUnshiftedTaylorAlgHom n (G.germs a)) *
        (actualExponentFactorial β * ((β i+1 : ℕ) : ℂ)) * v i =
      (v i • (MvPowerSeries.coeff (β+Finsupp.single i 1)
        (MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
          (actualUnshiftedTaylorAlgHom n (G.germs a))) * _)) * actualExponentFactorial β
    rw [MvPowerSeries.coeff_homogeneousComponent, if_pos ((degree_add_single β i).trans hdegree)]
    simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [he, hc, zero_mul]

private theorem fixed_jacobian_outside_block
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (k : ℕ) (hadapt : actualFixedSelectorContactAt S G.germs k)
    (j : fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k) (i : Fin n)
    (hi : i ∉ fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k) :
    HolGerm.eval (actualAnalyticCoordinateDerivative i
      (actualFixedSelectorDerivative S G.germs (fixedSelectorBlockEssential k j))) = 0 := by
  have hg := actualTaylor_mem_coordinateCentre_pow
    (fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k) 1
    (actualFixedSelectorDerivative S G.germs (fixedSelectorBlockEssential k j))
    (by simpa only [pow_one, actualAnalyticCoordinateIdeal, actualAnalyticCoordinateBlockIdeal] using hadapt j)
  have hc := (mem_actualFormalCoordinateIdeal_pow_iff _ 1 _).mp hg (Finsupp.single i 1)
    (by simp [Finsupp.weight_single, actualCoordinateWeight, hi])
  rw [← HironakaActualCauchyCoefficientLimits.actualTaylor_coeff_zero,
    actualTaylor_actualAnalyticCoordinateDerivative, MvPowerSeries.coeff_pderiv,
    zero_add, Finsupp.zero_apply]
  simpa only [Nat.cast_zero, zero_add, mul_one] using hc

/-- No Jacobian premise: it is produced from the actual monic family and selector. -/
theorem actual_fixed_selector_contact_direction_zero
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k) (v : Fin n → ℂ)
    (hDir : ∀ F ∈ actualHomogeneousInitialIdeal K,
      (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈ actualHomogeneousInitialIdeal K)
    (k : ℕ) (hadapt : actualFixedSelectorContactAt S G.germs k) :
    ∀ i ∈ actualDegreePrefixVariables MonomialOrder.degLex K k, v i = 0 := by
  let B := fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k
  let W : B → ℂ := fun i => v i.val
  have hmul : Matrix.mulVec (actualFixedSelectorJacobian S G.germs k) W = 0 := by
    funext j
    let f (i : Fin n) := HolGerm.eval (actualAnalyticCoordinateDerivative i
      (actualFixedSelectorDerivative S G.germs (fixedSelectorBlockEssential k j))) * v i
    change (∑ i : B, f i.val) = 0
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i => i ∈ B), f i :=
        (Finset.sum_subtype _ (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]) f).symm
      _ = ∑ i : Fin n, f i := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _ hi
        have hiB : i ∉ B := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
        dsimp only [f]
        rw [fixed_jacobian_outside_block G S k hadapt j i hiB, zero_mul]
      _ = 0 := fixed_linear_direction_zero G S hmem hred v hDir _
  have hdet := actualFixedSelectorJacobian_det_ne_zero S G.germs (fun a => G.monic a) (fun a β h => G.lower a β h) k
  have hzero : W = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  intro i hi
  exact congrFun hzero (⟨i,hi⟩ : B)

private theorem coordinate_weight_le_degree (A : Set (Fin n)) (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight A) α ≤ normalExponentDegree α := by
  rw [Finsupp.weight_eq_sum, normalExponentDegree]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ A <;> simp [actualCoordinateWeight, hi]

/-- Actual HS equality supplies the direction internally for the SAME fixed
historical selector, not a newly selected tied vertex. -/
theorem actual_normal_hs_equal_fixed_selector_chart_conditions
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K)
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal A ^ normalExponentDegree a.val)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (hadapt : ∀ k, actualFixedSelectorContactAt S G.germs k)
    (hHS : ∀ q : ℕ, genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K A e he b) q =
      genuineFormalHilbertSamuelValue n K q) :
    ∀ k : ℕ, actualDegreePrefixVariables MonomialOrder.degLex K k ⊆ A \ {e} ∧
      ∀ i ∈ actualDegreePrefixVariables MonomialOrder.degLex K k, b i = 0 := by
  have hlegal (k : ℕ) : actualDegreePrefixVariables MonomialOrder.degLex K k ⊆ A :=
    actualDegreePrefixVariables_subset_of_normal_powers G A hpower k
  have hpure : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i ∉ A, a.val i = 0 := by
    intro a i hi
    by_contra h
    exact hi (hlegal (normalExponentDegree a.val) ⟨a, le_rfl, h⟩)
  let B : ActualMonicVertexFamily MonomialOrder.degLex K :=
    { series := fun a => actualUnshiftedTaylorAlgHom n (G.germs a)
      mem := hmem
      monic := G.monic
      lower := G.lower }
  have hB (a : actualInitialVertices MonomialOrder.degLex K) :
      B.series a ∈ actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) a.val :=
    (Ideal.pow_le_pow_right (coordinate_weight_le_degree A a.val))
      (actualTaylor_mem_coordinateCentre_pow A _ (G.germs a) (hpower a))
  have hV := actualReducedVertexSeries_mem_coordinate_power_of_family MonomialOrder.degLex K B A hB
  have hD := actual_tangent_initial_stability_of_pure_vertices_normal_powers K A hpure hV
  let v (i : Fin n) := actualPointUnitBasePoint e (actualNormalPointDirection A b) i
  have hDir := actual_homogeneous_initial_normal_directional_stable_of_hs_eq K A e he b hD hV hHS
  intro k
  have hz := actual_fixed_selector_contact_direction_zero G S hmem hred v hDir k (hadapt k)
  have heB : e ∉ actualDegreePrefixVariables MonomialOrder.degLex K k := by
    intro heB
    have h := hz e heB
    simp only [v, actualPointUnitBasePoint_apply, ite_true] at h
    exact one_ne_zero h
  refine ⟨fun i hi => ⟨hlegal k hi, ?_⟩, fun i hi => ?_⟩
  · simpa only [Set.mem_singleton_iff] using (fun hie => heB (hie ▸ hi) : i ≠ e)
  · have hie : i ≠ e := fun h => heB (h ▸ hi)
    have h := hz i hi
    simpa only [v, actualPointUnitBasePoint_apply, if_neg hie,
      actualNormalPointDirection, if_pos (hlegal k hi)] using h

end
end Hironaka.HironakaActualFixedInheritedSelectorDirections
