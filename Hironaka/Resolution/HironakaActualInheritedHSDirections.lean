import Hironaka.Resolution.HironakaActualInheritedNestedContactFlag
import Hironaka.Resolution.HironakaActualCanonicalCentreCompatibility
import Hironaka.Resolution.HironakaActualCanonicalNormalZeroDirectionOrder
import Hironaka.Resolution.HironakaActualRelativeStandardnessNormalPointBridge
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Actual HS directions vanish on the current inherited contact blocks

The family is not assumed canonical. Genuine membership in the CURRENT
source ideal and whole proper-prefix support force its leading components
to be annihilated by every stable source initial direction. True selected
contact ideal memberships and the internally invertible current Jacobians
then force that direction to vanish on every block. The last producer gets
the direction internally from actual normal strict/source closed-point HS
equality and genuine source normal powers, without target chart certificates.
-/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualInheritedHSDirections
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualHomogeneousInitialHS
  HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
  HironakaActualRelativeStandardnessBlockSupport HironakaActualCanonicalBlockJacobian
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualAnalyticBlockGraphTranslation
  HironakaActualFormalCoordinatePowerDivision HironakaActualReducedBasisDivision
  HironakaActualCanonicalCentreCompatibility HironakaActualCanonicalNormalZeroDirectionOrder
  HironakaActualRelativeStandardnessNormalPointBridge HironakaActualPointDehomogenizedInitial
  HironakaActualAnalyticBlowupTaylor HironakaActualFormalStrictGenerators
  HironakaActualOriginalFormalHSTransfer HironakaActualPointUnitCoordinateChange
variable {n : ℕ} {K : Ideal (MvPowerSeries (Fin n) ℂ)}

/-- The actual leading homogeneous component of the SAME current member. -/
def actualInheritedLeadingHead (G : ActualAnalyticInheritedFamily n 0 K)
    (a : actualInitialVertices MonomialOrder.degLex K) : MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
    (actualUnshiftedTaylorAlgHom n (G.germs a))

private theorem inherited_leading_mem (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    actualInheritedLeadingHead G a ∈ actualHomogeneousInitialIdeal K := by
  let F := actualUnshiftedTaylorAlgHom n (G.germs a)
  have hne : F ≠ 0 := by
    intro hz
    have hc : MvPowerSeries.coeff a.val F = 1 := G.monic a
    rw [hz, map_zero] at hc
    exact zero_ne_one hc
  have hhead : actualInitialExponent MonomialOrder.degLex F hne = a.val :=
    actualInitialExponent_eq_of_coefficients MonomialOrder.degLex F hne a.val
      (by
        have hc : MvPowerSeries.coeff a.val F = 1 := G.monic a
        rw [hc]
        exact one_ne_zero) (G.lower a)
  have hdegree : actualHomogeneousInitialDegree F hne = normalExponentDegree a.val := by
    rw [actualHomogeneousInitialDegree, hhead]
  have hinit : actualHomogeneousInitialForm F hne ∈ actualHomogeneousInitialIdeal K :=
    Ideal.subset_span ⟨⟨F, hmem a, hne⟩, rfl⟩
  simpa only [actualInheritedLeadingHead, actualHomogeneousInitialForm, hdegree] using hinit

private theorem degree_mono {α β : Fin n →₀ ℕ} (h : α ≤ β) :
    normalExponentDegree α ≤ normalExponentDegree β := by
  apply Finset.sum_le_sum
  intro i _
  exact h i

private theorem degree_add_single (α : Fin n →₀ ℕ) (i : Fin n) :
    Finsupp.degree (α+Finsupp.single i 1) = normalExponentDegree α+1 := by
  simp [Finsupp.degree_eq_sum, normalExponentDegree, Finsupp.add_apply, Finset.sum_add_distrib]

/-- Source initial stability annihilates the leading component of each SAME
noncanonical inherited member. Whole proper-prefix support is essential. -/
theorem actual_inherited_leading_directional_derivative_zero
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (v : Fin n → ℂ)
    (hDir : ∀ F ∈ actualHomogeneousInitialIdeal K,
      (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈ actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i (actualInheritedLeadingHead G a)) = 0 := by
  apply eq_zero_of_mem_of_diagram_coefficients_zero MonomialOrder.degLex (actualHomogeneousInitialIdeal K)
  · exact hDir _ (inherited_leading_mem G hmem a)
  · intro β hβ
    rw [actual_homogeneous_initial_ideal_diagram] at hβ
    obtain ⟨c, hc, hcle⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K β).mp hβ
    let cV : actualInitialVertices MonomialOrder.degLex K := ⟨c,hc⟩
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [map_smul, MvPowerSeries.coeff_pderiv]
    change v i • (MvPowerSeries.coeff (β+Finsupp.single i 1)
      (MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
        (actualUnshiftedTaylorAlgHom n (G.germs a))) * _) = 0
    rw [MvPowerSeries.coeff_homogeneousComponent]
    by_cases hd : Finsupp.degree (β+Finsupp.single i 1) = normalExponentDegree a.val
    · rw [if_pos hd]
      have hca : normalExponentDegree c < normalExponentDegree a.val := by
        have hcβ := degree_mono hcle
        rw [degree_add_single] at hd
        omega
      have hcplus : c ≤ β+Finsupp.single i 1 := by
        intro j
        exact (hcle j).trans (by simp only [Finsupp.add_apply]; omega)
      have hz := hred (normalExponentDegree c) a hca cV le_rfl (β+Finsupp.single i 1) hcplus
      rw [hz, zero_mul, smul_zero]
    · rw [if_neg hd, zero_mul, smul_zero]

private theorem exponentFactorial_add_single (α : Fin n →₀ ℕ) (i : Fin n) :
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

private theorem selected_linear_direction_zero
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (v : Fin n → ℂ)
    (hDir : ∀ F ∈ actualHomogeneousInitialIdeal K,
      (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈ actualHomogeneousInitialIdeal K)
    (j : actualCanonicalEssentialVariables MonomialOrder.degLex K) :
    (∑ i : Fin n, HolGerm.eval (actualAnalyticCoordinateDerivative i
      (actualInheritedEssentialDerivative G j)) * v i) = 0 := by
  let a := actualCanonicalDerivativeVertex MonomialOrder.degLex K j
  let β := actualCanonicalDerivativeExponent MonomialOrder.degLex K j
  have hdegree : normalExponentDegree β+1 = normalExponentDegree a.val := by
    have h := congrArg normalExponentDegree (actualCanonicalDerivativeExponent_add_single MonomialOrder.degLex K j)
    simpa [normalExponentDegree, Finsupp.add_apply, Finset.sum_add_distrib] using h
  have hd := actual_inherited_leading_directional_derivative_zero G hmem hred v hDir a
  have hc := congrArg (MvPowerSeries.coeff β) hd
  rw [map_sum, map_zero] at hc
  have he : (∑ i : Fin n, HolGerm.eval (actualAnalyticCoordinateDerivative i
      (actualInheritedEssentialDerivative G j)) * v i) =
      (∑ i : Fin n, MvPowerSeries.coeff β
        (v i • MvPowerSeries.pderiv ℂ i (actualInheritedLeadingHead G a))) * actualExponentFactorial β := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [actualInheritedEssentialDerivative_jacobian_coefficient, map_smul,
      MvPowerSeries.coeff_pderiv, exponentFactorial_add_single]
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

private theorem selected_jacobian_outside_block
    (G : ActualAnalyticInheritedFamily n 0 K) (k : ℕ) (hadapt : ActualInheritedContactAt G k)
    (j : actualDegreePrefixVariables MonomialOrder.degLex K k) (i : Fin n)
    (hi : i ∉ actualDegreePrefixVariables MonomialOrder.degLex K k) :
    HolGerm.eval (actualAnalyticCoordinateDerivative i (actualInheritedEssentialDerivative G
      (actualCanonicalBlockEssentialVariable MonomialOrder.degLex K k j))) = 0 := by
  have hg := actualTaylor_mem_coordinateCentre_pow
    (actualDegreePrefixVariables MonomialOrder.degLex K k) 1
    (actualInheritedEssentialDerivative G (actualCanonicalBlockEssentialVariable MonomialOrder.degLex K k j))
    (by simpa only [pow_one, actualAnalyticCoordinateIdeal, actualAnalyticCoordinateBlockIdeal] using hadapt j)
  have hc := (mem_actualFormalCoordinateIdeal_pow_iff _ 1 _).mp hg (Finsupp.single i 1)
    (by simp [Finsupp.weight_single, actualCoordinateWeight, hi])
  rw [← HironakaActualCauchyCoefficientLimits.actualTaylor_coeff_zero,
    actualTaylor_actualAnalyticCoordinateDerivative, MvPowerSeries.coeff_pderiv,
    zero_add, Finsupp.zero_apply]
  simpa only [Nat.cast_zero, zero_add, mul_one] using hc

/-- The actual current contact Jacobian forces every stable source direction
to vanish on the actual block. Its nonzero determinant is supplied by the
SAME current monic/lower fields, not assumed. -/
theorem actual_inherited_contact_block_direction_zero
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (v : Fin n → ℂ)
    (hDir : ∀ F ∈ actualHomogeneousInitialIdeal K,
      (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈ actualHomogeneousInitialIdeal K)
    (k : ℕ) (hadapt : ActualInheritedContactAt G k) :
    ∀ i ∈ actualDegreePrefixVariables MonomialOrder.degLex K k, v i = 0 := by
  let B := actualDegreePrefixVariables MonomialOrder.degLex K k
  let V : B → ℂ := fun i => v i.val
  have hmul : Matrix.mulVec (actualInheritedBlockJacobian G k) V = 0 := by
    funext j
    let f (i : Fin n) := HolGerm.eval (actualAnalyticCoordinateDerivative i
      (actualInheritedEssentialDerivative G (actualCanonicalBlockEssentialVariable MonomialOrder.degLex K k j))) * v i
    change (∑ i : B, f i.val) = 0
    calc
      _ = ∑ i ∈ Finset.univ.filter (fun i => i ∈ B), f i :=
        (Finset.sum_subtype _ (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and]) f).symm
      _ = ∑ i : Fin n, f i := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro i _ hi
        have hiB : i ∉ B := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
        dsimp only [f]
        rw [selected_jacobian_outside_block G k hadapt j i hiB, zero_mul]
      _ = 0 := selected_linear_direction_zero G hmem hred v hDir _
  have hzero : V = 0 := Matrix.eq_zero_of_mulVec_eq_zero (actualInheritedBlockJacobian_det_ne_zero G k) hmul
  intro i hi
  exact congrFun hzero (⟨i,hi⟩ : B)

private theorem coordinate_weight_le_degree (A : Set (Fin n)) (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight A) α ≤ normalExponentDegree α := by
  rw [Finsupp.weight_eq_sum, normalExponentDegree]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ A <;> simp [actualCoordinateWeight, hi]

private theorem source_vertices_pure (G : ActualAnalyticInheritedFamily n 0 K)
    (A : Set (Fin n))
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal A ^ normalExponentDegree a.val) :
    ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i ∉ A, a.val i = 0 := by
  intro a i hi
  have hp := actualTaylor_mem_coordinateCentre_pow A _ (G.germs a) (hpower a)
  have hw : normalExponentDegree a.val ≤ Finsupp.weight (actualCoordinateWeight A) a.val := by
    by_contra h
    have hz := (mem_actualFormalCoordinateIdeal_pow_iff A _ _).mp hp a.val (lt_of_not_ge h)
    have hc : MvPowerSeries.coeff a.val
        (actualUnshiftedTaylorAlgHom n (G.germs a)) = 1 := G.monic a
    rw [hc] at hz
    exact one_ne_zero hz
  have he : Finsupp.weight (actualCoordinateWeight A) a.val = normalExponentDegree a.val :=
    le_antisymm (coordinate_weight_le_degree A a.val) hw
  have hsum : Finsupp.weight (actualCoordinateWeight A) a.val +
      Finsupp.weight (actualCoordinateWeight Aᶜ) a.val = normalExponentDegree a.val := by
    rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ∈ A <;> simp [actualCoordinateWeight, hj]
  have hle : a.val i ≤ Finsupp.weight (actualCoordinateWeight Aᶜ) a.val := by
    rw [Finsupp.weight_eq_sum]
    have h := Finset.single_le_sum
      (fun j (_ : j ∈ Finset.univ) => Nat.zero_le (a.val j • actualCoordinateWeight Aᶜ j))
      (Finset.mem_univ i)
    simpa only [actualCoordinateWeight, Set.mem_compl_iff, if_pos hi, smul_eq_mul, mul_one] using h
  omega

/-- Actual normal strict/source whole HS equality produces every legal
contact-block chart condition for the SAME current noncanonical family.
No direction, target diagram/order, regular symbol or jet map is a premise. -/
theorem actual_normal_hs_equal_inherited_flag_chart_conditions
    (G : ActualAnalyticInheritedFamily n 0 K)
    (hmem : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈ K)
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal A ^ normalExponentDegree a.val)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (hadapt : ∀ k, ActualInheritedContactAt G k)
    (hHS : ∀ q : ℕ, genuineFormalHilbertSamuelValue n (actualFormalStrictTransform K A e he b) q =
      genuineFormalHilbertSamuelValue n K q) :
    ∀ k : ℕ, actualDegreePrefixVariables MonomialOrder.degLex K k ⊆ A \ {e} ∧
      ∀ i ∈ actualDegreePrefixVariables MonomialOrder.degLex K k, b i = 0 := by
  let B : ActualMonicVertexFamily MonomialOrder.degLex K :=
    { series := fun a => actualUnshiftedTaylorAlgHom n (G.germs a)
      mem := hmem
      monic := G.monic
      lower := G.lower }
  have hB (a : actualInitialVertices MonomialOrder.degLex K) :
      B.series a ∈ actualFormalCoordinateIdeal n A ^ Finsupp.weight (actualCoordinateWeight A) a.val := by
    exact (Ideal.pow_le_pow_right (coordinate_weight_le_degree A a.val))
      (actualTaylor_mem_coordinateCentre_pow A _ (G.germs a) (hpower a))
  have hV := actualReducedVertexSeries_mem_coordinate_power_of_family MonomialOrder.degLex K B A hB
  have hpure := source_vertices_pure G A hpower
  have hD := actual_tangent_initial_stability_of_pure_vertices_normal_powers K A hpure hV
  let v (i : Fin n) := actualPointUnitBasePoint e (actualNormalPointDirection A b) i
  have hDir := actual_homogeneous_initial_normal_directional_stable_of_hs_eq K A e he b hD hV hHS
  have hlegal (k : ℕ) : actualDegreePrefixVariables MonomialOrder.degLex K k ⊆ A := by
    intro i hi
    obtain ⟨a, _hdegree, hai⟩ := hi
    by_contra hiA
    exact hai (hpure a i hiA)
  intro k
  have hz := actual_inherited_contact_block_direction_zero G hmem hred v hDir k (hadapt k)
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
end Hironaka.HironakaActualInheritedHSDirections
