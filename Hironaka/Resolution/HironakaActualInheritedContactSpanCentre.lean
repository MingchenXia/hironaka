import Hironaka.Resolution.HironakaActualFixedInheritedSelector
import Hironaka.Resolution.HironakaActualInheritedLocalHSContact
import Hironaka.Resolution.HironakaActualPointGeometricBennett

/-! Historical contacts generate the WHOLE coordinate ideal. The actual
Jacobian and the actual whole germ matrix inverse are produced from the
SAME monic/lower family and source contact condition. Local ORIGINAL HS
constancy then puts the actual centre germ in every historical block plane.
No desired span, rank, Jacobian unit or centre containment is an input.
Free-only product flattening is a separate, subsequent construction. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Matrix
namespace Hironaka.HironakaActualInheritedContactSpanCentre
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves HolGerm OkaRelationSheaf OkaIdealOperations
  HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualRelativeNormalJetDivision HironakaActualFixedInheritedSelector
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualInheritedNestedContactFlag
  HironakaActualAnalyticBlockGraphTranslation HironakaActualCoefficientPresentationCentrePower
  HironakaActualCauchyCoefficientLimits HironakaHolomorphicJetMonomialSpan
  HironakaActualInheritedHSContactContainment HironakaActualInheritedLocalHSContact
  HironakaRelativeNormalDeformationInitialRelations HironakaActualPointGeometricBennett
  HironakaHolomorphicJetChartInvariance HironakaSmoothCentreRealDomainSaturation
  HironakaSmoothCentreCoherentDomain
variable {n : ℕ} {K : Ideal (MvPowerSeries (Fin n) ℂ)}

private theorem coordinateIdeal_eq_span_range (B : Set (Fin n)) :
    actualAnalyticCoordinateBlockIdeal B =
      Ideal.span (Set.range (fun i : B => (coordinateGerm i.val : HolGerm (ComplexModel n)))) := by
  unfold actualAnalyticCoordinateBlockIdeal
  congr 1
  ext F
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.property, rfl⟩

private theorem eval_coordinateDerivative_mul_coordinate
    (i j : Fin n) (F : HolGerm (ComplexModel n)) :
    HolGerm.eval (actualAnalyticCoordinateDerivative i (F * coordinateGerm j)) =
      if j = i then HolGerm.eval F else 0 := by
  rw [← actualTaylor_coeff_zero, actualTaylor_actualAnalyticCoordinateDerivative,
    map_mul, actualUnshiftedTaylor_coordinate]
  change MvPowerSeries.constantCoeff
      (MvPowerSeries.pderiv ℂ i
        (actualUnshiftedTaylorAlgHom n F * MvPowerSeries.X j)) = _
  by_cases hji : j = i
  · subst j
    simp only [Derivation.leibniz, smul_eq_mul, MvPowerSeries.pderiv_X_self,
      map_add, map_mul, MvPowerSeries.constantCoeff_X, mul_one, zero_mul, add_zero]
    exact actualTaylor_coeff_zero F
  · simp only [if_neg hji, Derivation.leibniz, smul_eq_mul,
      MvPowerSeries.pderiv_X_of_ne hji, map_add, map_mul, map_zero,
      MvPowerSeries.constantCoeff_X, mul_zero, zero_mul, add_zero]

/-- The actual historical contacts supply an actual WHOLE germ coefficient
matrix. Its value is the true Jacobian and its determinant is internally a unit. -/
theorem exists_actualFixedSelectorContact_matrix
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (k : ℕ) (hadapt : actualFixedSelectorContactAt S G.germs k) :
    ∃ M : Matrix (fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k)
        (fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k)
        (HolGerm (ComplexModel n)),
      (∀ j, ∑ i, M j i * coordinateGerm i.val =
        actualFixedSelectorDerivative S G.germs (fixedSelectorBlockEssential k j)) ∧
      HolGerm.eval.mapMatrix M = actualFixedSelectorJacobian S G.germs k ∧
      IsUnit M.det := by
  have hrow (j : fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k) :
      ∃ c : fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k →
        HolGerm (ComplexModel n),
      ∑ i, c i * coordinateGerm i.val =
        actualFixedSelectorDerivative S G.germs (fixedSelectorBlockEssential k j) := by
    apply Ideal.mem_span_range_iff_exists_fun.mp
    rw [← coordinateIdeal_eq_span_range
      (fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k)]
    exact hadapt j
  choose rows hrows using hrow
  let M : Matrix (fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k)
      (fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k)
      (HolGerm (ComplexModel n)) := rows
  have hM (j : fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k) :
      ∑ i, M j i * coordinateGerm i.val =
        actualFixedSelectorDerivative S G.germs (fixedSelectorBlockEssential k j) := hrows j
  have hvalue : HolGerm.eval.mapMatrix M = actualFixedSelectorJacobian S G.germs k := by
    ext j i
    change HolGerm.eval (M j i) = HolGerm.eval
      (actualAnalyticCoordinateDerivative i.val
        (actualFixedSelectorDerivative S G.germs (fixedSelectorBlockEssential k j)))
    symm
    rw [← hM j, map_sum, map_sum]
    simp [eval_coordinateDerivative_mul_coordinate, Subtype.coe_inj]
  refine ⟨M, hM, hvalue, ?_⟩
  apply (HolGerm.isUnit_iff_eval_ne_zero _).mpr
  rw [RingHom.map_det, hvalue]
  exact actualFixedSelectorJacobian_det_ne_zero S G.germs G.monic G.lower k

/-- Genuine monic/lower data and the existing source whole contact condition
produce equality of ENTIRE analytic ideals, without a Jacobian certificate. -/
theorem span_actualFixedSelectorContact_eq_coordinateIdeal
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (k : ℕ) (hadapt : actualFixedSelectorContactAt S G.germs k) :
    Ideal.span (Set.range (fun j : fixedSelectorBlock
        (actualInitialVertices MonomialOrder.degLex K) k =>
      actualFixedSelectorDerivative S G.germs (fixedSelectorBlockEssential k j))) =
        actualAnalyticCoordinateBlockIdeal
          (fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k) := by
  obtain ⟨M, hM, _hvalue, hunit⟩ := exists_actualFixedSelectorContact_matrix G S k hadapt
  let x : fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k →
      HolGerm (ComplexModel n) := fun i => coordinateGerm i.val
  let g : fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k →
      HolGerm (ComplexModel n) := fun j =>
    actualFixedSelectorDerivative S G.germs (fixedSelectorBlockEssential k j)
  have hproduct : M *ᵥ x = g := by
    funext j
    exact hM j
  have hinverse : M⁻¹ *ᵥ g = x := by
    rw [← hproduct, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hunit, Matrix.one_mulVec]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro F ⟨j, rfl⟩
    exact hadapt j
  · rw [coordinateIdeal_eq_span_range
      (fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex K) k)]
    apply Ideal.span_le.mpr
    rintro F ⟨i, rfl⟩
    change x i ∈ Ideal.span (Set.range g)
    rw [← congrFun hinverse i]
    change (∑ j, (M⁻¹) i j * g j) ∈ Ideal.span (Set.range g)
    apply Ideal.sum_mem
    intro j _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

/-- Local original whole HS constancy puts the ENTIRE historical block ideal
in the true vanishing ideal. The SAME contact derivatives and actual span are
used; no caller-supplied centre-containment or Jacobian condition occurs. -/
theorem actual_coordinate_block_le_local_hs_centre
    (A : GermIdeal n (ComplexModel n)) (hfg : IdealFGAt A.mem 0)
    (G : ActualAnalyticInheritedFamily n 0 (actualInheritedOriginFormalIdeal A))
    (hspan : Ideal.span (Set.range G.germs) = originalCoherentOriginIdeal A)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A)))
    (k : ℕ) (hadapt : actualFixedSelectorContactAt S G.germs k)
    (C : Set (ComplexModel n))
    (hHS : ∀ᶠ p in 𝓝 (0 : ComplexModel n), p ∈ C →
      ∀ ℓ : ℕ, hilbertSamuelAt A p ℓ = hilbertSamuelAt A 0 ℓ) :
    actualAnalyticCoordinateBlockIdeal
        (fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex
          (actualInheritedOriginFormalIdeal A)) k) ≤
      originalCoherentOriginIdeal (vanishingIdeal (n := n) C) := by
  apply le_trans (span_actualFixedSelectorContact_eq_coordinateIdeal G S k hadapt).ge
  apply Ideal.span_le.mpr
  rintro F ⟨j, rfl⟩
  let e := fixedSelectorBlockEssential k j
  have hdegree : normalExponentDegree (fixedSelectorBeta S e) <
      normalExponentDegree (S.selected e).val := by
    have h := fixedSelector_beta_degree S e
    omega
  exact actual_inherited_low_derivatives_mem_local_hs_centre A hfg G hspan hred C hHS
    (S.selected e) (fixedSelectorBeta S e) hdegree

/-- The SAME actual HS centre lies in the whole essential historical plane on
ONE genuine open neighborhood. C is arbitrary; no smoothness is needed here. -/
theorem actual_hs_centre_germ_subset_historical_plane
    (A : GermIdeal n (ComplexModel n)) (hfg : IdealFGAt A.mem 0)
    (G : ActualAnalyticInheritedFamily n 0 (actualInheritedOriginFormalIdeal A))
    (hspan : Ideal.span (Set.range G.germs) = originalCoherentOriginIdeal A)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A)))
    (hadapt : ∀ k, actualFixedSelectorContactAt S G.germs k)
    (C : Set (ComplexModel n))
    (hHS : ∀ᶠ p in 𝓝 (0 : ComplexModel n), p ∈ C →
      ∀ ℓ : ℕ, hilbertSamuelAt A p ℓ = hilbertSamuelAt A 0 ℓ) :
    let B := fixedSelectorEssential
      (actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A))
    actualAnalyticCoordinateBlockIdeal B ≤
      originalCoherentOriginIdeal (vanishingIdeal (n := n) C) ∧
      ∃ U : Set (ComplexModel n), IsOpen U ∧ (0 : ComplexModel n) ∈ U ∧
        ∀ p ∈ U, p ∈ C → ∀ i ∈ B, p i = 0 := by
  let V := actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A)
  let B := fixedSelectorEssential V
  have hcoord (i : Fin n) (hi : i ∈ B) : coordinateGerm i ∈
      originalCoherentOriginIdeal (vanishingIdeal (n := n) C) := by
    obtain ⟨a, hai⟩ := hi
    have hiBlock : i ∈ fixedSelectorBlock V (normalExponentDegree a.val) :=
      ⟨a, le_rfl, hai⟩
    exact actual_coordinate_block_le_local_hs_centre A hfg G hspan hred S
      (normalExponentDegree a.val) (hadapt _) C hHS (Ideal.subset_span ⟨i, hiBlock, rfl⟩)
  have hle : actualAnalyticCoordinateBlockIdeal B ≤
      originalCoherentOriginIdeal (vanishingIdeal (n := n) C) := by
    apply Ideal.span_le.mpr
    rintro F ⟨i, hi, rfl⟩
    exact hcoord i hi
  have heach (i : Fin n) : ∀ᶠ p in 𝓝 (0 : ComplexModel n), p ∈ C → i ∈ B → p i = 0 := by
    by_cases hi : i ∈ B
    · have hf : HolAt (fun p : ComplexModel n => p i) 0 :=
        Eventually.of_forall fun _ =>
          (EuclideanSpace.proj i : ComplexModel n →L[ℂ] ℂ).differentiableAt
      have hzero := (mk_mem_original_vanishing_origin_ideal_iff C
        (fun p : ComplexModel n => p i) hf).mp (hcoord i hi)
      filter_upwards [hzero] with p hp hCp _hi
      exact hp hCp
    · exact Eventually.of_forall fun _ _ h => (hi h).elim
  have hall : ∀ᶠ p in 𝓝 (0 : ComplexModel n), p ∈ C → ∀ i ∈ B, p i = 0 := by
    filter_upwards [eventually_all.mpr heach] with p hp hCp i hi
    exact hp i hCp hi
  obtain ⟨U, hUsub, hU, h0U⟩ := mem_nhds_iff.mp hall
  exact ⟨hle, U, hU, h0U, fun p hp => hUsub hp⟩

/-- Genuine coherence only on the actual open chart gives the same CURRENT
historical plane containment, without any global coherent extension. -/
theorem actual_hs_centre_germ_subset_historical_plane_of_coherentOn
    (A : GermIdeal n (ComplexModel n)) (W : Set (ComplexModel n))
    (hW : IsOpen W) (h0W : (0 : ComplexModel n) ∈ W) (hA : CoherentOn A W)
    (G : ActualAnalyticInheritedFamily n 0 (actualInheritedOriginFormalIdeal A))
    (hspan : Ideal.span (Set.range G.germs) = originalCoherentOriginIdeal A)
    (hred : ∀ k, ActualInheritedPrefixReducedAt G k)
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A)))
    (hadapt : ∀ k, actualFixedSelectorContactAt S G.germs k)
    (C : Set (ComplexModel n))
    (hHS : ∀ p ∈ C, p ∈ W → ∀ ℓ : ℕ,
      hilbertSamuelAt A p ℓ = hilbertSamuelAt A 0 ℓ) :
    let B := fixedSelectorEssential
      (actualInitialVertices MonomialOrder.degLex (actualInheritedOriginFormalIdeal A))
    actualAnalyticCoordinateBlockIdeal B ≤
      originalCoherentOriginIdeal (vanishingIdeal (n := n) C) ∧
      ∃ U : Set (ComplexModel n), IsOpen U ∧ (0 : ComplexModel n) ∈ U ∧
        ∀ p ∈ U, p ∈ C → ∀ i ∈ B, p i = 0 := by
  have hfg := idealFGAt_of_coherentOn A W hA h0W
  have hlocal : ∀ᶠ p in 𝓝 (0 : ComplexModel n), p ∈ C →
      ∀ ℓ : ℕ, hilbertSamuelAt A p ℓ = hilbertSamuelAt A 0 ℓ := by
    filter_upwards [hW.mem_nhds h0W] with p hp hCp
    exact hHS p hCp hp
  exact actual_hs_centre_germ_subset_historical_plane A hfg G hspan hred S hadapt C hlocal

end
end Hironaka.HironakaActualInheritedContactSpanCentre
