import Hironaka.Resolution.HironakaActualNormalAllDirectionConverse
import Hironaka.Resolution.HironakaActualNormalZeroAnalyticSaturation

/-! SAME analytic quotients, WHOLE saturation and all HS values at arbitrary
normal pivots and directions. Actual quotients are chosen from source marks
before target orders; no auxiliary analytic shear realization is presumed.
Source-only draft, not kernel checked. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalAllDirectionAnalyticSaturation
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan
  HironakaHolomorphicJetChartInvariance HironakaActualOriginalFormalTaylor
  HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualOriginalFormalHSTransfer HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualFormalFamilyStrictGenerators
  HironakaActualReducedBasisDivision HironakaActualRelativeNormalJetDivision
  HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticStrictGenerators
  HironakaActualNormalZeroFormalSaturation HironakaActualNormalZeroAnalyticSaturation
  HironakaActualUnshiftedInitialHSTransfer HironakaActualNormalAllDirectionConverse

/-- The genuine SAME analytic quotient is chosen from the ORIGINAL source mark before any target-order input. -/
def sameAnalyticNormalNormalizedVertex
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (q e : Fin n) (hqe : q ≤ e) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici q) ^ normalExponentDegree a.val)
    (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
    : HolGerm (ComplexModel n) :=
  Classical.choose (exists_actualAnalyticBlowup_quotient (Set.Ici q) e hqe b
    (normalExponentDegree a.val) (G.germs a) (hpower a))

/-- The SAME quotient has its exact actual exceptional product. -/
theorem sameAnalyticNormalNormalizedVertex_product
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (q e : Fin n) (hqe : q ≤ e) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici q) ^ normalExponentDegree a.val)
    (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
    : (coordinateGerm e)^(normalExponentDegree a.val) * sameAnalyticNormalNormalizedVertex n I G q e hqe b hpower a =
      actualAnalyticBlowupPullback (Set.Ici q) e b (G.germs a) :=
  (Classical.choose_spec (exists_actualAnalyticBlowup_quotient (Set.Ici q) e hqe b
    (normalExponentDegree a.val) (G.germs a) (hpower a))).1

private theorem sameAnalyticNormalFormalMark
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (q : Fin n)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici q) ^ normalExponentDegree a.val)
    (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
    actualUnshiftedTaylorAlgHom n (G.germs a) ∈ actualFormalCoordinateIdeal n (Set.Ici q) ^ normalExponentDegree a.val :=
  actualTaylor_mem_coordinateCentre_pow (n := n) (Set.Ici q)
    (normalExponentDegree a.val) (G.germs a) (hpower a)

/-- The entire Taylor series is the SAME actual normalized formal member at its unchanged mark. -/
theorem actualTaylor_sameAnalyticNormalNormalizedVertex
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (q e : Fin n) (hqe : q ≤ e) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici q) ^ normalExponentDegree a.val)
    (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I))
    : actualUnshiftedTaylorAlgHom n (sameAnalyticNormalNormalizedVertex n I G q e hqe b hpower a) =
      actualNormalizedFormalMember (Set.Ici q) e hqe b (normalExponentDegree a.val)
        (actualUnshiftedTaylorAlgHom n (G.germs a)) (sameAnalyticNormalFormalMark n I G q hpower a) := by
  apply actualNormalizedFormalMember_unique
  have h := congrArg (actualUnshiftedTaylorAlgHom n)
    (sameAnalyticNormalNormalizedVertex_product n I G q e hqe b hpower a)
  rw [map_mul, map_pow, actualUnshiftedTaylor_coordinate] at h
  exact h.trans (DFunLike.congr_fun (actualTaylor_analyticBlowupPullback (Set.Ici q) e b) (G.germs a))

/-- The original-chart target span retains exactly these initially chosen analytic quotients. -/
def sameAnalyticNormalNormalizedIdeal
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (q e : Fin n) (hqe : q ≤ e) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici q) ^ normalExponentDegree a.val)
    : Ideal (HolGerm (ComplexModel n)) :=
  Ideal.span (Set.range (sameAnalyticNormalNormalizedVertex n I G q e hqe b hpower))

/-- Existing whole strict-generation identifies the literal SAME target Taylor ideal, without target orders or HS. -/
theorem map_sameAnalyticNormalNormalizedIdeal
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I)
    (q e : Fin n) (hqe : q ≤ e) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici q) ^ normalExponentDegree a.val)
    : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
      (sameAnalyticNormalNormalizedIdeal n I G q e hqe b hpower) =
        actualFormalStrictTransform (analyticZeroTaylorIdeal n I) (Set.Ici q) e hqe b := by
  let K := analyticZeroTaylorIdeal n I
  let B := analyticZeroMonicFamily n I G hmem
  have hw (a : actualInitialVertices MonomialOrder.degLex K) :
      Finsupp.weight (actualCoordinateWeight (Set.Ici q)) a.val = normalExponentDegree a.val :=
    normal_weight_eq_degree_of_monic_mark (Set.Ici q) a.val (B.series a) (B.monic a)
      (sameAnalyticNormalFormalMark n I G q hpower a)
  have hv (a : actualInitialVertices MonomialOrder.degLex K) : B.series a ∈
      actualFormalCoordinateIdeal n (Set.Ici q) ^ Finsupp.weight (actualCoordinateWeight (Set.Ici q)) a.val := by
    rw [hw a]
    exact sameAnalyticNormalFormalMark n I G q hpower a
  rw [actualFormalStrictTransform_eq_family_span MonomialOrder.degLex K B (Set.Ici q) e hqe b hv,
    sameAnalyticNormalNormalizedIdeal, Ideal.map_span, ← Set.range_comp]
  congr 1
  apply congrArg Set.range
  funext a
  apply actualNormalizedFormalMember_unique (Set.Ici q) e hqe b
    (Finsupp.weight (actualCoordinateWeight (Set.Ici q)) a.val) (B.series a) (hv a)
  rw [hw a]
  have h := congrArg (actualUnshiftedTaylorAlgHom n)
    (sameAnalyticNormalNormalizedVertex_product n I G q e hqe b hpower a)
  rw [map_mul, map_pow, actualUnshiftedTaylor_coordinate] at h
  exact h.trans (DFunLike.congr_fun (actualTaylor_analyticBlowupPullback (Set.Ici q) e b) (G.germs a))

/-- Both WHOLE analytic ideal inclusions retain the SAME span, independently of all target orders. -/
theorem actualAnalyticNormalizedMemberIdeal_eq_same_normal_span
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I)
    (q e : Fin n) (hqe : q ≤ e) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici q) ^ normalExponentDegree a.val)
    : actualAnalyticNormalizedMemberIdeal I (Set.Ici q) e b = sameAnalyticNormalNormalizedIdeal n I G q e hqe b hpower := by
  apply le_antisymm
  · intro g hg
    apply (mem_analytic_ideal_iff_actualUnshifted_extension n _ g).mpr
    rw [map_sameAnalyticNormalNormalizedIdeal n I G hmem q e hqe b hpower]
    exact map_actualAnalyticNormalizedMemberIdeal_le_formalStrictTransform I (Set.Ici q) e hqe b
      (Ideal.mem_map_of_mem _ hg)
  · apply Ideal.span_le.mpr
    rintro g ⟨a, rfl⟩
    exact Ideal.subset_span ⟨normalExponentDegree a.val, G.germs a, hmem a, hpower a,
      sameAnalyticNormalNormalizedVertex_product n I G q e hqe b hpower a⟩

/-- Actual analytic marked orders invoke the natural formal converse internally; no desired formal certificate is an input. -/
theorem actual_analytic_normal_formal_hs_and_regular_of_marked_orders
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I)
    (q e : Fin n) (hqe : q ≤ e) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici q) ^ normalExponentDegree a.val)
    (horder : ∀ a, sameAnalyticNormalNormalizedVertex n I G q e hqe b hpower a ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val)
    : (∀ ℓ, genuineFormalHilbertSamuelValue n
      (actualFormalStrictTransform (analyticZeroTaylorIdeal n I) (Set.Ici q) e hqe b) ℓ =
        genuineFormalHilbertSamuelValue n (analyticZeroTaylorIdeal n I) ℓ) ∧
    (∀ r (F : MvPowerSeries (Fin n) ℂ), (MvPowerSeries.X e)^r * F ∈
      actualFormalStrictTransform (analyticZeroTaylorIdeal n I) (Set.Ici q) e hqe b ↔
        F ∈ actualFormalStrictTransform (analyticZeroTaylorIdeal n I) (Set.Ici q) e hqe b) := by
  let B := analyticZeroMonicFamily n I G hmem
  have hp (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      B.series a ∈ actualFormalCoordinateIdeal n (Set.Ici q) ^ normalExponentDegree a.val :=
    sameAnalyticNormalFormalMark n I G q hpower a
  have ho (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      actualNormalizedFormalMember (Set.Ici q) e hqe b _ (B.series a) (hp a) ∈
        genuineFormalVariables n ^ normalExponentDegree a.val := by
    have h := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom (horder a)
    change actualUnshiftedTaylorAlgHom n (sameAnalyticNormalNormalizedVertex n I G q e hqe b hpower a) ∈
      Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val) at h
    rw [map_actualUnshifted_maximal_pow, actualTaylor_sameAnalyticNormalNormalizedVertex] at h
    exact h
  exact actual_normal_all_direction_hs_and_regular_of_marked_orders (analyticZeroTaylorIdeal n I) B q e hqe b hp ho

/-- Every exceptional power cancels in the SAME original-chart analytic ideal. -/
theorem coordinate_pow_mul_mem_same_normal_ideal_iff_of_marked_orders
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I)
    (q e : Fin n) (hqe : q ≤ e) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici q) ^ normalExponentDegree a.val)
    (horder : ∀ a, sameAnalyticNormalNormalizedVertex n I G q e hqe b hpower a ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val)
    (r : ℕ) (g : HolGerm (ComplexModel n))
    : (coordinateGerm e)^r * g ∈ sameAnalyticNormalNormalizedIdeal n I G q e hqe b hpower ↔
      g ∈ sameAnalyticNormalNormalizedIdeal n I G q e hqe b hpower := by
  constructor
  · intro hg
    apply (mem_analytic_ideal_iff_actualUnshifted_extension n _ g).mpr
    rw [map_sameAnalyticNormalNormalizedIdeal n I G hmem q e hqe b hpower]
    apply ((actual_analytic_normal_formal_hs_and_regular_of_marked_orders n I G hmem q e hqe b hpower horder).2
      r (actualUnshiftedTaylorAlgHom n g)).mp
    have h := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom hg
    change actualUnshiftedTaylorAlgHom n ((coordinateGerm e)^r * g) ∈
      Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom
        (sameAnalyticNormalNormalizedIdeal n I G q e hqe b hpower) at h
    rw [map_mul, map_pow, actualUnshiftedTaylor_coordinate,
      map_sameAnalyticNormalNormalizedIdeal n I G hmem q e hqe b hpower] at h
    exact h
  · exact Ideal.mul_mem_left _ _

/-- All genuine analytic HS values at the original arbitrary pivot and direction, including degree zero. -/
theorem hilbertSamuelValue_same_normal_ideal_eq_of_marked_orders
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I)
    (q e : Fin n) (hqe : q ≤ e) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici q) ^ normalExponentDegree a.val)
    (horder : ∀ a, sameAnalyticNormalNormalizedVertex n I G q e hqe b hpower a ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val) (ℓ : ℕ)
    : hilbertSamuelValue (sameAnalyticNormalNormalizedIdeal n I G q e hqe b hpower) ℓ = hilbertSamuelValue I ℓ := by
  rw [hilbertSamuelValue_eq_actual_unshifted_formal_extension,
    hilbertSamuelValue_eq_actual_unshifted_formal_extension,
    map_sameAnalyticNormalNormalizedIdeal n I G hmem q e hqe b hpower]
  exact (actual_analytic_normal_formal_hs_and_regular_of_marked_orders n I G hmem q e hqe b hpower horder).1 ℓ

/-- One finite common power, WHOLE analytic saturation and all HS values are internally produced from natural marked orders. -/
theorem exists_same_normal_analytic_fixed_colon_and_hs_of_marked_orders
    (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)) (hmem : ∀ a, G.germs a ∈ I)
    (q e : Fin n) (hqe : q ≤ e) (b : Fin n → ℂ)
    (hpower : ∀ a, G.germs a ∈ actualAnalyticCoordinateIdeal (Set.Ici q) ^ normalExponentDegree a.val)
    (horder : ∀ a, sameAnalyticNormalNormalizedVertex n I G q e hqe b hpower a ∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n)) ^ normalExponentDegree a.val)
    : ∃ M : ℕ,
      (∀ g ∈ sameAnalyticNormalNormalizedIdeal n I G q e hqe b hpower, (coordinateGerm e)^M * g ∈
        Ideal.map (actualAnalyticBlowupPullback (Set.Ici q) e b).toRingHom I) ∧
      sameAnalyticNormalNormalizedIdeal n I G q e hqe b hpower =
        (Ideal.map (actualAnalyticBlowupPullback (Set.Ici q) e b).toRingHom I).colon {(coordinateGerm e)^M} ∧
      (∀ g : HolGerm (ComplexModel n), g ∈ sameAnalyticNormalNormalizedIdeal n I G q e hqe b hpower ↔
        ∃ r : ℕ, (coordinateGerm e)^r * g ∈ Ideal.map (actualAnalyticBlowupPullback (Set.Ici q) e b).toRingHom I) ∧
      (∀ ℓ, hilbertSamuelValue (sameAnalyticNormalNormalizedIdeal n I G q e hqe b hpower) ℓ = hilbertSamuelValue I ℓ) := by
  let N := sameAnalyticNormalNormalizedIdeal n I G q e hqe b hpower
  let T := Ideal.map (actualAnalyticBlowupPullback (Set.Ici q) e b).toRingHom I
  let H := sameAnalyticNormalNormalizedVertex n I G q e hqe b hpower
  have hprod (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) :
      (coordinateGerm e)^(normalExponentDegree a.val) * H a ∈ T := by
    change (coordinateGerm e)^(normalExponentDegree a.val) *
      sameAnalyticNormalNormalizedVertex n I G q e hqe b hpower a ∈ T
    rw [sameAnalyticNormalNormalizedVertex_product]
    exact Ideal.mem_map_of_mem _ (hmem a)
  have hT : T ≤ N := by
    change Ideal.map (actualAnalyticBlowupPullback (Set.Ici q) e b).toRingHom I ≤ N
    rw [← analytic_ideal_eq_span_same_inherited_family n I G hmem, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro g ⟨f, ⟨a, rfl⟩, rfl⟩
    change actualAnalyticBlowupPullback (Set.Ici q) e b (G.germs a) ∈ N
    rw [← sameAnalyticNormalNormalizedVertex_product n I G q e hqe b hpower a]
    exact N.mul_mem_left _ (Ideal.subset_span ⟨a, rfl⟩)
  have hreg (g : HolGerm (ComplexModel n)) (hg : coordinateGerm e * g ∈ N) : g ∈ N := by
    apply (coordinate_pow_mul_mem_same_normal_ideal_iff_of_marked_orders n I G hmem q e hqe b hpower horder 1 g).mp
    simpa only [pow_one] using hg
  obtain ⟨M, _hM, hbound, hc, hs⟩ := exists_fixed_power_colon_of_finite_products T N (coordinateGerm e)
    (fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I) => normalExponentDegree a.val)
    H rfl hT hprod hreg
  exact ⟨M, hbound, hc, hs, hilbertSamuelValue_same_normal_ideal_eq_of_marked_orders n I G hmem q e hqe b hpower horder⟩

end
end Hironaka.HironakaActualNormalAllDirectionAnalyticSaturation
