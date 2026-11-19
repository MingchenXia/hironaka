import Hironaka.Resolution.HironakaActualRelativeStandardnessNormalPointBridge
import Hironaka.Resolution.HironakaActualCanonicalZeroDirectionOrder

/-! Closed-point HS equality forces every SAME canonical marked order in a
proper smooth-centre zero chart. Model fibres, direction stability, and the
concrete jet injectivity are produced from the original source data. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualCanonicalNormalZeroDirectionOrder
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalMonomialBlowupReflection HironakaActualFormalStrictGenerators
  HironakaActualCoefficientReducedStrictGenerators HironakaActualHomogeneousInitialHS
  HironakaActualCanonicalVertexDirectionalInvariance HironakaActualTangentInitialVertices
  HironakaActualCanonicalDirectionPivot HironakaActualCanonicalZeroDirectionOrder
  HironakaActualPointExceptionalInitialForm HironakaActualPointDehomogenizedInitial
  HironakaActualPointExceptionalFibre HironakaActualPointNormalizedHomogeneous
  HironakaActualPointUnitCoordinateChange HironakaActualRelativeStandardnessBlockSupport
  HironakaActualRelativeStandardnessCoordinateJetSpanning
  HironakaActualRelativeStandardnessNormalPointBridge
variable {n : ℕ}

private theorem normal_tangent_weight (A : Set (Fin n)) (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight A) α +
      Finsupp.weight (actualCoordinateWeight Aᶜ) α = normalExponentDegree α := by
  rw [Finsupp.weight_eq_sum, Finsupp.weight_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ A <;> simp [actualCoordinateWeight, hi]

private theorem coordinate_le_weight (A : Set (Fin n)) (α : Fin n →₀ ℕ)
    (i : Fin n) (hi : i ∈ A) : α i ≤ Finsupp.weight (actualCoordinateWeight A) α := by
  rw [Finsupp.weight_eq_sum]
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
    Nat.zero_le (α j • actualCoordinateWeight A j)) (Finset.mem_univ i)
  simpa only [actualCoordinateWeight, if_pos hi, smul_eq_mul, mul_one] using h

private theorem vertex_mark_eq_degree_of_pure (A : Set (Fin n))
    (α : Fin n →₀ ℕ) (hz : ∀ i ∉ A, α i = 0) :
    Finsupp.weight (actualCoordinateWeight A) α = normalExponentDegree α := by
  rw [Finsupp.weight_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ A
  · simp only [actualCoordinateWeight, if_pos hi, smul_eq_mul, mul_one]
  · simp only [actualCoordinateWeight, if_neg hi, hz i hi, zero_smul]

/-- The actual tangent initial hypothesis makes the SAME normal vertex mark
its total degree; it does not make the full source member tangent independent. -/
theorem actual_normal_vertex_mark_eq_degree
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n))
    (hD : ∀ i ∉ A, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    Finsupp.weight (actualCoordinateWeight A) a.val = normalExponentDegree a.val := by
  apply vertex_mark_eq_degree_of_pure A a.val
  intro i hi
  exact actualInitialVertex_coordinate_eq_zero_of_pderiv_stable MonomialOrder.degLex
    (actualHomogeneousInitialIdeal K) i (hD i hi) (actualHomogeneousInitialVertex K a)

private theorem component_mem_coordinate_power (A : Set (Fin n)) (μ d : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ) :
    MvPowerSeries.homogeneousComponent d F ∈ actualFormalCoordinateIdeal n A ^ μ := by
  apply (mem_actualFormalCoordinateIdeal_pow_iff A μ _).mpr
  intro α hα
  rw [MvPowerSeries.coeff_homogeneousComponent]
  split_ifs
  · exact (mem_actualFormalCoordinateIdeal_pow_iff A μ F).mp hF α hα
  · rfl

private theorem homogeneous_normal_tangent_weight_zero (A : Set (Fin n)) (μ : ℕ)
    (H : MvPowerSeries (Fin n) ℂ) (hH : H.IsHomogeneous μ)
    (hPow : H ∈ actualFormalCoordinateIdeal n A ^ μ)
    (α : Fin n →₀ ℕ) (hα : MvPowerSeries.coeff α H ≠ 0) :
    Finsupp.weight (actualCoordinateWeight Aᶜ) α = 0 := by
  have hd : normalExponentDegree α = μ := by
    simpa only [Finsupp.weight_eq_sum, Pi.one_apply, smul_eq_mul, mul_one,
      normalExponentDegree] using hH hα
  have hw : μ ≤ Finsupp.weight (actualCoordinateWeight A) α := by
    by_contra h
    exact hα ((mem_actualFormalCoordinateIdeal_pow_iff A μ H).mp hPow α (by omega))
  have hsum := normal_tangent_weight A α
  omega

private theorem homogeneous_normal_pderiv_tangent_zero (A : Set (Fin n)) (μ : ℕ)
    (H : MvPowerSeries (Fin n) ℂ) (hH : H.IsHomogeneous μ)
    (hPow : H ∈ actualFormalCoordinateIdeal n A ^ μ) (i : Fin n) (hi : i ∉ A) :
    MvPowerSeries.pderiv ℂ i H = 0 := by
  apply MvPowerSeries.ext
  intro α
  have hz : MvPowerSeries.coeff (α + Finsupp.single i 1) H = 0 := by
    by_contra hne
    have hw := homogeneous_normal_tangent_weight_zero A μ H hH hPow _ hne
    have hle := coordinate_le_weight Aᶜ (α + Finsupp.single i 1) i hi
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, hw] at hle
    omega
  rw [MvPowerSeries.coeff_pderiv, hz, zero_mul, map_zero]

private def initialVertexEquiv (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    actualInitialVertices MonomialOrder.degLex K ≃
      actualInitialVertices MonomialOrder.degLex (actualHomogeneousInitialIdeal K) where
  toFun := actualHomogeneousInitialVertex K
  invFun a := ⟨a.val, by
    simpa only [actualInitialVertices, actual_homogeneous_initial_ideal_diagram] using a.property⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext rfl

private theorem partial_stable_span (S : Set (MvPowerSeries (Fin n) ℂ)) (i : Fin n)
    (hS : ∀ F ∈ S, MvPowerSeries.pderiv ℂ i F = 0) :
    ∀ F ∈ Ideal.span S, MvPowerSeries.pderiv ℂ i F ∈ Ideal.span S := by
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F hF => rw [hS F hF]; exact Ideal.zero_mem _
  | zero => rw [map_zero]; exact Ideal.zero_mem _
  | add F G _ _ hF hG => simpa only [map_add] using (Ideal.span S).add_mem hF hG
  | smul C F hF ih =>
      change MvPowerSeries.pderiv ℂ i (C * F) ∈ Ideal.span S
      rw [Derivation.leibniz]
      exact (Ideal.span S).add_mem ((Ideal.span S).mul_mem_left C ih)
        ((Ideal.span S).mul_mem_right _ hF)

/-- After a genuine triangular normal shear, the retained SAME vertex powers
and pure-normal exponents internally reproduce whole tangent initial stability. -/
theorem actual_tangent_initial_stability_of_pure_vertices_normal_powers
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n))
    (hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i ∉ A, a.val i = 0)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      actualReducedVertexSeries MonomialOrder.degLex K a ∈ actualFormalCoordinateIdeal n A ^
        Finsupp.weight (actualCoordinateWeight A) a.val) :
    ∀ i ∉ A, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K := by
  intro i hi
  rw [actual_formal_ideal_eq_span_reduced_vertex_series MonomialOrder.degLex
    (actualHomogeneousInitialIdeal K)]
  apply partial_stable_span
  rintro H ⟨a, rfl⟩
  obtain ⟨a, rfl⟩ := (initialVertexEquiv K).surjective a
  change MvPowerSeries.pderiv ℂ i (actualReducedVertexSeries MonomialOrder.degLex
    (actualHomogeneousInitialIdeal K) (actualHomogeneousInitialVertex K a)) = 0
  rw [← homogeneousComponent_actualReducedVertexSeries_eq_initial]
  apply homogeneous_normal_pderiv_tangent_zero A (normalExponentDegree a.val) _
    (MvPowerSeries.isHomogeneous_homogeneousComponent _ _) ?_ i hi
  apply component_mem_coordinate_power
  simpa only [vertex_mark_eq_degree_of_pure A a.val (hv a)] using hV a

private theorem blowup_zero_fixed_of_support (B : Set (Fin n)) (e : Fin n)
    (H : MvPowerSeries (Fin n) ℂ)
    (hH : ∀ α, MvPowerSeries.coeff α H ≠ 0 → actualMonomialBlowupExponent B e α = α) :
    actualFormalBlowup B e (fun _ => 0) H = H := by
  apply MvPowerSeries.ext
  intro α
  rw [actualFormalBlowup, MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (actualFormalBlowupCoordinates_constant_zero B e (fun _ => 0))) H α]
  rw [finsum_eq_single _ α]
  · by_cases hc : MvPowerSeries.coeff α H = 0
    · simp only [hc, zero_smul]
    · rw [actualFormalBlowup_zero_coordinate_product, hH α hc,
        MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
  · intro β hβ
    by_cases hc : MvPowerSeries.coeff β H = 0
    · rw [hc, zero_smul]
    · rw [actualFormalBlowup_zero_coordinate_product, hH β hc,
        MvPowerSeries.coeff_monomial, if_neg (Ne.symm hβ), smul_zero]

private theorem tangentScaling_fixed_of_homogeneous_normal (A : Set (Fin n)) (e : Fin n)
    (he : e ∈ A) (μ : ℕ) (H : MvPowerSeries (Fin n) ℂ) (hH : H.IsHomogeneous μ)
    (hPow : H ∈ actualFormalCoordinateIdeal n A ^ μ) : actualTangentScaling A e H = H := by
  apply blowup_zero_fixed_of_support
  intro α hα
  have hw := homogeneous_normal_tangent_weight_zero A μ H hH hPow α hα
  have hset : Aᶜ \ {e} = Aᶜ := by
    ext i
    simp only [Set.mem_sdiff, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · exact And.left
    · intro hi
      refine ⟨hi, ?_⟩
      intro h
      subst i
      exact hi he
  change α + Finsupp.single e (Finsupp.weight (actualCoordinateWeight (Aᶜ \ {e})) α) = α
  rw [hset, hw, Finsupp.single_zero, add_zero]

private theorem point_power_of_normal_power (A : Set (Fin n)) (μ : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ) :
    F ∈ actualFormalCoordinateIdeal n Set.univ ^ μ := by
  have hI : actualFormalCoordinateIdeal n A ≤ actualFormalCoordinateIdeal n Set.univ := by
    apply Ideal.span_le.mpr
    rintro G ⟨i, hi, rfl⟩
    exact Ideal.subset_span ⟨i, mem_univ i, rfl⟩
  exact (pow_le_pow_left' hI μ) hF

/-- The SAME entire homogeneous normal head is literally fixed by its normal
zero-chart normalization. The tangent scaling is genuinely injective. -/
theorem actualNormalizedFormalMember_normal_zero_eq_of_homogeneous_independent
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (μ : ℕ)
    (H : MvPowerSeries (Fin n) ℂ) (hH : H.IsHomogeneous μ)
    (hD : MvPowerSeries.pderiv ℂ e H = 0)
    (hPow : H ∈ actualFormalCoordinateIdeal n A ^ μ) :
    actualNormalizedFormalMember A e he (fun _ => 0) μ H hPow = H := by
  apply actualFormalBlowup_zero_injective Aᶜ e
  change actualTangentScaling A e (actualNormalizedFormalMember A e he (fun _ => 0) μ H hPow) =
    actualTangentScaling A e H
  have hpoint := actualNormalizedPointMember_eq_tangentScaling_normal A e he (fun _ => 0) μ H hPow
  have hz : actualNormalPointDirection A (fun _ => 0) = (fun _ => 0) := by
    funext i
    simp [actualNormalPointDirection]
  rw [hz] at hpoint
  rw [← hpoint, actualNormalizedFormalMember_zero_eq_of_homogeneous_independent e μ H hH hD,
    tangentScaling_fixed_of_homogeneous_normal A e he μ H hH hPow]

private theorem tail_mem_normal_power (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n))
    (hD : ∀ i ∉ A, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      actualReducedVertexSeries MonomialOrder.degLex K a ∈ actualFormalCoordinateIdeal n A ^
        Finsupp.weight (actualCoordinateWeight A) a.val)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    actualCanonicalHigherTail K a ∈ actualFormalCoordinateIdeal n A ^ normalExponentDegree a.val := by
  have hR : actualReducedVertexSeries MonomialOrder.degLex K a ∈
      actualFormalCoordinateIdeal n A ^ normalExponentDegree a.val := by
    simpa only [actual_normal_vertex_mark_eq_degree K A hD a] using hV a
  exact (actualFormalCoordinateIdeal n A ^ normalExponentDegree a.val).sub_mem hR
    (component_mem_coordinate_power A _ _ _ hR)

private theorem diagram_depends_on_block_of_vertices (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (B : Set (Fin n))
    (hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i ∉ B, a.val i = 0)
    (α β : Fin n →₀ ℕ) (heq : ∀ i ∈ B, α i = β i) :
    (α ∈ actualInitialDiagram MonomialOrder.degLex K ↔
      β ∈ actualInitialDiagram MonomialOrder.degLex K) := by
  constructor
  · intro hα
    obtain ⟨a, ha, hle⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K α).mp hα
    apply (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K β).mpr
    refine ⟨a, ha, ?_⟩
    intro i
    by_cases hi : i ∈ B
    · rw [← heq i hi]
      exact hle i
    · rw [hv ⟨a, ha⟩ i hi]
      exact Nat.zero_le _
  · intro hβ
    obtain ⟨a, ha, hle⟩ := (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K β).mp hβ
    apply (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K α).mpr
    refine ⟨a, ha, ?_⟩
    intro i
    by_cases hi : i ∈ B
    · rw [heq i hi]
      exact hle i
    · rw [hv ⟨a, ha⟩ i hi]
      exact Nat.zero_le _

/-- The forbidden-block theorem applies to A\{e}, not to a fictitious point
chart. All source canonical tail coefficients on the ENTIRE D are zero. -/
theorem actualNormalized_normal_canonical_tail_diagram_coefficients_zero
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A)
    (hD : ∀ i ∉ A, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K)
    (heD : ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ e F ∈ actualHomogeneousInitialIdeal K)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      actualReducedVertexSeries MonomialOrder.degLex K a ∈ actualFormalCoordinateIdeal n A ^
        Finsupp.weight (actualCoordinateWeight A) a.val)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    ∀ γ ∈ actualInitialDiagram MonomialOrder.degLex K, MvPowerSeries.coeff γ
      (actualNormalizedFormalMember A e he (fun _ => 0) (normalExponentDegree a.val)
        (actualCanonicalHigherTail K a) (tail_mem_normal_power K A hD hV a)) = 0 := by
  have hv : ∀ a : actualInitialVertices MonomialOrder.degLex K, ∀ i ∉ A \ {e}, a.val i = 0 := by
    intro a i hi
    by_cases hiA : i ∈ A
    · have hie : i = e := by
        by_contra h
        exact hi ⟨hiA, by simpa only [Set.mem_singleton_iff] using h⟩
      subst i
      exact actualInitialVertex_coordinate_eq_zero_of_pderiv_stable MonomialOrder.degLex
        (actualHomogeneousInitialIdeal K) e heD (actualHomogeneousInitialVertex K a)
    · exact actualInitialVertex_coordinate_eq_zero_of_pderiv_stable MonomialOrder.degLex
        (actualHomogeneousInitialIdeal K) i (hD i hiA) (actualHomogeneousInitialVertex K a)
  have hzero (α : Fin n →₀ ℕ) (hα : α ∈ actualInitialDiagram MonomialOrder.degLex K) :
      MvPowerSeries.coeff α (actualCanonicalHigherTail K a) = 0 := by
    have hαJ : α ∈ actualInitialDiagram MonomialOrder.degLex (actualHomogeneousInitialIdeal K) := by
      rwa [actual_homogeneous_initial_ideal_diagram]
    rw [actualCanonicalHigherTail, actualCanonicalLeadingHead, map_sub,
      homogeneousComponent_actualReducedVertexSeries_eq_initial,
      actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex K a α hα,
      actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex (actualHomogeneousInitialIdeal K)
        (actualHomogeneousInitialVertex K a) α hαJ]
    exact sub_self _
  exact actualNormalizedFormalMember_forbidden_block_support A (A \ {e}) e he (fun _ => 0)
    (fun _ hi => hi.1) (by simp) (fun _ _ => rfl) _ _ (tail_mem_normal_power K A hD hV a)
    (fun α => α ∈ actualInitialDiagram MonomialOrder.degLex K)
    (diagram_depends_on_block_of_vertices K (A \ {e}) hv) hzero

private theorem truncation_remainder (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    F - (MvPowerSeries.truncTotal q F : MvPowerSeries (Fin n) ℂ) ∈ genuineFormalVariables n ^ q := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
  intro α hα
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal]
  · exact sub_self _
  · simpa only [normalExponentDegree, Finsupp.degree_eq_sum] using hα

/-- ONLY original tangent initial stability, SAME canonical normal powers, and
actual normal strict/source HS equality force these SAME zero-chart orders. -/
theorem actualNormalizedReducedFormalVertex_normal_zero_mem_degree_power_of_hs_eq
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A)
    (hD : ∀ i ∉ A, ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ i F ∈ actualHomogeneousInitialIdeal K)
    (hV : ∀ a : actualInitialVertices MonomialOrder.degLex K,
      actualReducedVertexSeries MonomialOrder.degLex K a ∈ actualFormalCoordinateIdeal n A ^
        Finsupp.weight (actualCoordinateWeight A) a.val)
    (hHS : ∀ ℓ : ℕ, genuineFormalHilbertSamuelValue n
      (actualFormalStrictTransform K A e he (fun _ => 0)) ℓ = genuineFormalHilbertSamuelValue n K ℓ)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    actualNormalizedReducedFormalVertex MonomialOrder.degLex K A e he (fun _ => 0) hV a ∈
      genuineFormalVariables n ^ normalExponentDegree a.val := by
  let μ := normalExponentDegree a.val
  by_cases hμ : μ = 0
  · simp only [μ] at hμ
    simp only [hμ, pow_zero, Ideal.one_eq_top, Submodule.mem_top]
  have hμpos : 0 < μ := Nat.pos_of_ne_zero hμ
  have hcut : (μ - 1) + 1 = μ := by omega
  let I := actualFormalStrictTransform K A e he (fun _ => 0)
  let R := actualReducedVertexSeries MonomialOrder.degLex K a
  let H := actualCanonicalLeadingHead K a
  have heD : ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ e F ∈ actualHomogeneousInitialIdeal K := by
    intro F hF
    have hd := actual_homogeneous_initial_normal_directional_stable_of_hs_eq K A e he
      (fun _ => 0) hD hV hHS F hF
    simpa only [actualPointUnitBasePoint_apply, actualNormalPointDirection, ite_self,
      ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hd
  have hRpow : R ∈ actualFormalCoordinateIdeal n A ^ μ := by
    simpa only [actual_normal_vertex_mark_eq_degree K A hD a] using hV a
  have hHpow : H ∈ actualFormalCoordinateIdeal n A ^ μ := component_mem_coordinate_power A _ _ _ hRpow
  have hHhom : H.IsHomogeneous μ := MvPowerSeries.isHomogeneous_homogeneousComponent _ _
  have hHder : MvPowerSeries.pderiv ℂ e H = 0 := by
    exact pderiv_homogeneousComponent_actualReducedVertexSeries_eq_zero_of_stable K e heD a
  have hnormH := actualNormalizedFormalMember_normal_zero_eq_of_homogeneous_independent
    A e he μ H hHhom hHder hHpow
  let N := actualNormalizedFormalMember A e he (fun _ => 0) μ R hRpow
  let T := actualNormalizedFormalMember A e he (fun _ => 0) μ
    (actualCanonicalHigherTail K a) (tail_mem_normal_power K A hD hV a)
  have hsub : N - H = T := by
    apply actualNormalizedFormalMember_unique
    change (MvPowerSeries.X e) ^ μ * (N - H) = actualFormalBlowup A e (fun _ => 0) (R - H)
    rw [map_sub, mul_sub, actualNormalizedFormalMember_spec]
    have hp := actualNormalizedFormalMember_spec A e he (fun _ => 0) μ H hHpow
    rw [hnormH] at hp
    rw [hp]
  have hN : N ∈ I := by
    dsimp only [I]
    rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
    exact Ideal.subset_span ⟨μ, R, actualReducedVertexSeries_mem MonomialOrder.degLex K a, hRpow, rfl⟩
  have hpoint : actualFormalCoordinateIdeal n Set.univ = genuineFormalVariables n := by
    simp only [actualFormalCoordinateIdeal, Set.image_univ, genuineFormalVariables]
  have hHhigh : H ∈ genuineFormalVariables n ^ μ := by
    rw [← hpoint]
    exact point_power_of_normal_power A μ H hHpow
  have hTmem : T ∈ I ⊔ genuineFormalVariables n ^ μ := by
    rw [← hsub]
    exact (I ⊔ genuineFormalVariables n ^ μ).sub_mem (Ideal.mem_sup_left hN) (Ideal.mem_sup_right hHhigh)
  have hTnormal := actualNormalized_normal_canonical_tail_diagram_coefficients_zero K A e he hD heD hV a
  let P : MvPowerSeries (Fin n) ℂ := MvPowerSeries.truncTotal μ T
  have hrem : T - P ∈ genuineFormalVariables n ^ μ := truncation_remainder μ T
  have hPmem : P ∈ I ⊔ genuineFormalVariables n ^ μ := by
    have hm := (I ⊔ genuineFormalVariables n ^ μ).sub_mem hTmem (Ideal.mem_sup_right hrem)
    simpa only [sub_sub_cancel] using hm
  have hzDirection : actualNormalPointDirection A (fun _ => 0) = (fun _ => 0) := by
    funext i
    simp [actualNormalPointDirection]
  have hQ : actualDehomogenizedPointInitialConeIdeal K e (actualNormalPointDirection A (fun _ => 0)) =
      actualHomogeneousInitialIdeal K := by
    rw [hzDirection]
    exact actualDehomogenizedPointInitialConeIdeal_zero_eq_initial_of_pderiv_stable K e heD
  have hPsupport : ∀ α, MvPowerSeries.coeff α P ≠ 0 →
      normalExponentDegree α < (μ - 1) + 1 ∧ α ∉ actualInitialDiagram MonomialOrder.degLex
        (actualDehomogenizedPointInitialConeIdeal K e (actualNormalPointDirection A (fun _ => 0))) := by
    intro α hα
    have hc : MvPowerSeries.coeff α P =
        if Finsupp.degree α < μ then MvPowerSeries.coeff α T else 0 := by
      dsimp only [P]
      rw [MvPolynomial.coeff_coe, MvPowerSeries.coeff_truncTotal_eq_ite]
    by_cases hd : Finsupp.degree α < μ
    · rw [if_pos hd] at hc
      refine ⟨by simpa only [hcut, normalExponentDegree, Finsupp.degree_eq_sum] using hd, ?_⟩
      rw [hQ, actual_homogeneous_initial_ideal_diagram]
      intro hdiag
      exact hα (hc.trans (hTnormal α hdiag))
    · exact False.elim (hα (by rw [hc, if_neg hd]))
  have hPzero := bounded_diagram_avoiding_series_eq_zero_of_dehomogenized_source_hs_eq K I e
    (actualNormalPointDirection A (fun _ => 0)) (actualNormalPointFibreVariables A e)
    (actual_normal_strict_fibre_eq_dehomogenized_point_model K A e he (fun _ => 0) hD hV)
    (actual_dehomogenized_point_model_coordinate_cylinder_of_tangent_initial_stability K A e he (fun _ => 0) hD)
    (μ - 1) (hHS (μ - 1)) P hPsupport (by simpa only [hcut] using hPmem)
  have hTpow : T ∈ genuineFormalVariables n ^ μ := by simpa only [hPzero, sub_zero] using hrem
  have hNpow : N ∈ genuineFormalVariables n ^ μ := by
    have hm := (genuineFormalVariables n ^ μ).add_mem hTpow hHhigh
    rw [← hsub, sub_add_cancel] at hm
    exact hm
  let V := actualNormalizedReducedFormalVertex MonomialOrder.degLex K A e he (fun _ => 0) hV a
  have hspec : (MvPowerSeries.X e) ^ Finsupp.weight (actualCoordinateWeight A) a.val * V =
      actualFormalBlowup A e (fun _ => 0) R :=
    actualNormalizedFormalMember_spec A e he (fun _ => 0) _
      (actualReducedVertexSeries MonomialOrder.degLex K a) (hV a)
  rw [actual_normal_vertex_mark_eq_degree K A hD a] at hspec
  have hVN : V = N := actualNormalizedFormalMember_unique A e he (fun _ => 0) μ R hRpow V hspec
  change V ∈ genuineFormalVariables n ^ μ
  rw [hVN]
  exact hNpow

end
end Hironaka.HironakaActualCanonicalNormalZeroDirectionOrder
