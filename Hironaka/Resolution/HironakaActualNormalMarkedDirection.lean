import Hironaka.Resolution.HironakaActualNormalZeroFormalSaturation
import Hironaka.Resolution.HironakaActualRelativeStandardnessNormalPointBridge
import Hironaka.Resolution.HironakaActualPointExceptionalFibreRadial
import Hironaka.Resolution.HironakaActualCanonicalDirectionPivot

/-! Actual marked orders of SAME normal members produce their finite leading
polynomial directional annihilation and an internally chosen unused pivot.
There is no HS, canonicality, target diagram or direction certificate input.
Source-only draft; no kernel acceptance is asserted. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualNormalMarkedDirection
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalBlowupAllDirections
  HironakaActualFormalStrictGenerators HironakaActualReducedBasisDivision
  HironakaActualNormalZeroFormalSaturation HironakaActualRelativeStandardnessNormalPointBridge
  HironakaActualPointExceptionalInitialForm HironakaActualPointDehomogenizedInitial
  HironakaActualPointExceptionalFibreRadial HironakaActualCanonicalDirectionPivot
variable {n : ℕ}

/-- The actual normal direction at the e-chart origin; tangent entries are zero. -/
def actualNormalMarkedDirection (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) : Fin n → ℂ :=
  fun i => if i=e then 1 else actualNormalPointDirection A b i

private theorem map_variables_le_blowup (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    Ideal.map (actualFormalBlowup A e b).toRingHom (genuineFormalVariables n) ≤ genuineFormalVariables n := by
  rw [genuineFormalVariables, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro G ⟨F, ⟨i, rfl⟩, rfl⟩
  change actualFormalBlowup A e b (MvPowerSeries.X i) ∈ genuineFormalVariables n
  rw [actualFormalBlowup_X, actualFormalBlowupCoordinates]
  split_ifs
  · exact Ideal.subset_span ⟨e, rfl⟩
  · exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨e, rfl⟩)
  · exact Ideal.subset_span ⟨i, rfl⟩

private theorem map_variables_le_projection (e : Fin n) :
    Ideal.map (actualPointExceptionalProjection e).toRingHom (genuineFormalVariables n) ≤ genuineFormalVariables n := by
  rw [genuineFormalVariables, Ideal.map_span]
  apply Ideal.span_le.mpr
  rintro G ⟨F, ⟨i, rfl⟩, rfl⟩
  change actualPointExceptionalProjection e (MvPowerSeries.X i) ∈ genuineFormalVariables n
  rw [actualPointExceptionalProjection_X]
  split_ifs
  · exact Ideal.zero_mem _
  · exact Ideal.subset_span ⟨i, rfl⟩

private theorem map_power_of_map_variables_le
    (φ : MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ)
    (hφ : Ideal.map φ.toRingHom (genuineFormalVariables n) ≤ genuineFormalVariables n)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ genuineFormalVariables n ^ μ) :
    φ F ∈ genuineFormalVariables n ^ μ := by
  have h := Ideal.mem_map_of_mem φ.toRingHom hF
  rw [Ideal.map_pow] at h
  exact (pow_le_pow_left' hφ μ) h

private theorem coordinate_power_le_point (A : Set (Fin n)) (μ : ℕ) :
    actualFormalCoordinateIdeal n A ^ μ ≤ actualFormalCoordinateIdeal n Set.univ ^ μ := by
  apply pow_le_pow_left'
  apply Ideal.span_le.mpr
  rintro F ⟨i, _hi, rfl⟩
  exact Ideal.subset_span ⟨i, mem_univ i, rfl⟩

private theorem dehom_totalDegree_le (e : Fin n) (b : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ) :
    (actualPointDehomogenization e b P).totalDegree ≤ P.totalDegree := by
  have hlin (i : Fin n) :
      (if i=e then (1 : MvPolynomial (Fin n) ℂ) else MvPolynomial.C (b i)+MvPolynomial.X i).totalDegree ≤ 1 := by
    split_ifs
    · simp
    · exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  conv_lhs => rw [← P.support_sum_monomial_coeff, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro α hα
  change (MvPolynomial.aeval (fun i => if i=e then 1 else MvPolynomial.C (b i)+MvPolynomial.X i)
    (MvPolynomial.monomial α (MvPolynomial.coeff α P))).totalDegree ≤ _
  rw [MvPolynomial.aeval_monomial]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  change (MvPolynomial.C (MvPolynomial.coeff α P)).totalDegree + _ ≤ _
  rw [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
    (by simpa using Nat.mul_le_mul_left (α i) (hlin i)))
  exact MvPolynomial.le_totalDegree hα

/-- Genuine normalized orders force the finite dehomogenized leading polynomial
itself to be homogeneous at the unchanged original mark. -/
theorem actual_normal_marked_shadow_isHomogeneous
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ)
    (horder : actualNormalizedFormalMember A e he b μ F hF ∈ genuineFormalVariables n ^ μ) :
    (actualPointDehomogenization e (actualNormalPointDirection A b)
      (actualPointHomogeneousPolynomial μ F)).IsHomogeneous μ := by
  let P := actualPointHomogeneousPolynomial μ F
  let Q := actualPointDehomogenization e (actualNormalPointDirection A b) P
  have hp := coordinate_power_le_point A μ hF
  let H := actualNormalizedFormalMember Set.univ e (mem_univ e) (actualNormalPointDirection A b) μ F hp
  have hH : H ∈ genuineFormalVariables n ^ μ := by
    rw [show H = actualTangentScaling A e (actualNormalizedFormalMember A e he b μ F hF) from
      actualNormalizedPointMember_eq_tangentScaling_normal A e he b μ F hF]
    exact map_power_of_map_variables_le (actualTangentScaling A e)
      (map_variables_le_blowup Aᶜ e (fun _ => 0)) μ _ horder
  have hdiff : H - (Q : MvPowerSeries (Fin n) ℂ) ∈ Ideal.span {MvPowerSeries.X e} :=
    actual_point_normalized_member_congr_dehomogenization e (actualNormalPointDirection A b) μ F hp
  have hproj : actualPointExceptionalProjection e H = (Q : MvPowerSeries (Fin n) ℂ) := by
    have hzero : Ideal.map (actualPointExceptionalProjection e).toRingHom
        (Ideal.span {(MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ)}) = ⊥ := by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {actualPointExceptionalProjection e (MvPowerSeries.X e)} = ⊥
      rw [actualPointExceptionalProjection_X, if_pos rfl]
      simp
    have h := Ideal.mem_map_of_mem (actualPointExceptionalProjection e).toRingHom hdiff
    rw [hzero, Ideal.mem_bot, map_sub] at h
    change actualPointExceptionalProjection e H - actualPointExceptionalProjection e (Q : MvPowerSeries (Fin n) ℂ) = 0 at h
    have hfix : actualPointExceptionalProjection e (Q : MvPowerSeries (Fin n) ℂ) = (Q : MvPowerSeries (Fin n) ℂ) :=
      actualPointExceptionalProjection_dehomogenization e (actualNormalPointDirection A b) P
    rw [hfix] at h
    exact sub_eq_zero.mp h
  have hQ : (Q : MvPowerSeries (Fin n) ℂ) ∈ genuineFormalVariables n ^ μ := by
    rw [← hproj]
    exact map_power_of_map_variables_le (actualPointExceptionalProjection e)
      (map_variables_le_projection e) μ H hH
  intro α hα
  have hc : MvPowerSeries.coeff α (Q : MvPowerSeries (Fin n) ℂ) ≠ 0 := by
    simpa only [MvPolynomial.coeff_coe] using hα
  have hlo : μ ≤ normalExponentDegree α := by
    by_contra h
    exact hc ((mem_genuineFormalVariables_pow_iff_coefficients_zero n μ _).mp hQ α (lt_of_not_ge h))
  have hdegree_sum : α.degree = normalExponentDegree α := by
    rw [Finsupp.degree_eq_sum]
    rfl
  have hhi : normalExponentDegree α ≤ μ := by
    have hd : (α.sum fun _ k => k) ≤ Q.totalDegree :=
      MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hα)
    rw [α.sum_fintype (fun _ k => k) (fun _ => rfl)] at hd
    exact hd.trans ((dehom_totalDegree_le e (actualNormalPointDirection A b) P).trans
      (actualPointHomogeneousPolynomial_isHomogeneous μ F).totalDegree_le)
  have hdegree : α.degree = μ := hdegree_sum.trans (le_antisymm hhi hlo)
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hdegree

private theorem dehom_pivot_independent (e : Fin n) (b : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ)
    (α : Fin n →₀ ℕ) (hα : α ∈ (actualPointDehomogenization e b P).support) : α e = 0 := by
  have hfix := congrArg (MvPowerSeries.coeff α) (actualPointExceptionalProjection_dehomogenization e b P)
  rw [coeff_actualPointExceptionalProjection] at hfix
  by_contra h
  rw [if_neg h] at hfix
  exact (MvPolynomial.mem_support_iff.mp hα) (by simpa only [MvPolynomial.coeff_coe] using hfix.symm)

private theorem dehom_zero_of_pivot_independent (e : Fin n) (P : MvPolynomial (Fin n) ℂ)
    (hP : ∀ α ∈ P.support, α e = 0) : actualPointDehomogenization e (fun _ => 0) P = P := by
  conv_lhs => rw [← P.support_sum_monomial_coeff, map_sum]
  conv_rhs => rw [← P.support_sum_monomial_coeff]
  apply Finset.sum_congr rfl
  intro α hα
  rw [actualPointDehomogenization, MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hie : i ≠ e := by
    intro h
    subst i
    exact (Finsupp.mem_support_iff.mp hi) (hP α hα)
  simp [hie]

private theorem centerShear_eq_dehom_of_homogeneous_dehom
    (e : Fin n) (b : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ) (μ : ℕ)
    (hP : P.IsHomogeneous μ) (hQ : (actualPointDehomogenization e b P).IsHomogeneous μ) :
    actualFormalCenterShear Set.univ e b (P : MvPowerSeries (Fin n) ℂ) =
      (actualPointDehomogenization e b P : MvPowerSeries (Fin n) ℂ) := by
  apply actualFormalBlowup_injective Set.univ e (mem_univ e) (fun _ => 0)
  rw [← actualFormalBlowup_eq_zero_comp_centerShear Set.univ e (mem_univ e) b,
    actualFormalBlowup_homogeneous_polynomial e b P μ hP,
    actualFormalBlowup_homogeneous_polynomial e (fun _ => 0) _ μ hQ,
    dehom_zero_of_pivot_independent e _ (dehom_pivot_independent e b P)]

private def markedDirectionDerivation (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) :
    Derivation ℂ (MvPowerSeries (Fin n) ℂ) (MvPowerSeries (Fin n) ℂ) :=
  ∑ i : Fin n, actualNormalMarkedDirection A e b i • MvPowerSeries.pderiv ℂ i

private theorem markedDirectionDerivation_apply (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ)
    (F : MvPowerSeries (Fin n) ℂ) :
    markedDirectionDerivation A e b F = ∑ i : Fin n, actualNormalMarkedDirection A e b i • MvPowerSeries.pderiv ℂ i F := by
  have hs (s : Finset (Fin n)) : (∑ i ∈ s, actualNormalMarkedDirection A e b i • MvPowerSeries.pderiv ℂ i) F =
      ∑ i ∈ s, actualNormalMarkedDirection A e b i • MvPowerSeries.pderiv ℂ i F := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty, Derivation.zero_apply]
    | @insert i s hi ih => simp only [Finset.sum_insert hi, Derivation.add_apply, Derivation.smul_apply, ih]
  exact hs Finset.univ

private theorem markedDirectionDerivation_X (A : Set (Fin n)) (e i : Fin n) (b : Fin n → ℂ) :
    markedDirectionDerivation A e b (MvPowerSeries.X i) = MvPowerSeries.C (actualNormalMarkedDirection A e b i) := by
  rw [markedDirectionDerivation_apply]
  simp [MvPowerSeries.pderiv_X, Pi.single_apply, MvPowerSeries.smul_eq_C_mul]

private theorem pderiv_shear_coordinate (A : Set (Fin n)) (e i : Fin n) (b : Fin n → ℂ) :
    MvPowerSeries.pderiv ℂ e
      (actualFormalCenterShear Set.univ e (actualNormalPointDirection A b) (MvPowerSeries.X i)) =
        MvPowerSeries.C (actualNormalMarkedDirection A e b i) := by
  rw [actualFormalCenterShear_X, actualFormalCenterShearCoordinates]
  by_cases hi : i=e
  · subst i
    simp [actualNormalMarkedDirection]
  · simp [hi, Set.mem_sdiff, actualNormalMarkedDirection, Derivation.leibniz, smul_eq_mul]

private theorem markedDirection_polynomial_chain_rule
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ) :
    actualFormalCenterShear Set.univ e (actualNormalPointDirection A b)
      (markedDirectionDerivation A e b (P : MvPowerSeries (Fin n) ℂ)) =
        MvPowerSeries.pderiv ℂ e
          (actualFormalCenterShear Set.univ e (actualNormalPointDirection A b) (P : MvPowerSeries (Fin n) ℂ)) := by
  let S := actualFormalCenterShear Set.univ e (actualNormalPointDirection A b)
  let D := markedDirectionDerivation A e b
  induction P using MvPolynomial.induction_on with
  | C c =>
    simp only [MvPolynomial.coe_C, MvPowerSeries.c_eq_algebraMap, Derivation.map_algebraMap,
      map_zero, AlgHom.commutes]
  | add P Q hP hQ => simpa only [MvPolynomial.coe_add, map_add] using congrArg₂ (·+·) hP hQ
  | mul_X P i hP =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      map_add, map_mul, map_mul, markedDirectionDerivation_X]
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderiv_shear_coordinate]
    rw [hP]
    have hC : actualFormalCenterShear Set.univ e (actualNormalPointDirection A b)
        (MvPowerSeries.C (actualNormalMarkedDirection A e b i)) =
          MvPowerSeries.C (actualNormalMarkedDirection A e b i) := by
      simpa only [MvPowerSeries.c_eq_algebraMap] using
        (actualFormalCenterShear Set.univ e (actualNormalPointDirection A b)).commutes
          (actualNormalMarkedDirection A e b i)
    rw [hC]

/-- Genuine normal marked orders annihilate the SAME finite leading polynomial
in the actual normal direction. No whole initial stability or HS premise. -/
theorem actual_normal_marked_leading_directional_derivative_zero
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ)
    (horder : actualNormalizedFormalMember A e he b μ F hF ∈ genuineFormalVariables n ^ μ) :
    (∑ i : Fin n, actualNormalMarkedDirection A e b i • MvPowerSeries.pderiv ℂ i
      (MvPowerSeries.homogeneousComponent μ F)) = 0 := by
  have hhom := actual_normal_marked_shadow_isHomogeneous A e he b μ F hF horder
  let P := actualPointHomogeneousPolynomial μ F
  have hS := centerShear_eq_dehom_of_homogeneous_dehom e (actualNormalPointDirection A b) P μ
    (actualPointHomogeneousPolynomial_isHomogeneous μ F) hhom
  have hchain := markedDirection_polynomial_chain_rule A e b P
  rw [hS, pderiv_actualPointDehomogenization_eq_zero] at hchain
  have hz : markedDirectionDerivation A e b (P : MvPowerSeries (Fin n) ℂ) = 0 := by
    apply (actualFormalCenterShearAlgEquiv Set.univ e (actualNormalPointDirection A b)).injective
    change actualFormalCenterShear Set.univ e (actualNormalPointDirection A b)
      (markedDirectionDerivation A e b (P : MvPowerSeries (Fin n) ℂ)) =
        actualFormalCenterShear Set.univ e (actualNormalPointDirection A b) 0
    simpa only [map_zero] using hchain
  simpa only [markedDirectionDerivation_apply, P, actualPointHomogeneousPolynomial_coe] using hz

private theorem monic_leading_direction_pivot_zero
    (v : Fin n → ℂ) (f : Fin n) (hvf : v f ≠ 0)
    (hmax : ∀ i, v i ≠ 0 → MonomialOrder.degLex.toSyn (Finsupp.single i 1) ≤
      MonomialOrder.degLex.toSyn (Finsupp.single f 1))
    (a : Fin n →₀ ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hmonic : MvPowerSeries.coeff a F = 1)
    (hlower : ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a → MvPowerSeries.coeff β F = 0)
    (hDir : (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i
      (MvPowerSeries.homogeneousComponent (normalExponentDegree a) F)) = 0) : a f = 0 := by
  by_contra haf
  have hafpos : 0 < a f := Nat.pos_of_ne_zero haf
  let c := a - Finsupp.single f 1
  have hsingle : Finsupp.single f 1 ≤ a := by
    intro i
    by_cases hi : i=f
    · subst i
      simpa only [Finsupp.single_eq_same] using Nat.succ_le_iff.mpr hafpos
    · simp [Finsupp.single_eq_of_ne hi]
  have hca : c + Finsupp.single f 1 = a := tsub_add_cancel_of_le hsingle
  have hzero := congrArg (MvPowerSeries.coeff c) hDir
  rw [map_sum, map_zero] at hzero
  have hsum : (∑ i : Fin n, MvPowerSeries.coeff c (v i • MvPowerSeries.pderiv ℂ i
      (MvPowerSeries.homogeneousComponent (normalExponentDegree a) F))) =
        v f * ((c f+1 : ℕ) : ℂ) := by
    rw [Finset.sum_eq_single f]
    · rw [map_smul, MvPowerSeries.coeff_pderiv, hca, MvPowerSeries.coeff_homogeneousComponent]
      simp only [Finsupp.degree_eq_sum, normalExponentDegree, if_true, hmonic, one_mul, smul_eq_mul, Nat.cast_add, Nat.cast_one]
    · intro i _ hif
      by_cases hvi : v i=0
      · simp [hvi]
      · have hne : MonomialOrder.degLex.toSyn (Finsupp.single i 1) ≠
            MonomialOrder.degLex.toSyn (Finsupp.single f 1) := by
          intro heq
          exact hif (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)
            (MonomialOrder.degLex.toSyn.injective heq))
        have hlt := lt_of_le_of_ne (hmax i hvi) hne
        have hci : MonomialOrder.degLex.toSyn (c+Finsupp.single i 1) < MonomialOrder.degLex.toSyn a := by
          rw [← hca, map_add, map_add]
          simpa only [add_comm] using add_lt_add_left hlt (MonomialOrder.degLex.toSyn c)
        rw [map_smul, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_homogeneousComponent]
        simp only [hlower _ hci, ite_self, zero_mul, smul_zero]
    · intro hf
      exact (hf (Finset.mem_univ f)).elim
  rw [hsum] at hzero
  have hnat : ((c f+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (c f)
  exact (mul_ne_zero hvf hnat) hzero

/-- Natural marked orders internally choose one actual normal direction pivot
and prove it absent from EVERY source vertex of the SAME full monic family. -/
theorem exists_actual_normal_unused_pivot_of_marked_orders
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (B : ActualMonicVertexFamily MonomialOrder.degLex K)
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hpower : ∀ a, B.series a ∈ actualFormalCoordinateIdeal n A ^ normalExponentDegree a.val)
    (horder : ∀ a, actualNormalizedFormalMember A e he b (normalExponentDegree a.val)
      (B.series a) (hpower a) ∈ genuineFormalVariables n ^ normalExponentDegree a.val) :
    ∃ f : Fin n, f ∈ A ∧ actualNormalMarkedDirection A e b f ≠ 0 ∧
      (∀ i, actualNormalMarkedDirection A e b i ≠ 0 →
        MonomialOrder.degLex.toSyn (Finsupp.single i 1) ≤ MonomialOrder.degLex.toSyn (Finsupp.single f 1)) ∧
      ∀ a : actualInitialVertices MonomialOrder.degLex K, a.val f = 0 := by
  let v := actualNormalMarkedDirection A e b
  have hv : ∃ i, v i ≠ 0 := ⟨e, by simp only [v, actualNormalMarkedDirection, if_true]; exact one_ne_zero⟩
  obtain ⟨f, hvf, hmax⟩ := exists_direction_maximal_coordinate MonomialOrder.degLex v hv
  have hfA : f ∈ A := by
    by_contra hf
    have hfe : f ≠ e := by intro h; subst f; exact hf he
    exact hvf (by simp [v, actualNormalMarkedDirection, hfe, actualNormalPointDirection, hf])
  refine ⟨f, hfA, hvf, hmax, ?_⟩
  intro a
  exact monic_leading_direction_pivot_zero v f hvf hmax a.val (B.series a) (B.monic a) (B.lower a)
    (actual_normal_marked_leading_directional_derivative_zero A e he b _ (B.series a) (hpower a) (horder a))

end
end Hironaka.HironakaActualNormalMarkedDirection
