import Hironaka.Resolution.HironakaActualCanonicalDirectionPivot
import Hironaka.Resolution.HironakaActualPointNormalizedHomogeneous
import Hironaka.Resolution.HironakaActualExceptionalNormalJetSeparation
import Hironaka.Resolution.HironakaActualConeEqualityDirectionalStability
import Hironaka.Resolution.HironakaActualRelativeStandardnessBlockSupport

/-! Actual HS equality preserves each SAME canonical reduced order in the zero-direction point chart. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualCanonicalZeroDirectionOrder
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualFormalStrictGenerators HironakaActualCoefficientReducedStrictGenerators
  HironakaActualPointCentreStrictGenerators HironakaActualHomogeneousInitialHS
  HironakaActualCanonicalVertexDirectionalInvariance HironakaActualCanonicalDirectionPivot
  HironakaActualPointExceptionalInitialForm HironakaActualPointDehomogenizedInitial
  HironakaActualPointExceptionalFibre HironakaActualPointExceptionalFibreRadial
  HironakaActualPointNormalizedHomogeneous HironakaActualExceptionalFibreJetClasses
  HironakaActualExceptionalNormalJetSeparation HironakaActualConeEqualityDirectionalStability
  HironakaActualRelativeStandardnessBlockSupport
variable {n : ℕ}

private theorem point_weight_eq_degree (α : Fin n →₀ ℕ) :
    Finsupp.weight (actualCoordinateWeight Set.univ) α=normalExponentDegree α := by
  simp [Finsupp.weight_eq_sum,actualCoordinateWeight,normalExponentDegree]

private theorem point_ideal_eq_variables :
    actualFormalCoordinateIdeal n Set.univ=genuineFormalVariables n := by
  simp only [actualFormalCoordinateIdeal,Set.image_univ,genuineFormalVariables]

private def initialVertexEquiv (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    actualInitialVertices MonomialOrder.degLex K ≃
      actualInitialVertices MonomialOrder.degLex (actualHomogeneousInitialIdeal K) where
  toFun := actualHomogeneousInitialVertex K
  invFun a := ⟨a.val,by
    simpa only [actualInitialVertices,actual_homogeneous_initial_ideal_diagram] using a.property⟩
  left_inv a := Subtype.ext rfl
  right_inv a := Subtype.ext rfl

private theorem map_exceptional_projection (e : Fin n) :
    Ideal.map (actualPointExceptionalProjection e).toRingHom (Ideal.span {MvPowerSeries.X e})=⊥ := by
  rw [Ideal.map_span,Set.image_singleton]
  change Ideal.span {actualPointExceptionalProjection e (MvPowerSeries.X e)}=⊥
  rw [actualPointExceptionalProjection_X,if_pos rfl,Ideal.span_singleton_zero]

private theorem projection_eq_zero_of_mem_exceptional (e : Fin n)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ Ideal.span {MvPowerSeries.X e}) :
    actualPointExceptionalProjection e F=0 := by
  have h := Ideal.mem_map_of_mem (actualPointExceptionalProjection e).toRingHom hF
  rw [map_exceptional_projection] at h
  exact Ideal.mem_bot.mp h

private theorem dehomogenization_eq_of_transverse_homogeneous (e : Fin n) (μ : ℕ)
    (P : MvPolynomial (Fin n) ℂ) (H : MvPowerSeries (Fin n) ℂ)
    (hPH : (P : MvPowerSeries (Fin n) ℂ)=H)
    (hH : H.IsHomogeneous μ) (hD : MvPowerSeries.pderiv ℂ e H=0)
    (hpow : H ∈ actualFormalCoordinateIdeal n Set.univ ^ μ) :
    (actualPointDehomogenization e (fun _ => 0) P : MvPowerSeries (Fin n) ℂ)=H := by
  have hP : actualPointHomogeneousPolynomial μ H=P := by
    apply MvPolynomial.coe_injective
    rw [actualPointHomogeneousPolynomial_coe]
    exact (MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp hH).symm.trans hPH.symm
  have hcongr := actual_point_normalized_member_congr_dehomogenization e (fun _ => 0) μ H hpow
  rw [actualNormalizedFormalMember_zero_eq_of_homogeneous_independent e μ H hH hD hpow,hP] at hcongr
  have hz := projection_eq_zero_of_mem_exceptional e _ hcongr
  rw [map_sub,actualPointExceptionalProjection_eq_self_of_pderiv_eq_zero e H hD,
    actualPointExceptionalProjection_dehomogenization] at hz
  exact (sub_eq_zero.mp hz).symm

private theorem map_initial_projection_of_pderiv_stable
    (J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n)
    (hD : ∀ F ∈ J, MvPowerSeries.pderiv ℂ e F ∈ J) :
    Ideal.map (actualPointExceptionalProjection e).toRingHom J=J := by
  rw [actual_formal_ideal_eq_span_reduced_vertex_series MonomialOrder.degLex J,
    Ideal.map_span,← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact actualPointExceptionalProjection_eq_self_of_pderiv_eq_zero e _
    (pderiv_actualReducedVertexSeries_eq_zero_of_stable MonomialOrder.degLex J e hD a)

/-- The actual whole zero-direction cone is the SAME source initial ideal when the axis is internally invariant. -/
theorem actualDehomogenizedPointInitialConeIdeal_zero_eq_initial_of_pderiv_stable
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n)
    (hD : ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ e F ∈ actualHomogeneousInitialIdeal K) :
    actualDehomogenizedPointInitialConeIdeal K e (fun _ => 0)=actualHomogeneousInitialIdeal K := by
  let J := actualHomogeneousInitialIdeal K
  let E := initialVertexEquiv K
  have hgen (a : actualInitialVertices MonomialOrder.degLex K) :
      (actualPointDehomogenization e (fun _ => 0)
        (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
          (actualReducedVertexSeries MonomialOrder.degLex K a)) : MvPowerSeries (Fin n) ℂ)=
        actualReducedVertexSeries MonomialOrder.degLex J (E a) := by
    let H := actualReducedVertexSeries MonomialOrder.degLex J (E a)
    have hhead : MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
        (actualReducedVertexSeries MonomialOrder.degLex K a)=H :=
      homogeneousComponent_actualReducedVertexSeries_eq_initial K a
    have hPH : (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
        (actualReducedVertexSeries MonomialOrder.degLex K a) : MvPowerSeries (Fin n) ℂ)=H := by
      rw [actualPointHomogeneousPolynomial_coe,hhead]
    have hhom : H.IsHomogeneous (normalExponentDegree a.val) := by
      rw [← hhead]
      exact MvPowerSeries.isHomogeneous_homogeneousComponent _ _
    have hpartial : MvPowerSeries.pderiv ℂ e H=0 :=
      pderiv_actualReducedVertexSeries_eq_zero_of_stable MonomialOrder.degLex J e hD (E a)
    have hpow : H ∈ actualFormalCoordinateIdeal n Set.univ ^ normalExponentDegree a.val := by
      have hEa : (E a).val = a.val := rfl
      simpa only [point_weight_eq_degree, hEa, H] using
        actualReducedVertexSeries_mem_point_power n J (E a)
    exact dehomogenization_eq_of_transverse_homogeneous e _ _ H hPH hhom hpartial hpow
  have hcanonical : actualCanonicalPointDehomogenizedIdeal K e (fun _ => 0)=J := by
    rw [actualCanonicalPointDehomogenizedIdeal]
    simp_rw [point_weight_eq_degree,hgen]
    calc
      Ideal.span (range (fun a => actualReducedVertexSeries MonomialOrder.degLex J (E a)))=
          Ideal.span (range (actualReducedVertexSeries MonomialOrder.degLex J)) := by
        apply congrArg Ideal.span
        ext F
        constructor
        · rintro ⟨a,rfl⟩
          exact ⟨E a,rfl⟩
        · rintro ⟨a,rfl⟩
          obtain ⟨a,rfl⟩ := E.surjective a
          exact ⟨a,rfl⟩
      _=J := (actual_formal_ideal_eq_span_reduced_vertex_series MonomialOrder.degLex J).symm
  have hfibre := actual_point_initial_cone_exceptional_fibre_eq_canonical_reduced K e (fun _ => 0)
  rw [hcanonical] at hfibre
  have hm := congrArg (Ideal.map (actualPointExceptionalProjection e).toRingHom) hfibre
  simpa only [Ideal.map_sup,map_actualDehomogenizedPointInitialConeIdeal_projection,
    map_initial_projection_of_pderiv_stable J e hD,map_exceptional_projection,sup_bot_eq] using hm

/-- The unchanged canonical source leading component. -/
def actualCanonicalLeadingHead (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex K) : MvPowerSeries (Fin n) ℂ :=
  MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
    (actualReducedVertexSeries MonomialOrder.degLex K a)

/-- The literal higher tail of the SAME canonical source member. -/
def actualCanonicalHigherTail (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex K) : MvPowerSeries (Fin n) ℂ :=
  actualReducedVertexSeries MonomialOrder.degLex K a-actualCanonicalLeadingHead K a

private theorem homogeneousComponent_mem_point_power (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.homogeneousComponent μ F ∈ actualFormalCoordinateIdeal n Set.univ ^ μ := by
  apply (mem_actualFormalCoordinateIdeal_pow_iff Set.univ μ _).mpr
  intro α hα
  rw [MvPowerSeries.coeff_homogeneousComponent,if_neg]
  have hd : Finsupp.degree α < μ := by
    simpa only [point_weight_eq_degree,normalExponentDegree,Finsupp.degree_eq_sum] using hα
  exact Nat.ne_of_lt hd

/-- True original point powers of the literal canonical higher tail are supplied internally. -/
theorem actualCanonicalHigherTail_mem_point_power (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (a : actualInitialVertices MonomialOrder.degLex K) :
    actualCanonicalHigherTail K a ∈ actualFormalCoordinateIdeal n Set.univ ^ normalExponentDegree a.val := by
  apply Ideal.sub_mem
  · simpa only [point_weight_eq_degree] using actualReducedVertexSeries_mem_point_power n K a
  · exact homogeneousComponent_mem_point_power _ _

/-- The true normalized SAME canonical tail avoids the ENTIRE unchanged source diagram. -/
theorem actualNormalized_canonical_tail_diagram_coefficients_zero
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n)
    (hD : ∀ F ∈ actualHomogeneousInitialIdeal K,
      MvPowerSeries.pderiv ℂ e F ∈ actualHomogeneousInitialIdeal K)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    ∀ γ ∈ actualInitialDiagram MonomialOrder.degLex K, MvPowerSeries.coeff γ
      (actualNormalizedFormalMember Set.univ e (mem_univ e) (fun _ => 0)
        (normalExponentDegree a.val) (actualCanonicalHigherTail K a)
        (actualCanonicalHigherTail_mem_point_power K a))=0 := by
  have herase (α : Fin n →₀ ℕ) :
      α ∈ actualInitialDiagram MonomialOrder.degLex K ↔
        α.erase e ∈ actualInitialDiagram MonomialOrder.degLex K := by
    simpa only [actual_homogeneous_initial_ideal_diagram] using
      actualInitialDiagram_erase_iff_of_pderiv_stable MonomialOrder.degLex
        (actualHomogeneousInitialIdeal K) e hD α
  have hdepends (α γ : Fin n →₀ ℕ) (heq : ∀ i ∈ ({i : Fin n | i ≠ e} : Set (Fin n)), α i=γ i) :
      (α ∈ actualInitialDiagram MonomialOrder.degLex K ↔ γ ∈ actualInitialDiagram MonomialOrder.degLex K) := by
    have her : α.erase e=γ.erase e := by
      ext i
      by_cases hi : i=e
      · subst i
        simp
      · simpa only [Finsupp.erase_ne hi] using heq i hi
    rw [herase α,herase γ,her]
  have hzero (α : Fin n →₀ ℕ) (hα : α ∈ actualInitialDiagram MonomialOrder.degLex K) :
      MvPowerSeries.coeff α (actualCanonicalHigherTail K a)=0 := by
    have hαJ : α ∈ actualInitialDiagram MonomialOrder.degLex (actualHomogeneousInitialIdeal K) := by
      rwa [actual_homogeneous_initial_ideal_diagram]
    rw [actualCanonicalHigherTail,actualCanonicalLeadingHead,map_sub,
      homogeneousComponent_actualReducedVertexSeries_eq_initial,
      actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex K a α hα,
      actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex (actualHomogeneousInitialIdeal K)
        (actualHomogeneousInitialVertex K a) α hαJ]
    exact sub_self _
  exact actualNormalizedFormalMember_forbidden_block_support Set.univ {i : Fin n | i ≠ e}
    e (mem_univ e) (fun _ => 0) (fun _ _ => mem_univ _) (by simp)
    (fun _ _ => rfl) _ _ (actualCanonicalHigherTail_mem_point_power K a)
    (fun α => α ∈ actualInitialDiagram MonomialOrder.degLex K) hdepends hzero

private theorem truncation_remainder (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    F-(MvPowerSeries.truncTotal q F : MvPowerSeries (Fin n) ℂ) ∈ genuineFormalVariables n ^ q := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
  intro α hα
  rw [map_sub,MvPolynomial.coeff_coe,MvPowerSeries.coeff_truncTotal]
  · exact sub_self _
  · simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hα

/-- Only genuine full HS equality supplies each SAME canonical vertex's actual zero-chart order. -/
theorem actualNormalizedReducedFormalVertex_zero_mem_degree_power_of_hs_eq
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n)
    (hHS : ∀ ℓ : ℕ, genuineFormalHilbertSamuelValue n
      (actualFormalStrictTransform K Set.univ e (mem_univ e) (fun _ => 0)) ℓ=
        genuineFormalHilbertSamuelValue n K ℓ)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    actualNormalizedReducedFormalVertex MonomialOrder.degLex K Set.univ e (mem_univ e)
      (fun _ => 0) (actualReducedVertexSeries_mem_point_power n K) a ∈
        genuineFormalVariables n ^ normalExponentDegree a.val := by
  let μ := normalExponentDegree a.val
  by_cases hμ : μ=0
  · simp only [μ] at hμ
    simp only [hμ,pow_zero,Ideal.one_eq_top,Submodule.mem_top]
  have hμpos : 0 < μ := Nat.pos_of_ne_zero hμ
  let J := actualHomogeneousInitialIdeal K
  let I := actualFormalStrictTransform K Set.univ e (mem_univ e) (fun _ => 0)
  let R := actualReducedVertexSeries MonomialOrder.degLex K a
  let H := actualCanonicalLeadingHead K a
  have hD : ∀ F ∈ J, MvPowerSeries.pderiv ℂ e F ∈ J := by
    intro F hF
    have hd := actual_homogeneous_initial_directional_stable_of_point_strict_hs_eq K e
      (fun _ => 0) hHS F hF
    simpa only [HironakaActualPointUnitCoordinateChange.actualPointUnitBasePoint_apply,
      ite_smul,one_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hd
  have hRpow : R ∈ actualFormalCoordinateIdeal n Set.univ ^ μ := by
    simpa only [point_weight_eq_degree] using actualReducedVertexSeries_mem_point_power n K a
  have hHpow : H ∈ actualFormalCoordinateIdeal n Set.univ ^ μ := homogeneousComponent_mem_point_power _ _
  have hHhom : H.IsHomogeneous μ := MvPowerSeries.isHomogeneous_homogeneousComponent _ _
  have hHder : MvPowerSeries.pderiv ℂ e H=0 := by
    change MvPowerSeries.pderiv ℂ e
      (MvPowerSeries.homogeneousComponent μ (actualReducedVertexSeries MonomialOrder.degLex K a))=0
    rw [homogeneousComponent_actualReducedVertexSeries_eq_initial]
    exact pderiv_actualReducedVertexSeries_eq_zero_of_stable MonomialOrder.degLex J e hD _
  have hnormH := actualNormalizedFormalMember_zero_eq_of_homogeneous_independent e μ H hHhom hHder hHpow
  let N := actualNormalizedFormalMember Set.univ e (mem_univ e) (fun _ => 0) μ R hRpow
  let T := actualNormalizedFormalMember Set.univ e (mem_univ e) (fun _ => 0) μ
    (actualCanonicalHigherTail K a) (actualCanonicalHigherTail_mem_point_power K a)
  have hsub : N-H=T := by
    apply actualNormalizedFormalMember_unique
    change (MvPowerSeries.X e)^μ*(N-H)=actualFormalBlowup Set.univ e (fun _ => 0) (R-H)
    rw [map_sub,mul_sub,actualNormalizedFormalMember_spec]
    have hprodH := actualNormalizedFormalMember_spec Set.univ e (mem_univ e) (fun _ => 0) μ H hHpow
    rw [hnormH] at hprodH
    rw [hprodH]
  have hN : N ∈ I := by
    dsimp only [I]
    rw [actualFormalStrictTransform_eq_normalizedOriginalMemberIdeal]
    exact Ideal.subset_span ⟨μ,R,actualReducedVertexSeries_mem MonomialOrder.degLex K a,hRpow,rfl⟩
  have hHhigh : H ∈ genuineFormalVariables n ^ μ := by rwa [← point_ideal_eq_variables]
  have hTmem : T ∈ I ⊔ genuineFormalVariables n ^ μ := by
    rw [← hsub]
    exact (I ⊔ genuineFormalVariables n ^ μ).sub_mem (Ideal.mem_sup_left hN) (Ideal.mem_sup_right hHhigh)
  have hTnormal := actualNormalized_canonical_tail_diagram_coefficients_zero K e hD a
  let P : MvPowerSeries (Fin n) ℂ := MvPowerSeries.truncTotal μ T
  have hrem : T-P ∈ genuineFormalVariables n ^ μ := truncation_remainder μ T
  have hPmem : P ∈ I ⊔ genuineFormalVariables n ^ μ := by
    have hm := (I ⊔ genuineFormalVariables n ^ μ).sub_mem hTmem (Ideal.mem_sup_right hrem)
    simpa only [sub_sub_cancel] using hm
  have hPsupport : ∀ α, MvPowerSeries.coeff α P ≠ 0 →
      normalExponentDegree α < μ ∧ α ∉ actualInitialDiagram MonomialOrder.degLex K := by
    intro α hα
    have hc : MvPowerSeries.coeff α P=
        if Finsupp.degree α < μ then MvPowerSeries.coeff α T else 0 := by
      dsimp only [P]
      rw [MvPolynomial.coeff_coe,MvPowerSeries.coeff_truncTotal_eq_ite]
    by_cases hd : Finsupp.degree α < μ
    · rw [if_pos hd] at hc
      refine ⟨by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hd,?_⟩
      intro hdiag
      exact hα (hc.trans (hTnormal α hdiag))
    · exact False.elim (hα (by rw [hc,if_neg hd]))
  have hdehom := actualDehomogenizedPointInitialConeIdeal_zero_eq_initial_of_pderiv_stable K e hD
  have hCyl (α : Fin n →₀ ℕ) :
      α ∉ actualInitialDiagram MonomialOrder.degLex K ↔ α.erase e ∉
        actualInitialDiagram MonomialOrder.degLex
          (actualExceptionalFibreIdeal (actualDehomogenizedPointInitialConeIdeal K e (fun _ => 0)) e) := by
    calc
      _ ↔ α ∉ actualInitialDiagram MonomialOrder.degLex
          (actualDehomogenizedPointInitialConeIdeal K e (fun _ => 0)) := by
        rw [hdehom,actual_homogeneous_initial_ideal_diagram]
      _ ↔ _ := actual_dehomogenized_initial_cone_diagram_cylinder K e (fun _ => 0) α
  have hcut : (μ-1)+1=μ := by omega
  have hinj : Function.Injective (actualExceptionalJetMap I
      (actualDehomogenizedPointInitialConeIdeal K e (fun _ => 0)) e μ) := by
    have hi := (actual_point_strict_exceptional_jetMap_bijective_of_hs_eq K e (fun _ => 0)
      (μ-1) (hHS (μ-1))).1
    rwa [hcut] at hi
  have hPzero := bounded_diagram_avoiding_eq_zero_of_exceptional_jet_injective I K
    (actualDehomogenizedPointInitialConeIdeal K e (fun _ => 0)) e μ hCyl hinj P hPsupport hPmem
  have hTpow : T ∈ genuineFormalVariables n ^ μ := by simpa only [hPzero,sub_zero] using hrem
  have hNpow : N ∈ genuineFormalVariables n ^ μ := by
    have hm := (genuineFormalVariables n ^ μ).add_mem hTpow hHhigh
    rw [← hsub,sub_add_cancel] at hm
    exact hm
  let V := actualNormalizedReducedFormalVertex MonomialOrder.degLex K Set.univ e
    (mem_univ e) (fun _ => 0) (actualReducedVertexSeries_mem_point_power n K) a
  have hspec : (MvPowerSeries.X e) ^
      Finsupp.weight (actualCoordinateWeight Set.univ) a.val * V =
        actualFormalBlowup Set.univ e (fun _ => 0) R :=
    actualNormalizedFormalMember_spec Set.univ e (mem_univ e) (fun _ => 0) _
      (actualReducedVertexSeries MonomialOrder.degLex K a)
      (actualReducedVertexSeries_mem_point_power n K a)
  rw [point_weight_eq_degree] at hspec
  have hVN : V = N := actualNormalizedFormalMember_unique Set.univ e (mem_univ e)
    (fun _ => 0) μ R hRpow V hspec
  change V ∈ genuineFormalVariables n ^ μ
  rw [hVN]
  exact hNpow

end
end Hironaka.HironakaActualCanonicalZeroDirectionOrder
