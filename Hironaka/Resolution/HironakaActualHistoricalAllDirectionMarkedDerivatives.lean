import Hironaka.Resolution.HironakaActualMultiDerivativeBlowup

/-! Genuine all-direction marked derivative quotients through the SAME
actual blowup, including the pivot. Whole chain rules are produced by
actual polynomial density and coefficientwise continuity. -/
set_option autoImplicit false
open Set Classical
open scoped Topology MvPowerSeries.WithPiTopology
namespace Hironaka.HironakaActualHistoricalAllDirectionMarkedDerivatives
noncomputable section
open HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualNormalizedBlowupDerivative HironakaActualMultiDerivativeBlowup
  HironakaActualCanonicalBlockJacobian HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalFormalHSTransfer

variable {n : ℕ}

/-- The ENTIRE finite-coordinate chain rule for the actual formal blowup;
the coefficientwise-continuous maps are compared on actual dense polynomials. -/
theorem pderiv_actualFormalBlowup_chain
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (j : Fin n)
    (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.pderiv ℂ j (actualFormalBlowup A e b F)=
      ∑i,MvPowerSeries.pderiv ℂ j (actualFormalBlowup A e b (MvPowerSeries.X i))*
        actualFormalBlowup A e b (MvPowerSeries.pderiv ℂ i F) := by
  let σ:=actualFormalBlowup A e b
  let d:=fun i=>MvPowerSeries.pderiv ℂ j (σ (MvPowerSeries.X i))
  have hC (c : ℂ) : σ (MvPowerSeries.C c)=MvPowerSeries.C c:=σ.commutes c
  have hCoordinate (i : Fin n) :
      (∑l,d l*σ (MvPowerSeries.pderiv ℂ l (MvPowerSeries.X i)))=d i := by
    rw [Finset.sum_eq_single i]
    · rw [MvPowerSeries.pderiv_X_self,map_one,mul_one]
    · intro l _ hli
      rw [MvPowerSeries.pderiv_X_of_ne (Ne.symm hli),map_zero,mul_zero]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hPolynomial (P : MvPolynomial (Fin n) ℂ) :
      MvPowerSeries.pderiv ℂ j (σ (P : MvPowerSeries (Fin n) ℂ))=
        ∑i,d i*σ (MvPowerSeries.pderiv ℂ i (P : MvPowerSeries (Fin n) ℂ)) := by
    induction P using MvPolynomial.induction_on with
    | C c =>
      simp only [MvPolynomial.coe_C,hC,MvPowerSeries.pderiv_C,map_zero,mul_zero,Finset.sum_const_zero]
    | add P Q hP hQ =>
      simp only [MvPolynomial.coe_add,map_add,hP,hQ,mul_add,Finset.sum_add_distrib]
    | mul_X P i hP =>
      rw [MvPolynomial.coe_mul,MvPolynomial.coe_X,map_mul,Derivation.leibniz,hP]
      change (σ (P : MvPowerSeries (Fin n) ℂ))*d i+
        (σ (MvPowerSeries.X i))*(∑l,d l*σ (MvPowerSeries.pderiv ℂ l (P : MvPowerSeries (Fin n) ℂ)))=_
      calc
        _=(∑l,d l*σ (MvPowerSeries.pderiv ℂ l (P : MvPowerSeries (Fin n) ℂ)))*σ (MvPowerSeries.X i)+
            σ (P : MvPowerSeries (Fin n) ℂ)*d i:=by ring
        _=(∑l,(d l*σ (MvPowerSeries.pderiv ℂ l (P : MvPowerSeries (Fin n) ℂ)))*σ (MvPowerSeries.X i))+
            ∑l,σ (P : MvPowerSeries (Fin n) ℂ)*(d l*σ (MvPowerSeries.pderiv ℂ l (MvPowerSeries.X i))):=by
          rw [Finset.sum_mul,←hCoordinate i,Finset.mul_sum]
        _=(∑l,((d l*σ (MvPowerSeries.pderiv ℂ l (P : MvPowerSeries (Fin n) ℂ)))*σ (MvPowerSeries.X i)+
            σ (P : MvPowerSeries (Fin n) ℂ)*(d l*σ (MvPowerSeries.pderiv ℂ l (MvPowerSeries.X i))))):=
          (Finset.sum_add_distrib).symm
        _=∑l,d l*σ (MvPowerSeries.pderiv ℂ l ((P : MvPowerSeries (Fin n) ℂ)*MvPowerSeries.X i)):=by
          apply Finset.sum_congr rfl
          intro l _
          simp only [Derivation.leibniz,smul_eq_mul,map_add,map_mul]
          ring
  let : UniformSpace ℂ:=⊥
  let : DiscreteUniformity ℂ:=inferInstance
  let : DiscreteTopology ℂ:=inferInstance
  have hD (i : Fin n) : Continuous (MvPowerSeries.pderiv ℂ i :
      MvPowerSeries (Fin n) ℂ → MvPowerSeries (Fin n) ℂ) := by
    apply continuous_pi
    intro α
    change Continuous (fun H : MvPowerSeries (Fin n) ℂ=>MvPowerSeries.coeff α (MvPowerSeries.pderiv ℂ i H))
    simpa only [MvPowerSeries.coeff_pderiv] using
      (MvPowerSeries.WithPiTopology.continuous_coeff ℂ (α+Finsupp.single i 1)).mul_const ((α i : ℂ)+1)
  have hσ : Continuous σ := by
    change Continuous (fun H : MvPowerSeries (Fin n) ℂ=>actualFormalBlowup A e b H)
    simp only [actualFormalBlowup,MvPowerSeries.substAlgHom_apply]
    exact MvPowerSeries.continuous_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (actualFormalBlowupCoordinates_constant_zero A e b))
  have hRight : Continuous (fun H : MvPowerSeries (Fin n) ℂ=>∑i,d i*σ (MvPowerSeries.pderiv ℂ i H)):=
    continuous_finsetSum Finset.univ fun i _=>continuous_const.mul (hσ.comp (hD i))
  have hEq : (fun H : MvPowerSeries (Fin n) ℂ=>MvPowerSeries.pderiv ℂ j (σ H))=
      (fun H : MvPowerSeries (Fin n) ℂ=>∑i,d i*σ (MvPowerSeries.pderiv ℂ i H)):=
    MvPowerSeries.WithPiTopology.denseRange_toMvPowerSeries.equalizer ((hD j).comp hσ) hRight (funext hPolynomial)
  exact congrFun hEq F

private theorem pderiv_actualFormalBlowup_pivot_coordinate
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ) (i : Fin n) :
    MvPowerSeries.pderiv ℂ e (actualFormalBlowup A e b (MvPowerSeries.X i)) =
      (if i=e then 1 else 0)+
        (if i∈A ∧ i≠e then MvPowerSeries.C (b i)+MvPowerSeries.X i else 0) := by
  rw [actualFormalBlowup_X]
  by_cases hie : i=e
  · subst i
    simp [actualFormalBlowupCoordinates,he]
  · by_cases hi : i∈A
    · rw [actualFormalBlowupCoordinates,if_pos hi,if_neg hie,Derivation.leibniz,
        map_add,MvPowerSeries.pderiv_C,MvPowerSeries.pderiv_X_of_ne hie,
        MvPowerSeries.pderiv_X_self]
      simp only [if_neg hie,if_pos (show i∈A ∧ i≠e from ⟨hi,hie⟩),
        zero_add,add_zero,smul_eq_mul,mul_zero,mul_one]
    · rw [actualFormalBlowupCoordinates,if_neg hi,MvPowerSeries.pderiv_X_of_ne hie]
      simp only [if_neg hie,hi,false_and,if_false,zero_add]

/-- The actual pivot chain rule on the ENTIRE formal ring, for arbitrary b. -/
theorem pderiv_actualFormalBlowup_pivot
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.pderiv ℂ e (actualFormalBlowup A e b F)=
      actualFormalBlowup A e b (MvPowerSeries.pderiv ℂ e F)+
      ∑i∈Finset.univ.filter (fun i=>i∈A ∧ i≠e),
        (MvPowerSeries.C (b i)+MvPowerSeries.X i)*
          actualFormalBlowup A e b (MvPowerSeries.pderiv ℂ i F) := by
  rw [pderiv_actualFormalBlowup_chain]
  simp only [pderiv_actualFormalBlowup_pivot_coordinate A e he,add_mul,
    ite_mul,one_mul,zero_mul,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,
    if_true,Finset.sum_filter]
  simp only [←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- The pivot lower-mark quotient is produced from the actual differentiated
normalization equation; no transformed derivative identity is assumed. -/
theorem actualNormalizedFormalMember_pivot_derivative
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F∈actualFormalCoordinateIdeal n A^(q+1)) :
    actualNormalizedFormalMember A e he b q (MvPowerSeries.pderiv ℂ e F)
      (pderiv_mem_actualCentrePower A e he q F hF)=
      ((q+1 : ℕ) : MvPowerSeries (Fin n) ℂ)*actualNormalizedFormalMember A e he b (q+1) F hF+
      MvPowerSeries.X e * MvPowerSeries.pderiv ℂ e
        (actualNormalizedFormalMember A e he b (q+1) F hF)-
      ∑i∈Finset.univ.filter (fun i=>i∈A ∧ i≠e),
        (MvPowerSeries.C (b i)+MvPowerSeries.X i)*MvPowerSeries.pderiv ℂ i
          (actualNormalizedFormalMember A e he b (q+1) F hF) := by
  let G:=actualNormalizedFormalMember A e he b (q+1) F hF
  have hOther (i : Fin n) (hi : i∈Finset.univ.filter (fun i=>i∈A ∧ i≠e)) :
      actualFormalBlowup A e b (MvPowerSeries.pderiv ℂ i F)=
        MvPowerSeries.X e^q*MvPowerSeries.pderiv ℂ i G := by
    have hiA:=((Finset.mem_filter.mp hi).2).1
    have hie:=((Finset.mem_filter.mp hi).2).2
    rw [show G=actualNormalizedFormalMember A e he b (q+1) F hF from rfl,
      pderiv_actualNormalizedFormalMember A e he b i hiA hie q F hF]
    exact (actualNormalizedFormalMember_spec A e he b q (MvPowerSeries.pderiv ℂ i F)
      (pderiv_mem_actualCentrePower A i hiA q F hF)).symm
  have hs:=congrArg (MvPowerSeries.pderiv ℂ e)
    (actualNormalizedFormalMember_spec A e he b (q+1) F hF)
  rw [Derivation.leibniz,MvPowerSeries.pderiv_pow,MvPowerSeries.pderiv_X_self,
    Nat.add_sub_cancel,mul_one,pderiv_actualFormalBlowup_pivot A e he] at hs
  rw [←actualNormalizedFormalMember_spec A e he b q (MvPowerSeries.pderiv ℂ e F)
    (pderiv_mem_actualCentrePower A e he q F hF)] at hs
  have hSum : (∑i∈Finset.univ.filter (fun i=>i∈A ∧ i≠e),
      (MvPowerSeries.C (b i)+MvPowerSeries.X i)*
        actualFormalBlowup A e b (MvPowerSeries.pderiv ℂ i F))=
      MvPowerSeries.X e^q*(∑i∈Finset.univ.filter (fun i=>i∈A ∧ i≠e),
        (MvPowerSeries.C (b i)+MvPowerSeries.X i)*MvPowerSeries.pderiv ℂ i G) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hOther i hi]
    ring
  rw [hSum] at hs
  apply mul_left_cancel₀ (pow_ne_zero q (actualFormalExceptional_ne_zero e))
  dsimp only [G] at hs ⊢
  simp only [smul_eq_mul,pow_succ,Nat.cast_add,Nat.cast_one] at hs ⊢
  linear_combination -hs

private theorem pderiv_mem_genuineFormalVariables_power
    (i : Fin n) (q : ℕ) (G : MvPowerSeries (Fin n) ℂ)
    (hG : G∈genuineFormalVariables n^(q+1)) :
    MvPowerSeries.pderiv ℂ i G∈genuineFormalVariables n^q := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
  intro α hα
  have hDegree : normalExponentDegree (α+Finsupp.single i 1)=normalExponentDegree α+1 := by
    simp [normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib]
  rw [MvPowerSeries.coeff_pderiv,
    (mem_genuineFormalVariables_pow_iff_coefficients_zero n (q+1) G).mp hG _
      (by rw [hDegree];omega),zero_mul]

/-- Actual point marks descend to the genuine lower-mark quotient in EVERY
normal direction, including the pivot. The lower source membership is derived. -/
theorem actualNormalizedFormalMember_pderiv_mem_point_power
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (i : Fin n) (hi : i∈A) (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F∈actualFormalCoordinateIdeal n A^(q+1))
    (hPoint : actualNormalizedFormalMember A e he b (q+1) F hF∈genuineFormalVariables n^(q+1)) :
    actualNormalizedFormalMember A e he b q (MvPowerSeries.pderiv ℂ i F)
      (pderiv_mem_actualCentrePower A i hi q F hF)∈genuineFormalVariables n^q := by
  by_cases hie : i=e
  · subst i
    rw [actualNormalizedFormalMember_pivot_derivative A e he b q F hF]
    apply Ideal.sub_mem
    · apply Ideal.add_mem
      · exact Ideal.mul_mem_left _ _ ((Ideal.pow_le_pow_right (by omega)) hPoint)
      · exact Ideal.mul_mem_left _ _ (pderiv_mem_genuineFormalVariables_power e q _ hPoint)
    · apply Ideal.sum_mem
      intro j _
      exact Ideal.mul_mem_left _ _ (pderiv_mem_genuineFormalVariables_power j q _ hPoint)
  · rw [←pderiv_actualNormalizedFormalMember A e he b i hi hie q F hF]
    exact pderiv_mem_genuineFormalVariables_power i q _ hPoint

private theorem normalized_congr (A : Set (Fin n)) (e : Fin n) (he : e∈A)
    (b : Fin n → ℂ) {q r : ℕ} {F G : MvPowerSeries (Fin n) ℂ}
    (hq : q=r) (hFG : F=G)
    (hF : F∈actualFormalCoordinateIdeal n A^q)
    (hG : G∈actualFormalCoordinateIdeal n A^r) :
    actualNormalizedFormalMember A e he b q F hF=
      actualNormalizedFormalMember A e he b r G hG := by
  cases hq
  cases hFG
  rfl

private theorem multiDerivative_normalized_mem_point_add
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (β : Fin n →₀ ℕ) (hβ : (↑β.support : Set (Fin n))⊆A)
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F∈actualFormalCoordinateIdeal n A^(q+normalExponentDegree β))
    (hPoint : actualNormalizedFormalMember A e he b (q+normalExponentDegree β) F hF∈
      genuineFormalVariables n^(q+normalExponentDegree β)) :
    actualNormalizedFormalMember A e he b q (actualFormalMultiDerivative β F)
      (actualMultiDerivative_mem_centre_add A β hβ q F hF)∈genuineFormalVariables n^q := by
  induction β using (measure normalExponentDegree).wf.induction generalizing q F with
  | h β ih =>
    by_cases hZero : β=0
    · subst β
      have hMark : q+normalExponentDegree (0 : Fin n →₀ ℕ)=q := by
        simp [normalExponentDegree]
      have hNorm:=normalized_congr A e he b hMark (actualFormalMultiDerivative_zero F).symm hF
        (actualMultiDerivative_mem_centre_add A 0 hβ q F hF)
      rw [←hNorm]
      simpa only [hMark] using hPoint
    · obtain ⟨i,hi⟩ : ∃i,β i≠0 := by
        by_contra! hz
        exact hZero (Finsupp.ext hz)
      have hSingle : Finsupp.single i 1≤β := by
        intro j
        by_cases hji : j=i
        · subst j
          simpa only [Finsupp.single_eq_same] using Nat.one_le_iff_ne_zero.mpr hi
        · simp [Finsupp.single_eq_of_ne hji]
      let γ:=β-Finsupp.single i 1
      have hDecomp : γ+Finsupp.single i 1=β:=tsub_add_cancel_of_le hSingle
      have hDegree : normalExponentDegree γ+1=normalExponentDegree β := by
        have hd:=congrArg normalExponentDegree hDecomp
        have hAdd : normalExponentDegree (γ+Finsupp.single i 1)=normalExponentDegree γ+1 := by
          simp [normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib]
        simpa only [hAdd] using hd
      have hγlt : normalExponentDegree γ<normalExponentDegree β:=by omega
      have hγle : γ≤β:=tsub_le_self
      have hγ : (↑γ.support : Set (Fin n))⊆A := by
        intro j hj
        have hjNe:=Finsupp.mem_support_iff.mp hj
        have hjβ : β j≠0 := by
          intro hz
          exact hjNe (Nat.eq_zero_of_le_zero (by simpa only [hz] using hγle j))
        exact hβ (Finsupp.mem_support_iff.mpr hjβ)
      have hiA : i∈A:=hβ (Finsupp.mem_support_iff.mpr hi)
      have hMark : (q+1)+normalExponentDegree γ=q+normalExponentDegree β:=by omega
      have hFγ : F∈actualFormalCoordinateIdeal n A^((q+1)+normalExponentDegree γ):=by
        simpa only [hMark] using hF
      have hNorm:=normalized_congr A e he b hMark rfl hFγ hF
      have hPointγ : actualNormalizedFormalMember A e he b ((q+1)+normalExponentDegree γ) F hFγ∈
          genuineFormalVariables n^((q+1)+normalExponentDegree γ) := by
        rw [hNorm,hMark]
        exact hPoint
      have hγPower:=actualMultiDerivative_mem_centre_add A γ hγ (q+1) F hFγ
      have hγPoint:=ih γ hγlt hγ (q+1) F hFγ hPointγ
      have hStep:=actualNormalizedFormalMember_pderiv_mem_point_power A e he b i hiA q
        (actualFormalMultiDerivative γ F) hγPower hγPoint
      have hDF : MvPowerSeries.pderiv ℂ i (actualFormalMultiDerivative γ F)=
          actualFormalMultiDerivative β F := by
        rw [←actualFormalMultiDerivative_add_single,hDecomp]
      have hResult:=normalized_congr A e he b rfl hDF
        (pderiv_mem_actualCentrePower A i hiA q (actualFormalMultiDerivative γ F) hγPower)
        (actualMultiDerivative_mem_centre_add A β hβ q F hF)
      exact hResult ▸ hStep

/-- The SAME original derivative has its true remaining marked point order
through the actual blowup. All centre directions, including the pivot, are allowed. -/
theorem actualMultiDerivative_normalized_mem_point_power
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (β : Fin n →₀ ℕ) (hβ : (↑β.support : Set (Fin n))⊆A)
    (μ : ℕ) (hβμ : normalExponentDegree β≤μ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F∈actualFormalCoordinateIdeal n A^μ)
    (hPoint : actualNormalizedFormalMember A e he b μ F hF∈genuineFormalVariables n^μ) :
    actualNormalizedFormalMember A e he b (μ-normalExponentDegree β) (actualFormalMultiDerivative β F)
      (actualMultiDerivative_mem_centre_sub A β hβ μ hβμ F hF)∈
      genuineFormalVariables n^(μ-normalExponentDegree β) := by
  have hF' : F∈actualFormalCoordinateIdeal n A^((μ-normalExponentDegree β)+normalExponentDegree β) := by
    simpa only [Nat.sub_add_cancel hβμ] using hF
  have hNorm:=normalized_congr A e he b (Nat.sub_add_cancel hβμ) rfl hF' hF
  have hPoint' : actualNormalizedFormalMember A e he b
      ((μ-normalExponentDegree β)+normalExponentDegree β) F hF'∈
      genuineFormalVariables n^((μ-normalExponentDegree β)+normalExponentDegree β) := by
    rw [hNorm,Nat.sub_add_cancel hβμ]
    exact hPoint
  exact multiDerivative_normalized_mem_point_add A e he b β hβ (μ-normalExponentDegree β) F hF' hPoint'

end
end Hironaka.HironakaActualHistoricalAllDirectionMarkedDerivatives
