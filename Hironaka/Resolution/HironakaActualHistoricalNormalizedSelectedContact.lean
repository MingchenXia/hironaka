import Hironaka.Resolution.HironakaActualHistoricalEssentialPivotDrop

/-! The SAME actual selected functions retain whole contact and the exact
block Jacobian after actual marked normalization. All exceptional block
directions are derived from the whole source factorization and point marks. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalNormalizedSelectedContact
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualNormalizedBlowupDerivative HironakaActualMultiDerivativeBlowup
  HironakaActualHistoricalAllDirectionMarkedDerivatives HironakaActualHistoricalEssentialPivotDrop
  HironakaActualFixedInheritedSelector HironakaActualHistoricalMovingSelectedContact
  HironakaActualCanonicalBlockJacobian HironakaActualOriginalFormalHSTransfer
  HironakaActualCoefficientPresentationCentrePower HironakaHolomorphicJetMonomialSpan
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualCauchyCoefficientLimits
  HironakaActualAnalyticBlowupTaylor HironakaActualAnalyticFormalNormalPowers

variable {n : ℕ} {V : Finset (Fin n →₀ ℕ)}

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

private theorem selected_source_centre_power
    (S : ActualFixedInheritedSelector V) (Γ : V → HolGerm (ComplexModel n))
    (A : Set (Fin n)) (R : ℕ) (hBlock : fixedSelectorBlock V R⊆A)
    (hCentre : ∀a,actualUnshiftedTaylorAlgHom n (Γ a)∈actualFormalCoordinateIdeal n A^normalExponentDegree a.val)
    (j : fixedSelectorBlock V R) :
    actualUnshiftedTaylorAlgHom n (actualFixedSelectorDerivative S Γ (fixedSelectorBlockEssential R j))∈
      actualFormalCoordinateIdeal n A^1 := by
  let s:=fixedSelectorBlockEssential R j
  have hβ : (↑(fixedSelectorBeta S s).support : Set (Fin n))⊆A := by
    intro i hi
    apply hBlock
    by_contra hiB
    exact (Finsupp.mem_support_iff.mp hi) (fixedSelector_beta_support S R j i hiB)
  have hDegree:=fixedSelector_beta_degree S s
  rw [actualFixedSelectorDerivative,actualTaylor_actualAnalyticMultiDerivative]
  apply actualMultiDerivative_mem_centre_add A (fixedSelectorBeta S s) hβ 1
  simpa only [show 1+normalExponentDegree (fixedSelectorBeta S s)=
    normalExponentDegree (S.selected s).val by omega] using hCentre (S.selected s)

private theorem selected_normalized_point_power
    (S : ActualFixedInheritedSelector V) (Γ : V → HolGerm (ComplexModel n))
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ) (R : ℕ)
    (hBlock : fixedSelectorBlock V R⊆A)
    (hCentre : ∀a,actualUnshiftedTaylorAlgHom n (Γ a)∈actualFormalCoordinateIdeal n A^normalExponentDegree a.val)
    (hPoint : ∀a : V,normalExponentDegree a.val≤R →
      actualNormalizedFormalMember A e he b (normalExponentDegree a.val)
        (actualUnshiftedTaylorAlgHom n (Γ a)) (hCentre a)∈genuineFormalVariables n^normalExponentDegree a.val)
    (j : fixedSelectorBlock V R) :
    actualNormalizedFormalMember A e he b 1
      (actualUnshiftedTaylorAlgHom n (actualFixedSelectorDerivative S Γ (fixedSelectorBlockEssential R j)))
      (selected_source_centre_power S Γ A R hBlock hCentre j)∈genuineFormalVariables n^1 := by
  let s:=fixedSelectorBlockEssential R j
  let β:=fixedSelectorBeta S s
  let μ:=normalExponentDegree (S.selected s).val
  have hDegree : normalExponentDegree β+1=μ:=fixedSelector_beta_degree S s
  have hβ : (↑β.support : Set (Fin n))⊆A := by
    intro i hi
    apply hBlock
    by_contra hiB
    exact (Finsupp.mem_support_iff.mp hi) (fixedSelector_beta_support S R j i hiB)
  have h:=actualMultiDerivative_normalized_mem_point_power A e he b β hβ μ (by omega)
    (actualUnshiftedTaylorAlgHom n (Γ (S.selected s))) (hCentre (S.selected s))
    (hPoint (S.selected s) (fixedSelector_selected_degree_le S R j))
  have hMark : μ-normalExponentDegree β=1:=by omega
  have hDerivative : actualFormalMultiDerivative β (actualUnshiftedTaylorAlgHom n (Γ (S.selected s)))=
      actualUnshiftedTaylorAlgHom n (actualFixedSelectorDerivative S Γ s) := by
    rw [actualFixedSelectorDerivative,actualTaylor_actualAnalyticMultiDerivative]
  have hNorm:=normalized_congr A e he b hMark hDerivative
    (actualMultiDerivative_mem_centre_sub A β hβ μ (by omega)
      (actualUnshiftedTaylorAlgHom n (Γ (S.selected s))) (hCentre (S.selected s)))
    (selected_source_centre_power S Γ A R hBlock hCentre j)
  rw [hNorm,hMark] at h
  exact h

/-- The WHOLE actual source contact and marked selected derivatives force
the actual exceptional vector to vanish on the entire original degree block. -/
theorem actual_selected_block_direction_zero_of_marks
    (S : ActualFixedInheritedSelector V) (Γ : V → HolGerm (ComplexModel n))
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ) (R : ℕ)
    (hBlock : fixedSelectorBlock V R⊆A)
    (hCentre : ∀a,actualUnshiftedTaylorAlgHom n (Γ a)∈actualFormalCoordinateIdeal n A^normalExponentDegree a.val)
    (hPoint : ∀a : V,normalExponentDegree a.val≤R →
      actualNormalizedFormalMember A e he b (normalExponentDegree a.val)
        (actualUnshiftedTaylorAlgHom n (Γ a)) (hCentre a)∈genuineFormalVariables n^normalExponentDegree a.val)
    (hContact : actualFixedSelectorContactAt S Γ R)
    (hDet : (actualFixedSelectorJacobian S Γ R).det≠0) :
    ∀i∈fixedSelectorBlock V R,(if i=e then (1 : ℂ) else b i)=0 := by
  let B:=fixedSelectorBlock V R
  let D : B → MvPowerSeries (Fin n) ℂ:=fun j=>actualUnshiftedTaylorAlgHom n
    (actualFixedSelectorDerivative S Γ (fixedSelectorBlockEssential R j))
  have hDPower:=selected_source_centre_power S Γ A R hBlock hCentre
  have hDPoint:=selected_normalized_point_power S Γ A e he b R hBlock hCentre hPoint
  obtain ⟨M,hFactor,hMatrix⟩:=actual_selected_contact_coefficient_matrix S Γ R hContact
  let MF : Matrix B B (MvPowerSeries (Fin n) ℂ):=fun j i=>actualUnshiftedTaylorAlgHom n (M j i)
  have hFactorF (j : B) : ∑i,MF j i*MvPowerSeries.X i.val=D j := by
    have h:=congrArg (actualUnshiftedTaylorAlgHom n) (hFactor j)
    simpa only [map_sum,map_mul,actualUnshiftedTaylor_coordinate] using h
  have hValues:=actual_normalized_block_factorization_constant A B e he hBlock b MF D hFactorF hDPower
  let v : B → ℂ:=fun i=>if i.val=e then 1 else b i.val
  have hZero : (actualFixedSelectorJacobian S Γ R).mulVec v=0 := by
    funext j
    have hz : MvPowerSeries.constantCoeff
        (actualNormalizedFormalMember A e he b 1 (D j) (hDPower j))=0 :=
      (mem_genuineFormalVariables_pow_iff_coefficients_zero n 1 _).mp (hDPoint j) 0
        (by simp [normalExponentDegree])
    rw [hValues j] at hz
    rw [←hMatrix]
    change (∑i,HolGerm.eval (M j i)*v i)=0
    simpa only [MF,v,←MvPowerSeries.coeff_zero_eq_constantCoeff_apply,actualTaylor_coeff_zero] using hz
  have hv : v=0:=Matrix.mulVec_injective_of_det_ne_zero hDet
    (hZero.trans (Matrix.mulVec_zero _).symm)
  intro i hi
  exact congrFun hv ⟨i,hi⟩

private theorem actualTaylor_blowup_apply
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (F : HolGerm (ComplexModel n)) :
    actualUnshiftedTaylorAlgHom n (actualAnalyticBlowupPullback A e b F)=
      actualFormalBlowup A e b (actualUnshiftedTaylorAlgHom n F) :=
  DFunLike.congr_fun (actualTaylor_analyticBlowupPullback A e b) F

private theorem actualAnalyticBlowupPullback_eval
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (F : HolGerm (ComplexModel n)) :
    HolGerm.eval (actualAnalyticBlowupPullback A e b F)=HolGerm.eval F := by
  rw [←actualTaylor_coeff_zero,actualTaylor_blowup_apply,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply,constantCoeff_actualFormalBlowup,
    ←MvPowerSeries.coeff_zero_eq_constantCoeff_apply,actualTaylor_coeff_zero]

/-- ANY genuine analytic quotients of the SAME original family retain all
original selected contacts and literal block Jacobians. Pivot freeness and
vanishing of all essential chart parameters are internally derived from marks. -/
theorem actual_normalized_same_selected_contact_of_marks
    (S : ActualFixedInheritedSelector V) (Γ N : V → HolGerm (ComplexModel n))
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hHeads : ∀a : V,(↑a.val.support : Set (Fin n))⊆A)
    (hCentre : ∀a,Γ a∈actualAnalyticCoordinateIdeal A^normalExponentDegree a.val)
    (hProduct : ∀a,(coordinateGerm e)^normalExponentDegree a.val*N a=
      actualAnalyticBlowupPullback A e b (Γ a))
    (hPoint : ∀a : V,actualUnshiftedTaylorAlgHom n (N a)∈genuineFormalVariables n^normalExponentDegree a.val)
    (hContact : ∀R,actualFixedSelectorContactAt S Γ R)
    (hDet : ∀R,(actualFixedSelectorJacobian S Γ R).det≠0) :
    e∉fixedSelectorEssential V ∧
    (∀i∈fixedSelectorEssential V,b i=0) ∧
    ∀R,actualFixedSelectorContactAt S N R ∧
      actualFixedSelectorJacobian S N R=actualFixedSelectorJacobian S Γ R ∧
      (actualFixedSelectorJacobian S N R).det≠0 := by
  have hCentreF (a : V) : actualUnshiftedTaylorAlgHom n (Γ a)∈
      actualFormalCoordinateIdeal n A^normalExponentDegree a.val:=
    actualTaylor_mem_coordinateCentre_pow A (normalExponentDegree a.val) (Γ a) (hCentre a)
  have hTaylor (a : V) : actualUnshiftedTaylorAlgHom n (N a)=actualNormalizedFormalMember A e he b
      (normalExponentDegree a.val) (actualUnshiftedTaylorAlgHom n (Γ a)) (hCentreF a) := by
    apply actualNormalizedFormalMember_unique
    have h:=congrArg (actualUnshiftedTaylorAlgHom n) (hProduct a)
    rw [map_mul,map_pow,actualUnshiftedTaylor_coordinate] at h
    exact h.trans (DFunLike.congr_fun (actualTaylor_analyticBlowupPullback A e b) (Γ a))
  have hMarked (a : V) : actualNormalizedFormalMember A e he b (normalExponentDegree a.val)
      (actualUnshiftedTaylorAlgHom n (Γ a)) (hCentreF a)∈genuineFormalVariables n^normalExponentDegree a.val:=
    hTaylor a ▸ hPoint a
  have hFree : e∉fixedSelectorEssential V := by
    intro heV
    let s : fixedSelectorEssential V:=⟨e,heV⟩
    let R:=normalExponentDegree (S.selected s).val
    exact essential_pivot_impossible_of_actual_marks S Γ A e he b R hHeads
      ⟨S.selected s,le_rfl,S.positive s⟩ hCentreF (fun a _=>hMarked a) (hContact R) (hDet R)
  have hBlock (R : ℕ) : fixedSelectorBlock V R⊆A := by
    rintro i ⟨a,_ha,hai⟩
    exact hHeads a (Finsupp.mem_support_iff.mpr hai)
  have hBlockFree (R : ℕ) : fixedSelectorBlock V R⊆A\{e} := by
    intro i hi
    refine ⟨hBlock R hi,?_⟩
    intro hie
    have hiE : i∈fixedSelectorEssential V:=(fixedSelectorBlockEssential R ⟨i,hi⟩).property
    exact hFree ((Set.mem_singleton_iff.mp hie) ▸ hiE)
  have hbBlock (R : ℕ) (i : Fin n) (hi : i∈fixedSelectorBlock V R) : b i=0 := by
    have h:=actual_selected_block_direction_zero_of_marks S Γ A e he b R (hBlock R)
      hCentreF (fun a _=>hMarked a) (hContact R) (hDet R) i hi
    have hie : i≠e:=by simpa only [Set.mem_singleton_iff] using (hBlockFree R hi).2
    simpa only [if_neg hie] using h
  refine ⟨hFree,?_,?_⟩
  · rintro i ⟨a,hai⟩
    exact hbBlock (normalExponentDegree a.val) i ⟨a,le_rfl,hai⟩
  intro R
  let B:=fixedSelectorBlock V R
  have hDPower:=selected_source_centre_power S Γ A R (hBlock R) hCentreF
  have hSelectedTaylor (j : B) : actualUnshiftedTaylorAlgHom n
      (actualFixedSelectorDerivative S N (fixedSelectorBlockEssential R j))=
      actualNormalizedFormalMember A e he b 1
        (actualUnshiftedTaylorAlgHom n (actualFixedSelectorDerivative S Γ (fixedSelectorBlockEssential R j)))
        (hDPower j) := by
    let s:=fixedSelectorBlockEssential R j
    let β:=fixedSelectorBeta S s
    let μ:=normalExponentDegree (S.selected s).val
    have hDegree : normalExponentDegree β+1=μ:=fixedSelector_beta_degree S s
    have hβ : (↑β.support : Set (Fin n))⊆A\{e} := by
      intro i hi
      apply hBlockFree R
      by_contra hiB
      exact (Finsupp.mem_support_iff.mp hi) (fixedSelector_beta_support S R j i hiB)
    have hComm:=actualMultiDerivative_actualNormalizedFormalMember A e he b β hβ μ (by omega)
      (actualUnshiftedTaylorAlgHom n (Γ (S.selected s))) (hCentreF (S.selected s))
    have hNorm:=normalized_congr A e he b (show μ-normalExponentDegree β=1 by omega)
      (actualTaylor_actualAnalyticMultiDerivative β (Γ (S.selected s))).symm
      (actualMultiDerivative_mem_centre_sub A β (fun i hi=>(hβ hi).1) μ (by omega)
        (actualUnshiftedTaylorAlgHom n (Γ (S.selected s))) (hCentreF (S.selected s))) (hDPower j)
    rw [actualFixedSelectorDerivative,actualTaylor_actualAnalyticMultiDerivative,hTaylor]
    exact hComm.trans hNorm
  have hSelectedProduct (j : B) : coordinateGerm e*
      actualFixedSelectorDerivative S N (fixedSelectorBlockEssential R j)=
      actualAnalyticBlowupPullback A e b
        (actualFixedSelectorDerivative S Γ (fixedSelectorBlockEssential R j)) := by
    apply actualUnshiftedTaylorAlgHom_injective n
    rw [map_mul,actualUnshiftedTaylor_coordinate,hSelectedTaylor,actualTaylor_blowup_apply]
    simpa only [pow_one] using actualNormalizedFormalMember_spec A e he b 1
      (actualUnshiftedTaylorAlgHom n (actualFixedSelectorDerivative S Γ (fixedSelectorBlockEssential R j)))
      (hDPower j)
  obtain ⟨M,hFactor,hMatrix⟩:=actual_selected_contact_coefficient_matrix S Γ R (hContact R)
  let MN : Matrix B B (HolGerm (ComplexModel n)):=fun j i=>actualAnalyticBlowupPullback A e b (M j i)
  have hFactorN (j : B) : ∑i,MN j i*coordinateGerm i.val=
      actualFixedSelectorDerivative S N (fixedSelectorBlockEssential R j) := by
    have hSum : coordinateGerm e*(∑i,MN j i*coordinateGerm i.val)=
        actualAnalyticBlowupPullback A e b
          (actualFixedSelectorDerivative S Γ (fixedSelectorBlockEssential R j)) := by
      rw [←hFactor j,map_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul,actualAnalyticBlowupPullback_coordinate,if_pos (hBlock R i.property),
        if_neg (show i.val≠e by simpa only [Set.mem_singleton_iff] using (hBlockFree R i.property).2),
        hbBlock R i.val i.property,map_zero,zero_add]
      dsimp only [MN]
      ring
    have hne : coordinateGerm e≠0:=HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e
    exact mul_left_cancel₀ hne (hSum.trans (hSelectedProduct j).symm)
  have hContactN:=coordinate_block_contact_of_factorization B
    (fun j=>actualFixedSelectorDerivative S N (fixedSelectorBlockEssential R j)) MN hFactorN
  have hJacN:=coordinate_block_jacobian_of_factorization B
    (fun j=>actualFixedSelectorDerivative S N (fixedSelectorBlockEssential R j)) MN hFactorN
  have hEval : Matrix.map MN HolGerm.eval=Matrix.map M HolGerm.eval := by
    ext j i
    exact actualAnalyticBlowupPullback_eval A e b (M j i)
  have hJac : actualFixedSelectorJacobian S N R=actualFixedSelectorJacobian S Γ R:=
    hJacN.symm.trans (hEval.trans hMatrix)
  exact ⟨hContactN,hJac,hJac ▸ hDet R⟩

end
end Hironaka.HironakaActualHistoricalNormalizedSelectedContact
