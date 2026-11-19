import Hironaka.Resolution.HironakaActualHistoricalAllDirectionMarkedDerivatives
import Hironaka.Resolution.HironakaActualHistoricalHSReverseMarks
import Hironaka.Resolution.HironakaActualHistoricalMovingSelectedContact

/-! An actual essential pivot cannot preserve the SAME historical marked
contact. All outside-block coefficients are controlled by WHOLE source contact,
and genuine all-direction marked derivatives include the pivot. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalEssentialPivotDrop
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualNormalizedBlowupDerivative HironakaActualMultiDerivativeBlowup
  HironakaActualHistoricalAllDirectionMarkedDerivatives HironakaActualHistoricalHSReverseMarks
  HironakaActualFixedInheritedSelector HironakaActualHistoricalMovingSelectedContact
  HironakaActualCanonicalBlockJacobian HironakaActualOriginalFormalHSTransfer
  HironakaActualCoefficientPresentationCentrePower HironakaHolomorphicJetMonomialSpan
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualCauchyCoefficientLimits
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
  HironakaActualHistoricalFormalSupportedDivision HironakaActualCauchyMonomialDivision
  HironakaActualHistoricalCentreFilteredDivision
  Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  HironakaActualAnalyticBlowupTaylor HironakaRelativeNormalDeformationInitialRelations
  HironakaActualPointGeometricBennett HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicPointJets HironakaActualUnshiftedInitialHSTransfer

variable {n k : ℕ}

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

/-- The ENTIRE block factorization computes the actual mark-one quotient
value. The original pivot entry is one, with arbitrary chart parameter b. -/
theorem actual_normalized_block_factorization_constant
    (A B : Set (Fin n)) (e : Fin n) (he : e∈A) (hB : B⊆A) (b : Fin n → ℂ)
    (M : Matrix B B (MvPowerSeries (Fin n) ℂ)) (F : B → MvPowerSeries (Fin n) ℂ)
    (hFactor : ∀j,∑i,M j i*MvPowerSeries.X i.val=F j)
    (hF : ∀j,F j∈actualFormalCoordinateIdeal n A^1) :
    ∀j,MvPowerSeries.constantCoeff (actualNormalizedFormalMember A e he b 1 (F j) (hF j))=
      ∑i,MvPowerSeries.constantCoeff (M j i)*(if i.val=e then 1 else b i.val) := by
  intro j
  let v : B → MvPowerSeries (Fin n) ℂ:=fun i=>
    if i.val=e then 1 else MvPowerSeries.C (b i.val)+MvPowerSeries.X i.val
  have hCoordinate (i : B) : actualFormalBlowup A e b (MvPowerSeries.X i.val)=
      MvPowerSeries.X e*v i := by
    rw [actualFormalBlowup_X,actualFormalBlowupCoordinates,if_pos (hB i.property)]
    dsimp only [v]
    split_ifs with hi
    · rw [mul_one]
    · rfl
  have hProduct : MvPowerSeries.X e*(∑i,actualFormalBlowup A e b (M j i)*v i)=
      actualFormalBlowup A e b (F j) := by
    rw [←hFactor j,map_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_mul,hCoordinate]
    ring
  have hNorm:=actualNormalizedFormalMember_unique A e he b 1 (F j) (hF j)
    (∑i,actualFormalBlowup A e b (M j i)*v i) (by simpa only [pow_one] using hProduct)
  rw [←hNorm,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul,constantCoeff_actualFormalBlowup]
  dsimp only [v]
  split_ifs <;> simp

/-- The SAME marked selected contact cannot vanish along an essential pivot.
Whole contact supplies every coefficient in the block matrix internally. -/
theorem essential_pivot_impossible_of_actual_marks
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n))
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ) (R : ℕ)
    (hHeads : ∀a : V,(↑a.val.support : Set (Fin n))⊆A)
    (heB : e∈fixedSelectorBlock V R)
    (hCentre : ∀a,actualUnshiftedTaylorAlgHom n (Γ a)∈actualFormalCoordinateIdeal n A^normalExponentDegree a.val)
    (hPoint : ∀a : V,normalExponentDegree a.val≤R →
      actualNormalizedFormalMember A e he b (normalExponentDegree a.val)
        (actualUnshiftedTaylorAlgHom n (Γ a)) (hCentre a)∈genuineFormalVariables n^normalExponentDegree a.val)
    (hContact : actualFixedSelectorContactAt S Γ R)
    (hDet : (actualFixedSelectorJacobian S Γ R).det≠0) : False := by
  let B:=fixedSelectorBlock V R
  have hBA : B⊆A:=by
    rintro i ⟨a,_ha,hai⟩
    exact hHeads a (Finsupp.mem_support_iff.mpr hai)
  let D : B → MvPowerSeries (Fin n) ℂ:=fun j=>actualUnshiftedTaylorAlgHom n
    (actualFixedSelectorDerivative S Γ (fixedSelectorBlockEssential R j))
  have hDPower (j : B) : D j∈actualFormalCoordinateIdeal n A^1 := by
    let s:=fixedSelectorBlockEssential R j
    have hβ : (↑(fixedSelectorBeta S s).support : Set (Fin n))⊆A:=by
      intro i hi
      apply hBA
      by_contra hiB
      exact (Finsupp.mem_support_iff.mp hi) (fixedSelector_beta_support S R j i hiB)
    have hDegree:=fixedSelector_beta_degree S s
    have hPower:=actualMultiDerivative_mem_centre_add A (fixedSelectorBeta S s) hβ 1
      (actualUnshiftedTaylorAlgHom n (Γ (S.selected s)))
      (by simpa only [show 1+normalExponentDegree (fixedSelectorBeta S s)=
        normalExponentDegree (S.selected s).val by omega] using hCentre (S.selected s))
    simpa only [D,actualFixedSelectorDerivative,actualTaylor_actualAnalyticMultiDerivative] using hPower
  have hDPoint (j : B) : actualNormalizedFormalMember A e he b 1 (D j) (hDPower j)∈
      genuineFormalVariables n^1 := by
    let s:=fixedSelectorBlockEssential R j
    let β:=fixedSelectorBeta S s
    let μ:=normalExponentDegree (S.selected s).val
    have hDegree : normalExponentDegree β+1=μ:=fixedSelector_beta_degree S s
    have hβ : (↑β.support : Set (Fin n))⊆A := by
      intro i hi
      apply hBA
      by_contra hiB
      exact (Finsupp.mem_support_iff.mp hi) (fixedSelector_beta_support S R j i hiB)
    have h:=actualMultiDerivative_normalized_mem_point_power A e he b β hβ μ (by omega)
      (actualUnshiftedTaylorAlgHom n (Γ (S.selected s))) (hCentre (S.selected s))
      (hPoint (S.selected s) (fixedSelector_selected_degree_le S R j))
    have hMark : μ-normalExponentDegree β=1:=by omega
    have hDerivative : actualFormalMultiDerivative β (actualUnshiftedTaylorAlgHom n (Γ (S.selected s)))=D j := by
      simp only [D,actualFixedSelectorDerivative,actualTaylor_actualAnalyticMultiDerivative,s,β]
    have hNorm:=normalized_congr A e he b hMark hDerivative
      (actualMultiDerivative_mem_centre_sub A β hβ μ (by omega)
        (actualUnshiftedTaylorAlgHom n (Γ (S.selected s))) (hCentre (S.selected s))) (hDPower j)
    rw [hNorm,hMark] at h
    exact h
  obtain ⟨M,hFactor,hMatrix⟩:=actual_selected_contact_coefficient_matrix S Γ R hContact
  let MF : Matrix B B (MvPowerSeries (Fin n) ℂ):=fun j i=>actualUnshiftedTaylorAlgHom n (M j i)
  have hFactorF (j : B) : ∑i,MF j i*MvPowerSeries.X i.val=D j := by
    have h:=congrArg (actualUnshiftedTaylorAlgHom n) (hFactor j)
    simpa only [map_sum,map_mul,actualUnshiftedTaylor_coordinate] using h
  have hValues:=actual_normalized_block_factorization_constant A B e he hBA b MF D hFactorF hDPower
  let v : B → ℂ:=fun i=>if i.val=e then 1 else b i.val
  have hZero : (actualFixedSelectorJacobian S Γ R).mulVec v=0 := by
    funext j
    have hz : MvPowerSeries.constantCoeff
        (actualNormalizedFormalMember A e he b 1 (D j) (hDPower j))=0 := by
      exact (mem_genuineFormalVariables_pow_iff_coefficients_zero n 1 _).mp (hDPoint j) 0
        (by simp [normalExponentDegree])
    rw [hValues j] at hz
    rw [←hMatrix]
    change (∑i,HolGerm.eval (M j i)*v i)=0
    simpa only [MF,v,←MvPowerSeries.coeff_zero_eq_constantCoeff_apply,actualTaylor_coeff_zero] using hz
  have hv : v=0:=Matrix.mulVec_injective_of_det_ne_zero hDet
    (hZero.trans (Matrix.mulVec_zero _).symm)
  have hPivot:=congrFun hv (⟨e,heB⟩ : B)
  exact one_ne_zero (by simpa only [v,if_pos rfl,Pi.zero_apply] using hPivot)

private theorem first_pivot_lower_heads
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (A : Set (Fin n)) (e : Fin n) (heV : e∈fixedSelectorEssential V)
    (hHeads : ∀v : V,(↑v.val.support : Set (Fin n))⊆A) :
    ∀i,normalExponentDegree (wordExponent (w i))<normalExponentDegree (S.selected ⟨e,heV⟩).val →
      (↑(wordExponent (w i)).support : Set (Fin n))⊆A\{e} := by
  intro i hi x hx
  have hxA : x∈A:=hHeads (a i) (by simpa only [hw] using hx)
  refine ⟨hxA,?_⟩
  intro hxe
  have hxe' : x=e:=Set.mem_singleton_iff.mp hxe
  subst x
  change e∈(wordExponent (w i)).support at hx
  rw [hw] at hx
  have ha : (a i).val e≠0:=Finsupp.mem_support_iff.mp hx
  have hd:=S.least_degree ⟨e,heV⟩ (a i) ha
  rw [hw] at hi
  exact (not_le_of_gt hi) hd

/-- ENTIRE target HS equality for a whole containing ideal forces the actual
pivot to avoid ALL original essential variables of the SAME selector. -/
theorem actual_equal_hs_pivot_not_essential
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n))
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hMarked : ∀i,actualUnshiftedTaylorAlgHom n (Γ (a i))∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (w i)))
    (hWhole : ∀q,Function.Bijective (historicalWholeJetMap w
      (fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i))) q))
    (hSupported : HistoricalWholeSupportedDivision w (fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i))))
    (hPrefix : ∀m,HistoricalDegreePrefixFrames w (fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i))) m)
    (hCones : ∀j i,normalExponentDegree (wordExponent (w i))<normalExponentDegree (wordExponent (w j)) →
      ∀β,wordExponent (w i)≤β → MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom n (Γ (a j)))=0)
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hHeads : ∀v : V,(↑v.val.support : Set (Fin n))⊆A)
    (hCentre : ∀i,actualUnshiftedTaylorAlgHom n (Γ (a i))∈
      actualFormalCoordinateIdeal n A^normalExponentDegree (wordExponent (w i)))
    (hContact : ∀r,actualFixedSelectorContactAt S Γ r)
    (hDet : ∀r,(actualFixedSelectorJacobian S Γ r).det≠0)
    (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (hIn : ∀i,actualNormalizedFormalMember A e he b (normalExponentDegree (wordExponent (w i)))
      (actualUnshiftedTaylorAlgHom n (Γ (a i))) (hCentre i)∈K)
    (hHS : ∀ℓ,genuineFormalHilbertSamuelValue n K ℓ=
      genuineFormalHilbertSamuelValue n (Ideal.span (range (fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i))))) ℓ) :
    e∉fixedSelectorEssential V := by
  intro heV
  let s : fixedSelectorEssential V:=⟨e,heV⟩
  let R:=normalExponentDegree (S.selected s).val
  have heB : e∈fixedSelectorBlock V R:=⟨S.selected s,le_rfl,S.positive s⟩
  have hOrders:=actual_normalized_marks_up_to_of_equal_hs w
    (fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i))) hMarked hWhole hSupported hPrefix hCones
    A e he b R (first_pivot_lower_heads S a w hw A e heV hHeads) hCentre K hIn hHS
  have hCentreV (v : V) : actualUnshiftedTaylorAlgHom n (Γ v)∈
      actualFormalCoordinateIdeal n A^normalExponentDegree v.val := by
    simpa only [hw,Equiv.apply_symm_apply] using hCentre (a.symm v)
  apply essential_pivot_impossible_of_actual_marks S Γ A e he b R hHeads heB hCentreV ?_
    (hContact R) (hDet R)
  intro v hv
  have hv' : normalExponentDegree (wordExponent (w (a.symm v)))≤R:=by
    simpa only [hw,Equiv.apply_symm_apply] using hv
  have h:=hOrders (a.symm v) hv'
  have hWord : wordExponent (w (a.symm v))=v.val:=by rw [hw,Equiv.apply_symm_apply]
  have hG : actualUnshiftedTaylorAlgHom n (Γ (a (a.symm v)))=
      actualUnshiftedTaylorAlgHom n (Γ v):=by rw [Equiv.apply_symm_apply]
  have hNorm:=normalized_congr A e he b (congrArg normalExponentDegree hWord) hG
    (hCentre (a.symm v)) (hCentreV v)
  rw [hNorm] at h
  simpa only [hWord] using h

/-- On an actual essential chart the TRUE geometric strict transform cannot
have the original ENTIRE Hilbert--Samuel profile. No target certificate is input. -/
theorem actual_geometric_essential_pivot_hs_difference
    (d t : ℕ) (ht : 2≤t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t)))
    {V : Finset (Fin (d+t) →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel (d+t)))
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord (d+t))
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hSpan : Ideal.span (range (fun i=>Γ (a i)))=originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) W))
    (hMarked : ∀i,actualUnshiftedTaylorAlgHom (d+t) (Γ (a i))∈
      genuineFormalVariables (d+t)^normalExponentDegree (wordExponent (w i)))
    (hWhole : ∀q,Function.Bijective (historicalWholeJetMap w
      (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ (a i))) q))
    (hSupported : HistoricalWholeSupportedDivision w (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ (a i))))
    (hPrefix : ∀m,HistoricalDegreePrefixFrames w (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ (a i))) m)
    (hCones : ∀l i,normalExponentDegree (wordExponent (w i))<normalExponentDegree (wordExponent (w l)) →
      ∀β,wordExponent (w i)≤β → MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (Γ (a l)))=0)
    (hHeads : ∀v : V,(↑v.val.support : Set (Fin (d+t)))⊆actualTangentCentreVariables d t)
    (hCentre : ∀v,Γ v∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^normalExponentDegree v.val)
    (hContact : ∀r,actualFixedSelectorContactAt S Γ r)
    (hDet : ∀r,(actualFixedSelectorJacobian S Γ r).det≠0)
    (heV : j.natAdd d∈fixedSelectorEssential V) :
    ∃ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+t) (strictTransform (d+t)
      (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ≠
      hilbertSamuelAt (vanishingIdeal (n:=d+t) W) 0 ℓ := by
  by_contra! hHS
  let A:=actualTangentCentreVariables d t
  let e:=j.natAdd d
  have he : e∈A:=⟨j,rfl⟩
  let s : fixedSelectorEssential V:=⟨e,heV⟩
  let R:=normalExponentDegree (S.selected s).val
  have heB : e∈fixedSelectorBlock V R:=⟨S.selected s,le_rfl,S.positive s⟩
  have hCentreFin (i : Fin k) : Γ (a i)∈actualAnalyticCoordinateIdeal A^
      normalExponentDegree (wordExponent (w i)) := by
    simpa only [hw] using hCentre (a i)
  have hOrders:=same_historical_normalized_orders_up_to_of_geometric_hs_eq d t ht j b R W w
    (fun i=>Γ (a i)) hSpan hMarked hWhole hSupported hPrefix hCones
    (first_pivot_lower_heads S a w hw A e heV hHeads) hCentreFin hHS
  have hCentreF (v : V) : actualUnshiftedTaylorAlgHom (d+t) (Γ v)∈
      actualFormalCoordinateIdeal (d+t) A^normalExponentDegree v.val :=
    actualTaylor_mem_coordinateCentre_pow A (normalExponentDegree v.val) (Γ v) (hCentre v)
  choose N hProduct hTaylor using fun v=>exists_actualAnalyticBlowup_quotient A e he b
    (normalExponentDegree v.val) (Γ v) (hCentre v)
  apply essential_pivot_impossible_of_actual_marks S Γ A e he b R hHeads heB hCentreF ?_
    (hContact R) (hDet R)
  intro v hv
  have hv' : normalExponentDegree (wordExponent (w (a.symm v)))≤R:=by
    simpa only [hw,Equiv.apply_symm_apply] using hv
  have hProductV : (coordinateGerm e)^normalExponentDegree (wordExponent (w (a.symm v)))*N v=
      actualAnalyticBlowupPullback A e b (Γ (a (a.symm v))) := by
    simpa only [hw,Equiv.apply_symm_apply] using hProduct v
  have hNOrder:=hOrders (a.symm v) hv' (N v) hProductV
  have hNOrder' : N v∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^normalExponentDegree v.val:=by
    simpa only [hw,Equiv.apply_symm_apply] using hNOrder
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero (d+t) (normalExponentDegree v.val) _).mpr
  rw [←hTaylor v]
  exact (actual_maximal_power_iff_formal_coefficients_zero (d+t) (normalExponentDegree v.val) (N v)).mp hNOrder'

end
end Hironaka.HironakaActualHistoricalEssentialPivotDrop
