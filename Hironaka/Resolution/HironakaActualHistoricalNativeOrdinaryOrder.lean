import Hironaka.Resolution.HironakaActualWeightedHSNativeOrder
import Hironaka.Resolution.HironakaActualHistoricalNativeStageStep

/-! Actual current native point data give ORDINARY raw order at the SAME
original mark, retaining the full Q/E and without a monomial-part premise.
Blueprint: hironaka-actual-historical-native-ordinary-order-20261102.tex. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalNativeOrdinaryOrder
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualWeightedHSNativeOrder HironakaActualHistoricalNativeStageStep
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualFixedInheritedSelector
  HironakaActualWeightedHSNormalInput HironakaActualGeometricCurrentNeighborhoodHS
  HironakaActualRelativeNormalJetDivision HironakaActualNormalZeroAnalyticSaturation
  HironakaActualFormalInitialDiagram HironakaActualHistoricalHSMarkedDomain
  HironakaActualOriginalInitialHSPhase HironakaActualWeightedCoefficientCompression
  HironakaActualCoherentWeightedCoefficientMarked HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaActualInheritedNeighborhoodMarkedHS
  HironakaSmoothSubmersionGermIdealColon HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualCauchyMonomialDivision
  HironakaActualOriginalFormalHSTransfer HironakaSharpOriginalProductTraceOrder
  GermIdealOrder IdealWeightPowers OrderTaylor OrderMultiplicativity CompanionReduction
  MarkedIdeals BlowupTowers ResolutionInvariantSpec NonmonomialOrderLocal
  InvertibleIdealQuotient RelativePrincipalizationSpan

variable {n : ℕ}

/-- The ORIGINAL source domain forces nonempty labels, with full E retained. -/
theorem initial_phase_labels_nonempty {B : GermIdeal n (ComplexModel n)}
    {I : Ideal (HolGerm (ComplexModel n))}
    {G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I)} {R : ℕ→ℕ}
    (PHS : ActualGeometricInheritedNeighborhoodHS B I G R)
    {M : Type*} (η : presentationOpen PHS→M) (E : List (Set M)) {q : ℕ}
    (hQ : IsInvDomain q (initialWeightedRecord PHS η E)) :
    Nonempty (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) := by
  by_contra hNo
  let x : presentationOpen PHS:=⟨0,PHS.zero_mem⟩
  obtain ⟨f,hf,hFreq⟩:=hQ.isNonzeroAlongAt x (mem_univ _)
  obtain ⟨_hhol,K,s,a,hs,_ha,hSum⟩:=hf
  apply hFreq
  filter_upwards [hSum] with y hy
  rintro ⟨_,hne⟩
  apply hne
  rw [hy]
  apply Finset.sum_eq_zero
  intro i _
  obtain ⟨v,_⟩:=hs i
  exact False.elim (hNo ⟨v⟩)

variable {X : CMfd.{0} n} {k : ℕ}

private theorem adaptedGerm_pow (x : X)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
    (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (F : X→ℂ) (hF : HolomorphicAt n F x) (j : ℕ) :
    adaptedGerm x Φ h0 (fun z=>F z^j) (holomorphicAt_pow_of hF j)=
      (adaptedGerm x Φ h0 F hF)^j :=
  HolGerm.mk_pow _ ((holomorphic_adapted_iff x Φ h0 F).mpr hF) j

/-- Actual current whole-compression data give ORDINARY raw order M and
the genuine next-order exclusion. No nmPart premise or future CAN is used. -/
theorem actual_native_point_ordinary_order
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (hV : V.Nonempty) (a : Fin k ≃ V) (w : Fin k→CoordinateWord n)
    (hWords : ∀i,wordExponent (w i)=(a i).val)
    (W : Set X) (Q : MarkedIdeal n X) (hQN : Q.N=univ) (hQI : Q.ideal.IsCoherent)
    (hQMark : Q.d=weightedCommonMark (fun v : V=>normalExponentDegree v.val))
    (x : X) (hx : x∈Q.cosupp)
    (hAt : ActualHistoricalNativePointPresentation S a w W Q x) :
    ordinaryTraceOrder (X:=X) univ Q.ideal x=
      weightedCommonMark (fun v : V=>normalExponentDegree v.val) ∧
    x∉cosupport n univ Q.ideal
      (weightedCommonMark (fun v : V=>normalExponentDegree v.val)+1) := by
  let μ:=fun v : V=>normalExponentDegree v.val
  let d:=weightedCommonMark μ
  let O:=ordinaryTraceMarked (X:=X) univ Q.ideal
  obtain ⟨Φ,hΦsrc,hΦ0,Γ,hFive,_hSpan,hCompression⟩:=hAt
  obtain ⟨v,hv⟩:=hV
  let v₀ : V:=⟨v,hv⟩
  let i:=a.symm v₀
  have hDegree : normalExponentDegree (wordExponent (w i))=μ v₀ := by
    rw [hWords]
    exact congrArg (fun z=>normalExponentDegree z.val) (a.apply_symm_apply v₀)
  obtain ⟨F,hF,hFΓ⟩:=exists_original_adapted_representative x Φ hΦ0 (Γ v₀)
  have hFnot : ¬(idealPow (pointIdeal n x) (μ v₀+1)).mem x F := by
    intro h
    have hGerm:=adaptedGerm_point_power x Φ hΦsrc hΦ0 F hF h
    rw [hFΓ] at hGerm
    have hTaylor : actualUnshiftedTaylorAlgHom n (Γ v₀)∈genuineFormalVariables n^(μ v₀+1) := by
      rw [←map_actualUnshifted_maximal_pow n (μ v₀+1)]
      exact Ideal.mem_map_of_mem _ hGerm
    have hHigh:=(hFive.1 i).2
    rw [hDegree] at hHigh
    have hV₀ : a i=v₀:=a.apply_symm_apply v₀
    rw [hV₀] at hHigh
    exact hHigh hTaylor
  let e:=d/μ v₀
  have hPowerNot:=pow_notMem_idealPow hF hFnot e
  have hNumber : e*μ v₀=d:=
    (Nat.mul_comm e (μ v₀)).trans (weight_mul_compressionExponent μ v₀)
  rw [hNumber] at hPowerNot
  have hPow : adaptedGerm x Φ hΦ0 (fun y=>F y^e) (holomorphicAt_pow_of hF e)=(Γ v₀)^e :=
    (adaptedGerm_pow x Φ hΦ0 F hF e).trans (congrArg (fun g=>g^e) hFΓ)
  have hIn : (Γ v₀)^e∈adaptedIdeal Q.ideal x Φ hΦ0 := by
    rw [hCompression]
    exact Ideal.subset_span ⟨v₀,rfl⟩
  have hNativeMember : Q.ideal.mem x (fun y=>F y^e):=
    (mem_adaptedIdeal_iff Q.ideal hQI x Φ hΦ0 _ (holomorphicAt_pow_of hF e)).mp
      (hPow.symm ▸ hIn)
  have hNext : x∉cosupport n univ Q.ideal (d+1) := by
    intro h
    exact hPowerNot (mem_idealPow_of_vanishesToOrderOn_univ (h.2 _ hNativeMember))
  have hGe (j : ℕ) : ordGe (M:=X) O j=cosupport n univ Q.ideal j:=
    ordGe_ordinaryTraceMarked_eq_cosupport (X:=X) univ Q.ideal hQI j
  have hUpper : x∉ordGe (M:=X) O (d+1):=(hGe (d+1)).symm ▸ hNext
  have hLow : x∈ordGe (M:=X) O d := by
    rw [hGe]
    have h:=hx
    change x∈cosupport n Q.N Q.ideal Q.d at h
    rwa [hQN,hQMark] at h
  have hLower : d≤nmOrd (M:=X) O x := by
    cases hd : d with
    | zero => exact Nat.zero_le _
    | succ j =>
      have hLow' : x∈ordGe (M:=X) O (j+1):=hd ▸ hLow
      have hBound:=succ_le_nmOrd_of_mem (M:=X) ⟨d,hUpper⟩ hLow'
      simpa only [hd] using hBound
  exact ⟨(nmOrd_le_of_notMem (M:=X) hUpper).antisymm hLower,hNext⟩

/-- Source actual point presentations imply maximal order on the SAME current
full Q. No ordinary or nonmonomial order output is assumed. -/
theorem actual_native_current_maximal_order
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (hV : V.Nonempty) (a : Fin k ≃ V) (w : Fin k→CoordinateWord n)
    (hWords : ∀i,wordExponent (w i)=(a i).val)
    (W : Set X) (Q : MarkedIdeal n X) (hQN : Q.N=univ) (hQI : Q.ideal.IsCoherent)
    (hQMark : Q.d=weightedCommonMark (fun v : V=>normalExponentDegree v.val))
    (hPoints : ∀x∈Q.cosupp,ActualHistoricalNativePointPresentation S a w W Q x) :
    HomogenizedIdealAlong.IsMaximalOrderAlong Q.N Q.ideal Q.d := by
  intro x hNext
  have hx : x∈Q.cosupp:=cosupport_anti (Nat.le_succ Q.d) hNext
  have hNot:=(actual_native_point_ordinary_order S hV a w hWords W Q hQN hQI hQMark x hx
    (hPoints x hx)).2
  apply hNot
  rwa [hQN,hQMark] at hNext

end
end Hironaka.HironakaActualHistoricalNativeOrdinaryOrder
