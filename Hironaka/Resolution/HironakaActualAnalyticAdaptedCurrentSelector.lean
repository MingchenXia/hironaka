import Hironaka.Resolution.HironakaActualAnalyticAdaptedCurrentFamily
import Hironaka.Resolution.HironakaActualAnalyticSourceShearSelector
import Hironaka.Resolution.HironakaActualZeroNormalizedCurrentSelector

/-! Arbitrary-direction source adaptation and current normalization transport
one fixed historical selector with its literal old labels. Every current
family/contact/Jacobian certificate is produced from original source data. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualAnalyticAdaptedCurrentSelector
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaHolomorphicJetChartInvariance
 HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
 HironakaActualFormalInitialDiagram HironakaActualRelativeNormalJetDivision
 HironakaActualInheritedNestedContactFlag HironakaActualFixedInheritedSelector
 HironakaActualNormalZeroAnalyticSaturation HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaActualNormalAllDirectionGeometricConverse HironakaActualZeroNormalizedCurrentFamily
 HironakaActualInheritedSourcePermutationFamily HironakaActualInheritedNextBlockGraph
 HironakaActualCauchyCoefficientLimits HironakaActualFixedInheritedSelectorBlowup
 HironakaActualInheritedAnalyticBlockJacobian HironakaActualOriginalTaylorDerivatives
 HironakaActualAnalyticAdaptedCurrentFamily HironakaActualAnalyticSourceShearSelector
 HironakaActualFixedInheritedSelectorPermutation HironakaActualRelativeStandardnessNormalPivotPriority
 HironakaActualNormalMarkedDirection HironakaActualAnalyticDirectionRemovalQuotient
 HironakaActualAnalyticBlowupTaylor
variable {n : ℕ}

private theorem same_zero_normalized_historical_selector_contact_and_jacobian
    (I : Ideal (HolGerm (ComplexModel n)))
    (G : ActualAnalyticInheritedFamily n 0 (analyticZeroTaylorIdeal n I))
    (hmem : ∀a,G.germs a∈I) (e : Fin n)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici e)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticZeroNormalizedVertex n I G e hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)))
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (hadapt : ∀k,actualFixedSelectorContactAt S G.germs k) :
    let H:=sameAnalyticZeroNormalizedVertex n I G e hp
    (∀k,actualFixedSelectorContactAt S H k) ∧
      ∀k,actualFixedSelectorJacobian S H k=actualFixedSelectorJacobian S G.germs k := by
  have hNormalOrders : ∀a,sameAnalyticNormalNormalizedVertex n I G e e le_rfl
      (fun _=>0) hp a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^normalExponentDegree a.val :=
    hOrder
  obtain ⟨hpf,hAll⟩:=actual_normal_marked_orders_preserve_same_historical_selector n I G hmem
    e e le_rfl (fun _=>0) hp hNormalOrders S hred hadapt
  let H:=sameAnalyticZeroNormalizedVertex n I G e hp
  have hDerivative (k)
      (j : fixedSelectorBlock (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal n I)) k) :
      actualUnshiftedTaylorAlgHom n (actualFixedSelectorDerivative S H (fixedSelectorBlockEssential k j))=
        actualNormalizedFixedSelectorDerivative G S k (Set.Ici e) e
          (Set.mem_Ici.mpr le_rfl) (fun _=>0) hpf j := by
    unfold actualFixedSelectorDerivative actualNormalizedFixedSelectorDerivative
    rw [actualTaylor_actualAnalyticMultiDerivative,actualTaylor_sameAnalyticZeroNormalizedVertex]
  constructor
  · intro k j
    apply (mem_analytic_ideal_iff_actualUnshifted_extension n _ _).mpr
    rw [map_actualAnalyticCoordinateBlockIdeal_actualTaylor]
    have hm:=(hAll k).2.1 j
    rw [←hDerivative k j] at hm
    exact hm
  · intro k
    ext j i
    have heq:=congrArg (fun A=>A j i) ((hAll k).2.2.1)
    change HolGerm.eval (actualAnalyticCoordinateDerivative i.val
      (actualFixedSelectorDerivative S H (fixedSelectorBlockEssential k j)))=_
    rw [←actualTaylor_coeff_zero,actualTaylor_actualAnalyticCoordinateDerivative,hDerivative k j]
    exact heq


private theorem renamed_vertex_set_eq {m : ℕ}
    (p : Fin m≃Fin m) {V W : Finset (Fin m →₀ ℕ)}
    (E : V≃W) (hlabel : ∀a,(E a).val=Finsupp.domCongr p a.val) :
    fixedPermutedVertices p V=W := by
  ext α
  constructor
  · intro hα
    obtain ⟨a,ha,he⟩:=Finset.mem_map.mp hα
    have hv : (E ⟨a,ha⟩).val=α:=(hlabel ⟨a,ha⟩).trans he
    exact hv ▸ (E ⟨a,ha⟩).property
  · intro hα
    obtain ⟨a,ha⟩:=E.surjective ⟨α,hα⟩
    exact Finset.mem_map.mpr ⟨a.val,a.property,(hlabel a).symm.trans (congrArg Subtype.val ha)⟩

private theorem fixed_selector_renamed_raw {m : ℕ}
    (p : Fin m≃Fin m) {V W : Finset (Fin m →₀ ℕ)}
    (E : V≃W) (hlabel : ∀a,(E a).val=Finsupp.domCongr p a.val)
    (F : V → HolGerm (ComplexModel m)) (GS : W → HolGerm (ComplexModel m))
    (hLiteral : ∀a,GS (E a)=actualPermutationGermEquiv p (F a))
    (S : ActualFixedInheritedSelector V) (hContact : ∀k,actualFixedSelectorContactAt S F k) :
    ∃hP : fixedPermutedVertices p V=W,
      (∀k,actualFixedSelectorContactAt (sourceFixedSelectorCast hP (actualFixedSelectorPermutation p S)) GS k) ∧
      ∀k,(actualFixedSelectorJacobian (sourceFixedSelectorCast hP (actualFixedSelectorPermutation p S)) GS k).submatrix
        ((fixedBlockPermutation p V k).trans (sourceBlockCast hP k))
        ((fixedBlockPermutation p V k).trans (sourceBlockCast hP k))=actualFixedSelectorJacobian S F k := by
  let hP:=renamed_vertex_set_eq p E hlabel
  have hGS : GS=sourceRawFamilyCast hP (actualPermutedSelectorFamily p F) := by
    funext a
    obtain ⟨a,rfl⟩:=E.surjective a
    have hLab : sourceVertexSetCast hP (fixedVertexPermutation p V a)=E a := by
      apply Subtype.ext
      exact (hlabel a).symm
    calc
      GS (E a)=actualPermutationGermEquiv p (F a):=hLiteral a
      _=sourceRawFamilyCast hP (actualPermutedSelectorFamily p F) (E a):=by
        rw [←hLab,sourceRawFamilyCast_apply]
        simp only [actualPermutedSelectorFamily,Equiv.symm_apply_apply]
  refine ⟨hP,?_,?_⟩
  · intro k
    rw [hGS]
    exact (sourceFixedSelectorCast_contact hP (actualFixedSelectorPermutation p S) _ k).mpr
      (actualFixedSelectorContact_permutation p S F k (hContact k))
  · intro k
    rw [hGS]
    ext j i
    have h1:=congrArg (fun M=>M (fixedBlockPermutation p V k j) (fixedBlockPermutation p V k i))
      (sourceFixedSelectorCast_jacobian hP (actualFixedSelectorPermutation p S) (actualPermutedSelectorFamily p F) k)
    have h2:=congrArg (fun M=>M j i) (actualFixedSelectorJacobian_permutation p S F k)
    exact h1.trans h2

private theorem fixed_selector_given_zero_family {m : ℕ}
    (I : Ideal (HolGerm (ComplexModel m)))
    (G : ActualAnalyticInheritedFamily m 0 (analyticZeroTaylorIdeal m I))
    (hmem : ∀a,G.germs a∈I) (q : Fin m)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticZeroNormalizedVertex m I G q hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel m))^normalExponentDegree a.val)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal m I)))
    (hPrefix : ∀k,ActualInheritedPrefixReducedAt G k)
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k)
    (hV : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal m I)=
      actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal m (sameAnalyticZeroNormalizedIdeal m I G q hp)))
    (GT : ActualAnalyticInheritedFamily m 0
      (analyticZeroTaylorIdeal m (sameAnalyticZeroNormalizedIdeal m I G q hp)))
    (hGT : ∀a,GT.germs (sourceVertexSetCast hV a)=sameAnalyticZeroNormalizedVertex m I G q hp a) :
    (∀k,actualFixedSelectorContactAt (sourceFixedSelectorCast hV S) GT.germs k) ∧
      ∀k,(actualFixedSelectorJacobian (sourceFixedSelectorCast hV S) GT.germs k).submatrix
        (sourceBlockCast hV k) (sourceBlockCast hV k)=actualFixedSelectorJacobian S G.germs k := by
  let H:=sameAnalyticZeroNormalizedVertex m I G q hp
  obtain ⟨hZeroC,hZeroJ⟩:=same_zero_normalized_historical_selector_contact_and_jacobian
    I G hmem q hp hOrder S hPrefix hContact
  have hGTFamily : GT.germs=sourceRawFamilyCast hV H := by
    funext a
    obtain ⟨a,rfl⟩:=(sourceVertexSetCast hV).surjective a
    exact (hGT a).trans (sourceRawFamilyCast_apply hV H a).symm
  constructor
  · intro k
    rw [hGTFamily]
    exact (sourceFixedSelectorCast_contact hV S H k).mpr (hZeroC k)
  · intro k
    rw [hGTFamily,sourceFixedSelectorCast_jacobian]
    exact hZeroJ k

structure ActualAdaptedCurrentFamilyData
    (I : Ideal (HolGerm (ComplexModel (n+1))))
    (G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I))
    (q e f : Fin (n+1)) (b : Fin (n+1) → ℂ)
    where
  sourceFamily : ActualAnalyticInheritedFamily (n+1) 0
    (analyticZeroTaylorIdeal (n+1) (actualAnalyticNormalAdaptedSourceIdeal I q e f b))
  sourceVertexEquiv : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I) ≃
    actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (n+1) (actualAnalyticNormalAdaptedSourceIdeal I q e f b))
  sourceLabels : ∀a,(sourceVertexEquiv a).val=Finsupp.domCongr (normalPivotEquiv q f) a.val
  sourceLiterals : ∀a,sourceFamily.germs (sourceVertexEquiv a)=actualPermutationGermEquiv (normalPivotEquiv q f)
    (actualAnalyticDirectionShearGermEquiv (Set.Ici q) f
      (fun i=>actualNormalMarkedDirection (Set.Ici q) e b i /
        actualNormalMarkedDirection (Set.Ici q) e b f) (G.germs a))
  sourceMember : ∀a,sourceFamily.germs a∈actualAnalyticNormalAdaptedSourceIdeal I q e f b
  sourcePrefix : ∀k,ActualInheritedPrefixReducedAt sourceFamily k
  sourcePower : ∀a,sourceFamily.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val
  sourceOrder : ∀a,sameAnalyticZeroNormalizedVertex (n+1) _ sourceFamily q sourcePower a∈
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^normalExponentDegree a.val
  targetDiagram : actualInitialDiagram MonomialOrder.degLex
      (analyticZeroTaylorIdeal (n+1) (sameAnalyticZeroNormalizedIdeal (n+1) _ sourceFamily q sourcePower))=
    actualInitialDiagram MonomialOrder.degLex
      (analyticZeroTaylorIdeal (n+1) (actualAnalyticNormalAdaptedSourceIdeal I q e f b))
  targetVertexSet : actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (n+1) (actualAnalyticNormalAdaptedSourceIdeal I q e f b))=
    actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (n+1) (sameAnalyticZeroNormalizedIdeal (n+1) _ sourceFamily q sourcePower))
  targetFamily : ActualAnalyticInheritedFamily (n+1) 0
    (analyticZeroTaylorIdeal (n+1) (sameAnalyticZeroNormalizedIdeal (n+1) _ sourceFamily q sourcePower))
  targetLiterals : ∀a,targetFamily.germs (sourceVertexSetCast targetVertexSet a)=
    sameAnalyticZeroNormalizedVertex (n+1) _ sourceFamily q sourcePower a
  targetSpan : Ideal.span (range targetFamily.germs)=sameAnalyticZeroNormalizedIdeal (n+1) _ sourceFamily q sourcePower
  targetMember : ∀a,targetFamily.germs a∈sameAnalyticZeroNormalizedIdeal (n+1) _ sourceFamily q sourcePower
  targetPrefix : ∀k,ActualInheritedPrefixReducedAt targetFamily k
  targetHS : ∀ℓ,hilbertSamuelValue (sameAnalyticZeroNormalizedIdeal (n+1) _ sourceFamily q sourcePower) ℓ=
    hilbertSamuelValue I ℓ

structure ActualAdaptedCurrentSelectorData
    (I : Ideal (HolGerm (ComplexModel (n+1))))
    (G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I))
    (q e f : Fin (n+1)) (b : Fin (n+1) → ℂ)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    extends ActualAdaptedCurrentFamilyData I G q e f b where
  permutationVertexSet : fixedPermutedVertices (normalPivotEquiv q f)
      (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I))=
    actualInitialVertices MonomialOrder.degLex
      (analyticZeroTaylorIdeal (n+1) (actualAnalyticNormalAdaptedSourceIdeal I q e f b))
  sourceContact : ∀k,actualFixedSelectorContactAt
    (sourceFixedSelectorCast permutationVertexSet (actualFixedSelectorPermutation (normalPivotEquiv q f) S))
    sourceFamily.germs k
  targetContact : ∀k,actualFixedSelectorContactAt
    (sourceFixedSelectorCast targetVertexSet
      (sourceFixedSelectorCast permutationVertexSet (actualFixedSelectorPermutation (normalPivotEquiv q f) S)))
    targetFamily.germs k
  targetJacobian : ∀k,(actualFixedSelectorJacobian
    (sourceFixedSelectorCast targetVertexSet
      (sourceFixedSelectorCast permutationVertexSet (actualFixedSelectorPermutation (normalPivotEquiv q f) S)))
    targetFamily.germs k).submatrix
      ((fixedBlockPermutation (normalPivotEquiv q f) _ k).trans
        ((sourceBlockCast permutationVertexSet k).trans (sourceBlockCast targetVertexSet k)))
      ((fixedBlockPermutation (normalPivotEquiv q f) _ k).trans
        ((sourceBlockCast permutationVertexSet k).trans (sourceBlockCast targetVertexSet k)))=
    actualFixedSelectorJacobian S G.germs k

private theorem exists_adapted_current_base_data
    (I : Ideal (HolGerm (ComplexModel (n+1))))
    (G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I))
    (hmem : ∀a,G.germs a∈I) (q e : Fin (n+1)) (hqe : q≤e) (b : Fin (n+1) → ℂ)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticNormalNormalizedVertex (n+1) I G q e hqe b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^normalExponentDegree a.val)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
 :
    ∃f : Fin (n+1),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      Nonempty (ActualAdaptedCurrentFamilyData I G q e f b) := by
  obtain ⟨f,hqf,hvf,GS,ES,hES,hLiteral,hMember,hPrefix,hpS,hOrdS,hD,hV,GT,hGT,hSpan,hMT,hPT,hHS⟩:=
    exists_actual_analytic_adapted_current_family I G hmem q e hqe b hp hOrder hred
  exact ⟨f,hqf,hvf,⟨{
    sourceFamily:=GS
    sourceVertexEquiv:=ES
    sourceLabels:=hES
    sourceLiterals:=hLiteral
    sourceMember:=hMember
    sourcePrefix:=hPrefix
    sourcePower:=hpS
    sourceOrder:=hOrdS
    targetDiagram:=hD
    targetVertexSet:=hV
    targetFamily:=GT
    targetLiterals:=hGT
    targetSpan:=hSpan
    targetMember:=hMT
    targetPrefix:=hPT
    targetHS:=hHS }⟩⟩

private theorem matrix_submatrix_chain {ι₀ ι₁ ι₂ : Type*}
    (e₁ : ι₀≃ι₁) (e₂ : ι₁≃ι₂)
    {M₂ : Matrix ι₂ ι₂ ℂ} {M₁ : Matrix ι₁ ι₁ ℂ} {M₀ N₀ : Matrix ι₀ ι₀ ℂ}
    (h₂ : M₂.submatrix e₂ e₂=M₁) (h₁ : M₁.submatrix e₁ e₁=M₀) (h₀ : M₀=N₀) :
    M₂.submatrix (e₁.trans e₂) (e₁.trans e₂)=N₀ := by
  calc
    M₂.submatrix (e₁.trans e₂) (e₁.trans e₂)=(M₂.submatrix e₂ e₂).submatrix e₁ e₁:=rfl
    _=M₁.submatrix e₁ e₁:=congrArg (fun M=>M.submatrix e₁ e₁) h₂
    _=N₀:=h₁.trans h₀

private theorem selector_data_of_base_data
    (I : Ideal (HolGerm (ComplexModel (n+1))))
    (G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I))
    (hmem : ∀a,G.germs a∈I) (q e : Fin (n+1)) (hqe : q≤e) (b : Fin (n+1) → ℂ)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticNormalNormalizedVertex (n+1) I G q e hqe b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^normalExponentDegree a.val)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k) (f : Fin (n+1)) (hqf : q≤f)
    (hvf : actualNormalMarkedDirection (Set.Ici q) e b f≠0)
    (D : ActualAdaptedCurrentFamilyData I G q e f b) :
    Nonempty (ActualAdaptedCurrentSelectorData I G q e f b S) := by
  let p:=normalPivotEquiv q f
  let F:=fun a=>actualAnalyticDirectionShearGermEquiv (Set.Ici q) f
    (fun i=>actualNormalMarkedDirection (Set.Ici q) e b i /
      actualNormalMarkedDirection (Set.Ici q) e b f) (G.germs a)
  obtain ⟨hShearC,hShearJ⟩:=actual_marked_orders_source_shear_selector
    I G hmem q e hqe b hp hOrder S hred hContact f hqf hvf
  obtain ⟨hP,hSSContact,hPermJ⟩:=fixed_selector_renamed_raw p D.sourceVertexEquiv D.sourceLabels
    F D.sourceFamily.germs D.sourceLiterals S hShearC
  let SS:=sourceFixedSelectorCast hP (actualFixedSelectorPermutation p S)
  obtain ⟨hSTContact,hSTJac⟩:=fixed_selector_given_zero_family
    (actualAnalyticNormalAdaptedSourceIdeal I q e f b) D.sourceFamily D.sourceMember q D.sourcePower D.sourceOrder
    SS D.sourcePrefix hSSContact D.targetVertexSet D.targetFamily D.targetLiterals
  refine ⟨{
    toActualAdaptedCurrentFamilyData:=D
    permutationVertexSet:=hP
    sourceContact:=hSSContact
    targetContact:=hSTContact
    targetJacobian:=?_ }⟩
  intro k
  exact matrix_submatrix_chain
    ((fixedBlockPermutation p _ k).trans (sourceBlockCast hP k))
    (sourceBlockCast D.targetVertexSet k) (hSTJac k) (hPermJ k) (hShearJ k)


theorem exists_actual_analytic_adapted_current_family_and_selector
    (I : Ideal (HolGerm (ComplexModel (n+1))))
    (G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I))
    (hmem : ∀a,G.germs a∈I) (q e : Fin (n+1)) (hqe : q≤e) (b : Fin (n+1) → ℂ)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticNormalNormalizedVertex (n+1) I G q e hqe b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^normalExponentDegree a.val)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)))
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k) :
    ∃f : Fin (n+1),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      Nonempty (ActualAdaptedCurrentSelectorData I G q e f b S) := by
  obtain ⟨f,hqf,hvf,⟨D⟩⟩:=exists_adapted_current_base_data I G hmem q e hqe b hp hOrder hred
  exact ⟨f,hqf,hvf,selector_data_of_base_data I G hmem q e hqe b hp hOrder hred S hContact f hqf hvf D⟩

end
end Hironaka.HironakaActualAnalyticAdaptedCurrentSelector
