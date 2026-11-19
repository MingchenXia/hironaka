import Hironaka.Resolution.HironakaActualAnalyticSourceNormalizedTransport
import Hironaka.Resolution.HironakaActualAnalyticAdaptedCurrentSelector
import Hironaka.Resolution.HironakaActualWeightedCoefficientCompression

/-! A single actual analytic unit transports EVERY same original normalized
member to its produced adapted zero-chart member at the unchanged mark.
Whole independently named normalized ideals use the SAME equivalence. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualOriginalAdaptedMarkedTransport
noncomputable section
open HolGerm HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
 HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticBlowupTaylor
 HironakaActualAnalyticDirectionRemovalQuotient HironakaActualAnalyticSourceShearTaylor
 HironakaActualNormalZeroAnalyticSaturation HironakaActualFormalBlowupAllDirections
 HironakaActualFormalCoordinatePowerDivision HironakaActualAnalyticStrictGenerators
 HironakaActualNormalCoordinateReindex HironakaActualAnalyticNormalTargetTransition
 HironakaActualFixedInheritedSelectorPermutation HironakaActualAnalyticFormalNormalPowers
 HironakaActualAnalyticAdaptedCurrentFamily HironakaActualNormalMarkedDirection
 HironakaActualRelativeStandardnessNormalPivotPriority HironakaActualRelativeStandardnessNormalPointBridge
 HironakaActualNormalCentreChartTransition HironakaActualAnalyticSourceNormalizedTransport
 HironakaActualAnalyticAdaptedCurrentSelector HironakaActualInheritedSourcePermutationFamily
 HironakaActualInheritedSourceOwnerPermutation HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaActualFixedInheritedSelector HironakaActualFormalInitialDiagram HironakaRelativeNormalMonomialBasis
 HironakaActualRelativeNormalJetDivision HironakaActualInheritedNestedContactFlag
 HironakaActualWeightedCoefficientCompression
variable {n : ℕ}

private theorem coordinateEquiv_eq_actualPermutation (r : Fin n ≃ Fin n) :
    coordinateGermEquiv r=actualPermutationGermEquiv r := by
  apply AlgEquiv.ext
  intro g
  apply actualUnshiftedTaylorAlgHom_injective n
  have h : actualUnshiftedTaylorAlgHom n (coordinateGermEquiv r g)=
      MvPowerSeries.rename r (actualUnshiftedTaylorAlgHom n g) :=
    DFunLike.congr_fun (actualTaylor_coordinateGermEquiv r) g
  rw [h,actualTaylor_actualPermutationGermEquiv]

private theorem inverse_map_of_map_eq
    (E : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (J K : Ideal (HolGerm (ComplexModel n))) (h : Ideal.map E.toRingEquiv.toRingHom J=K) :
    Ideal.map E.symm.toRingEquiv.toRingHom K=J := by
  rw [←h,Ideal.map_map]
  have he : E.symm.toRingEquiv.toRingHom.comp E.toRingEquiv.toRingHom=RingHom.id _ := by
    apply RingHom.ext
    intro g
    exact E.symm_apply_apply g
  rw [he,Ideal.map_id]

private theorem normal_pivot_preserves_tail {m : ℕ} (q f : Fin (m+1)) (hqf : q≤f)
    (i : Fin (m+1)) : normalPivotEquiv q f i∈Set.Ici q ↔ i∈Set.Ici q := by
  constructor
  · intro hi
    by_contra h
    have ht:=normalPivotEquiv_tangent q f hqf i (lt_of_not_ge h)
    rw [ht] at hi
    exact h hi
  · intro hi
    by_contra h
    have hpi : normalPivotEquiv q f i<q:=lt_of_not_ge h
    have hfix:=normalPivotEquiv_tangent q f hqf (normalPivotEquiv q f i) hpi
    have heq : normalPivotEquiv q f i=i:=(normalPivotEquiv q f).injective hfix
    rw [heq] at hpi
    exact (not_lt_of_ge hi) hpi

private theorem normal_pivot_tail_image {m : ℕ} (q f : Fin (m+1)) (hqf : q≤f) :
    normalPivotEquiv q f '' Set.Ici q=Set.Ici q := by
  ext i
  constructor
  · rintro ⟨j,hj,rfl⟩
    exact (normal_pivot_preserves_tail q f hqf j).mpr hj
  · intro hi
    refine ⟨(normalPivotEquiv q f).symm i,?_,by simp⟩
    exact (normal_pivot_preserves_tail q f hqf _).mp (by simpa using hi)

private theorem actual_pullback_eq_normal_direction (A : Set (Fin n))
    (e : Fin n) (b : Fin n → ℂ) :
    actualAnalyticBlowupPullback A e b=
      actualAnalyticBlowupPullback A e (actualNormalMarkedDirection A e b) := by
  have hMap : actualAnalyticBlowupMap A e b=
      actualAnalyticBlowupMap A e (actualNormalMarkedDirection A e b) := by
    funext z
    ext i
    by_cases hi : i∈A <;> by_cases hie : i=e <;>
      simp [actualAnalyticBlowupMap_apply,actualAnalyticBlowupCoordinate,
        actualNormalMarkedDirection,actualNormalPointDirection,hi,hie]
  apply AlgHom.ext
  intro g
  obtain ⟨H,hH,rfl⟩:=HolGerm.exists_eq_mk g
  unfold actualAnalyticBlowupPullback
  rw [compAlgHom_mk,compAlgHom_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Filter.Eventually.of_forall fun z=>congrArg H (congrFun hMap z)

private theorem actual_permutation_pullback (p : Fin n≃Fin n)
    (A : Set (Fin n)) (e : Fin n) (b : Fin n → ℂ) (g : HolGerm (ComplexModel n)) :
    actualPermutationGermEquiv p (actualAnalyticBlowupPullback A e b g)=
      actualAnalyticBlowupPullback (p '' A) (p e) (b ∘ p.symm) (actualPermutationGermEquiv p g) := by
  simpa only [coordinateEquiv_eq_actualPermutation] using
    coordinateGermEquiv_actualAnalyticBlowupPullback p A e b g

private theorem same_quotient_after_source_adaptation {m : ℕ}
    (q f : Fin (m+1)) (hqf : q≤f) (w : Fin (m+1) → ℂ) (μ : ℕ)
    (g Hf Hnew : HolGerm (ComplexModel (m+1)))
    (hHf : coordinateGerm f^μ*Hf=actualAnalyticBlowupPullback (Set.Ici q) f w g)
    (hHnew : coordinateGerm q^μ*Hnew=actualAnalyticBlowupPullback (Set.Ici q) q (fun _=>0)
      (actualPermutationGermEquiv (normalPivotEquiv q f)
        (actualAnalyticDirectionShearGermEquiv (Set.Ici q) f w g))) :
    actualPermutationGermEquiv (normalPivotEquiv q f) Hf=Hnew := by
  have hZero:=hHf.trans (actualAnalyticBlowupPullback_direction_shear (Set.Ici q) f w g)
  have h:=congrArg (actualPermutationGermEquiv (normalPivotEquiv q f)) hZero
  rw [map_mul,map_pow,actualPermutationGermEquiv_coordinate,normalPivotEquiv_pivot q f hqf,
    actual_permutation_pullback,normal_pivot_tail_image q f hqf,normalPivotEquiv_pivot q f hqf] at h
  apply mul_left_cancel₀ (pow_ne_zero μ (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero q))
  exact h.trans hHnew.symm

/-- One equivalence and one genuine unit, chosen BEFORE all source members,
retain each literal mark under the full source/target analytic adaptation. -/
theorem exists_actual_original_to_adapted_marked_transport {m : ℕ}
    (q e f : Fin (m+1)) (hqe : q≤e) (hqf : q≤f) (b : Fin (m+1) → ℂ)
    (hvf : actualNormalMarkedDirection (Set.Ici q) e b f≠0) :
    ∃C : HolGerm (ComplexModel (m+1))≃ₐ[ℂ]HolGerm (ComplexModel (m+1)),
    ∃u : HolGerm (ComplexModel (m+1)),IsUnit u ∧
      (∀(μ : ℕ)(g : HolGerm (ComplexModel (m+1))),g∈actualAnalyticCoordinateIdeal (Set.Ici q)^μ →
        ∀Ho Hnew : HolGerm (ComplexModel (m+1)),
        coordinateGerm e^μ*Ho=actualAnalyticBlowupPullback (Set.Ici q) e b g →
        coordinateGerm q^μ*Hnew=actualAnalyticBlowupPullback (Set.Ici q) q (fun _=>0)
          (actualPermutationGermEquiv (normalPivotEquiv q f)
            (actualAnalyticDirectionShearGermEquiv (Set.Ici q) f
              (fun i=>actualNormalMarkedDirection (Set.Ici q) e b i /
                actualNormalMarkedDirection (Set.Ici q) e b f) g)) →
        C Ho=u^μ*Hnew) ∧
      ∀I : Ideal (HolGerm (ComplexModel (m+1))),
        Ideal.map C.toRingEquiv.toRingHom (actualAnalyticNormalizedMemberIdeal I (Set.Ici q) e b)=
          actualAnalyticNormalizedMemberIdeal (actualAnalyticNormalAdaptedSourceIdeal I q e f b)
            (Set.Ici q) q (fun _=>0) := by
  let A:=Set.Ici q
  let v:=actualNormalMarkedDirection A e b
  let w:=actualNormalChartNormalizedDirection f v
  let p:=normalPivotEquiv q f
  let P:=actualPermutationGermEquiv p
  let S:=actualAnalyticDirectionShearGermEquiv A f w
  have hve : v e=1:=by simp [v,actualNormalMarkedDirection]
  obtain ⟨E,_hCoord,_hTaylor,hUnit,hMember,hNorm⟩:=
    exists_actual_analytic_normal_target_transport A e f hqe hqf v hve hvf
  let C:=E.symm.trans P
  let u:=P (E.symm (actualTargetPivotGerm e f v))
  refine ⟨C,u,?_,?_,?_⟩
  · exact (hUnit.map E.symm.toRingEquiv.toRingHom).map P.toRingEquiv.toRingHom
  · intro μ g hg Ho Hnew hHo hHnew
    obtain ⟨Hf,hHf,_hTaylorF⟩:=exists_actualAnalyticBlowup_quotient A f hqf w μ g hg
    have hHoV : coordinateGerm e^μ*Ho=actualAnalyticBlowupPullback A e v g := by
      rw [hHo,actual_pullback_eq_normal_direction A e b]
    have hCov:=hMember μ g hg Hf Ho hHf hHoV
    have h:=congrArg (fun H=>P (E.symm H)) hCov
    simp only [map_mul,map_pow,AlgEquiv.symm_apply_apply] at h
    have hSame:=same_quotient_after_source_adaptation q f hqf w μ g Hf Hnew hHf hHnew
    exact h.symm.trans (congrArg (fun H=>u^μ*H) hSame)
  · intro I
    have hNb : actualAnalyticNormalizedMemberIdeal I A e b=
        actualAnalyticNormalizedMemberIdeal I A e v := by
      simp only [actualAnalyticNormalizedMemberIdeal,actual_pullback_eq_normal_direction A e b]
      rfl
    have hInv : Ideal.map E.symm.toRingEquiv.toRingHom (actualAnalyticNormalizedMemberIdeal I A e b)=
        actualAnalyticNormalizedMemberIdeal I A f w := by
      rw [hNb]
      exact inverse_map_of_map_eq E _ _ (hNorm I)
    have hPerm:=analytic_normalized_ideal_coordinate_permutation p (Ideal.map S.toRingEquiv.toRingHom I)
      A f (fun _=>0)
    have hImage : p '' A=A:=normal_pivot_tail_image q f hqf
    have hpf : p f=q:=normalPivotEquiv_pivot q f hqf
    rw [hImage,hpf,coordinateEquiv_eq_actualPermutation] at hPerm
    have hS : actualAnalyticNormalizedMemberIdeal I A f w=
        actualAnalyticNormalizedMemberIdeal (Ideal.map S.toRingEquiv.toRingHom I) A f (fun _=>0) :=
      analytic_normalized_ideal_source_shear I A f hqf w
    have hMap : C.toRingEquiv.toRingHom=P.toRingEquiv.toRingHom.comp E.symm.toRingEquiv.toRingHom:=rfl
    rw [hMap,←Ideal.map_map,hInv,hS]
    exact hPerm

private theorem cast_vertex_val {m : ℕ} {V W : Finset (Fin m →₀ ℕ)} (h : V=W) (a : V) :
    (sourceVertexSetCast h a).val=a.val := by cases h;rfl

section CurrentLabels
variable {I : Ideal (HolGerm (ComplexModel (n+1)))}
 {G : ActualAnalyticInheritedFamily (n+1) 0 (analyticZeroTaylorIdeal (n+1) I)}
 {q e f : Fin (n+1)} {b : Fin (n+1) → ℂ}
 {S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I))}

/-- Explicit bijection from the OLD labels to the internally produced
CURRENT labels; no independent target relabelling is chosen. -/
def actualAdaptedOriginalLabelEquiv (D : ActualAdaptedCurrentSelectorData I G q e f b S) :
    actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I) ≃
      actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1)
        (sameAnalyticZeroNormalizedIdeal (n+1) _ D.sourceFamily q D.sourcePower)) :=
  D.sourceVertexEquiv.trans (sourceVertexSetCast D.targetVertexSet)

theorem actualAdaptedOriginalLabelEquiv_degree
    (D : ActualAdaptedCurrentSelectorData I G q e f b S)
    (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)) :
    normalExponentDegree (actualAdaptedOriginalLabelEquiv D a).val=normalExponentDegree a.val := by
  change normalExponentDegree (sourceVertexSetCast D.targetVertexSet (D.sourceVertexEquiv a)).val=_
  rw [cast_vertex_val,D.sourceLabels]
  exact sourceExponentPermutation_degree (normalPivotEquiv q f) a.val
end CurrentLabels

/-- ONE common actual unit transports every literal OLD normalized member
to the exact internally PRODUCED current monic family at its UNCHANGED mark,
while the SAME target equivalence identifies the WHOLE normalized ideal. -/
theorem exists_actual_same_current_family_common_unit_transport
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
      ∃C : HolGerm (ComplexModel (n+1))≃ₐ[ℂ]HolGerm (ComplexModel (n+1)),
      ∃u : HolGerm (ComplexModel (n+1)),IsUnit u ∧
      ∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
      Ideal.map C.toRingEquiv.toRingHom (actualAnalyticNormalizedMemberIdeal I (Set.Ici q) e b)=
        sameAnalyticZeroNormalizedIdeal (n+1) _ D.sourceFamily q D.sourcePower ∧
      ∀a,C (sameAnalyticNormalNormalizedVertex (n+1) I G q e hqe b hp a)=
        u^normalExponentDegree a.val*D.targetFamily.germs (actualAdaptedOriginalLabelEquiv D a) := by
  obtain ⟨f,hqf,hvf,⟨D⟩⟩:=exists_actual_analytic_adapted_current_family_and_selector
    I G hmem q e hqe b hp hOrder hred S hContact
  obtain ⟨C,u,hu,hCov,hNorm⟩:=exists_actual_original_to_adapted_marked_transport q e f hqe hqf b hvf
  have hDegree (a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)) :
      normalExponentDegree (D.sourceVertexEquiv a).val=normalExponentDegree a.val := by
    rw [D.sourceLabels]
    exact sourceExponentPermutation_degree (normalPivotEquiv q f) a.val
  refine ⟨f,hqf,hvf,C,u,hu,D,?_,?_⟩
  · exact (hNorm I).trans (actualAnalyticNormalizedMemberIdeal_eq_same_zero_span
      (n+1) _ D.sourceFamily D.sourceMember q D.sourcePower)
  · intro a
    apply hCov (normalExponentDegree a.val) (G.germs a) (hp a)
    · exact sameAnalyticNormalNormalizedVertex_product (n+1) I G q e hqe b hp a
    · change coordinateGerm q^normalExponentDegree a.val*
        D.targetFamily.germs (sourceVertexSetCast D.targetVertexSet (D.sourceVertexEquiv a))=_
      rw [D.targetLiterals]
      have h:=sameAnalyticZeroNormalizedVertex_product (n+1) _ D.sourceFamily q D.sourcePower (D.sourceVertexEquiv a)
      rw [hDegree,D.sourceLiterals] at h
      exact h

/-- A single common unit at the original literal marks cancels in the
ENTIRE weighted compressed ideal. No positive-weight premise is needed. -/
theorem map_weightedCompression_of_common_unit
    {R T : Type*} [CommRing R] [CommRing T] {ι : Type*} [Fintype ι]
    (F : R →+* T) (w : ι → ℕ) (c : ι → R) (g : ι → T) (u : T) (hu : IsUnit u)
    (hCov : ∀i,F (c i)=u^(w i)*g i) :
    Ideal.map F (weightedCompression w c)=weightedCompression w g := by
  unfold weightedCompression
  rw [Ideal.map_span]
  have hSet : F '' range (fun i=>c i^(weightedCommonMark w/w i))=
      range (fun i=>u^weightedCommonMark w*g i^(weightedCommonMark w/w i)) := by
    rw [←range_comp]
    congr 1
    funext i
    change F (c i^(weightedCommonMark w/w i))=_
    rw [map_pow,hCov,mul_pow,←pow_mul,weight_mul_compressionExponent]
  rw [hSet]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (Ideal.unit_mul_mem_iff_mem _ (hu.pow (weightedCommonMark w))).mp
      (Ideal.subset_span ⟨i,rfl⟩)

private theorem weightedCompression_reindex
    {R : Type*} [CommRing R] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (E : ι≃κ) (w : κ → ℕ) (g : κ → R) :
    weightedCompression (w ∘ E) (g ∘ E)=weightedCompression w g := by
  have hMark : weightedCommonMark (w ∘ E)=weightedCommonMark w:=
    Fintype.prod_equiv E _ _ (fun _=>rfl)
  unfold weightedCompression
  rw [hMark]
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨E i,rfl⟩
  · rintro ⟨j,rfl⟩
    obtain ⟨i,rfl⟩:=E.surjective j
    exact ⟨i,rfl⟩

/-- Exact old/current common marks and the whole compressed ideal for the
SAME internally produced current family. Neither weights nor coefficients
are replaced by desired target data. -/
theorem exists_actual_current_weighted_compression_transport
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
      ∃C : HolGerm (ComplexModel (n+1))≃ₐ[ℂ]HolGerm (ComplexModel (n+1)),
      ∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
        weightedCommonMark (fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)=>
          normalExponentDegree a.val)=
        weightedCommonMark (fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1)
          (sameAnalyticZeroNormalizedIdeal (n+1) _ D.sourceFamily q D.sourcePower))=>normalExponentDegree a.val) ∧
        Ideal.map C.toRingEquiv.toRingHom
          (weightedCompression (fun a=>normalExponentDegree a.val)
            (sameAnalyticNormalNormalizedVertex (n+1) I G q e hqe b hp))=
          weightedCompression (fun a=>normalExponentDegree a.val) D.targetFamily.germs := by
  obtain ⟨f,hqf,hvf,C,u,hu,D,_hNorm,hCov⟩:=exists_actual_same_current_family_common_unit_transport
    I G hmem q e hqe b hp hOrder hred S hContact
  let E:=actualAdaptedOriginalLabelEquiv D
  have hDegree : (fun a=>normalExponentDegree (E a).val)=(fun a=>normalExponentDegree a.val) :=
    funext fun a=>actualAdaptedOriginalLabelEquiv_degree D a
  have hMark : weightedCommonMark (fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1) I)=>
      normalExponentDegree a.val)=weightedCommonMark
        (fun a : actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (n+1)
          (sameAnalyticZeroNormalizedIdeal (n+1) _ D.sourceFamily q D.sourcePower))=>normalExponentDegree a.val) :=
    Fintype.prod_equiv E _ _ (fun a=>(actualAdaptedOriginalLabelEquiv_degree D a).symm)
  have hMap:=map_weightedCompression_of_common_unit C.toRingEquiv.toRingHom
    (fun a=>normalExponentDegree a.val) (sameAnalyticNormalNormalizedVertex (n+1) I G q e hqe b hp)
    (fun a=>D.targetFamily.germs (E a)) u hu hCov
  have hReindex:=weightedCompression_reindex E (fun a=>normalExponentDegree a.val) D.targetFamily.germs
  change weightedCompression (fun a=>normalExponentDegree (E a).val)
    (fun a=>D.targetFamily.germs (E a))=_ at hReindex
  rw [hDegree] at hReindex
  exact ⟨f,hqf,hvf,C,D,hMark,hMap.trans hReindex⟩

end
end Hironaka.HironakaActualOriginalAdaptedMarkedTransport
