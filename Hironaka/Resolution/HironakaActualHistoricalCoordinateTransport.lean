import Hironaka.Resolution.HironakaActualGeometricMarkedSquare

/-! The SAME rational analytic target transition and SAME unit transport
literal marked members and the entire zero-direction coordinate flags. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualHistoricalCoordinateTransport
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
 HironakaActualAnalyticNormalTargetTransition HironakaActualNormalCentreChartTransition
 HironakaActualAnalyticBlowupTaylor HironakaActualNormalMarkedDirection
 HironakaActualFixedInheritedSelectorPermutation HironakaHolomorphicJetMonomialSpan
 HironakaActualCoefficientPresentationCentrePower
variable {n : ℕ}

private theorem map_coordinate_ideal_of_unit
    (C : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (p : Fin n≃Fin n) (u : HolGerm (ComplexModel n)) (hu : IsUnit u)
    (T : Set (Fin n)) (hCoord : ∀i∈T,C (coordinateGerm i)=u*coordinateGerm (p i)) :
    Ideal.map C.toRingEquiv.toRingHom (actualAnalyticCoordinateIdeal T)=
      actualAnalyticCoordinateIdeal (p '' T) := by
  apply le_antisymm
  · rw [actualAnalyticCoordinateIdeal,Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro g ⟨h,⟨i,hi,rfl⟩,rfl⟩
    change C (coordinateGerm i)∈actualAnalyticCoordinateIdeal (p '' T)
    rw [hCoord i hi]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p i,⟨i,hi,rfl⟩,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro g ⟨j,⟨i,hi,rfl⟩,rfl⟩
    have hm : C (coordinateGerm i)∈Ideal.map C.toRingEquiv.toRingHom (actualAnalyticCoordinateIdeal T) :=
      Ideal.mem_map_of_mem C.toRingEquiv.toRingHom (Ideal.subset_span ⟨i,hi,rfl⟩)
    rw [hCoord i hi] at hm
    exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hm

/-- One actual analytic equivalence and one unit, chosen BEFORE every
source member or coordinate subset, retain both marked quotient covariance
and all whole zero-direction coordinate ideals. -/
theorem exists_actual_marked_transport_with_coordinate_flags
    (A : Set (Fin n)) (e f : Fin n) (heA : e∈A) (hfA : f∈A)
    (p : Fin n≃Fin n) (v : Fin n → ℂ) (he : v e=1) (hf : v f≠0) :
    ∃C : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n),
    ∃u : HolGerm (ComplexModel n),IsUnit u ∧
      (∀(μ : ℕ)(g : HolGerm (ComplexModel n)),g∈actualAnalyticCoordinateIdeal A^μ →
        ∀Hf He : HolGerm (ComplexModel n),
        coordinateGerm f^μ*Hf=actualAnalyticBlowupPullback A f (actualNormalChartNormalizedDirection f v) g →
        coordinateGerm e^μ*He=actualAnalyticBlowupPullback A e v g →
        C He=u^μ*actualPermutationGermEquiv p Hf) ∧
      (∀i,i∈A → i≠e → v i=0 → C (coordinateGerm i)=u*coordinateGerm (p i)) ∧
      ∀T : Set (Fin n),(∀i∈T,i∈A ∧ i≠e ∧ v i=0) →
        Ideal.map C.toRingEquiv.toRingHom (actualAnalyticCoordinateIdeal T)=
          actualAnalyticCoordinateIdeal (p '' T) := by
  obtain ⟨E,hCoord,_hTaylor,hUnit,hMember,_hNorm⟩:=
    exists_actual_analytic_normal_target_transport A e f heA hfA v he hf
  let P:=actualPermutationGermEquiv p
  let C:=E.symm.trans P
  let u:=P (E.symm (actualTargetPivotGerm e f v))
  have hu : IsUnit u:=(hUnit.map E.symm.toRingEquiv.toRingHom).map P.toRingEquiv.toRingHom
  have hC (i : Fin n) (hiA : i∈A) (hie : i≠e) (hvi : v i=0) :
      C (coordinateGerm i)=u*coordinateGerm (p i) := by
    have hif : i≠f:=fun h=>hf (h ▸ hvi)
    have hx : E (coordinateGerm i)*actualTargetPivotGerm e f v=coordinateGerm i := by
      rw [hCoord i]
      simp only [actualTargetCoordinateGerm,if_pos hiA,if_neg hif,
        actualTargetTransverseGerm,if_neg hie,hvi,map_zero,zero_add,zero_div,sub_zero]
      rw [mul_assoc,Ring.inverse_mul_cancel _ hUnit,mul_one]
    have h:=congrArg E.symm hx
    simp only [map_mul,AlgEquiv.symm_apply_apply] at h
    change P (E.symm (coordinateGerm i))=_
    rw [←h,map_mul,actualPermutationGermEquiv_coordinate]
    exact mul_comm _ _
  refine ⟨C,u,hu,?_,hC,?_⟩
  · intro μ g hg Hf He hHf hHe
    have h:=congrArg (fun H=>P (E.symm H)) (hMember μ g hg Hf He hHf hHe)
    simp only [map_mul,map_pow,AlgEquiv.symm_apply_apply] at h
    exact h.symm
  · intro T hT
    exact map_coordinate_ideal_of_unit C p u hu T (fun i hi=>hC i (hT i hi).1 (hT i hi).2.1 (hT i hi).2.2)


open HironakaActualAnalyticFormalNormalPowers HironakaActualTaylorCoordinateNaturality
 HironakaHolomorphicJetChartInvariance HironakaActualRelativeStandardnessNormalPivotPriority
 HironakaActualRelativeStandardnessNormalPointBridge HironakaActualAnalyticDirectionRemovalQuotient
 HironakaActualAnalyticSourceShearTaylor HironakaActualAnalyticAdaptedCurrentSelector
 HironakaActualRelativeNormalJetDivision HironakaActualFormalInitialDiagram
 HironakaActualNormalZeroAnalyticSaturation HironakaActualNormalAllDirectionAnalyticSaturation
 HironakaActualNormalAllDirectionGeometricConverse HironakaActualInheritedNestedContactFlag
 HironakaActualFixedInheritedSelector HironakaRelativeNormalMonomialBasis
 HironakaActualInheritedSourceOwnerPermutation HironakaActualOriginalAdaptedMarkedTransport
 HironakaActualNormalCoordinateReindex HironakaActualInheritedSourcePermutationFamily
 HironakaActualRelativeStandardnessBlockSupport

private theorem coordinateEquiv_eq_actualPermutation (r : Fin n≃Fin n) :
    coordinateGermEquiv r=actualPermutationGermEquiv r := by
  apply AlgEquiv.ext
  intro g
  apply actualUnshiftedTaylorAlgHom_injective n
  have h : actualUnshiftedTaylorAlgHom n (coordinateGermEquiv r g)=
      MvPowerSeries.rename r (actualUnshiftedTaylorAlgHom n g) :=
    DFunLike.congr_fun (actualTaylor_coordinateGermEquiv r) g
  rw [h,actualTaylor_actualPermutationGermEquiv]

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
  have hPerm (g : HolGerm (ComplexModel (m+1))) :
      actualPermutationGermEquiv (normalPivotEquiv q f)
          (actualAnalyticBlowupPullback (Set.Ici q) f (fun _=>0) g)=
        actualAnalyticBlowupPullback (Set.Ici q) q (fun _=>0)
          (actualPermutationGermEquiv (normalPivotEquiv q f) g) := by
    simpa only [coordinateEquiv_eq_actualPermutation,normal_pivot_tail_image q f hqf,
      normalPivotEquiv_pivot q f hqf,Function.comp_def] using
      coordinateGermEquiv_actualAnalyticBlowupPullback (normalPivotEquiv q f) (Set.Ici q) f (fun _=>0) g
  rw [map_mul,map_pow,actualPermutationGermEquiv_coordinate,normalPivotEquiv_pivot q f hqf,hPerm] at h
  apply mul_left_cancel₀ (pow_ne_zero μ (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero q))
  exact h.trans hHnew.symm

/-- Original retained marked orders internally give ONE SAME current family,
unit and equivalence satisfying BOTH member covariance and every old
historical coordinate-block identity. No contact-coordinate transport
certificate is supplied. -/
theorem exists_actual_current_transport_with_historical_coordinate_flags
    {m : ℕ} (I : Ideal (HolGerm (ComplexModel (m+1))))
    (G : ActualAnalyticInheritedFamily (m+1) 0 (analyticZeroTaylorIdeal (m+1) I))
    (hmem : ∀a,G.germs a∈I) (q e : Fin (m+1)) (hqe : q≤e) (b : Fin (m+1) → ℂ)
    (hp : ∀a,G.germs a∈actualAnalyticCoordinateIdeal (Set.Ici q)^normalExponentDegree a.val)
    (hOrder : ∀a,sameAnalyticNormalNormalizedVertex (m+1) I G q e hqe b hp a∈
      IsLocalRing.maximalIdeal (HolGerm (ComplexModel (m+1)))^normalExponentDegree a.val)
    (hred : ∀k,ActualInheritedPrefixReducedAt G k)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (m+1) I)))
    (hContact : ∀k,actualFixedSelectorContactAt S G.germs k) :
    ∃f : Fin (m+1),∃_hqf : q≤f,actualNormalMarkedDirection (Set.Ici q) e b f≠0 ∧
      ∃C : HolGerm (ComplexModel (m+1))≃ₐ[ℂ]HolGerm (ComplexModel (m+1)),
      ∃u : HolGerm (ComplexModel (m+1)),IsUnit u ∧
      ∃D : ActualAdaptedCurrentSelectorData I G q e f b S,
        (∀a,C (sameAnalyticNormalNormalizedVertex (m+1) I G q e hqe b hp a)=
          u^normalExponentDegree a.val*D.targetFamily.germs (actualAdaptedOriginalLabelEquiv D a)) ∧
        (∀i,i∈fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (m+1) I)) →
          C (coordinateGerm i)=u*coordinateGerm (normalPivotEquiv q f i)) ∧
        ∀k,Ideal.map C.toRingEquiv.toRingHom
          (actualAnalyticCoordinateIdeal (fixedSelectorBlock
            (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (m+1) I)) k))=
          actualAnalyticCoordinateIdeal ((normalPivotEquiv q f) '' fixedSelectorBlock
            (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (m+1) I)) k) := by
  obtain ⟨f,hqf,hvf,⟨D⟩⟩:=exists_actual_analytic_adapted_current_family_and_selector
    I G hmem q e hqe b hp hOrder hred S hContact
  let A:=Set.Ici q
  let v:=actualNormalMarkedDirection A e b
  have hve : v e=1:=by simp [v,actualNormalMarkedDirection]
  obtain ⟨C,u,hu,hMember,hCoord,hBlocks⟩:=exists_actual_marked_transport_with_coordinate_flags
    A e f hqe hqf (normalPivotEquiv q f) v hve hvf
  obtain ⟨_hpf,hAll⟩:=actual_normal_marked_orders_preserve_same_historical_selector
    (m+1) I G hmem q e hqe b hp hOrder S hred hContact
  have hLegal (i : Fin (m+1))
      (hi : i∈fixedSelectorEssential (actualInitialVertices MonomialOrder.degLex (analyticZeroTaylorIdeal (m+1) I))) :
      i∈A ∧ i≠e ∧ v i=0 := by
    obtain ⟨a,ha⟩:=hi
    have hiBlock : i∈actualDegreePrefixVariables MonomialOrder.degLex (analyticZeroTaylorIdeal (m+1) I)
      (normalExponentDegree a.val):=⟨a,le_rfl,ha⟩
    have h:=(hAll (normalExponentDegree a.val)).1
    have hie : i≠e:=(h.1 hiBlock).2
    refine ⟨(h.1 hiBlock).1,hie,?_⟩
    simp only [v,actualNormalMarkedDirection,if_neg hie,actualNormalPointDirection,
      h.2 i hiBlock,ite_self]
  refine ⟨f,hqf,hvf,C,u,hu,D,?_,?_,?_⟩
  · intro a
    let μ:=normalExponentDegree a.val
    let w:=actualNormalChartNormalizedDirection f v
    obtain ⟨Hf,hHf,_hTaylor⟩:=exists_actualAnalyticBlowup_quotient A f hqf w μ (G.germs a) (hp a)
    have hHo : coordinateGerm e^μ*sameAnalyticNormalNormalizedVertex (m+1) I G q e hqe b hp a=
        actualAnalyticBlowupPullback A e v (G.germs a) := by
      rw [sameAnalyticNormalNormalizedVertex_product,actual_pullback_eq_normal_direction]
    have hM:=hMember μ (G.germs a) (hp a) Hf
      (sameAnalyticNormalNormalizedVertex (m+1) I G q e hqe b hp a) hHf hHo
    have hDegree : normalExponentDegree (D.sourceVertexEquiv a).val=μ := by
      rw [D.sourceLabels]
      exact sourceExponentPermutation_degree (normalPivotEquiv q f) a.val
    have hNew : coordinateGerm q^μ*D.targetFamily.germs (actualAdaptedOriginalLabelEquiv D a)=
        actualAnalyticBlowupPullback A q (fun _=>0)
          (actualPermutationGermEquiv (normalPivotEquiv q f)
            (actualAnalyticDirectionShearGermEquiv A f w (G.germs a))) := by
      change coordinateGerm q^μ*
        D.targetFamily.germs (sourceVertexSetCast D.targetVertexSet (D.sourceVertexEquiv a))=_
      rw [D.targetLiterals]
      have h:=sameAnalyticZeroNormalizedVertex_product (m+1) _ D.sourceFamily q D.sourcePower (D.sourceVertexEquiv a)
      rw [hDegree,D.sourceLiterals] at h
      exact h
    exact hM.trans (congrArg (fun g=>u^μ*g) (same_quotient_after_source_adaptation q f hqf w μ _ _ _ hHf hNew))
  · intro i hi
    exact hCoord i (hLegal i hi).1 (hLegal i hi).2.1 (hLegal i hi).2.2
  · intro k
    apply hBlocks
    intro i hi
    obtain ⟨a,_ha,hai⟩:=hi
    exact hLegal i ⟨a,hai⟩


/-- The entire coordinate germ law spreads on ONE actual neighborhood
simultaneously for ALL subsets of the finite essential set. Any genuine
realization of the SAME C and SAME unit may be used, including the actual
marked function square already chosen for the current family. -/
theorem exists_actual_common_coordinate_flag_neighborhood
    (C : HolGerm (ComplexModel n)≃ₐ[ℂ]HolGerm (ComplexModel n))
    (p : Fin n≃Fin n) (u : HolGerm (ComplexModel n)) (hu : IsUnit u)
    (L : Set (Fin n)) (hCoord : ∀i∈L,C (coordinateGerm i)=u*coordinateGerm (p i))
    (Φ : LocalHolomorphicEquivAt (n:=n) (0 : ComplexModel n))
    (hΦ0 : Φ.toFun 0=0) (hΦC : localGermAlgEquiv Φ hΦ0=C)
    (v : ComplexModel n → ℂ) (hv : ∀ᶠz in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ v z)
    (hGu : u=HolGerm.mk v hv) :
    ∃U : Set (ComplexModel n),IsOpen U ∧ (0 : ComplexModel n)∈U ∧ U⊆Φ.source ∧
      DifferentiableOn ℂ v U ∧ (∀z∈U,v z≠0) ∧
      (∀i∈L,∀z∈U,Φ.toFun z i=v z*z (p i)) ∧
      ∀T : Set (Fin n),T⊆L → ∀z∈U,
        (∀i∈T,Φ.toFun z i=0) ↔ ∀j∈p '' T,z j=0 := by
  have hv0 : v 0≠0 := by
    have h:HolGerm.eval u≠0:=(HolGerm.isUnit_iff_eval_ne_zero u).mp hu
    simpa only [hGu,HolGerm.eval_mk] using h
  have hEq (i : Fin n) (hi : i∈L) :
      ∀ᶠz in 𝓝 (0 : ComplexModel n),Φ.toFun z i=v z*z (p i) := by
    have h:=hCoord i hi
    rw [←hΦC] at h
    unfold coordinateGerm at h
    rw [localGermAlgEquiv_mk,hGu,←HolGerm.mk_mul] at h
    exact HolGerm.mk_eq_mk_iff.mp h
  have hAll : ∀ᶠz in 𝓝 (0 : ComplexModel n),∀i,i∈L → Φ.toFun z i=v z*z (p i) :=
    eventually_all.mpr fun i=>by
      by_cases hi : i∈L
      · exact (hEq i hi).mono fun _ hz _=>hz
      · exact Eventually.of_forall fun _ hz=>(hi hz).elim
  have hNear : ∀ᶠz in 𝓝 (0 : ComplexModel n),
      (∀i,i∈L → Φ.toFun z i=v z*z (p i)) ∧ DifferentiableAt ℂ v z ∧ v z≠0 ∧ z∈Φ.source := by
    filter_upwards [hAll,hv,hv.self_of_nhds.continuousAt.eventually_ne hv0,
      Φ.isOpen_source.mem_nhds Φ.center_mem_source] with z heq hhol hne hs
    exact ⟨heq,hhol,hne,hs⟩
  obtain ⟨U,hUS,hU,h0U⟩:=mem_nhds_iff.mp hNear
  refine ⟨U,hU,h0U,fun _ hz=>(hUS hz).2.2.2,
    fun z hz=>(hUS hz).2.1.differentiableWithinAt,fun _ hz=>(hUS hz).2.2.1,
    fun i hi z hz=>(hUS hz).1 i hi,?_⟩
  intro T hTL z hz
  obtain ⟨heq,_hhol,hne,_hs⟩:=hUS hz
  constructor
  · intro h j hj
    obtain ⟨i,hi,rfl⟩:=hj
    have hzero:=h i hi
    rw [heq i (hTL hi)] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left hne
  · intro h i hi
    rw [heq i (hTL hi),h (p i) ⟨i,hi,rfl⟩,mul_zero]

end
end Hironaka.HironakaActualHistoricalCoordinateTransport

