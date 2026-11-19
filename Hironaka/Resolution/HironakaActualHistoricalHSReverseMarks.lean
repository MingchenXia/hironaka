import Hironaka.Resolution.HironakaActualHistoricalMarkedHSPreservation
import Hironaka.Resolution.HironakaActualHistoricalNormalizedSupport
import Hironaka.Resolution.HironakaActualNormalBlowupExceptionalLocus

/-! Actual bounded prefix complements for the free-pivot reverse HS
criterion. Essential-pivot strict drop is a separate mathematical edge. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalHSReverseMarks
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualCauchyMonomialDivision
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
  HironakaActualHistoricalCentreFilteredDivision HironakaActualHistoricalFormalSupportedDivision
  HironakaActualOriginalFormalHSTransfer HironakaActualCoefficientPresentationCentrePower
  HironakaActualHistoricalNormalizedLeadingFrames HironakaActualHistoricalNormalizedSupport
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualAnalyticBlowupTaylor HironakaActualNormalBlowupExceptionalLocus
  HironakaRelativeNormalDeformationInitialRelations HironakaActualPointGeometricBennett
  HironakaActualUnshiftedInitialHSTransfer HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicPointJets HironakaHolomorphicJetMonomialSpan

variable {n k : ℕ}

private theorem degree_mono {α β : Fin n →₀ ℕ} (h : α≤β) :
    normalExponentDegree α≤normalExponentDegree β:=
  Finset.sum_le_sum fun i _=>h i

private theorem degree_prefix_owner_none
    (w : Fin k → CoordinateWord n) (m : ℕ) (α : Fin n →₀ ℕ)
    (hα : normalExponentDegree α≤m) :
    historicalOwner (historicalDegreePrefixWords w m) α=none ↔ historicalOwner w α=none := by
  constructor
  · intro hPrefix
    apply (historicalOwner_eq_none_iff w α).mpr
    intro a ha hDiv
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha
    have hμ : normalExponentDegree (wordExponent (w i))≤m:=(degree_mono hDiv).trans hα
    let z : {j : Fin k // normalExponentDegree (wordExponent (w j))≤m}:=⟨i,hμ⟩
    let l:=(historicalDegreePrefixLabelEquiv w m).symm z
    have hLabel : historicalDegreePrefixLabel w m l=i:=
      congrArg Subtype.val ((historicalDegreePrefixLabelEquiv w m).apply_symm_apply z)
    have hMem : w i∈List.ofFn (historicalDegreePrefixWords w m):=by
      refine List.mem_ofFn.mpr ⟨l,?_⟩
      change w (historicalDegreePrefixLabel w m l)=w i
      rw [hLabel]
    exact (historicalOwner_eq_none_iff _ α).mp hPrefix (w i) hMem hDiv
  · intro hFull
    apply (historicalOwner_eq_none_iff _ α).mpr
    intro a ha hDiv
    obtain ⟨i,rfl⟩:=List.mem_ofFn.mp ha
    exact (historicalOwner_eq_none_iff w α).mp hFull _
      (List.mem_ofFn.mpr ⟨historicalDegreePrefixLabel w m i,rfl⟩) hDiv

/-- The ACTUAL entire bounded old complement is unchanged by retaining
exactly the original degree prefix, with its genuine label equivalence. -/
theorem historical_degree_prefix_complement_eq (w : Fin k → CoordinateWord n) (m : ℕ) :
    historicalComplementJetSpace w (m+1)=
      historicalComplementJetSpace (historicalDegreePrefixWords w m) (m+1) := by
  ext v
  change (∀α : normalExponentIndex n (m+1),historicalOwner w α.val≠none → v α=0) ↔
    (∀α : normalExponentIndex n (m+1),
      historicalOwner (historicalDegreePrefixWords w m) α.val≠none → v α=0)
  constructor
  · intro hv α hOwner
    apply hv α
    intro hNone
    exact hOwner ((degree_prefix_owner_none w m α.val (by have h:=α.property;omega)).mpr hNone)
  · intro hv α hOwner
    apply hv α
    intro hNone
    exact hOwner ((degree_prefix_owner_none w m α.val (by have h:=α.property;omega)).mp hNone)

private def complement_target_map
    {l : ℕ} (v : Fin l → CoordinateWord n) (h : Fin l → MvPowerSeries (Fin n) ℂ)
    (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (hK : Ideal.span (range h)≤K) (q : ℕ) :
    historicalComplementJetSpace v q →ₗ[ℂ]
      (MvPowerSeries (Fin n) ℂ ⧸ (K⊔genuineFormalVariables n^q)) :=
  (Ideal.Quotient.factorₐ ℂ (sup_le_sup hK le_rfl)).toLinearMap.comp
    (historicalComplementQuotientMap v h q)

private theorem bounded_coefficient_zero_of_equal_hs
    (w : Fin k → CoordinateWord n) (g H : Fin k → MvPowerSeries (Fin n) ℂ)
    (hg : ∀i,g i∈genuineFormalVariables n^normalExponentDegree (wordExponent (w i)))
    (hWholeG : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupportedG : HistoricalWholeSupportedDivision w g)
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (hIn : ∀i,H i∈K)
    (hHS : ∀ℓ,genuineFormalHilbertSamuelValue n K ℓ=
      genuineFormalHilbertSamuelValue n (Ideal.span (range g)) ℓ)
    (j : Fin k) (α : Fin n →₀ ℕ)
    (hPrefixMarks : ∀i,H (historicalDegreePrefixLabel w (normalExponentDegree α) i)∈
      genuineFormalVariables n^normalExponentDegree
        (wordExponent (historicalDegreePrefixWords w (normalExponentDegree α) i)))
    (hPrefixWhole : ∀q,Function.Bijective (historicalWholeJetMap
      (historicalDegreePrefixWords w (normalExponentDegree α))
      (fun i=>H (historicalDegreePrefixLabel w (normalExponentDegree α) i)) q))
    (hHigherCones : ∀i,normalExponentDegree (wordExponent (w i))≤normalExponentDegree α →
      ∀β,wordExponent (w i)≤β → MvPowerSeries.coeff β (H j)=0) :
    MvPowerSeries.coeff α (H j)=0 := by
  let m:=normalExponentDegree α
  let q:=m+1
  let v:=historicalDegreePrefixWords w m
  let p:=historicalDegreePrefixLabel w m
  let h:=fun i=>H (p i)
  let :=normalExponentFintype n q
  let EG:=LinearEquiv.ofBijective (historicalComplementQuotientMap w g q)
    ⟨historicalComplementQuotientMap_injective w g hg hWholeG hSupportedG q,
      historicalComplementQuotientMap_surjective w g hg hWholeG q⟩
  have hSourceDim : Module.finrank ℂ (historicalComplementJetSpace v q)=
      genuineFormalHilbertSamuelValue n (Ideal.span (range g)) m := by
    change Module.finrank ℂ (historicalComplementJetSpace (historicalDegreePrefixWords w m) (m+1))=_
    rw [←historical_degree_prefix_complement_eq w m]
    exact EG.finrank_eq
  have hK : Ideal.span (range h)≤K := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact hIn (p i)
  let M:=complement_target_map v h K hK q
  have hSurj : Function.Surjective M :=
    (Ideal.Quotient.factor_surjective (sup_le_sup hK (le_refl (genuineFormalVariables n^q)))).comp
      (historicalComplementQuotientMap_surjective v h hPrefixMarks hPrefixWhole q)
  let : FiniteDimensional ℂ (MvPowerSeries (Fin n) ℂ ⧸ (K⊔genuineFormalVariables n^q)):=
    FiniteDimensional.of_surjective M hSurj
  have hDim : Module.finrank ℂ (historicalComplementJetSpace v q)=
      Module.finrank ℂ (MvPowerSeries (Fin n) ℂ ⧸ (K⊔genuineFormalVariables n^q)):=
    hSourceDim.trans (hHS m).symm
  have hInj : Function.Injective M:=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hDim).mpr hSurj
  let c : historicalComplementJetSpace v q:=⟨boundedCoefficients q (H j),by
    intro β hOwner
    change MvPowerSeries.coeff β.val (H j)=0
    cases ho : historicalOwner v β.val with
    | none => exact (hOwner ho).elim
    | some i =>
      exact hHigherCones (p i) (historicalDegreePrefixLabel_mem w m i) β.val
        ((historicalOwner_eq_some_iff v β.val i).mp ho).1⟩
  have hZero : M c=0 := by
    change Ideal.Quotient.mk (K⊔genuineFormalVariables n^q) (boundedSeries q c.val)=0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hRem : H j-boundedSeries q c.val∈genuineFormalVariables n^q:=
      sub_boundedSeries_mem_power q (H j)
    have hm:=Ideal.sub_mem (K⊔genuineFormalVariables n^q)
      (Ideal.mem_sup_left (hIn j)) (Ideal.mem_sup_right hRem)
    simpa only [sub_sub_cancel] using hm
  have hc : c=0:=hInj (hZero.trans (map_zero M).symm)
  exact congrArg (fun z : historicalComplementJetSpace v q=>
    z.val (⟨α,Nat.lt_succ_self _⟩ : normalExponentIndex n q)) hc

/-- ENTIRE actual target HS equality forces every SAME normalized member's
original mark. Target prefix frames and all lower marked orders are
internally derived by joint degree induction, not supplied certificates.
Only STRICTLY lower-degree heads must be free of the pivot. -/
theorem actual_normalized_marks_up_to_of_equal_hs
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hg : ∀i,g i∈genuineFormalVariables n^normalExponentDegree (wordExponent (w i)))
    (hWholeG : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupportedG : HistoricalWholeSupportedDivision w g)
    (hPrefixFrames : ∀m,HistoricalDegreePrefixFrames w g m)
    (hProperCones : ∀j i,normalExponentDegree (wordExponent (w i))<normalExponentDegree (wordExponent (w j)) →
      ∀β,wordExponent (w i)≤β → MvPowerSeries.coeff β (g j)=0)
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (R : ℕ)
    (hHeads : ∀i : Fin k,normalExponentDegree (wordExponent (w i))<R →
      (↑(wordExponent (w i)).support : Set (Fin n))⊆A\{e})
    (hcentre : ∀i,g i∈actualFormalCoordinateIdeal n A^normalExponentDegree (wordExponent (w i)))
    (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (hIn : ∀i,actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w i))) (g i) (hcentre i)∈K)
    (hHS : ∀ℓ,genuineFormalHilbertSamuelValue n K ℓ=
      genuineFormalHilbertSamuelValue n (Ideal.span (range g)) ℓ) :
    ∀i,normalExponentDegree (wordExponent (w i))≤R → actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w i))) (g i) (hcentre i)∈
        genuineFormalVariables n^normalExponentDegree (wordExponent (w i)) := by
  let μ:=fun i=>normalExponentDegree (wordExponent (w i))
  let H:=fun i=>actualNormalizedFormalMember A e he b (μ i) (g i) (hcentre i)
  have hHeadZero (j : Fin k) (hj : μ j<R) (i : Fin n) (hi : i∉A\{e}) : wordExponent (w j) i=0:=by
    by_contra hz
    exact hi (hHeads j hj (Finsupp.mem_support_iff.mpr hz))
  have hOrders (r : ℕ) : r≤R → ∀j : Fin k,μ j=r → H j∈genuineFormalVariables n^μ j := by
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro hr j hj
      apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n (μ j) (H j)).mpr
      intro α hα
      let m:=normalExponentDegree α
      let v:=historicalDegreePrefixWords w m
      let p:=historicalDegreePrefixLabel w m
      have hLowerMarked (i : Fin (historicalDegreePrefixCount w m)) :
          H (p i)∈genuineFormalVariables n^normalExponentDegree (wordExponent (v i)) := by
        have hμ : μ (p i)≤m:=historicalDegreePrefixLabel_mem w m i
        have hl : μ (p i)<r:=by change m<μ j at hα;omega
        exact ih (μ (p i)) hl ((le_of_lt hl).trans hr) (p i) rfl
      have hLowerWhole (q : ℕ) : Function.Bijective (historicalWholeJetMap v (fun i=>H (p i)) q) := by
        apply historicalWholeJetMap_bijective_of_pure_leading_agreement v
          (fun i=>g (p i)) (fun i=>H (p i)) (fun i=>hg (p i)) hLowerMarked
          (A\{e}) (fun i=>hHeadZero (p i) (by
            have hμ : μ (p i)≤m:=historicalDegreePrefixLabel_mem w m i
            change m<μ j at hα
            omega)) ?_ q ((hPrefixFrames m).1 q)
        intro i β hDegree hPure
        have hβ : (↑β.support : Set (Fin n))⊆A\{e}:=by
          intro x hx
          by_contra hxb
          exact (Finsupp.mem_support_iff.mp hx) (hPure x hxb)
        exact actual_normalized_pure_top_coefficient A e he b (μ (p i)) (g (p i))
          (hcentre (p i)) β hβ hDegree
      have hHigherCones (i : Fin k) (hi : μ i≤m) :
          ∀β,wordExponent (w i)≤β → MvPowerSeries.coeff β (H j)=0:=by
        exact actualNormalizedFormalMember_cone_zero_all_orders A e he b
          (wordExponent (w i)) (hHeads i (by change μ i<R;change m<μ j at hα;omega))
          (μ j) (g j) (hcentre j)
          (hProperCones j i (by change μ i<μ j;exact lt_of_le_of_lt hi hα))
      exact bounded_coefficient_zero_of_equal_hs w g H hg hWholeG hSupportedG K hIn hHS j α
        hLowerMarked hLowerWhole hHigherCones
  intro i hi
  exact hOrders (μ i) hi i rfl

/-- Full free-pivot reverse criterion: the bounded degree induction is
applied at each actual member's own original mark. -/
theorem actual_normalized_marks_of_equal_hs
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hg : ∀i,g i∈genuineFormalVariables n^normalExponentDegree (wordExponent (w i)))
    (hWholeG : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupportedG : HistoricalWholeSupportedDivision w g)
    (hPrefixFrames : ∀m,HistoricalDegreePrefixFrames w g m)
    (hProperCones : ∀j i,normalExponentDegree (wordExponent (w i))<normalExponentDegree (wordExponent (w j)) →
      ∀β,wordExponent (w i)≤β → MvPowerSeries.coeff β (g j)=0)
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hHeads : ∀i : Fin k,(↑(wordExponent (w i)).support : Set (Fin n))⊆A\{e})
    (hcentre : ∀i,g i∈actualFormalCoordinateIdeal n A^normalExponentDegree (wordExponent (w i)))
    (K : Ideal (MvPowerSeries (Fin n) ℂ))
    (hIn : ∀i,actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w i))) (g i) (hcentre i)∈K)
    (hHS : ∀ℓ,genuineFormalHilbertSamuelValue n K ℓ=
      genuineFormalHilbertSamuelValue n (Ideal.span (range g)) ℓ) :
    ∀i,actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w i))) (g i) (hcentre i)∈
        genuineFormalVariables n^normalExponentDegree (wordExponent (w i)) := by
  intro i
  exact actual_normalized_marks_up_to_of_equal_hs w g hg hWholeG hSupportedG hPrefixFrames hProperCones
    A e he b (normalExponentDegree (wordExponent (w i))) (fun j _=>hHeads j) hcentre K hIn hHS i le_rfl

/-- TRUE geometric HS persistence forces the original marks through a
chosen bound. Only STRICTLY lower-degree heads avoid the pivot, and the
SAME actual quotient is retained without moving monicity. -/
theorem same_historical_normalized_orders_up_to_of_geometric_hs_eq
    (d t : ℕ) (ht : 2≤t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (R : ℕ)
    (W : Set (ComplexModel (d+t)))
    (w : Fin k → CoordinateWord (d+t)) (Γ : Fin k → HolGerm (ComplexModel (d+t)))
    (hspan : Ideal.span (range Γ)=originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) W))
    (hmarked : ∀i,actualUnshiftedTaylorAlgHom (d+t) (Γ i)∈
      genuineFormalVariables (d+t)^normalExponentDegree (wordExponent (w i)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w
      (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)) q))
    (hSupported : HistoricalWholeSupportedDivision w (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)))
    (hPrefixFrames : ∀m,HistoricalDegreePrefixFrames w (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)) m)
    (hProperCones : ∀l i,normalExponentDegree (wordExponent (w i))<normalExponentDegree (wordExponent (w l)) →
      ∀β,wordExponent (w i)≤β → MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (Γ l))=0)
    (hHeads : ∀i : Fin k,normalExponentDegree (wordExponent (w i))<R →
      (↑(wordExponent (w i)).support : Set (Fin (d+t)))⊆actualTangentCentreVariables d t\{j.natAdd d})
    (hCentre : ∀i,Γ i∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^
      normalExponentDegree (wordExponent (w i)))
    (hHS : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+t) (strictTransform (d+t)
      (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=d+t) W) 0 ℓ) :
    ∀i,normalExponentDegree (wordExponent (w i))≤R → ∀H : HolGerm (ComplexModel (d+t)),
      (coordinateGerm (j.natAdd d))^normalExponentDegree (wordExponent (w i))*H=
        actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (Γ i) →
      H∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^
        normalExponentDegree (wordExponent (w i)) := by
  let A:=actualTangentCentreVariables d t
  let e:=j.natAdd d
  have he : e∈A:=⟨j,rfl⟩
  let μ:=fun i=>normalExponentDegree (wordExponent (w i))
  let g:=fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)
  have hp (i) : g i∈actualFormalCoordinateIdeal (d+t) A^μ i:=
    actualTaylor_mem_coordinateCentre_pow A (μ i) (Γ i) (hCentre i)
  choose N hProduct hTaylor using fun i=>exists_actualAnalyticBlowup_quotient A e he b (μ i) (Γ i) (hCentre i)
  let J:=originalCoherentOriginIdeal (vanishingIdeal (n:=d+t)
    (strictTransform (d+t) (actualAnalyticBlowupMap A e b) W))
  have hNmem (i : Fin k) : N i∈J := by
    apply actual_normal_normalized_ideal_le_geometric_strict_vanishing d t ht j b W
    apply Ideal.subset_span
    refine ⟨μ i,Γ i,?_,hCentre i,hProduct i⟩
    rw [←hspan]
    exact Ideal.subset_span ⟨i,rfl⟩
  let K:=Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom J
  have hIn (i) : actualNormalizedFormalMember A e he b (μ i) (g i) (hp i)∈K := by
    have hm:=Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom (d+t)).toRingHom (hNmem i)
    change actualUnshiftedTaylorAlgHom (d+t) (N i)∈K at hm
    rwa [hTaylor i] at hm
  have hSourceMap : Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom
      (originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) W))=Ideal.span (range g) := by
    rw [←hspan,Ideal.map_span,←range_comp]
    rfl
  have hFormalHS (ℓ : ℕ) : genuineFormalHilbertSamuelValue (d+t) K ℓ=
      genuineFormalHilbertSamuelValue (d+t) (Ideal.span (range g)) ℓ := by
    calc
      _=hilbertSamuelValue J ℓ:=(hilbertSamuelValue_eq_actual_unshifted_formal_extension (d+t) J ℓ).symm
      _=hilbertSamuelAt (vanishingIdeal (n:=d+t) (strictTransform (d+t)
          (actualAnalyticBlowupMap A e b) W)) 0 ℓ:=(hilbertSamuelAt_model_zero _ ℓ).symm
      _=hilbertSamuelAt (vanishingIdeal (n:=d+t) W) 0 ℓ:=hHS ℓ
      _=hilbertSamuelValue (originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) W)) ℓ:=
        hilbertSamuelAt_model_zero _ ℓ
      _=genuineFormalHilbertSamuelValue (d+t)
          (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom
            (originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) W))) ℓ:=
        hilbertSamuelValue_eq_actual_unshifted_formal_extension (d+t) _ ℓ
      _=_:=by rw [hSourceMap]
  have hOrders:=actual_normalized_marks_up_to_of_equal_hs w g hmarked hwhole hSupported hPrefixFrames
    hProperCones A e he b R hHeads hp K hIn hFormalHS
  have hNorders (i) (hi : μ i≤R) : N i∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^μ i := by
    apply (actual_maximal_power_iff_formal_coefficients_zero (d+t) (μ i) (N i)).mpr
    rw [hTaylor i]
    exact (mem_genuineFormalVariables_pow_iff_coefficients_zero (d+t) (μ i) _).mp (hOrders i hi)
  intro i hi H hProd
  have hSame : N i=H:=mul_left_cancel₀
    (pow_ne_zero (μ i) (HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e))
    ((hProduct i).trans hProd.symm)
  exact hSame ▸ hNorders i hi

/-- Natural full free-pivot endpoint for EVERY actual quotient of the SAME
nonmonic historical family, without reselecting its members or marks. -/
theorem same_historical_normalized_orders_of_geometric_hs_eq
    (d t : ℕ) (ht : 2≤t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t)))
    (w : Fin k → CoordinateWord (d+t)) (Γ : Fin k → HolGerm (ComplexModel (d+t)))
    (hspan : Ideal.span (range Γ)=originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) W))
    (hmarked : ∀i,actualUnshiftedTaylorAlgHom (d+t) (Γ i)∈
      genuineFormalVariables (d+t)^normalExponentDegree (wordExponent (w i)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w
      (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)) q))
    (hSupported : HistoricalWholeSupportedDivision w (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)))
    (hPrefixFrames : ∀m,HistoricalDegreePrefixFrames w (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ i)) m)
    (hProperCones : ∀l i,normalExponentDegree (wordExponent (w i))<normalExponentDegree (wordExponent (w l)) →
      ∀β,wordExponent (w i)≤β → MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t) (Γ l))=0)
    (hHeads : ∀i : Fin k,(↑(wordExponent (w i)).support : Set (Fin (d+t)))⊆
      actualTangentCentreVariables d t\{j.natAdd d})
    (hCentre : ∀i,Γ i∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^
      normalExponentDegree (wordExponent (w i)))
    (hHS : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+t) (strictTransform (d+t)
      (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=d+t) W) 0 ℓ) :
    ∀i (H : HolGerm (ComplexModel (d+t))),
      (coordinateGerm (j.natAdd d))^normalExponentDegree (wordExponent (w i))*H=
        actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (Γ i) →
      H∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^
        normalExponentDegree (wordExponent (w i)) := by
  intro i H hProd
  exact same_historical_normalized_orders_up_to_of_geometric_hs_eq d t ht j b
    (normalExponentDegree (wordExponent (w i))) W w Γ hspan hmarked hwhole hSupported
    hPrefixFrames hProperCones (fun l _=>hHeads l) hCentre hHS i le_rfl H hProd

end
end Hironaka.HironakaActualHistoricalHSReverseMarks
