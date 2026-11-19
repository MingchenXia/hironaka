import Hironaka.Resolution.HironakaActualHistoricalNormalizedSelectedContact

/-! All five actual historical point laws for the SAME genuine normalized
family. Whole division and the true geometric ideal are established before
the source and target Hilbert--Samuel functions are compared. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalNormalizedWeakPresentation
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
  HironakaActualHistoricalCentreFilteredDivision HironakaActualHistoricalFormalSupportedDivision
  HironakaActualOriginalFormalHSTransfer HironakaActualCauchyMonomialDivision
  HironakaActualHistoricalNormalizedLeadingFrames HironakaActualHistoricalNormalizedSupport
  HironakaActualFixedInheritedSelector HironakaActualHistoricalMovingPrefixSupport
  HironakaActualHistoricalNormalizedSelectedContact HironakaActualHistoricalEssentialPivotDrop
  HironakaActualHistoricalHSReverseMarks HironakaActualHistoricalMarkedHSPreservation
  HironakaActualHistoricalAnalyticStrictDictionary HironakaActualAnalyticBlowupTaylor
  HironakaActualCoefficientPresentationCentrePower HironakaHolomorphicJetMonomialSpan
  HironakaActualPointGeometricBennett HironakaRelativeNormalDeformationInitialRelations
  HironakaHolomorphicJetChartInvariance
  Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences

variable {n k : ℕ}

/-- A literal head which owns its actual column has its exact original
mark whenever the whole historical jet map is injective. -/
theorem historical_owned_head_exact_order
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hMarked : ∀i,g i∈genuineFormalVariables n^normalExponentDegree (wordExponent (w i)))
    (hWhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (i : Fin k) (hOwn : historicalOwner w (wordExponent (w i))=some i) :
    g i∉genuineFormalVariables n^(normalExponentDegree (wordExponent (w i))+1) := by
  intro hHigh
  let α:=wordExponent (w i)
  let q:=normalExponentDegree α+1
  let F : MvPowerSeries (Fin n) ℂ:=MvPowerSeries.monomial α 1
  have hColumn : historicalReassemble w g F=g i := by
    rw [historicalReassemble_monomial,historicalWholeColumn,hOwn]
    simp only [α,tsub_self,MvPowerSeries.monomial_zero_one,one_mul]
  have hImage : historicalWholeJetMap w g q (boundedCoefficients q F)=0 := by
    rw [historicalWholeJetMap_truncation w g hMarked,hColumn]
    funext β
    exact (mem_genuineFormalVariables_pow_iff_coefficients_zero n q (g i)).mp hHigh β.val β.property
  have hZero : boundedCoefficients q F=0:=(hWhole q).1 (hImage.trans (map_zero _).symm)
  have hAt:=congrFun hZero (⟨α,by dsimp only [q];omega⟩ : normalExponentIndex n q)
  simp [F,boundedCoefficients] at hAt

/-- Every literal source degree-prefix frame survives actual normalization,
with the same labels, from actual marked orders and genuine source powers. -/
theorem actual_normalized_degree_prefix_frames_of_marks
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hMarked : ∀i,g i∈genuineFormalVariables n^normalExponentDegree (wordExponent (w i)))
    (hPrefix : ∀m,HistoricalDegreePrefixFrames w g m)
    (A B : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hHeads : ∀i x,x∉B → wordExponent (w i) x=0) (hBA : B⊆A\{e})
    (hCentre : ∀i,g i∈actualFormalCoordinateIdeal n A^normalExponentDegree (wordExponent (w i)))
    (hTarget : ∀i,actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w i))) (g i) (hCentre i)∈
        genuineFormalVariables n^normalExponentDegree (wordExponent (w i))) :
    ∀m,HistoricalDegreePrefixFrames w (fun i=>actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w i))) (g i) (hCentre i)) m := by
  intro m
  let v:=historicalDegreePrefixWords w m
  let p:=historicalDegreePrefixLabel w m
  let H:=fun i=>actualNormalizedFormalMember A e he b
    (normalExponentDegree (wordExponent (w i))) (g i) (hCentre i)
  have hPrefixMarked (i) : g (p i)∈genuineFormalVariables n^normalExponentDegree (wordExponent (v i)):=hMarked (p i)
  have hPrefixTarget (i) : H (p i)∈genuineFormalVariables n^normalExponentDegree (wordExponent (v i)):=hTarget (p i)
  have hWhole (q : ℕ) : Function.Bijective (historicalWholeJetMap v (fun i=>H (p i)) q) := by
    apply historicalWholeJetMap_bijective_of_pure_leading_agreement v
      (fun i=>g (p i)) (fun i=>H (p i)) hPrefixMarked hPrefixTarget B (fun i=>hHeads (p i)) ?_ q
      ((hPrefix m).1 q)
    intro i α hDegree hPure
    have hSupport : (↑α.support : Set (Fin n))⊆A\{e} := by
      intro x hx
      apply hBA
      by_contra hxB
      exact (Finsupp.mem_support_iff.mp hx) (hPure x hxB)
    exact actual_normalized_pure_top_coefficient A e he b
      (normalExponentDegree (wordExponent (w (p i)))) (g (p i)) (hCentre (p i)) α hSupport hDegree
  refine ⟨hWhole,?_⟩
  intro d
  rw [historicalHomogeneousColumnMap_eq_operator]
  exact historicalHomogeneousOperator_bijective v (fun i=>H (p i)) hPrefixTarget hWhole d

/-- The actual five point laws, with the SAME labels, selector, words and
whole prefix partitions. Ideal equality is recorded separately at the true set. -/
def ActualHistoricalFivePointLaws
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n) (Γ : V → HolGerm (ComplexModel n)) : Prop :=
  (∀i,actualUnshiftedTaylorAlgHom n (Γ (a i))∈genuineFormalVariables n^normalExponentDegree (wordExponent (w i)) ∧
    actualUnshiftedTaylorAlgHom n (Γ (a i))∉genuineFormalVariables n^(normalExponentDegree (wordExponent (w i))+1)) ∧
  (∀q,Function.Bijective (historicalWholeJetMap w (fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i))) q)) ∧
  (∀m,HistoricalDegreePrefixFrames w (fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i))) m) ∧
  HistoricalWholeSupportedDivision w (fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i))) ∧
  (∀R,actualFixedSelectorContactAt S Γ R ∧ (actualFixedSelectorJacobian S Γ R).det≠0) ∧
  HistoricalWholePrefixSupport V (fun v=>actualUnshiftedTaylorAlgHom n (Γ v))

private theorem actual_same_quotient_taylor
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (μ : ℕ) (Γ N : HolGerm (ComplexModel n))
    (hCentre : Γ∈actualAnalyticCoordinateIdeal A^μ)
    (hProduct : (coordinateGerm e)^μ*N=actualAnalyticBlowupPullback A e b Γ) :
    actualUnshiftedTaylorAlgHom n N=actualNormalizedFormalMember A e he b μ
      (actualUnshiftedTaylorAlgHom n Γ) (actualTaylor_mem_coordinateCentre_pow A μ Γ hCentre) := by
  apply actualNormalizedFormalMember_unique
  have h:=congrArg (actualUnshiftedTaylorAlgHom n) hProduct
  rw [map_mul,map_pow,actualUnshiftedTaylor_coordinate] at h
  exact h.trans (DFunLike.congr_fun (actualTaylor_analyticBlowupPullback A e b) Γ)

private theorem prefix_support_proper_cones
    {V : Finset (Fin n →₀ ℕ)} (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val) (g : V → MvPowerSeries (Fin n) ℂ)
    (hPrefix : HistoricalWholePrefixSupport V g) :
    ∀j i,normalExponentDegree (wordExponent (w i))<normalExponentDegree (wordExponent (w j)) →
      ∀β,wordExponent (w i)≤β → MvPowerSeries.coeff β (g (a j))=0 := by
  intro j i hij β hβ
  rw [hw,hw] at hij
  rw [hw] at hβ
  exact hPrefix (normalExponentDegree (a i).val) (a j) hij (a i) le_rfl β hβ

private theorem historical_head_outside_essential
    {V : Finset (Fin n →₀ ℕ)} (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val) :
    ∀i x,x∉fixedSelectorEssential V → wordExponent (w i) x=0 := by
  intro i x hx
  rw [hw]
  by_contra h
  exact hx ⟨a i,h⟩

private theorem historical_essential_subset_centre
    {V : Finset (Fin n →₀ ℕ)} (A : Set (Fin n))
    (hHeads : ∀v : V,(↑v.val.support : Set (Fin n))⊆A) :
    fixedSelectorEssential V⊆A := by
  rintro x ⟨v,hv⟩
  exact hHeads v (Finsupp.mem_support_iff.mpr hv)

/-- TRUE geometric profile equality is equivalent to the actual point marks
of ANY genuine quotients of the SAME original historical member family. -/
theorem actual_geometric_hs_iff_same_quotient_marks
    (d t : ℕ) (ht : 2≤t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t))) (hW : IsComplexAnalyticSubset (n:=d+t) W)
    {V : Finset (Fin (d+t) →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ N : V → HolGerm (ComplexModel (d+t)))
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord (d+t))
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hSpan : Ideal.span (range (fun i=>Γ (a i)))=originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) W))
    (hSource : ActualHistoricalFivePointLaws S a w Γ)
    (hHeads : ∀v : V,(↑v.val.support : Set (Fin (d+t)))⊆actualTangentCentreVariables d t)
    (hCentre : ∀v,Γ v∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^normalExponentDegree v.val)
    (hProduct : ∀v,(coordinateGerm (j.natAdd d))^normalExponentDegree v.val*N v=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (Γ v)) :
    (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+t) (strictTransform (d+t)
      (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=d+t) W) 0 ℓ) ↔
    ∀v : V,actualUnshiftedTaylorAlgHom (d+t) (N v)∈genuineFormalVariables (d+t)^normalExponentDegree v.val := by
  rcases hSource with ⟨hMarked,hWhole,hPrefix,hSupported,hContact,hCones⟩
  let A:=actualTangentCentreVariables d t
  let e:=j.natAdd d
  have he : e∈A:=⟨j,rfl⟩
  have hCentreFin (i : Fin k) : Γ (a i)∈actualAnalyticCoordinateIdeal A^
      normalExponentDegree (wordExponent (w i)) := by
    simpa only [hw] using hCentre (a i)
  have hProductFin (i : Fin k) : (coordinateGerm e)^normalExponentDegree (wordExponent (w i))*N (a i)=
      actualAnalyticBlowupPullback A e b (Γ (a i)) := by
    simpa only [hw] using hProduct (a i)
  have hTaylorFin (i : Fin k) :=actual_same_quotient_taylor A e he b
    (normalExponentDegree (wordExponent (w i))) (Γ (a i)) (N (a i)) (hCentreFin i) (hProductFin i)
  have hProper:=prefix_support_proper_cones a w hw (fun v=>actualUnshiftedTaylorAlgHom (d+t) (Γ v)) hCones
  have hBA:=historical_essential_subset_centre A hHeads
  constructor
  · intro hHS
    have hFree : e∉fixedSelectorEssential V := by
      intro heV
      obtain ⟨ℓ,hℓ⟩:=actual_geometric_essential_pivot_hs_difference d t ht j b W S Γ a w hw hSpan
        (fun i=>(hMarked i).1) hWhole hSupported hPrefix hProper hHeads hCentre
        (fun r=>(hContact r).1) (fun r=>(hContact r).2) heV
      exact hℓ (hHS ℓ)
    have hFreeHeads (i : Fin k) : (↑(wordExponent (w i)).support : Set (Fin (d+t)))⊆A\{e} := by
      intro x hx
      have hxE : x∈fixedSelectorEssential V:=⟨a i,by
        rw [←hw]
        exact Finsupp.mem_support_iff.mp hx⟩
      refine ⟨hBA hxE,?_⟩
      intro hxe
      exact hFree ((Set.mem_singleton_iff.mp hxe) ▸ hxE)
    have hOrders:=same_historical_normalized_orders_of_geometric_hs_eq d t ht j b W w
      (fun i=>Γ (a i)) hSpan (fun i=>(hMarked i).1) hWhole hSupported hPrefix hProper
      hFreeHeads hCentreFin hHS
    intro v
    have hProductV : (coordinateGerm e)^normalExponentDegree (wordExponent (w (a.symm v)))*N v=
        actualAnalyticBlowupPullback A e b (Γ (a (a.symm v))) := by
      simpa only [hw,Equiv.apply_symm_apply] using hProduct v
    have hOrder:=hOrders (a.symm v) (N v) hProductV
    have hOrder' : N v∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (d+t)))^normalExponentDegree v.val:=by
      simpa only [hw,Equiv.apply_symm_apply] using hOrder
    exact (mem_genuineFormalVariables_pow_iff_coefficients_zero (d+t) (normalExponentDegree v.val) _).mpr
      ((actual_maximal_power_iff_formal_coefficients_zero (d+t) (normalExponentDegree v.val) (N v)).mp hOrder')
  · intro hPoint
    have hSelected:=actual_normalized_same_selected_contact_of_marks S Γ N A e he b hHeads hCentre
      hProduct hPoint (fun r=>(hContact r).1) (fun r=>(hContact r).2)
    have hFree:=hSelected.1
    have hBAFree : fixedSelectorEssential V⊆A\{e} := by
      intro x hx
      refine ⟨hBA hx,?_⟩
      intro hxe
      exact hFree ((Set.mem_singleton_iff.mp hxe) ▸ hx)
    have hTarget (i : Fin k) : actualNormalizedFormalMember A e he b
        (normalExponentDegree (wordExponent (w i))) (actualUnshiftedTaylorAlgHom (d+t) (Γ (a i)))
        (actualTaylor_mem_coordinateCentre_pow A _ _ (hCentreFin i))∈
          genuineFormalVariables (d+t)^normalExponentDegree (wordExponent (w i)) := by
      rw [←hTaylorFin i]
      simpa only [hw] using hPoint (a i)
    exact actual_geometric_strict_hilbertSamuel_eq_of_marks d t ht j b W hW w (fun i=>Γ (a i)) hSpan
      (fixedSelectorEssential V) (historical_head_outside_essential a w hw) hBAFree hCentreFin
      (fun i=>(hMarked i).1) hWhole hSupported hTarget

/-- Every TRUE profile-persistent actual point has ALL five SAME historical
laws for ANY genuine quotient family; its ENTIRE strict ideal is generated by
those actual quotients, with original block Jacobians exactly preserved. -/
theorem actual_geometric_same_quotients_five_laws
    (d t : ℕ) (ht : 2≤t) (j : Fin t) (b : Fin (d+t) → ℂ)
    (W : Set (ComplexModel (d+t))) (hW : IsComplexAnalyticSubset (n:=d+t) W)
    {V : Finset (Fin (d+t) →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ N : V → HolGerm (ComplexModel (d+t)))
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord (d+t))
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hOwn : ∀i,historicalOwner w (wordExponent (w i))=some i)
    (hSpan : Ideal.span (range (fun i=>Γ (a i)))=originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) W))
    (hSource : ActualHistoricalFivePointLaws S a w Γ)
    (hHeads : ∀v : V,(↑v.val.support : Set (Fin (d+t)))⊆actualTangentCentreVariables d t)
    (hCentre : ∀v,Γ v∈actualAnalyticCoordinateIdeal (actualTangentCentreVariables d t)^normalExponentDegree v.val)
    (hProduct : ∀v,(coordinateGerm (j.natAdd d))^normalExponentDegree v.val*N v=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (Γ v))
    (hHS : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=d+t) (strictTransform (d+t)
      (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W)) 0 ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=d+t) W) 0 ℓ) :
    ActualHistoricalFivePointLaws S a w N ∧
    (∀R,actualFixedSelectorJacobian S N R=actualFixedSelectorJacobian S Γ R) ∧
    originalCoherentOriginIdeal (vanishingIdeal (n:=d+t) (strictTransform (d+t)
      (actualAnalyticBlowupMap (actualTangentCentreVariables d t) (j.natAdd d) b) W))=
      Ideal.span (range N) := by
  have hPoint:=(actual_geometric_hs_iff_same_quotient_marks d t ht j b W hW S Γ N a w hw hSpan
    hSource hHeads hCentre hProduct).mp hHS
  rcases hSource with ⟨hMarked,hWhole,hPrefix,hSupported,hContact,hCones⟩
  let A:=actualTangentCentreVariables d t
  let e:=j.natAdd d
  have he : e∈A:=⟨j,rfl⟩
  have hCentreFin (i : Fin k) : Γ (a i)∈actualAnalyticCoordinateIdeal A^
      normalExponentDegree (wordExponent (w i)) := by
    simpa only [hw] using hCentre (a i)
  have hProductFin (i : Fin k) : (coordinateGerm e)^normalExponentDegree (wordExponent (w i))*N (a i)=
      actualAnalyticBlowupPullback A e b (Γ (a i)) := by
    simpa only [hw] using hProduct (a i)
  have hTaylorFin (i : Fin k) :=actual_same_quotient_taylor A e he b
    (normalExponentDegree (wordExponent (w i))) (Γ (a i)) (N (a i)) (hCentreFin i) (hProductFin i)
  have hTaylorV (v : V) :=actual_same_quotient_taylor A e he b
    (normalExponentDegree v.val) (Γ v) (N v) (hCentre v) (hProduct v)
  have hSelected:=actual_normalized_same_selected_contact_of_marks S Γ N A e he b hHeads hCentre
    hProduct hPoint (fun r=>(hContact r).1) (fun r=>(hContact r).2)
  have hBA:=historical_essential_subset_centre A hHeads
  have hFree:=hSelected.1
  have hBAFree : fixedSelectorEssential V⊆A\{e} := by
    intro x hx
    refine ⟨hBA hx,?_⟩
    intro hxe
    exact hFree ((Set.mem_singleton_iff.mp hxe) ▸ hx)
  have hTargetMarked (i : Fin k) : actualUnshiftedTaylorAlgHom (d+t) (N (a i))∈
      genuineFormalVariables (d+t)^normalExponentDegree (wordExponent (w i)) := by
    simpa only [hw] using hPoint (a i)
  have hTargetNorm (i : Fin k) : actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w i))) (actualUnshiftedTaylorAlgHom (d+t) (Γ (a i)))
      (actualTaylor_mem_coordinateCentre_pow A _ _ (hCentreFin i))∈
        genuineFormalVariables (d+t)^normalExponentDegree (wordExponent (w i)) := by
    rw [←hTaylorFin i]
    exact hTargetMarked i
  have hFormalCentre (i : Fin k) :=actualTaylor_mem_coordinateCentre_pow A
    (normalExponentDegree (wordExponent (w i))) (Γ (a i)) (hCentreFin i)
  have hTargetDivision:=actual_normalized_whole_supported_division_of_marks w
    (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ (a i))) (fun i=>(hMarked i).1)
    hWhole hSupported A (fixedSelectorEssential V) e he b
    (historical_head_outside_essential a w hw) hBAFree hFormalCentre hTargetNorm
  have hTargetFull : (∀q,Function.Bijective (historicalWholeJetMap w
      (fun i=>actualUnshiftedTaylorAlgHom (d+t) (N (a i))) q)) ∧
      HistoricalWholeSupportedDivision w (fun i=>actualUnshiftedTaylorAlgHom (d+t) (N (a i))) := by
    simpa only [hTaylorFin] using hTargetDivision
  have hTargetPrefix : ∀m,HistoricalDegreePrefixFrames w
      (fun i=>actualUnshiftedTaylorAlgHom (d+t) (N (a i))) m := by
    have h:=actual_normalized_degree_prefix_frames_of_marks w
      (fun i=>actualUnshiftedTaylorAlgHom (d+t) (Γ (a i))) (fun i=>(hMarked i).1) hPrefix
      A (fixedSelectorEssential V) e he b (historical_head_outside_essential a w hw) hBAFree
      hFormalCentre hTargetNorm
    simpa only [hTaylorFin] using h
  have hTargetCones : HistoricalWholePrefixSupport V
      (fun v=>actualUnshiftedTaylorAlgHom (d+t) (N v)) := by
    have h:=actualNormalizedFormalMembers_whole_prefix_support V
      (fun v=>actualUnshiftedTaylorAlgHom (d+t) (Γ v)) hCones A e he b hBA hFree
      (fun v=>actualTaylor_mem_coordinateCentre_pow A (normalExponentDegree v.val) (Γ v) (hCentre v))
    simpa only [hTaylorV] using h
  obtain ⟨P,hProductP,_hTaylorP,hStrict⟩:=exists_actual_historical_analytic_strict_generators_of_marks
    d t ht j b W hW w (fun i=>Γ (a i)) hSpan (fixedSelectorEssential V)
    (historical_head_outside_essential a w hw) hBAFree hCentreFin (fun i=>(hMarked i).1)
    hWhole hSupported hTargetNorm
  have hPN : P=fun i=>N (a i) := by
    funext i
    have hne : coordinateGerm e≠0:=HolomorphicGermReducednessBridge.coordinate_germ_ne_zero e
    exact mul_left_cancel₀ (pow_ne_zero _ hne) ((hProductP i).trans (hProductFin i).symm)
  rw [hPN] at hStrict
  have hRange : range (fun i=>N (a i))=range N := by
    ext F
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨a i,rfl⟩
    · rintro ⟨v,rfl⟩
      exact ⟨a.symm v,by change N (a (a.symm v))=N v; rw [Equiv.apply_symm_apply]⟩
  rw [hRange] at hStrict
  refine ⟨?_,fun R=>(hSelected.2.2 R).2.1,hStrict⟩
  exact ⟨(fun i=>⟨hTargetMarked i,historical_owned_head_exact_order w
      (fun i=>actualUnshiftedTaylorAlgHom (d+t) (N (a i))) hTargetMarked hTargetFull.1 i (hOwn i)⟩),
    hTargetFull.1,hTargetPrefix,hTargetFull.2,
    (fun R=>⟨(hSelected.2.2 R).1,(hSelected.2.2 R).2.2⟩),hTargetCones⟩

end
end Hironaka.HironakaActualHistoricalNormalizedWeakPresentation
