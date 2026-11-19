import Hironaka.Resolution.HironakaActualLocalFGStrictSaturation
import Hironaka.Resolution.HironakaActualHistoricalNormalizedWeakPresentation

/-! The genuine original-index successor needs only SOURCE-local finite
generation, as supplied by actual native coordinate charts. No global analytic
coordinate representative is assumed. Every original label and mark is retained,
and ENTIRE true strict-ideal equality precedes Hilbert--Samuel comparison. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalLocalSelectedSuccessor
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaRelativeNormalMonomialBasis HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalFormalSupportedDivision
  HironakaActualHistoricalCentreFilteredDivision HironakaActualHistoricalNormalizedLeadingFrames
  HironakaActualCauchyMonomialDivision HironakaActualOriginalFormalHSTransfer
  HironakaActualHistoricalAnalyticStrictDictionary HironakaActualAnalyticBlowupTaylor
  HironakaActualUnshiftedInitialHSTransfer HironakaActualPointGeometricBennett
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicPointJets
  HironakaActualSelectedCentreStrictSaturation HironakaActualLocalFGStrictSaturation
  HironakaActualHistoricalMarkedHSPreservation
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualHistoricalNormalizedSelectedContact
  HironakaActualFixedInheritedSelector HironakaActualHistoricalEssentialPivotDrop
  HironakaActualHistoricalHSReverseMarks HironakaActualHistoricalPrefixJetFrames
  HironakaActualHistoricalMovingPrefixSupport HironakaActualHistoricalNormalizedSupport

variable {n k : ℕ}

/-- Source powers and ACTUAL target marks construct genuine normalized
analytic generators of the ENTIRE true strict ideal, in original indices. -/
theorem exists_actual_local_selected_historical_strict_generators_of_marks
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (hA : ∃f∈A,f≠e) (b : Fin n → ℂ)
    (W : Set (ComplexModel n)) (hFG : OkaIdealOperations.IdealFGAt (vanishingIdeal (n:=n) W).mem (0 : ComplexModel n))
    (w : Fin k → CoordinateWord n) (Γ : Fin k → HolGerm (ComplexModel n))
    (hspan : Ideal.span (range Γ)=originalCoherentOriginIdeal (vanishingIdeal (n:=n) W))
    (B : Set (Fin n)) (hHeads : ∀i q,q∉B → wordExponent (w i) q=0)
    (hBA : B⊆A\{e})
    (hCentre : ∀i,Γ i∈actualAnalyticCoordinateIdeal A^
      normalExponentDegree (wordExponent (w i)))
    (hmarked : ∀i,actualUnshiftedTaylorAlgHom n (Γ i)∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (w i)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w
      (fun i=>actualUnshiftedTaylorAlgHom n (Γ i)) q))
    (hSupported : HistoricalWholeSupportedDivision w (fun i=>actualUnshiftedTaylorAlgHom n (Γ i)))
    (hTargetMarked : ∀i,actualNormalizedFormalMember A e
      he b
      (normalExponentDegree (wordExponent (w i))) (actualUnshiftedTaylorAlgHom n (Γ i))
      (actualTaylor_mem_coordinateCentre_pow _ _ _ (hCentre i))∈
        genuineFormalVariables n^normalExponentDegree (wordExponent (w i))) :
    ∃N : Fin k → HolGerm (ComplexModel n),
      (∀i,(coordinateGerm e)^normalExponentDegree (wordExponent (w i))*N i=
        actualAnalyticBlowupPullback A e b (Γ i)) ∧
      (∀i,actualUnshiftedTaylorAlgHom n (N i)=
        actualNormalizedFormalMember A e
          he b
          (normalExponentDegree (wordExponent (w i))) (actualUnshiftedTaylorAlgHom n (Γ i))
          (actualTaylor_mem_coordinateCentre_pow _ _ _ (hCentre i))) ∧
      originalCoherentOriginIdeal (vanishingIdeal (n:=n)
        (strictTransform n
          (actualAnalyticBlowupMap A e b) W))=
        Ideal.span (range N) := by
  let μ:=fun i=>normalExponentDegree (wordExponent (w i))
  let g:=fun i=>actualUnshiftedTaylorAlgHom n (Γ i)
  have hFormalCentre (i) : g i∈actualFormalCoordinateIdeal n A^μ i:=
    actualTaylor_mem_coordinateCentre_pow A (μ i) (Γ i) (hCentre i)
  choose N hProduct hTaylor using fun i=>exists_actualAnalyticBlowup_quotient A e he b (μ i) (Γ i) (hCentre i)
  have hFramesSupported:=actual_normalized_whole_supported_division_of_marks
    w g hmarked hwhole hSupported A B e he b hHeads hBA hFormalCentre hTargetMarked
  have hNmarked : ∀i,actualUnshiftedTaylorAlgHom n (N i)∈
      genuineFormalVariables n^μ i:=by
    simpa only [hTaylor] using hTargetMarked
  have hNwhole : ∀q,Function.Bijective (historicalWholeJetMap w
      (fun i=>actualUnshiftedTaylorAlgHom n (N i)) q):=by
    simpa only [hTaylor] using hFramesSupported.1
  have hNSupported : HistoricalWholeSupportedDivision w
      (fun i=>actualUnshiftedTaylorAlgHom n (N i)):=by
    simpa only [hTaylor] using hFramesSupported.2
  have hFree (i : Fin k) : wordExponent (w i) e=0:=
    hHeads i e (fun heB=>(hBA heB).2 rfl)
  let a:=coordinateGerm e
  let I:=originalCoherentOriginIdeal (vanishingIdeal (n:=n) W)
  let K:=Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom I
  let J:=Ideal.span (range N)
  have hSat (q : ℕ) (F : HolGerm (ComplexModel n)) : a^q*F∈J ↔ F∈J:=
    actual_historical_analytic_free_pivot_power_iff w N hNmarked hNwhole hNSupported e hFree q F
  have hK : K=Ideal.span (range fun i=>a^(μ i)*N i):=by
    change Ideal.map (actualAnalyticBlowupPullback A e b).toRingHom
      (originalCoherentOriginIdeal (vanishingIdeal (n:=n) W))=_
    rw [←hspan,Ideal.map_span]
    apply congrArg Ideal.span
    ext F
    constructor
    · rintro ⟨G,⟨i,rfl⟩,rfl⟩
      exact ⟨i,hProduct i⟩
    · rintro ⟨i,rfl⟩
      exact ⟨Γ i,⟨i,rfl⟩,(hProduct i).symm⟩
  have hKJ : K≤J:=by
    rw [hK]
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i,rfl⟩)
  let M:=Finset.univ.sup μ
  have hμ (i : Fin k) : μ i≤M:=Finset.le_sup (Finset.mem_univ i)
  have hIntoK (F : HolGerm (ComplexModel n)) (hF : F∈J) : a^M*F∈K:=by
    obtain ⟨c,hc⟩:=Ideal.mem_span_range_iff_exists_fun.mp hF
    rw [←hc,Finset.mul_sum]
    apply Ideal.sum_mem
    intro i _
    have hGen : a^(μ i)*N i∈K:=by rw [hK];exact Ideal.subset_span ⟨i,rfl⟩
    have hm:=Ideal.mul_mem_left K (a^(M-μ i)*c i) hGen
    have hPow : a^M=a^(M-μ i)*a^(μ i):=by rw [←pow_add,Nat.sub_add_cancel (hμ i)]
    have heq : (a^(M-μ i)*c i)*(a^(μ i)*N i)=a^M*(c i*N i):=by rw [hPow];ring
    exact heq ▸ hm
  refine ⟨N,hProduct,hTaylor,?_⟩
  ext F
  rw [mem_actual_selected_strict_ideal_iff_power_of_local_fg A e hA b W hFG F]
  constructor
  · rintro ⟨q,hq⟩
    exact (hSat q F).mp (hKJ hq)
  · intro hF
    exact ⟨M,hIntoK F hF⟩


private theorem map_taylor_span (Γ : Fin k → HolGerm (ComplexModel n)) :
    Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom (Ideal.span (range Γ))=
      Ideal.span (range fun j=>actualUnshiftedTaylorAlgHom n (Γ j)) := by
  rw [Ideal.map_span,←range_comp]
  rfl

/-- In the TRUE actual geometric strict chart, normalized marked orders
produce the SAME ENTIRE original HS function, not a finite profile cut. -/
theorem actual_local_selected_strict_hilbertSamuel_eq_of_marks
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (hA : ∃f∈A,f≠e) (b : Fin n → ℂ)
    (W : Set (ComplexModel n)) (hFG : OkaIdealOperations.IdealFGAt (vanishingIdeal (n:=n) W).mem (0 : ComplexModel n))
    (w : Fin k → CoordinateWord n) (Γ : Fin k → HolGerm (ComplexModel n))
    (hspan : Ideal.span (range Γ)=originalCoherentOriginIdeal (vanishingIdeal (n:=n) W))
    (B : Set (Fin n)) (hHeads : ∀i q,q∉B → wordExponent (w i) q=0)
    (hBA : B⊆A\{e})
    (hCentre : ∀i,Γ i∈actualAnalyticCoordinateIdeal A^
      normalExponentDegree (wordExponent (w i)))
    (hmarked : ∀i,actualUnshiftedTaylorAlgHom n (Γ i)∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (w i)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w
      (fun i=>actualUnshiftedTaylorAlgHom n (Γ i)) q))
    (hSupported : HistoricalWholeSupportedDivision w (fun i=>actualUnshiftedTaylorAlgHom n (Γ i)))
    (hTargetMarked : ∀i,actualNormalizedFormalMember A e
      he b
      (normalExponentDegree (wordExponent (w i))) (actualUnshiftedTaylorAlgHom n (Γ i))
      (actualTaylor_mem_coordinateCentre_pow _ _ _ (hCentre i))∈
        genuineFormalVariables n^normalExponentDegree (wordExponent (w i))) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n
      (actualAnalyticBlowupMap A e b) W)) 0 ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n) W) 0 ℓ := by
  obtain ⟨N,_hProduct,hTaylor,hStrict⟩:=exists_actual_local_selected_historical_strict_generators_of_marks
    A e he hA b W hFG w Γ hspan B hHeads hBA hCentre hmarked hwhole hSupported hTargetMarked
  have hFormal:=actual_normalized_hilbertSamuel_eq_of_marks w
    (fun i=>actualUnshiftedTaylorAlgHom n (Γ i)) hmarked hwhole hSupported
    A B e he b hHeads hBA
    (fun i=>actualTaylor_mem_coordinateCentre_pow _ _ _ (hCentre i)) hTargetMarked ℓ
  rw [hilbertSamuelAt_model_zero,hilbertSamuelAt_model_zero,hStrict,←hspan,
    hilbertSamuelValue_eq_actual_unshifted_formal_extension,
    hilbertSamuelValue_eq_actual_unshifted_formal_extension,map_taylor_span,map_taylor_span]
  simpa only [hTaylor] using hFormal

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

/-- TRUE selected geometric HS persistence is equivalent to actual point
marks of ANY genuine quotients, in the SAME original centre indices. -/
theorem actual_local_selected_hs_iff_same_quotient_marks
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (hA : ∃f∈A,f≠e) (b : Fin n → ℂ)
    (W : Set (ComplexModel n)) (hFG : OkaIdealOperations.IdealFGAt (vanishingIdeal (n:=n) W).mem (0 : ComplexModel n))
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ N : V → HolGerm (ComplexModel n))
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hSpan : Ideal.span (range (fun i=>Γ (a i)))=originalCoherentOriginIdeal (vanishingIdeal (n:=n) W))
    (hSource : ActualHistoricalFivePointLaws S a w Γ)
    (hHeads : ∀v : V,(↑v.val.support : Set (Fin n))⊆A)
    (hCentre : ∀v,Γ v∈actualAnalyticCoordinateIdeal A^normalExponentDegree v.val)
    (hProduct : ∀v,(coordinateGerm e)^normalExponentDegree v.val*N v=
      actualAnalyticBlowupPullback A e b (Γ v)) :
    (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n
      (actualAnalyticBlowupMap A e b) W)) 0 ℓ=hilbertSamuelAt (vanishingIdeal (n:=n) W) 0 ℓ) ↔
    ∀v : V,actualUnshiftedTaylorAlgHom n (N v)∈genuineFormalVariables n^normalExponentDegree v.val := by
  rcases hSource with ⟨hMarked,hWhole,hPrefix,hSupported,hContact,hCones⟩
  have hCentreFin (i : Fin k) : Γ (a i)∈actualAnalyticCoordinateIdeal A^
      normalExponentDegree (wordExponent (w i)) := by
    simpa only [hw] using hCentre (a i)
  have hProductFin (i : Fin k) : (coordinateGerm e)^normalExponentDegree (wordExponent (w i))*N (a i)=
      actualAnalyticBlowupPullback A e b (Γ (a i)) := by
    simpa only [hw] using hProduct (a i)
  have hTaylorFin (i : Fin k) :=actual_same_quotient_taylor A e he b
    (normalExponentDegree (wordExponent (w i))) (Γ (a i)) (N (a i)) (hCentreFin i) (hProductFin i)
  have hFormalCentre (i : Fin k) :=actualTaylor_mem_coordinateCentre_pow A
    (normalExponentDegree (wordExponent (w i))) (Γ (a i)) (hCentreFin i)
  have hProper:=prefix_support_proper_cones a w hw (fun v=>actualUnshiftedTaylorAlgHom n (Γ v)) hCones
  have hBA:=historical_essential_subset_centre A hHeads
  constructor
  · intro hHS
    let I:=originalCoherentOriginIdeal (vanishingIdeal (n:=n) W)
    let J:=originalCoherentOriginIdeal (vanishingIdeal (n:=n) (strictTransform n
      (actualAnalyticBlowupMap A e b) W))
    let K:=Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom J
    have hNmem (i : Fin k) : N (a i)∈J := by
      apply actual_selected_normalized_ideal_le_geometric_strict_vanishing A e hA b W
      apply Ideal.subset_span
      refine ⟨normalExponentDegree (wordExponent (w i)),Γ (a i),?_,hCentreFin i,hProductFin i⟩
      rw [←hSpan]
      exact Ideal.subset_span ⟨i,rfl⟩
    have hIn (i : Fin k) : actualNormalizedFormalMember A e he b
        (normalExponentDegree (wordExponent (w i))) (actualUnshiftedTaylorAlgHom n (Γ (a i)))
        (hFormalCentre i)∈K := by
      have h:=Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom (hNmem i)
      change actualUnshiftedTaylorAlgHom n (N (a i))∈K at h
      rwa [hTaylorFin i] at h
    have hSourceMap : Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I=
        Ideal.span (range fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i))) := by
      dsimp only [I]
      rw [←hSpan,map_taylor_span]
    have hFormalHS (ℓ : ℕ) : genuineFormalHilbertSamuelValue n K ℓ=
        genuineFormalHilbertSamuelValue n (Ideal.span (range fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i)))) ℓ := by
      calc
        _=hilbertSamuelValue J ℓ:=(hilbertSamuelValue_eq_actual_unshifted_formal_extension n J ℓ).symm
        _=hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n
            (actualAnalyticBlowupMap A e b) W)) 0 ℓ:=(hilbertSamuelAt_model_zero _ ℓ).symm
        _=hilbertSamuelAt (vanishingIdeal (n:=n) W) 0 ℓ:=hHS ℓ
        _=hilbertSamuelValue I ℓ:=hilbertSamuelAt_model_zero _ ℓ
        _=genuineFormalHilbertSamuelValue n (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) ℓ:=
          hilbertSamuelValue_eq_actual_unshifted_formal_extension n I ℓ
        _=_:=by rw [hSourceMap]
    have hFree:=actual_equal_hs_pivot_not_essential S Γ a w hw (fun i=>(hMarked i).1) hWhole
      hSupported hPrefix hProper A e he b hHeads hFormalCentre
      (fun r=>(hContact r).1) (fun r=>(hContact r).2) K hIn hFormalHS
    have hFreeHeads (i : Fin k) : (↑(wordExponent (w i)).support : Set (Fin n))⊆A\{e} := by
      intro x hx
      have hxE : x∈fixedSelectorEssential V:=⟨a i,by
        rw [←hw]
        exact Finsupp.mem_support_iff.mp hx⟩
      refine ⟨hBA hxE,?_⟩
      intro hxe
      exact hFree ((Set.mem_singleton_iff.mp hxe) ▸ hxE)
    have hOrders:=actual_normalized_marks_of_equal_hs w
      (fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i))) (fun i=>(hMarked i).1)
      hWhole hSupported hPrefix hProper A e he b hFreeHeads hFormalCentre K hIn hFormalHS
    intro v
    have h:=hOrders (a.symm v)
    rw [←hTaylorFin (a.symm v)] at h
    simpa only [hw,Equiv.apply_symm_apply] using h
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
        (normalExponentDegree (wordExponent (w i))) (actualUnshiftedTaylorAlgHom n (Γ (a i)))
        (actualTaylor_mem_coordinateCentre_pow A _ _ (hCentreFin i))∈
          genuineFormalVariables n^normalExponentDegree (wordExponent (w i)) := by
      rw [←hTaylorFin i]
      simpa only [hw] using hPoint (a i)
    exact actual_local_selected_strict_hilbertSamuel_eq_of_marks A e he hA b W hFG w (fun i=>Γ (a i)) hSpan
      (fixedSelectorEssential V) (historical_head_outside_essential a w hw) hBAFree hCentreFin
      (fun i=>(hMarked i).1) hWhole hSupported hTarget

/-- Every TRUE profile-persistent actual point has ALL five SAME historical
laws for ANY genuine quotient family; its ENTIRE strict ideal is generated by
those actual quotients, with original block Jacobians exactly preserved. -/
theorem actual_local_selected_same_quotients_five_laws
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (hA : ∃f∈A,f≠e) (b : Fin n → ℂ)
    (W : Set (ComplexModel n)) (hFG : OkaIdealOperations.IdealFGAt (vanishingIdeal (n:=n) W).mem (0 : ComplexModel n))
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ N : V → HolGerm (ComplexModel n))
    (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hOwn : ∀i,historicalOwner w (wordExponent (w i))=some i)
    (hSpan : Ideal.span (range (fun i=>Γ (a i)))=originalCoherentOriginIdeal (vanishingIdeal (n:=n) W))
    (hSource : ActualHistoricalFivePointLaws S a w Γ)
    (hHeads : ∀v : V,(↑v.val.support : Set (Fin n))⊆A)
    (hCentre : ∀v,Γ v∈actualAnalyticCoordinateIdeal A^normalExponentDegree v.val)
    (hProduct : ∀v,(coordinateGerm e)^normalExponentDegree v.val*N v=
      actualAnalyticBlowupPullback A e b (Γ v))
    (hHS : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n
      (actualAnalyticBlowupMap A e b) W)) 0 ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) 0 ℓ) :
    ActualHistoricalFivePointLaws S a w N ∧
    (∀R,actualFixedSelectorJacobian S N R=actualFixedSelectorJacobian S Γ R) ∧
    originalCoherentOriginIdeal (vanishingIdeal (n:=n) (strictTransform n
      (actualAnalyticBlowupMap A e b) W))=
      Ideal.span (range N) := by
  have hPoint:=(actual_local_selected_hs_iff_same_quotient_marks A e he hA b W hFG S Γ N a w hw hSpan
    hSource hHeads hCentre hProduct).mp hHS
  rcases hSource with ⟨hMarked,hWhole,hPrefix,hSupported,hContact,hCones⟩
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
  have hTargetMarked (i : Fin k) : actualUnshiftedTaylorAlgHom n (N (a i))∈
      genuineFormalVariables n^normalExponentDegree (wordExponent (w i)) := by
    simpa only [hw] using hPoint (a i)
  have hTargetNorm (i : Fin k) : actualNormalizedFormalMember A e he b
      (normalExponentDegree (wordExponent (w i))) (actualUnshiftedTaylorAlgHom n (Γ (a i)))
      (actualTaylor_mem_coordinateCentre_pow A _ _ (hCentreFin i))∈
        genuineFormalVariables n^normalExponentDegree (wordExponent (w i)) := by
    rw [←hTaylorFin i]
    exact hTargetMarked i
  have hFormalCentre (i : Fin k) :=actualTaylor_mem_coordinateCentre_pow A
    (normalExponentDegree (wordExponent (w i))) (Γ (a i)) (hCentreFin i)
  have hTargetDivision:=actual_normalized_whole_supported_division_of_marks w
    (fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i))) (fun i=>(hMarked i).1)
    hWhole hSupported A (fixedSelectorEssential V) e he b
    (historical_head_outside_essential a w hw) hBAFree hFormalCentre hTargetNorm
  have hTargetFull : (∀q,Function.Bijective (historicalWholeJetMap w
      (fun i=>actualUnshiftedTaylorAlgHom n (N (a i))) q)) ∧
      HistoricalWholeSupportedDivision w (fun i=>actualUnshiftedTaylorAlgHom n (N (a i))) := by
    simpa only [hTaylorFin] using hTargetDivision
  have hTargetPrefix : ∀m,HistoricalDegreePrefixFrames w
      (fun i=>actualUnshiftedTaylorAlgHom n (N (a i))) m := by
    have h:=actual_normalized_degree_prefix_frames_of_marks w
      (fun i=>actualUnshiftedTaylorAlgHom n (Γ (a i))) (fun i=>(hMarked i).1) hPrefix
      A (fixedSelectorEssential V) e he b (historical_head_outside_essential a w hw) hBAFree
      hFormalCentre hTargetNorm
    simpa only [hTaylorFin] using h
  have hTargetCones : HistoricalWholePrefixSupport V
      (fun v=>actualUnshiftedTaylorAlgHom n (N v)) := by
    have h:=actualNormalizedFormalMembers_whole_prefix_support V
      (fun v=>actualUnshiftedTaylorAlgHom n (Γ v)) hCones A e he b hBA hFree
      (fun v=>actualTaylor_mem_coordinateCentre_pow A (normalExponentDegree v.val) (Γ v) (hCentre v))
    simpa only [hTaylorV] using h
  obtain ⟨P,hProductP,_hTaylorP,hStrict⟩:=exists_actual_local_selected_historical_strict_generators_of_marks
    A e he hA b W hFG w (fun i=>Γ (a i)) hSpan (fixedSelectorEssential V)
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
      (fun i=>actualUnshiftedTaylorAlgHom n (N (a i))) hTargetMarked hTargetFull.1 i (hOwn i)⟩),
    hTargetFull.1,hTargetPrefix,hTargetFull.2,
    (fun R=>⟨(hSelected.2.2 R).1,(hSelected.2.2 R).2.2⟩),hTargetCones⟩

end
end Hironaka.HironakaActualHistoricalLocalSelectedSuccessor
