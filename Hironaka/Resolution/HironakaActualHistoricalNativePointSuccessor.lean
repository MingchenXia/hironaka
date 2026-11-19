import Hironaka.Resolution.HironakaActualSelectedFlatteningHSComparison
import Hironaka.Resolution.HironakaActualHistoricalLocalSelectedSuccessor
import Hironaka.Resolution.HironakaActualLocalStrictSaturation
import Hironaka.Resolution.HironakaActualHSConstantCentreBennett
import Hironaka.Resolution.HironakaActualHilbertSamuelLexOrder

/-! A genuine native blowup INTERNALLY constructs its SAME historical point
successor. Only actual source laws/coherence/centre powers are supplied. Whole
native strict ideals and profiles, target charts and all five laws are outputs. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualHistoricalNativePointSuccessor
noncomputable section
attribute [local instance] Classical.propDecidable
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HolGerm
  HironakaActualSelectedFlatteningHSComparison HironakaActualFixedFlatteningHSComparison
  HironakaActualHistoricalLocalSelectedSuccessor HironakaActualLocalStrictSaturation
  HironakaActualHistoricalNormalizedWeakPresentation HironakaActualFixedInheritedSelector
  HironakaActualCoefficientPresentationCentrePower HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalFormalHSTransfer HironakaActualAnalyticBlowupTaylor
  HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalDeformationInitialRelations
  HironakaRelativeNormalCoherentTranslatedJets HironakaSmoothCentreCoherentDomain
  HironakaActualHistoricalNormalizedSelectedContact HironakaActualHistoricalMovingCentreChart
  HironakaHolomorphicJetChartInvariance BlowupFlatCoordinates
  HironakaActualCauchyMonomialDivision
  HironakaActualHSConstantCentreBennett

variable {n k : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

private theorem other_priority_normal (c : ℕ) (p : Fin n ≃ Fin n) (hc : c+2≤n) (e : Fin n) :
    ∃f∈({i : Fin n | c≤(p i).val} : Set (Fin n)),f≠e := by
  let i₀ : Fin n:=⟨c,by omega⟩
  let i₁ : Fin n:=⟨c+1,by omega⟩
  have hi₀ : p.symm i₀∈({i : Fin n | c≤(p i).val} : Set (Fin n)) := by
    change c≤(p (p.symm i₀)).val
    rw [p.apply_symm_apply]
  have hi₁ : p.symm i₁∈({i : Fin n | c≤(p i).val} : Set (Fin n)) := by
    change c≤(p (p.symm i₁)).val
    rw [p.apply_symm_apply]
    exact Nat.le_succ c
  by_cases he : e=p.symm i₀
  · refine ⟨p.symm i₁,hi₁,?_⟩
    intro h
    have h' : i₁=i₀:=p.symm.injective (h.trans he)
    have hv:=congrArg Fin.val h'
    dsimp only [i₀,i₁] at hv
    omega
  · exact ⟨p.symm i₀,hi₀,Ne.symm he⟩

/-- Genuine source data produce the actual native target chart, whole
polynomial square, SAME analytic quotient family and TRUE native point
successor. No target weak law/ideal/profile or global model-analyticity input. -/
theorem exists_actual_native_same_historical_point_successor
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (z : Y)
    (c : ℕ) (hc : c+2≤n) (p : Fin n ≃ Fin n)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) (π z)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0)
    (hFlat : ∀{x : X},x∈(chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) x∈Φ.source →
      (x∈C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) x)∈
        coordinateSubsetPlane {i : Fin n | c≤(p i).val}))
    (W : Set X) (hW : (vanishingIdeal (n:=n) W).IsCoherent)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hOwn : ∀i,HironakaActualHistoricalWholeJetFrames.historicalOwner w (wordExponent (w i))=some i)
    (hSpan : Ideal.span (range (fun i=>Γ (a i)))=originalCoherentOriginIdeal
      (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) (π z) Φ) 0))
    (hSource : ActualHistoricalFivePointLaws S a w Γ)
    (hHeads : ∀v : V,(↑v.val.support : Set (Fin n))⊆{i : Fin n | c≤(p i).val})
    (hCentre : ∀v,Γ v∈actualAnalyticCoordinateIdeal {i : Fin n | c≤(p i).val}^normalExponentDegree v.val) :
    ∃e : Fin n,c≤(p e).val ∧ ∃(b : Fin n → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
      (N : V → HolGerm (ComplexModel n)),
      Θ.source⊆(chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z)=0 ∧
      (∀i : Fin n,(p i).val<c → b i=0) ∧ b e=0 ∧
      (∀i : Fin n,c≤(p i).val → i≠e → ‖b i‖≤1) ∧
      (∀y : Y,y∈(chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z y∈Θ.source → π y∈flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
          actualAnalyticBlowupMap {i : Fin n | c≤(p i).val} e b
            (Θ.toFun (chartAt (ComplexModel n) z y))) ∧
      (∀v,(coordinateGerm e)^normalExponentDegree v.val*N v=
        actualAnalyticBlowupPullback {i : Fin n | c≤(p i).val} e b (Γ v)) ∧
      ((∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ) ↔
        ∀v : V,actualUnshiftedTaylorAlgHom n (N v)∈genuineFormalVariables n^normalExponentDegree v.val) ∧
      ((∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ) →
        e∉fixedSelectorEssential V ∧ (∀i∈fixedSelectorEssential V,b i=0) ∧
        ActualHistoricalFivePointLaws S a w N ∧
        (∀R,actualFixedSelectorJacobian S N R=actualFixedSelectorJacobian S Γ R) ∧
        originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) (strictTransform n π W)) z Θ) 0)=
            Ideal.span (range N)) := by
  obtain ⟨e,he,b,Θ,hbT,hbe,hBound,hΘsrc,hΘ0,hNormal,hTargetHS⟩:=
    exists_actual_given_selected_flattening_blowup_square hπ z c p Φ hΦsrc hΦ0 hFlat
  let A : Set (Fin n):={i | c≤(p i).val}
  have heA : e∈A:=he
  have hOther : ∃f∈A,f≠e:=other_priority_normal c p hc e
  let W₀:=actualFixedFlatteningSet (π z) Φ W
  have hFG:=fixedFlattening_vanishing_local_fg W hW (π z) Φ hΦsrc hΦ0
  have hSpanModel : Ideal.span (range (fun i=>Γ (a i)))=
      originalCoherentOriginIdeal (vanishingIdeal (n:=n) W₀):=
    hSpan.trans (originalFlattenedVanishingOriginIdeal_eq_model (π z) Φ hΦsrc hΦ0 W)
  choose N hProduct _hTaylor using fun v=>exists_actualAnalyticBlowup_quotient A e heA b
    (normalExponentDegree v.val) (Γ v) (hCentre v)
  have hOriginalHS (ℓ : ℕ) :=hilbertSamuelAt_eq_fixedFlattening_model (π z) Φ hΦsrc hΦ0 W ℓ
  have hNativeModel : (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ) ↔
      (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n (actualAnalyticBlowupMap A e b) W₀)) 0 ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=n) W₀) 0 ℓ) := by
    constructor
    · intro h ℓ
      rw [←hTargetHS W ℓ,←hOriginalHS ℓ]
      exact h ℓ
    · intro h ℓ
      rw [hTargetHS W ℓ,hOriginalHS ℓ]
      exact h ℓ
  have hMarksIff:=hNativeModel.trans (actual_local_selected_hs_iff_same_quotient_marks A e heA hOther b
    W₀ hFG S Γ N a w hw hSpanModel hSource hHeads hCentre hProduct)
  refine ⟨e,he,b,Θ,N,hΘsrc,hΘ0,hbT,hbe,hBound,hNormal,hProduct,hMarksIff,?_⟩
  intro hHS
  have hMarks:=hMarksIff.mp hHS
  have hSelected:=actual_normalized_same_selected_contact_of_marks S Γ N A e heA b hHeads hCentre
    hProduct hMarks (fun R=>(hSource.2.2.2.2.1 R).1) (fun R=>(hSource.2.2.2.2.1 R).2)
  have hFive:=actual_local_selected_same_quotients_five_laws A e heA hOther b W₀ hFG S Γ N a w hw hOwn
    hSpanModel hSource hHeads hCentre hProduct (hNativeModel.mp hHS)
  have hNativeIdeal:=originalStrictFlattenedOriginIdeal_eq_selected_model hπ.contMDiff z A Φ hΦsrc e b Θ
    hΘsrc hΘ0 hNormal W
  exact ⟨hSelected.1,hSelected.2.1,hFive.1,hFive.2.1,hNativeIdeal.trans hFive.2.2⟩


/-- Original native HS-constant smooth-centre geometry gives actual Bennett
and STRICT native lex decrease on every produced essential-pivot chart. -/
theorem exists_actual_native_same_historical_point_successor_with_bennett
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (z : Y)
    (c : ℕ) (hc : c+2≤n) (p : Fin n ≃ Fin n)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) (π z)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0)
    (hFlat : ∀{x : X},x∈(chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) x∈Φ.source →
      (x∈C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) x)∈
        coordinateSubsetPlane {i : Fin n | c≤(p i).val}))
    (W : Set X) (hC : IsClosedSubmanifold n C) (hW : IsComplexAnalyticSubset (n:=n) W)
    (hHSConst : ∀x∈C,∀y∈C,∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) W) x ℓ=
      hilbertSamuelAt (vanishingIdeal (n:=n) W) y ℓ)
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (Γ : V → HolGerm (ComplexModel n)) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀i,wordExponent (w i)=(a i).val)
    (hOwn : ∀i,HironakaActualHistoricalWholeJetFrames.historicalOwner w (wordExponent (w i))=some i)
    (hSpan : Ideal.span (range (fun i=>Γ (a i)))=originalCoherentOriginIdeal
      (actualTranslatedOriginalSheaf (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) (π z) Φ) 0))
    (hSource : ActualHistoricalFivePointLaws S a w Γ)
    (hHeads : ∀v : V,(↑v.val.support : Set (Fin n))⊆{i : Fin n | c≤(p i).val})
    (hCentre : ∀v,Γ v∈actualAnalyticCoordinateIdeal {i : Fin n | c≤(p i).val}^normalExponentDegree v.val) :
    ∃e : Fin n,c≤(p e).val ∧ ∃(b : Fin n → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
      (N : V → HolGerm (ComplexModel n)),
      Θ.source⊆(chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z)=0 ∧
      (∀i : Fin n,(p i).val<c → b i=0) ∧ b e=0 ∧
      (∀i : Fin n,c≤(p i).val → i≠e → ‖b i‖≤1) ∧
      (∀y : Y,y∈(chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z y∈Θ.source → π y∈flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
          actualAnalyticBlowupMap {i : Fin n | c≤(p i).val} e b
            (Θ.toFun (chartAt (ComplexModel n) z y))) ∧
      (∀v,(coordinateGerm e)^normalExponentDegree v.val*N v=
        actualAnalyticBlowupPullback {i : Fin n | c≤(p i).val} e b (Γ v)) ∧
      (∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ≤
        hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ) ∧
      (e∈fixedSelectorEssential V →
        toLex (hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z)<
          toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z))) ∧
      ((∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ) ↔
        ∀v : V,actualUnshiftedTaylorAlgHom n (N v)∈genuineFormalVariables n^normalExponentDegree v.val) ∧
      ((∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
          hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ) →
        e∉fixedSelectorEssential V ∧ (∀i∈fixedSelectorEssential V,b i=0) ∧
        ActualHistoricalFivePointLaws S a w N ∧
        (∀R,actualFixedSelectorJacobian S N R=actualFixedSelectorJacobian S Γ R) ∧
        originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
          (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) (strictTransform n π W)) z Θ) 0)=
            Ideal.span (range N)) := by
  obtain ⟨e,he,b,Θ,N,hΘsrc,hΘ0,hbT,hbe,hBound,hNormal,hProduct,hMarksIff,hPoint⟩:=
    exists_actual_native_same_historical_point_successor hπ z c hc p Φ hΦsrc hΦ0 hFlat W
      (CartanIrreducible.cartanCoherence W hW) S Γ a w hw hOwn hSpan hSource hHeads hCentre
  have hLe (ℓ : ℕ) : hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ≤
      hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ:=
    hilbertSamuelAt_actual_hs_constant_smooth_centre_blowup_le hπ hC hW hHSConst z ℓ
  have hDrop : e∈fixedSelectorEssential V →
      toLex (hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z)<
        toLex (hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z)) := by
    intro heV
    apply lt_of_le_of_ne (Pi.toLex_monotone hLe)
    intro hEq
    have hProfiles : hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z):=congrArg ofLex hEq
    have hHS : ∀ℓ,hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=n) W) (π z) ℓ:=fun ℓ=>congrFun hProfiles ℓ
    exact (hPoint hHS).1 heV
  exact ⟨e,he,b,Θ,N,hΘsrc,hΘ0,hbT,hbe,hBound,hNormal,hProduct,hLe,hDrop,hMarksIff,hPoint⟩

end
end Hironaka.HironakaActualHistoricalNativePointSuccessor
