import Hironaka.Resolution.HironakaActualHistoricalNativeStageStep

/-! Positive original weighted compression preserves the ENTIRE germ radical
and reflects actual reduced-ideal tests on genuine native coordinates.
Blueprint: hironaka-actual-weighted-native-radical-20261102.tex. -/
set_option autoImplicit false
open Set Classical
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualWeightedNativeRadical
noncomputable section
open Hironaka.HolomorphicIdealSheaves HolGerm
  HironakaActualWeightedCoefficientCompression HironakaActualHistoricalNativeStageStep
  HironakaActualFixedInheritedSelector HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaHolomorphicJetRankLoci
  HironakaHolomorphicJetChartInvariance HironakaActualCauchyMonomialDivision
  HironakaRelativeNormalDeformationInitialRelations HironakaRelativeNormalCoherentTranslatedJets
  HironakaSmoothCentreCoherentDomain HironakaSmoothSubmersionGermIdealColon MarkedIdeals

/-- Positive literal compression preserves the ENTIRE original germ radical. -/
theorem weightedCompression_radical {ι : Type*} [Fintype ι] {R : Type*} [CommRing R]
    (w : ι→ℕ) (hw : ∀i,0<w i) (c : ι→R) :
    (weightedCompression w c).radical=(Ideal.span (range c)).radical := by
  have hLe : weightedCompression w c≤Ideal.span (range c) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change c i^(weightedCommonMark w/w i)∈Ideal.span (range c)
    have he:=compressionExponent_pos w hw i
    obtain ⟨j,hj⟩:=Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt he)
    rw [hj,pow_succ]
    exact (Ideal.span (range c)).mul_mem_left (c i^j) (Ideal.subset_span ⟨i,rfl⟩)
  apply le_antisymm (Ideal.radical_mono hLe)
  apply Ideal.radical_le_radical_iff.mpr
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  exact ⟨weightedCommonMark w/w i,Ideal.subset_span ⟨i,rfl⟩⟩

/-- Containment in ANY actual radical ideal is reflected by the entire
original powered compression. In particular genuine prime tests are allowed. -/
theorem weightedCompression_le_radical_iff {ι : Type*} [Fintype ι]
    {R : Type*} [CommRing R] (w : ι→ℕ) (hw : ∀i,0<w i) (c : ι→R)
    (P : Ideal R) (hP : P.IsRadical) :
    weightedCompression w c≤P ↔ Ideal.span (range c)≤P := by
  rw [←hP.radical_le_iff,weightedCompression_radical w hw c,hP.radical_le_iff]

variable {n k : ℕ} {X : Type} [TopologicalSpace X]
  [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]

/-- Actual CURRENT native whole point data internally give genuine centered
coordinates and the entire radical/reduced-test dictionary for the SAME Q. -/
theorem actual_native_point_radical_dictionary
    {V : Finset (Fin n →₀ ℕ)} (S : ActualFixedInheritedSelector V)
    (a : Fin k ≃ V) (w : Fin k→CoordinateWord n)
    (hPositive : ∀v : V,0<normalExponentDegree v.val)
    (W : Set X) (Q : MarkedIdeal n X) (x : X)
    (hAt : ActualHistoricalNativePointPresentation S a w W Q x) :
    ∃(Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) x x))
      (_hsrc : Φ.source⊆(chartAt (ComplexModel n) x).target)
      (h0 : Φ.toFun (chartAt (ComplexModel n) x x)=0),
      let J:=originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) W) x Φ) 0)
      (adaptedIdeal Q.ideal x Φ h0).radical=J.radical ∧
      ∀P : Ideal (HolGerm (ComplexModel n)),P.IsRadical →
        (adaptedIdeal Q.ideal x Φ h0≤P ↔ J≤P) := by
  obtain ⟨Φ,hsrc,h0,Γ,_hFive,hGeneration,hCompression⟩:=hAt
  have hRange : range (fun i=>Γ (a i))=range Γ:=a.surjective.range_comp Γ
  rw [hRange] at hGeneration
  refine ⟨Φ,hsrc,h0,?_,?_⟩
  · rw [hCompression,weightedCompression_radical _ hPositive Γ,hGeneration]
  · intro P hP
    rw [hCompression,weightedCompression_le_radical_iff _ hPositive Γ P hP,hGeneration]

end
end Hironaka.HironakaActualWeightedNativeRadical
