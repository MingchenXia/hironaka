import TranscendentalNakamaye.Pending.HironakaActualFormalMonomialBlowupReflection
import TranscendentalNakamaye.Pending.HironakaActualPointCentreStrictGenerators

/-!
# Actual canonical source tails control every low zero-chart coefficient

The genuine zero point blowup exponent map internally identifies each low
normalized coefficient with its literal original source coefficient. Upward
closure of the ENTIRE source diagram and true canonical vertex minimality
force its vanishing there. Original data choose ONE actual normalized family
with whole finite low-jet and homogeneous-component source normality, with
no desired obstruction or old/new diagram inclusion input.
Arbitrary directions and current lower-initial-span comparison remain separate.
Blueprint: `hironaka-actual-zero-point-reduced-tail-extension.tex`.
-/

set_option autoImplicit false
open Set Classical
namespace TranscendentalNakamaye.Pending.HironakaActualZeroPointReducedTail
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalMonomialBlowupReflection
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualPointCentreStrictGenerators
variable {n : ℕ}
local notation "R" => MvPowerSeries (Fin n) ℂ

/-- The literal unique source exponent in the actual low-current range. -/
def zeroPointLowSourceExponent (e : Fin n) (w : ℕ) (β : Fin n →₀ ℕ) : Fin n →₀ ℕ :=
  β+Finsupp.single e (β e+(w-β.degree))

private theorem degree_add (α β : Fin n →₀ ℕ) : (α+β).degree=α.degree+β.degree := by
  simp only [Finsupp.degree_eq_weight_one,map_add]

private theorem low_source_degree (e : Fin n) (w : ℕ) (β : Fin n →₀ ℕ) (hβ : β.degree<w) :
    (zeroPointLowSourceExponent e w β).degree=w+β e := by
  rw [zeroPointLowSourceExponent,degree_add,Finsupp.degree_single]
  omega

private theorem low_source_above (e : Fin n) (w : ℕ) (β : Fin n →₀ ℕ) :
    β≤zeroPointLowSourceExponent e w β := by
  exact le_add_of_nonneg_right zero_le

private theorem low_source_pivot_strict (e : Fin n) (w : ℕ) (β : Fin n →₀ ℕ) (hβ : β.degree<w) :
    β e<zeroPointLowSourceExponent e w β e := by
  simp only [zeroPointLowSourceExponent,Finsupp.add_apply,Finsupp.single_eq_same]
  omega

/-- The genuine monomial chart sends the actual lifted source exponent to
EXACTLY the shifted current exponent. -/
theorem zeroPointLowSourceExponent_blowup (e : Fin n) (w : ℕ) (β : Fin n →₀ ℕ) (hβ : β.degree<w) :
    actualMonomialBlowupExponent univ e (zeroPointLowSourceExponent e w β)=Finsupp.single e w+β := by
  ext i
  by_cases hi : i=e
  · subst i
    rw [actualMonomialBlowupExponent_exceptional univ e (mem_univ e)]
    have hw (α : Fin n →₀ ℕ) : Finsupp.weight (actualCoordinateWeight (univ : Set (Fin n))) α=α.degree := by
      simp [Finsupp.weight_eq_sum,actualCoordinateWeight,Finsupp.degree_eq_sum]
    rw [hw,low_source_degree e w β hβ]
    simp
  · change zeroPointLowSourceExponent e w β i+
      Finsupp.single e (Finsupp.weight (actualCoordinateWeight (univ\{e})) (zeroPointLowSourceExponent e w β)) i=_
    simp [zeroPointLowSourceExponent,hi]

/-- The ACTUAL entire quotient equation internally gives the precise low coefficient dictionary. -/
theorem normalized_zero_point_low_coefficient (e : Fin n) (w : ℕ) (F H : R)
    (hH : (MvPowerSeries.X e)^w*H=actualFormalBlowup univ e (fun _ => 0) F)
    (β : Fin n →₀ ℕ) (hβ : β.degree<w) :
    MvPowerSeries.coeff β H=MvPowerSeries.coeff (zeroPointLowSourceExponent e w β) F := by
  have h := congrArg (MvPowerSeries.coeff (Finsupp.single e w+β)) hH
  rw [MvPowerSeries.X_pow_eq,MvPowerSeries.coeff_add_monomial_mul,one_mul,
    ←zeroPointLowSourceExponent_blowup e w β hβ,actualFormalBlowup_zero_coefficient] at h
  exact h

/-- Literal reduced source support and vertex minimality kill EVERY low
normalized coefficient on the ENTIRE original source diagram. -/
theorem canonical_zero_point_low_coefficient_zero_on_source_diagram
    (I : Ideal R) (a : actualInitialVertices MonomialOrder.degLex I) (e : Fin n) (H : R)
    (hH : (MvPowerSeries.X e)^(normalExponentDegree a.val)*H=
      actualFormalBlowup univ e (fun _ => 0) (actualReducedVertexSeries MonomialOrder.degLex I a))
    (β : Fin n →₀ ℕ) (hβ : normalExponentDegree β<normalExponentDegree a.val)
    (hΓ : β∈actualInitialDiagram MonomialOrder.degLex I) : MvPowerSeries.coeff β H=0 := by
  have hβ' : β.degree<normalExponentDegree a.val := by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hβ
  let α := zeroPointLowSourceExponent e (normalExponentDegree a.val) β
  have hβα : β≤α := low_source_above e _ β
  have hαΓ : α∈actualInitialDiagram MonomialOrder.degLex I :=
    actualInitialDiagram_upper MonomialOrder.degLex I β α hΓ hβα
  have hne : α≠a.val := by
    intro ha
    have hmin : Minimal (·∈actualInitialDiagram MonomialOrder.degLex I) a.val := by
      simpa [actualInitialVertices] using a.property
    have hback : a.val≤β := hmin.2 hΓ (by rwa [←ha])
    have hs := low_source_pivot_strict e (normalExponentDegree a.val) β hβ'
    change β e<α e at hs
    rw [ha] at hs
    exact (not_lt_of_ge (hback e)) hs
  rw [normalized_zero_point_low_coefficient e _ _ H hH β hβ',
    actualReducedVertexSeries_coefficient_diagram MonomialOrder.degLex I a α hαΓ,if_neg hne]

private theorem canonical_point_power (I : Ideal R) (a : actualInitialVertices MonomialOrder.degLex I) :
    actualReducedVertexSeries MonomialOrder.degLex I a∈actualFormalCoordinateIdeal n univ^(normalExponentDegree a.val) := by
  have h := actualReducedVertexSeries_mem_point_power n I a
  have hw : Finsupp.weight (actualCoordinateWeight (univ : Set (Fin n))) a.val=normalExponentDegree a.val := by
    simp [Finsupp.weight_eq_sum,actualCoordinateWeight,normalExponentDegree]
  rwa [hw] at h

/-- ONLY original ideal/pivot data choose ONE true normalized canonical family
before all coefficients, with actual entire-source-diagram low-jet normality. -/
theorem exists_canonical_zero_point_normalized_low_jet (I : Ideal R) (e : Fin n) :
    ∃ H : actualInitialVertices MonomialOrder.degLex I → R,
      (∀ a,(MvPowerSeries.X e)^(normalExponentDegree a.val)*H a=
        actualFormalBlowup univ e (fun _ => 0) (actualReducedVertexSeries MonomialOrder.degLex I a)) ∧
      (∀ a β,normalExponentDegree β<normalExponentDegree a.val →
        β∈actualInitialDiagram MonomialOrder.degLex I → MvPowerSeries.coeff β (H a)=0) ∧
      (∀ a β,β∈actualInitialDiagram MonomialOrder.degLex I →
        MvPolynomial.coeff β (MvPowerSeries.truncTotal (normalExponentDegree a.val) (H a))=0) ∧
      ∀ a r,r<normalExponentDegree a.val → ∀ β,β∈actualInitialDiagram MonomialOrder.degLex I →
        MvPowerSeries.coeff β (MvPowerSeries.homogeneousComponent r (H a))=0 := by
  let H (a : actualInitialVertices MonomialOrder.degLex I) := actualNormalizedFormalMember univ e (mem_univ e)
    (fun _ => 0) (normalExponentDegree a.val) (actualReducedVertexSeries MonomialOrder.degLex I a) (canonical_point_power I a)
  have hH (a : actualInitialVertices MonomialOrder.degLex I) : (MvPowerSeries.X e)^(normalExponentDegree a.val)*H a=
      actualFormalBlowup univ e (fun _ => 0) (actualReducedVertexSeries MonomialOrder.degLex I a) :=
    actualNormalizedFormalMember_spec univ e (mem_univ e) (fun _ => 0) _ _ _
  have hLow (a : actualInitialVertices MonomialOrder.degLex I) (β : Fin n →₀ ℕ)
      (hβ : normalExponentDegree β<normalExponentDegree a.val) (hΓ : β∈actualInitialDiagram MonomialOrder.degLex I) :=
    canonical_zero_point_low_coefficient_zero_on_source_diagram I a e (H a) (hH a) β hβ hΓ
  refine ⟨H,hH,hLow,?_,?_⟩
  · intro a β hΓ
    rw [MvPowerSeries.coeff_truncTotal_eq_ite]
    split_ifs with hβ
    · apply hLow a β _ hΓ
      simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hβ
    · rfl
  · intro a r hr β hΓ
    rw [MvPowerSeries.coeff_homogeneousComponent]
    split_ifs with hβ
    · apply hLow a β _ hΓ
      have hd : normalExponentDegree β=r := by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hβ
      omega
    · rfl

end
end TranscendentalNakamaye.Pending.HironakaActualZeroPointReducedTail
