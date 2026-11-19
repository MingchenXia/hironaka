import Hironaka.Resolution.HironakaActualHistoricalCentreFilteredDivision
import Hironaka.Resolution.HironakaActualHistoricalNormalizedSupport

/-! Genuine marked normalization of the SAME entire supported historical
quotients. Their ORIGINAL owner partition survives, without a derivative
degree bound or a target whole-ideal supported-division/HS certificate. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalNormalizedQuotients
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualCanonicalBlockJacobian
  HironakaActualFormalBlowupMemberGeneration HironakaActualFormalCoordinatePowerDivision
  HironakaActualHistoricalWholeJetFrames HironakaActualHistoricalPrefixJetFrames
  HironakaActualHistoricalFormalSupportedDivision HironakaActualHistoricalCentreFilteredDivision
  HironakaActualHistoricalNormalizedSupport
  HironakaActualCauchyMonomialDivision HironakaActualOriginalFormalHSTransfer

variable {n k : ℕ}

private theorem earlier_owner_of_ne
    (w : Fin k → CoordinateWord n) (j : Fin k) (β : Fin n →₀ ℕ)
    (ho : historicalOwner w (β+wordExponent (w j))≠some j) :
    ∃i : Fin k,i<j ∧ wordExponent (w i)≤β+wordExponent (w j) := by
  by_contra! hEarlier
  apply ho
  apply (historicalOwner_eq_some_iff w _ j).mpr
  refine ⟨?_,(avoidsCones_take_iff w j _).mpr hEarlier⟩
  intro i
  simp only [Finsupp.add_apply]
  omega

private theorem quotient_cone_of_earlier
    (w : Fin k → CoordinateWord n) (j i : Fin k) (hij : i<j)
    (γ : Fin n →₀ ℕ) (hγ : wordExponent (w i)-wordExponent (w j)≤γ) :
    historicalOwner w (γ+wordExponent (w j))≠some j := by
  intro hOwner
  have hAvoid:=(avoidsCones_take_iff w j _).mp
    ((historicalOwner_eq_some_iff w _ j).mp hOwner).2 i hij
  apply hAvoid
  intro x
  have hx:=hγ x
  simp only [Finsupp.tsub_apply,Finsupp.add_apply] at hx ⊢
  omega

/-- A SAME whole supported quotient retains its EXACT original owner
region through actual normalization, at unrestricted forbidden order. -/
theorem actualNormalizedFormalMember_historical_quotient_support
    (w : Fin k → CoordinateWord n) (j : Fin k)
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hHeads : ∀i : Fin k,(↑(wordExponent (w i)).support : Set (Fin n))⊆A\{e})
    (d : ℕ) (Q : MvPowerSeries (Fin n) ℂ)
    (hQ : Q∈actualFormalCoordinateIdeal n A^d)
    (hSupport : ∀β,historicalOwner w (β+wordExponent (w j))≠some j → MvPowerSeries.coeff β Q=0) :
    ∀β,historicalOwner w (β+wordExponent (w j))≠some j →
      MvPowerSeries.coeff β (actualNormalizedFormalMember A e he b d Q hQ)=0 := by
  intro β hβ
  obtain ⟨i,hij,hi⟩:=earlier_owner_of_ne w j β hβ
  let δ:=wordExponent (w i)-wordExponent (w j)
  have hδβ : δ≤β:=by
    intro x
    have hx:=hi x
    simp only [δ,Finsupp.tsub_apply,Finsupp.add_apply] at hx ⊢
    omega
  have hδ : (↑δ.support : Set (Fin n))⊆A\{e}:=by
    intro x hx
    apply hHeads i
    apply Finsupp.mem_support_iff.mpr
    intro hz
    have hle : δ x≤wordExponent (w i) x:=tsub_le_self
    exact (Finsupp.mem_support_iff.mp hx) (Nat.eq_zero_of_le_zero (by simpa only [hz] using hle))
  have hCone : ∀γ : Fin n →₀ ℕ,δ≤γ → MvPowerSeries.coeff γ Q=0:=by
    intro γ hγ
    exact hSupport γ (quotient_cone_of_earlier w j i hij γ hγ)
  exact actualNormalizedFormalMember_cone_zero_all_orders A e he b δ hδ d Q hQ hCone β hδβ

private theorem weight_eq_degree_of_heads
    (A : Set (Fin n)) (α : Fin n →₀ ℕ) (hα : (↑α.support : Set (Fin n))⊆A) :
    Finsupp.weight (actualCoordinateWeight A) α=normalExponentDegree α := by
  rw [Finsupp.weight_eq_sum]
  unfold normalExponentDegree
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : α i=0
  · simp only [hi,zero_smul]
  · simp only [actualCoordinateWeight,if_pos (hα (Finsupp.mem_support_iff.mpr hi)),smul_eq_mul,mul_one]

/-- EVERY actual normalized source ideal member has its SAME whole old
supported division. The quotients are internally normalized from the
actual filtered inverse; target marks/frames/division/HS are absent. -/
theorem actualNormalizedFormalMember_supported_historical_division
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupported : HistoricalWholeSupportedDivision w g)
    (A : Set (Fin n)) (e : Fin n) (he : e∈A) (b : Fin n → ℂ)
    (hHeads : ∀j : Fin k,(↑(wordExponent (w j)).support : Set (Fin n))⊆A\{e})
    (hcentre : ∀j,g j∈actualFormalCoordinateIdeal n A^normalExponentDegree (wordExponent (w j)))
    (d : ℕ) (hd : ∀j,normalExponentDegree (wordExponent (w j))≤d)
    (F : MvPowerSeries (Fin n) ℂ) (hI : F∈Ideal.span (range g))
    (hF : F∈actualFormalCoordinateIdeal n A^d) :
    ∃Q : Fin k → MvPowerSeries (Fin n) ℂ,
      actualNormalizedFormalMember A e he b d F hF=
        ∑j,Q j*actualNormalizedFormalMember A e he b
          (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j) ∧
      ∀j β,historicalOwner w (β+wordExponent (w j))≠some j → MvPowerSeries.coeff β (Q j)=0 := by
  have hWeight (j : Fin k) : Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j))=
      normalExponentDegree (wordExponent (w j)):=
    weight_eq_degree_of_heads A _ (fun i hi=>(hHeads j hi).1)
  have hcentreW : ∀j,g j∈actualFormalCoordinateIdeal n A^
      Finsupp.weight (actualCoordinateWeight A) (wordExponent (w j)):=by
    simpa only [hWeight] using hcentre
  have hDiv:=historical_formal_centre_power_whole_division w g hmarked hwhole hSupported A hcentreW d F hI hF
  let Q₀:=fun j=>historicalFormalQuotient w g hmarked hwhole j F
  have hQ₀ (j : Fin k) : Q₀ j∈actualFormalCoordinateIdeal n A^
      (d-normalExponentDegree (wordExponent (w j))):=by
    simpa only [hWeight] using hDiv.2 j
  let Q:=fun j=>actualNormalizedFormalMember A e he b
    (d-normalExponentDegree (wordExponent (w j))) (Q₀ j) (hQ₀ j)
  let G:=fun j=>actualNormalizedFormalMember A e he b
    (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j)
  have hTerm (j : Fin k) : actualFormalBlowup A e b (Q₀ j*g j)=
      (MvPowerSeries.X e)^d*(Q j*G j) := by
    rw [map_mul,←actualNormalizedFormalMember_spec A e he b
      (d-normalExponentDegree (wordExponent (w j))) (Q₀ j) (hQ₀ j),
      ←actualNormalizedFormalMember_spec A e he b
      (normalExponentDegree (wordExponent (w j))) (g j) (hcentre j)]
    change ((MvPowerSeries.X e)^(d-normalExponentDegree (wordExponent (w j)))*Q j)*
      ((MvPowerSeries.X e)^normalExponentDegree (wordExponent (w j))*G j)=_
    calc
      _=(MvPowerSeries.X e)^((d-normalExponentDegree (wordExponent (w j)))+
          normalExponentDegree (wordExponent (w j)))*(Q j*G j):=by rw [pow_add];ring
      _=(MvPowerSeries.X e)^d*(Q j*G j):=by rw [Nat.sub_add_cancel (hd j)]
  have hSum : (MvPowerSeries.X e)^d*(∑j,Q j*G j)=actualFormalBlowup A e b F := by
    rw [hDiv.1,map_sum,Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _=>(hTerm j).symm
  refine ⟨Q,(actualNormalizedFormalMember_unique A e he b d F hF (∑j,Q j*G j) hSum).symm,?_⟩
  intro j
  exact actualNormalizedFormalMember_historical_quotient_support w j A e he b hHeads
    (d-normalExponentDegree (wordExponent (w j))) (Q₀ j) (hQ₀ j)
    (historicalFormalQuotient_support w g hmarked hwhole F j)

end
end Hironaka.HironakaActualHistoricalNormalizedQuotients
