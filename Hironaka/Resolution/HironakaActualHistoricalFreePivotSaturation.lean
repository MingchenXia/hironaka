import Hironaka.Resolution.HironakaActualHistoricalCentreFilteredDivision

/-! The SAME entire historical supported inverse supplies actual free
exceptional saturation. No target HS, colon equality or shift-covariance
certificate is an input. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHistoricalFreePivotSaturation
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualHistoricalWholeJetFrames
  HironakaActualHistoricalPrefixJetFrames HironakaActualHistoricalFormalSupportedDivision
  HironakaActualHistoricalCentreFilteredDivision HironakaActualCauchyMonomialDivision
  HironakaActualOriginalFormalHSTransfer

variable {n k : ℕ}

private theorem singleton_weight_zero
    (e : Fin n) (α : Fin n →₀ ℕ) (he : α e=0) :
    Finsupp.weight (actualCoordinateWeight ({e} : Set (Fin n))) α=0 := by
  rw [Finsupp.weight_eq_sum]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i=e
  · subst i
    simp only [he,zero_smul]
  · simp only [actualCoordinateWeight,mem_singleton_iff,if_neg hi,smul_eq_mul,mul_zero]

/-- Whole historical division DERIVES cancellation of a free exceptional
factor, by actual singleton-centre filtration of its SAME quotients. -/
theorem historical_ideal_free_pivot_cancel
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupported : HistoricalWholeSupportedDivision w g)
    (e : Fin n) (hFree : ∀j,wordExponent (w j) e=0)
    (F : MvPowerSeries (Fin n) ℂ)
    (hI : MvPowerSeries.X e*F∈Ideal.span (range g)) : F∈Ideal.span (range g) := by
  have hWeight (j : Fin k) : Finsupp.weight (actualCoordinateWeight ({e} : Set (Fin n)))
      (wordExponent (w j))=0:=singleton_weight_zero e _ (hFree j)
  have hCentre : ∀j,g j∈actualFormalCoordinateIdeal n ({e} : Set (Fin n))^
      Finsupp.weight (actualCoordinateWeight ({e} : Set (Fin n))) (wordExponent (w j)):=by
    intro j
    rw [hWeight,pow_zero,Ideal.one_eq_top]
    exact Submodule.mem_top
  have hPower : MvPowerSeries.X e*F∈actualFormalCoordinateIdeal n ({e} : Set (Fin n))^1:=by
    rw [pow_one]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨e,rfl,rfl⟩)
  have hDiv:=historical_formal_centre_power_whole_division w g hmarked hwhole hSupported
    ({e} : Set (Fin n)) hCentre 1 (MvPowerSeries.X e*F) hI hPower
  let Q₀:=fun j=>historicalFormalQuotient w g hmarked hwhole j (MvPowerSeries.X e*F)
  have hFactor (j : Fin k) : ∃q : MvPowerSeries (Fin n) ℂ,q*MvPowerSeries.X e=Q₀ j := by
    have hm:=hDiv.2 j
    rw [hWeight,Nat.sub_zero,pow_one] at hm
    have hCoordinate : actualFormalCoordinateIdeal n ({e} : Set (Fin n))=
        Ideal.span {MvPowerSeries.X e}:=by
      simp only [actualFormalCoordinateIdeal,image_singleton]
    rw [hCoordinate] at hm
    exact Ideal.mem_span_singleton'.mp hm
  choose Q hQ using hFactor
  have hCancel : MvPowerSeries.X e*F=MvPowerSeries.X e*(∑j,Q j*g j) := by
    calc
      _=∑j,Q₀ j*g j:=hDiv.1
      _=∑j,MvPowerSeries.X e*(Q j*g j):=by
        apply Finset.sum_congr rfl
        intro j _
        rw [←hQ j]
        ring
      _=MvPowerSeries.X e*(∑j,Q j*g j):=(Finset.mul_sum _ _ _).symm
  have hF : F=∑j,Q j*g j:=mul_left_cancel₀ (actualFormalExceptional_ne_zero e) hCancel
  rw [hF]
  exact Ideal.sum_mem _ fun j _=>Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j,rfl⟩)

/-- Every actual exceptional power is cancelled in the entire SAME family
ideal. This is genuine produced saturation, not a supplied colon law. -/
theorem historical_ideal_free_pivot_power_iff
    (w : Fin k → CoordinateWord n) (g : Fin k → MvPowerSeries (Fin n) ℂ)
    (hmarked : ∀j,g j∈genuineFormalVariables n^normalExponentDegree (wordExponent (w j)))
    (hwhole : ∀q,Function.Bijective (historicalWholeJetMap w g q))
    (hSupported : HistoricalWholeSupportedDivision w g)
    (e : Fin n) (hFree : ∀j,wordExponent (w j) e=0)
    (d : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    (MvPowerSeries.X e)^d*F∈Ideal.span (range g) ↔ F∈Ideal.span (range g) := by
  constructor
  · intro hI
    induction d with
    | zero => simpa only [pow_zero,one_mul] using hI
    | succ d ih =>
      apply ih
      apply historical_ideal_free_pivot_cancel w g hmarked hwhole hSupported e hFree ((MvPowerSeries.X e)^d*F)
      simpa only [pow_succ',mul_assoc] using hI
  · intro hI
    exact Ideal.mul_mem_left _ _ hI

end
end Hironaka.HironakaActualHistoricalFreePivotSaturation
