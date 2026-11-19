import Hironaka.Resolution.HironakaActualCanonicalTriangularShear

/-! Whole proper-degree-prefix cone complements survive a genuine source
shear whose pivot is absent from the source vertices. No prefix GB, finite
jet replacement, contact certificate or target diagram is assumed. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualInheritedPrefixShearSupport
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualFormalBlowupAllDirections HironakaActualCanonicalTriangularShear
variable {n : ℕ}

private def shearPolynomialCoordinate (f : Fin n) (b : Fin n → ℂ) (i : Fin n) :
    MvPolynomial (Fin n) ℂ :=
  MvPolynomial.X i+if i ≠ f then MvPolynomial.C (b i)*MvPolynomial.X f else 0

private theorem shearPolynomialCoordinate_coe (f : Fin n) (b : Fin n → ℂ) (i : Fin n) :
    (shearPolynomialCoordinate f b i : MvPowerSeries (Fin n) ℂ)=
      actualFormalCenterShearCoordinates Set.univ f b i := by
  by_cases hi : i=f <;> simp [shearPolynomialCoordinate,actualFormalCenterShearCoordinates,hi]

private def shearPolynomialProduct (f : Fin n) (b : Fin n → ℂ) (α : Fin n →₀ ℕ) :
    MvPolynomial (Fin n) ℂ := α.prod (fun i k => (shearPolynomialCoordinate f b i)^k)

private theorem shearPolynomialProduct_coe (f : Fin n) (b : Fin n → ℂ) (α : Fin n →₀ ℕ) :
    (shearPolynomialProduct f b α : MvPowerSeries (Fin n) ℂ)=
      α.prod (fun i k => (actualFormalCenterShearCoordinates Set.univ f b i)^k) := by
  change MvPolynomial.coeToMvPowerSeries.ringHom
      (∏ i ∈ α.support,(shearPolynomialCoordinate f b i)^(α i))=
    ∏ i ∈ α.support,(actualFormalCenterShearCoordinates Set.univ f b i)^(α i)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow]
  exact congrArg (fun F : MvPowerSeries (Fin n) ℂ => F^(α i)) (shearPolynomialCoordinate_coe f b i)

private theorem shearPolynomialCoordinate_degreeOf_le (f : Fin n) (b : Fin n → ℂ)
    (i j : Fin n) (hi : i ≠ f) :
    (shearPolynomialCoordinate f b j).degreeOf i ≤ if j=i then 1 else 0 := by
  dsimp only [shearPolynomialCoordinate]
  apply (MvPolynomial.degreeOf_add_le i _ _).trans
  apply max_le
  · by_cases hj : j=i
    · subst j
      simp only [MvPolynomial.degreeOf_X_self,if_true,le_refl]
    · simp only [MvPolynomial.degreeOf_X,Ne.symm hj,if_false,zero_le]
  · by_cases hj : j ≠ f
    · rw [if_pos hj]
      exact (MvPolynomial.degreeOf_C_mul_le (MvPolynomial.X f) i (b j)).trans
        (by rw [MvPolynomial.degreeOf_X_of_ne hi]; exact Nat.zero_le _)
    · rw [if_neg hj,MvPolynomial.degreeOf_zero]
      exact Nat.zero_le _

private theorem shearPolynomialProduct_degreeOf_le (f : Fin n) (b : Fin n → ℂ)
    (α : Fin n →₀ ℕ) (i : Fin n) (hi : i ≠ f) :
    (shearPolynomialProduct f b α).degreeOf i ≤ α i := by
  have hsum : (∑ j ∈ α.support,α j*(if j=i then 1 else 0))=α i := by
    by_cases hs : i ∈ α.support
    · simp [hs]
    · have hz : α i=0 := Finsupp.notMem_support_iff.mp hs
      simp [hs,hz]
  calc
    _ ≤ ∑ j ∈ α.support,((shearPolynomialCoordinate f b j)^(α j)).degreeOf i :=
      MvPolynomial.degreeOf_prod_le i α.support _
    _ ≤ ∑ j ∈ α.support,α j*(if j=i then 1 else 0) := by
      apply Finset.sum_le_sum
      intro j _
      exact (MvPolynomial.degreeOf_pow_le i _ _).trans
        (Nat.mul_le_mul_left (α j) (shearPolynomialCoordinate_degreeOf_le f b i j hi))
    _=α i := hsum

private theorem shear_coordinate_product_support_le (f : Fin n) (b : Fin n → ℂ)
    (α γ : Fin n →₀ ℕ)
    (hγ : MvPowerSeries.coeff γ
      (α.prod (fun i k => (actualFormalCenterShearCoordinates Set.univ f b i)^k)) ≠ 0)
    (i : Fin n) (hi : i ≠ f) : γ i ≤ α i := by
  have hpoly : MvPolynomial.coeff γ (shearPolynomialProduct f b α) ≠ 0 := by
    rwa [← shearPolynomialProduct_coe,MvPolynomial.coeff_coe] at hγ
  exact (MvPolynomial.le_degreeOf_of_mem_support i (MvPolynomial.mem_support_iff.mpr hpoly)).trans
    (shearPolynomialProduct_degreeOf_le f b α i hi)

/-- The entire proper-prefix support of the SAME member survives the true
source shear. The pivot condition is a source vertex condition only. -/
theorem actualFormalCenterShear_proper_prefix_support
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (f : Fin n) (w : Fin n → ℂ)
    (hf : ∀ c : actualInitialVertices MonomialOrder.degLex K, c.val f = 0)
    (μ : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : ∀ c : actualInitialVertices MonomialOrder.degLex K,
      normalExponentDegree c.val < μ → ∀ α, c.val ≤ α → MvPowerSeries.coeff α F = 0) :
    ∀ c : actualInitialVertices MonomialOrder.degLex K,
      normalExponentDegree c.val < μ → ∀ γ, c.val ≤ γ →
        MvPowerSeries.coeff γ (actualFormalCenterShear Set.univ f w F) = 0 := by
  intro c hc γ hcγ
  rw [actualFormalCenterShear, MvPowerSeries.substAlgHom_apply,
    MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero
      (actualFormalCenterShearCoordinates_constant_zero Set.univ f w)) F γ]
  apply finsum_eq_zero_of_forall_eq_zero
  intro α
  by_cases hz : MvPowerSeries.coeff γ
      (α.prod (fun i k => actualFormalCenterShearCoordinates Set.univ f w i ^ k)) = 0
  · rw [hz, smul_zero]
  · have hcα : c.val ≤ α := by
      intro i
      by_cases hi : i = f
      · subst i
        rw [hf c]
        exact Nat.zero_le _
      · exact (hcγ i).trans (shear_coordinate_product_support_le f w α γ hz i hi)
    rw [hF c hc α hcα, zero_smul]

end
end Hironaka.HironakaActualInheritedPrefixShearSupport
