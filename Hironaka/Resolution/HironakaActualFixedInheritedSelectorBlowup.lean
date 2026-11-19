import Hironaka.Resolution.HironakaActualFixedInheritedSelector
import Hironaka.Resolution.HironakaActualMultiDerivativeBlowup
import Hironaka.Resolution.HironakaActualInheritedNextBlockGraph

/-! All normalized contacts use the same historical selector. The generic
normalized higher-derivative and mark-one theorems are reused unchanged. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFixedInheritedSelectorBlowup
noncomputable section
open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaActualFixedInheritedSelector HironakaActualRelativeNormalJetDivision
  HironakaActualFormalInitialDiagram HironakaActualCoefficientPresentationCentrePower
  HironakaActualFormalCoordinatePowerDivision HironakaActualFormalBlowupMemberGeneration
  HironakaActualMultiDerivativeBlowup HironakaActualNormalizedBlowupDerivative
  HironakaActualInheritedAnalyticBlockJacobian HironakaActualRelativeStandardnessBlockSupport
  HironakaActualInheritedNextBlockGraph HironakaActualAnalyticBlockGraphTranslation
  HironakaActualCanonicalBlockJacobian
variable {n : ℕ} {K : Ideal (MvPowerSeries (Fin n) ℂ)}

private theorem legal_support
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (k : ℕ) (A : Set (Fin n)) (e : Fin n)
    (hB : actualDegreePrefixVariables MonomialOrder.degLex K k ⊆ A \ {e})
    (j : actualDegreePrefixVariables MonomialOrder.degLex K k) :
    (↑(fixedSelectorBeta S (fixedSelectorBlockEssential k j)).support : Set (Fin n)) ⊆ A \ {e} := by
  intro i hi
  apply hB
  by_contra h
  exact (Finsupp.mem_support_iff.mp hi) (fixedSelector_beta_support S k j i h)

private theorem normalized_congr (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    {q r : ℕ} {F H : MvPowerSeries (Fin n) ℂ} (hqr : q = r) (hFH : F = H)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ q) (hH : H ∈ actualFormalCoordinateIdeal n A ^ r) :
    actualNormalizedFormalMember A e he b q F hF = actualNormalizedFormalMember A e he b r H hH := by
  cases hqr
  cases hFH
  rfl

theorem actualFixedSelectorDerivative_centre_one
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (k : ℕ) (A : Set (Fin n)) (e : Fin n)
    (hB : actualDegreePrefixVariables MonomialOrder.degLex K k ⊆ A \ {e})
    (hpower : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈
      actualFormalCoordinateIdeal n A ^ normalExponentDegree a.val)
    (j : actualDegreePrefixVariables MonomialOrder.degLex K k) :
    actualUnshiftedTaylorAlgHom n (actualFixedSelectorDerivative S G.germs (fixedSelectorBlockEssential k j)) ∈
      actualFormalCoordinateIdeal n A ^ 1 := by
  let v := fixedSelectorBlockEssential k j
  have hd := fixedSelector_beta_degree S v
  have hmark : 1 + normalExponentDegree (fixedSelectorBeta S v) = normalExponentDegree (S.selected v).val := by omega
  rw [actualFixedSelectorDerivative, actualTaylor_actualAnalyticMultiDerivative]
  exact actualMultiDerivative_mem_centre_add A (fixedSelectorBeta S v)
    (fun i hi => (legal_support S k A e hB j hi).1) 1
    (actualUnshiftedTaylorAlgHom n (G.germs (S.selected v)))
    (by simpa only [hmark] using hpower (S.selected v))

def actualNormalizedFixedSelectorDerivative
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (k : ℕ) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hpower : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈
      actualFormalCoordinateIdeal n A ^ normalExponentDegree a.val)
    (j : actualDegreePrefixVariables MonomialOrder.degLex K k) : MvPowerSeries (Fin n) ℂ :=
  let v := fixedSelectorBlockEssential k j
  actualFormalMultiDerivative (fixedSelectorBeta S v)
    (actualNormalizedFormalMember A e he b (normalExponentDegree (S.selected v).val)
      (actualUnshiftedTaylorAlgHom n (G.germs (S.selected v))) (hpower (S.selected v)))

set_option maxHeartbeats 800000 in
theorem actualNormalizedFixedSelectorDerivative_eq
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (k : ℕ) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hB : actualDegreePrefixVariables MonomialOrder.degLex K k ⊆ A \ {e})
    (hpower : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈
      actualFormalCoordinateIdeal n A ^ normalExponentDegree a.val)
    (j : actualDegreePrefixVariables MonomialOrder.degLex K k) :
    actualNormalizedFixedSelectorDerivative G S k A e he b hpower j =
      actualNormalizedFormalMember A e he b 1
        (actualUnshiftedTaylorAlgHom n (actualFixedSelectorDerivative S G.germs (fixedSelectorBlockEssential k j)))
        (actualFixedSelectorDerivative_centre_one G S k A e hB hpower j) := by
  let v := fixedSelectorBlockEssential k j
  let a := S.selected v
  let β := fixedSelectorBeta S v
  have hd : normalExponentDegree β + 1 = normalExponentDegree a.val := fixedSelector_beta_degree S v
  have hle : normalExponentDegree β ≤ normalExponentDegree a.val := by omega
  have hsub : normalExponentDegree a.val - normalExponentDegree β = 1 := by omega
  have h := actualMultiDerivative_actualNormalizedFormalMember A e he b β (legal_support S k A e hB j)
    (normalExponentDegree a.val) hle (actualUnshiftedTaylorAlgHom n (G.germs a)) (hpower a)
  have hN := normalized_congr A e he b hsub
    (actualTaylor_actualAnalyticMultiDerivative β (G.germs a)).symm
    (actualMultiDerivative_mem_centre_sub A β (fun i hi => (legal_support S k A e hB j hi).1)
      (normalExponentDegree a.val) hle (actualUnshiftedTaylorAlgHom n (G.germs a)) (hpower a))
    (actualFixedSelectorDerivative_centre_one G S k A e hB hpower j)
  exact h.trans hN

private theorem constantCoeff_pderiv_eq_linear (i : Fin n) (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv ℂ i F) = MvPowerSeries.coeff (Finsupp.single i 1) F := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv,
    zero_add, Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one]

private theorem actualTaylor_linear_coefficient (F : HolGerm (ComplexModel n)) (i : Fin n) :
    MvPowerSeries.coeff (Finsupp.single i 1) (actualUnshiftedTaylorAlgHom n F) =
      HolGerm.eval (actualAnalyticCoordinateDerivative i F) := by
  have h := congrArg (MvPowerSeries.coeff 0) (actualTaylor_actualAnalyticCoordinateDerivative i F)
  rw [HironakaActualCauchyCoefficientLimits.actualTaylor_coeff_zero,
    MvPowerSeries.coeff_pderiv, zero_add, Finsupp.zero_apply] at h
  simpa only [Nat.cast_zero, zero_add, mul_one] using h.symm

def actualNormalizedFixedSelectorJacobian
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (k : ℕ) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hpower : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈
      actualFormalCoordinateIdeal n A ^ normalExponentDegree a.val) :
    Matrix (actualDegreePrefixVariables MonomialOrder.degLex K k) (actualDegreePrefixVariables MonomialOrder.degLex K k) ℂ :=
  fun j i => MvPowerSeries.constantCoeff (MvPowerSeries.pderiv ℂ i.val
    (actualNormalizedFixedSelectorDerivative G S k A e he b hpower j))

theorem actualNormalizedFixedSelectorJacobian_eq
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (k : ℕ) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hB : actualDegreePrefixVariables MonomialOrder.degLex K k ⊆ A \ {e})
    (hpower : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈
      actualFormalCoordinateIdeal n A ^ normalExponentDegree a.val) :
    actualNormalizedFixedSelectorJacobian G S k A e he b hpower = actualFixedSelectorJacobian S G.germs k := by
  ext j i
  change MvPowerSeries.constantCoeff (MvPowerSeries.pderiv ℂ i.val
    (actualNormalizedFixedSelectorDerivative G S k A e he b hpower j)) =
      HolGerm.eval (actualAnalyticCoordinateDerivative i.val
        (actualFixedSelectorDerivative S G.germs (fixedSelectorBlockEssential k j)))
  rw [actualNormalizedFixedSelectorDerivative_eq G S k A e he b hB hpower j,
    constantCoeff_pderiv_eq_linear,
    normalized_mark_one_linear_coefficient A e he b i.val (hB i.property).1
      (by simpa only [Set.mem_singleton_iff] using (hB i.property).2)]
  exact actualTaylor_linear_coefficient _ _

theorem actualNormalizedFixedSelectorDerivative_mem_block
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (k : ℕ) (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hB : actualDegreePrefixVariables MonomialOrder.degLex K k ⊆ A \ {e})
    (hpower : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈
      actualFormalCoordinateIdeal n A ^ normalExponentDegree a.val)
    (hadapt : actualFixedSelectorContactAt S G.germs k)
    (hb : ∀ i ∈ actualDegreePrefixVariables MonomialOrder.degLex K k, b i = 0)
    (j : actualDegreePrefixVariables MonomialOrder.degLex K k) :
    actualNormalizedFixedSelectorDerivative G S k A e he b hpower j ∈
      actualFormalCoordinateIdeal n (actualDegreePrefixVariables MonomialOrder.degLex K k) := by
  rw [actualNormalizedFixedSelectorDerivative_eq G S k A e he b hB hpower j]
  have hm := Ideal.mem_map_of_mem (actualUnshiftedTaylorAlgHom n).toRingHom (hadapt j)
  rw [map_actualAnalyticCoordinateBlockIdeal_actualTaylor] at hm
  exact normalized_mark_one_mem_actualBlock A (actualDegreePrefixVariables MonomialOrder.degLex K k)
    e he hB b hb _ hm

set_option maxHeartbeats 800000 in
theorem actual_normalized_fixed_selector_all_blocks_contact
    (G : ActualAnalyticInheritedFamily n 0 K)
    (S : ActualFixedInheritedSelector (actualInitialVertices MonomialOrder.degLex K))
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hpower : ∀ a, actualUnshiftedTaylorAlgHom n (G.germs a) ∈
      actualFormalCoordinateIdeal n A ^ normalExponentDegree a.val)
    (hB : ∀ k, actualDegreePrefixVariables MonomialOrder.degLex K k ⊆ A \ {e})
    (hadapt : ∀ k, actualFixedSelectorContactAt S G.germs k)
    (hb : ∀ k, ∀ i ∈ actualDegreePrefixVariables MonomialOrder.degLex K k, b i = 0) :
    ∀ k,
      (∀ j : actualDegreePrefixVariables MonomialOrder.degLex K k,
        actualNormalizedFixedSelectorDerivative G S k A e he b hpower j ∈
          actualFormalCoordinateIdeal n (actualDegreePrefixVariables MonomialOrder.degLex K k)) ∧
      actualNormalizedFixedSelectorJacobian G S k A e he b hpower = actualFixedSelectorJacobian S G.germs k ∧
      (actualNormalizedFixedSelectorJacobian G S k A e he b hpower).det ≠ 0 := by
  intro k
  refine ⟨actualNormalizedFixedSelectorDerivative_mem_block G S k A e he b (hB k) hpower (hadapt k) (hb k),
    actualNormalizedFixedSelectorJacobian_eq G S k A e he b (hB k) hpower, ?_⟩
  rw [actualNormalizedFixedSelectorJacobian_eq G S k A e he b (hB k) hpower]
  exact actualFixedSelectorJacobian_det_ne_zero S G.germs (fun a => G.monic a) (fun a β h => G.lower a β h) k

end
end Hironaka.HironakaActualFixedInheritedSelectorBlowup
