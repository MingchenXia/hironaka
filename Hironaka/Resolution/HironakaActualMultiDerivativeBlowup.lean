import Hironaka.Resolution.HironakaActualNormalizedBlowupDerivative
import Hironaka.Resolution.HironakaActualCanonicalBlockJacobian

/-!
# The SAME actual higher canonical derivatives through a legal blowup

The accepted actualFormalMultiDerivative, its whole coefficient formula and
its genuine coordinate-derivative recursion are reused literally. All derivative
centre powers and normalized identities are produced from source powers.
The original selected vertices and the original block Jacobian are unchanged.
-/

set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaActualMultiDerivativeBlowup

noncomputable section

open HironakaRelativeNormalMonomialBasis HironakaActualFormalInitialDiagram
  HironakaActualReducedFormalStandardBasis HironakaActualRelativeStandardnessBlockSupport
  HironakaActualCanonicalBlockJacobian HironakaActualFormalCoordinatePowerDivision
  HironakaActualFormalBlowupMemberGeneration HironakaActualNormalizedBlowupDerivative

variable {n : ℕ}

private theorem degree_zero : normalExponentDegree (0 : Fin n →₀ ℕ) = 0 := by
  simp [normalExponentDegree]

private theorem degree_add_single (β : Fin n →₀ ℕ) (i : Fin n) :
    normalExponentDegree (β + Finsupp.single i 1) = normalExponentDegree β + 1 := by
  simp [normalExponentDegree,Finsupp.add_apply,Finset.sum_add_distrib]

private theorem weight_eq_degree_of_support (A : Set (Fin n)) (β : Fin n →₀ ℕ)
    (hβ : (↑β.support : Set (Fin n)) ⊆ A) :
    Finsupp.weight (actualCoordinateWeight A) β = normalExponentDegree β := by
  rw [Finsupp.weight_eq_sum]
  unfold normalExponentDegree
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : β i = 0
  · simp only [hi,zero_smul]
  · have hiA : i ∈ A := hβ (Finsupp.mem_support_iff.mpr hi)
    simp only [actualCoordinateWeight,if_pos hiA,smul_eq_mul,mul_one]

/-- The accepted SAME actual higher derivative internally acquires the lower
whole centre power from genuine original centre-power membership. -/
theorem actualMultiDerivative_mem_centre_add (A : Set (Fin n)) (β : Fin n →₀ ℕ)
    (hβ : (↑β.support : Set (Fin n)) ⊆ A) (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ (q + normalExponentDegree β)) :
    actualFormalMultiDerivative β F ∈ actualFormalCoordinateIdeal n A ^ q := by
  apply (mem_actualFormalCoordinateIdeal_pow_iff A q _).mpr
  intro α hα
  have hw : Finsupp.weight (actualCoordinateWeight A) (α + β) =
      Finsupp.weight (actualCoordinateWeight A) α + normalExponentDegree β := by
    rw [map_add,weight_eq_degree_of_support A β hβ]
  rw [coeff_actualFormalMultiDerivative,
    (mem_actualFormalCoordinateIdeal_pow_iff A _ F).mp hF _ (by rw [hw]; omega),zero_mul]

/-- The actual subtraction-mark source derivative membership is produced internally. -/
theorem actualMultiDerivative_mem_centre_sub (A : Set (Fin n)) (β : Fin n →₀ ℕ)
    (hβ : (↑β.support : Set (Fin n)) ⊆ A) (μ : ℕ) (hβμ : normalExponentDegree β ≤ μ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ) :
    actualFormalMultiDerivative β F ∈ actualFormalCoordinateIdeal n A ^ (μ - normalExponentDegree β) :=
  actualMultiDerivative_mem_centre_add A β hβ (μ - normalExponentDegree β) F
    (by simpa only [Nat.sub_add_cancel hβμ] using hF)

private theorem normalized_congr (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) {q r : ℕ} {F G : MvPowerSeries (Fin n) ℂ}
    (hq : q = r) (hFG : F = G)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ q)
    (hG : G ∈ actualFormalCoordinateIdeal n A ^ r) :
    actualNormalizedFormalMember A e he b q F hF =
      actualNormalizedFormalMember A e he b r G hG := by
  cases hq
  cases hFG
  rfl

private theorem multiDerivative_normalized_add (A : Set (Fin n)) (e : Fin n) (he : e ∈ A)
    (b : Fin n → ℂ) (β : Fin n →₀ ℕ) (hβ : (↑β.support : Set (Fin n)) ⊆ A \ {e})
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F ∈ actualFormalCoordinateIdeal n A ^ (q + normalExponentDegree β)) :
    actualFormalMultiDerivative β (actualNormalizedFormalMember A e he b (q + normalExponentDegree β) F hF) =
      actualNormalizedFormalMember A e he b q (actualFormalMultiDerivative β F)
        (actualMultiDerivative_mem_centre_add A β (fun _i hi => (hβ hi).1) q F hF) := by
  induction β using (measure normalExponentDegree).wf.induction generalizing q F with
  | h β ih =>
    by_cases hzero : β = 0
    · subst β
      have hmark : q + normalExponentDegree (0 : Fin n →₀ ℕ) = q := by
        rw [degree_zero,Nat.add_zero]
      exact (actualFormalMultiDerivative_zero _).trans
        (normalized_congr A e he b hmark (actualFormalMultiDerivative_zero F).symm hF
          (actualMultiDerivative_mem_centre_add A 0 (fun _i hi => (hβ hi).1) q F hF))
    · obtain ⟨i,hi⟩ : ∃ i, β i ≠ 0 := by
        by_contra! hz
        exact hzero (Finsupp.ext hz)
      have hsingle : Finsupp.single i 1 ≤ β := by
        intro j
        by_cases hj : j = i
        · subst j
          simpa only [Finsupp.single_eq_same] using Nat.one_le_iff_ne_zero.mpr hi
        · simp [Finsupp.single_eq_of_ne hj]
      let γ := β - Finsupp.single i 1
      have hdecomp : γ + Finsupp.single i 1 = β := tsub_add_cancel_of_le hsingle
      have hdegree : normalExponentDegree γ + 1 = normalExponentDegree β := by
        have hd := congrArg normalExponentDegree hdecomp
        simpa only [degree_add_single] using hd
      have hγlt : normalExponentDegree γ < normalExponentDegree β := by omega
      have hγle : γ ≤ β := tsub_le_self
      have hγ : (↑γ.support : Set (Fin n)) ⊆ A \ {e} := by
        intro j hj
        have hjne : γ j ≠ 0 := Finsupp.mem_support_iff.mp hj
        have hjβ : β j ≠ 0 := by
          intro hz
          exact hjne (Nat.eq_zero_of_le_zero (by simpa only [hz] using hγle j))
        exact hβ (Finsupp.mem_support_iff.mpr hjβ)
      have hiA : i ∈ A := (hβ (Finsupp.mem_support_iff.mpr hi)).1
      have hie : i ≠ e := by
        simpa only [Set.mem_singleton_iff] using (hβ (Finsupp.mem_support_iff.mpr hi)).2
      have hmark : (q+1) + normalExponentDegree γ = q + normalExponentDegree β := by omega
      have hFγ : F ∈ actualFormalCoordinateIdeal n A ^ ((q+1) + normalExponentDegree γ) := by
        simpa only [hmark] using hF
      have hind := ih γ hγlt hγ (q+1) F hFγ
      have hγpow := actualMultiDerivative_mem_centre_add A γ
        (fun j hj => (hγ hj).1) (q+1) F hFγ
      have hstep := pderiv_actualNormalizedFormalMember A e he b i hiA hie q
        (actualFormalMultiDerivative γ F) hγpow
      have hboth := (congrArg (MvPowerSeries.pderiv ℂ i) hind).trans hstep
      have hN := normalized_congr A e he b hmark rfl hFγ hF
      have hleft : MvPowerSeries.pderiv ℂ i
          (actualFormalMultiDerivative γ
            (actualNormalizedFormalMember A e he b ((q+1) + normalExponentDegree γ) F hFγ)) =
          actualFormalMultiDerivative β
            (actualNormalizedFormalMember A e he b (q + normalExponentDegree β) F hF) := by
        rw [← actualFormalMultiDerivative_add_single,hdecomp,hN]
      have hDF : MvPowerSeries.pderiv ℂ i (actualFormalMultiDerivative γ F) =
          actualFormalMultiDerivative β F := by
        rw [← actualFormalMultiDerivative_add_single,hdecomp]
      have hright := normalized_congr A e he b rfl hDF
        (pderiv_mem_actualCentrePower A i hiA q (actualFormalMultiDerivative γ F) hγpow)
        (actualMultiDerivative_mem_centre_add A β (fun j hj => (hβ hj).1) q F hF)
      exact hleft.symm.trans (hboth.trans hright)

/-- The literal accepted Dβ commutes with actual normalization in every legal
direction, with the exact lower mark and internally produced source membership. -/
theorem actualMultiDerivative_actualNormalizedFormalMember
    (A : Set (Fin n)) (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (β : Fin n →₀ ℕ) (hβ : (↑β.support : Set (Fin n)) ⊆ A \ {e})
    (μ : ℕ) (hβμ : normalExponentDegree β ≤ μ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualFormalCoordinateIdeal n A ^ μ) :
    actualFormalMultiDerivative β (actualNormalizedFormalMember A e he b μ F hF) =
      actualNormalizedFormalMember A e he b (μ - normalExponentDegree β) (actualFormalMultiDerivative β F)
        (actualMultiDerivative_mem_centre_sub A β (fun _i hi => (hβ hi).1) μ hβμ F hF) := by
  have hF' : F ∈ actualFormalCoordinateIdeal n A ^
      ((μ - normalExponentDegree β) + normalExponentDegree β) := by
    simpa only [Nat.sub_add_cancel hβμ] using hF
  have h := multiDerivative_normalized_add A e he b β hβ (μ - normalExponentDegree β) F hF'
  have hN := normalized_congr A e he b (Nat.sub_add_cancel hβμ) rfl hF' hF
  exact (congrArg (actualFormalMultiDerivative β) hN).symm.trans h

private theorem selected_degree (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (j : actualCanonicalEssentialVariables m K) :
    normalExponentDegree (actualCanonicalDerivativeExponent m K j) + 1 =
      normalExponentDegree (actualCanonicalDerivativeVertex m K j).val := by
  have hd := congrArg normalExponentDegree (actualCanonicalDerivativeExponent_add_single m K j)
  simpa only [degree_add_single] using hd

private theorem selected_support_legal (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) (A : Set (Fin n)) (e : Fin n)
    (hB : actualDegreePrefixVariables m K k ⊆ A \ {e}) (j : actualDegreePrefixVariables m K k) :
    (↑(actualCanonicalDerivativeExponent m K (actualCanonicalBlockEssentialVariable m K k j)).support :
      Set (Fin n)) ⊆ A \ {e} := by
  intro i hi
  apply hB
  by_contra hiB
  exact (Finsupp.mem_support_iff.mp hi)
    (actualCanonicalDerivativeExponent_support m K k j i hiB)

/-- The SAME source selected canonical derivative gets actual centre-power one
from its original canonical member's genuine source power. -/
theorem canonical_selected_derivative_centre_one (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) (A : Set (Fin n)) (e : Fin n)
    (hB : actualDegreePrefixVariables m K k ⊆ A \ {e}) (j : actualDegreePrefixVariables m K k)
    (hR : actualReducedVertexSeries m K (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)) ∈ actualFormalCoordinateIdeal n A ^
      normalExponentDegree (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)).val) :
    actualCanonicalEssentialDerivative m K (actualCanonicalBlockEssentialVariable m K k j) ∈
      actualFormalCoordinateIdeal n A ^ 1 := by
  let v := actualCanonicalBlockEssentialVariable m K k j
  have hd := selected_degree m K v
  have hmark : 1 + normalExponentDegree (actualCanonicalDerivativeExponent m K v) =
      normalExponentDegree (actualCanonicalDerivativeVertex m K v).val := by omega
  exact actualMultiDerivative_mem_centre_add A (actualCanonicalDerivativeExponent m K v)
    (fun i hi => (selected_support_legal m K k A e hB j hi).1) 1
    (actualReducedVertexSeries m K (actualCanonicalDerivativeVertex m K v))
    (by simpa only [hmark] using hR)

/-- The actual transformed family applies the SAME accepted derivative to the
SAME source canonical member's literal normalized transform. -/
def actualNormalizedCanonicalBlockDerivative (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hR : ∀ j : actualDegreePrefixVariables m K k,
      actualReducedVertexSeries m K (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)) ∈ actualFormalCoordinateIdeal n A ^
      normalExponentDegree (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)).val)
    (j : actualDegreePrefixVariables m K k) : MvPowerSeries (Fin n) ℂ :=
  actualFormalMultiDerivative (actualCanonicalDerivativeExponent m K (actualCanonicalBlockEssentialVariable m K k j))
    (actualNormalizedFormalMember A e he b
      (normalExponentDegree (actualCanonicalDerivativeVertex m K (actualCanonicalBlockEssentialVariable m K k j)).val)
      (actualReducedVertexSeries m K (actualCanonicalDerivativeVertex m K (actualCanonicalBlockEssentialVariable m K k j)))
      (hR j))

/-- The actual transformed selected function is the SAME original selected
function with genuine mark-one normalization; neither family is reselected. -/
theorem actualNormalizedCanonicalBlockDerivative_eq (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hB : actualDegreePrefixVariables m K k ⊆ A \ {e})
    (hR : ∀ j : actualDegreePrefixVariables m K k,
      actualReducedVertexSeries m K (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)) ∈ actualFormalCoordinateIdeal n A ^
      normalExponentDegree (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)).val)
    (j : actualDegreePrefixVariables m K k) :
    actualNormalizedCanonicalBlockDerivative m K k A e he b hR j =
      actualNormalizedFormalMember A e he b 1
        (actualCanonicalEssentialDerivative m K (actualCanonicalBlockEssentialVariable m K k j))
        (canonical_selected_derivative_centre_one m K k A e hB j (hR j)) := by
  let v := actualCanonicalBlockEssentialVariable m K k j
  have hd := selected_degree m K v
  have hle : normalExponentDegree (actualCanonicalDerivativeExponent m K v) ≤
      normalExponentDegree (actualCanonicalDerivativeVertex m K v).val := by omega
  have hsub : normalExponentDegree (actualCanonicalDerivativeVertex m K v).val -
      normalExponentDegree (actualCanonicalDerivativeExponent m K v) = 1 := by omega
  have h := actualMultiDerivative_actualNormalizedFormalMember A e he b
    (actualCanonicalDerivativeExponent m K v) (selected_support_legal m K k A e hB j)
    (normalExponentDegree (actualCanonicalDerivativeVertex m K v).val) hle
    (actualReducedVertexSeries m K (actualCanonicalDerivativeVertex m K v)) (hR j)
  have hN := normalized_congr A e he b hsub rfl
    (actualMultiDerivative_mem_centre_sub A (actualCanonicalDerivativeExponent m K v)
      (fun i hi => (selected_support_legal m K k A e hB j hi).1)
      (normalExponentDegree (actualCanonicalDerivativeVertex m K v).val) hle
      (actualReducedVertexSeries m K (actualCanonicalDerivativeVertex m K v)) (hR j))
    (canonical_selected_derivative_centre_one m K k A e hB j (hR j))
  exact h.trans hN

private theorem constantCoeff_pderiv_eq_linear (i : Fin n) (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv ℂ i F) =
      MvPowerSeries.coeff (Finsupp.single i 1) F := by
  simp only [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,MvPowerSeries.coeff_pderiv,
    zero_add,Finsupp.zero_apply,Nat.cast_zero,zero_add,mul_one]

/-- The actual finite origin Jacobian of the literal transformed selected family. -/
def actualNormalizedCanonicalBlockJacobian (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hR : ∀ j : actualDegreePrefixVariables m K k,
      actualReducedVertexSeries m K (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)) ∈ actualFormalCoordinateIdeal n A ^
      normalExponentDegree (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)).val) :
    Matrix (actualDegreePrefixVariables m K k) (actualDegreePrefixVariables m K k) ℂ :=
  fun j i => MvPowerSeries.constantCoeff (MvPowerSeries.pderiv ℂ i.val
    (actualNormalizedCanonicalBlockDerivative m K k A e he b hR j))

/-- Every entry is the SAME actual original block Jacobian, for arbitrary b. -/
theorem actualNormalizedCanonicalBlockJacobian_eq (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hB : actualDegreePrefixVariables m K k ⊆ A \ {e})
    (hR : ∀ j : actualDegreePrefixVariables m K k,
      actualReducedVertexSeries m K (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)) ∈ actualFormalCoordinateIdeal n A ^
      normalExponentDegree (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)).val) :
    actualNormalizedCanonicalBlockJacobian m K k A e he b hR = actualCanonicalBlockJacobian m K k := by
  ext j i
  change MvPowerSeries.constantCoeff (MvPowerSeries.pderiv ℂ i.val
      (actualNormalizedCanonicalBlockDerivative m K k A e he b hR j)) =
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv ℂ i.val
      (actualCanonicalEssentialDerivative m K (actualCanonicalBlockEssentialVariable m K k j)))
  rw [actualNormalizedCanonicalBlockDerivative_eq m K k A e he b hB hR j,
    constantCoeff_pderiv_eq_linear,constantCoeff_pderiv_eq_linear]
  have hiA : i.val ∈ A := (hB i.property).1
  have hie : i.val ≠ e := by simpa only [Set.mem_singleton_iff] using (hB i.property).2
  exact normalized_mark_one_linear_coefficient A e he b i.val hiA hie _ _

/-- The transformed finite block's nonzero determinant is internally inherited
from the SAME existing factorial-product determinant, with no rank input. -/
theorem actualNormalizedCanonicalBlockJacobian_det_ne_zero (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hB : actualDegreePrefixVariables m K k ⊆ A \ {e})
    (hR : ∀ j : actualDegreePrefixVariables m K k,
      actualReducedVertexSeries m K (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)) ∈ actualFormalCoordinateIdeal n A ^
      normalExponentDegree (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)).val) :
    (actualNormalizedCanonicalBlockJacobian m K k A e he b hR).det ≠ 0 := by
  rw [actualNormalizedCanonicalBlockJacobian_eq m K k A e he b hB hR]
  exact actualCanonicalBlockJacobian_det_ne_zero m K k

/-- A genuinely source-adapted SAME selected family stays in the SAME block
coordinate ideal. The source adaptation and b|B=0 remain explicit. -/
theorem actualNormalizedCanonicalBlockDerivative_mem_block (m : MonomialOrder (Fin n))
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (k : ℕ) (A : Set (Fin n))
    (e : Fin n) (he : e ∈ A) (b : Fin n → ℂ)
    (hB : actualDegreePrefixVariables m K k ⊆ A \ {e})
    (hR : ∀ j : actualDegreePrefixVariables m K k,
      actualReducedVertexSeries m K (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)) ∈ actualFormalCoordinateIdeal n A ^
      normalExponentDegree (actualCanonicalDerivativeVertex m K
        (actualCanonicalBlockEssentialVariable m K k j)).val)
    (hadapt : ∀ j : actualDegreePrefixVariables m K k,
      actualCanonicalEssentialDerivative m K (actualCanonicalBlockEssentialVariable m K k j) ∈
        actualFormalCoordinateIdeal n (actualDegreePrefixVariables m K k))
    (hb : ∀ i ∈ actualDegreePrefixVariables m K k, b i = 0)
    (j : actualDegreePrefixVariables m K k) :
    actualNormalizedCanonicalBlockDerivative m K k A e he b hR j ∈
      actualFormalCoordinateIdeal n (actualDegreePrefixVariables m K k) := by
  rw [actualNormalizedCanonicalBlockDerivative_eq m K k A e he b hB hR j]
  exact normalized_mark_one_mem_actualBlock A (actualDegreePrefixVariables m K k) e he hB b hb _ (hadapt j)

end

end Hironaka.HironakaActualMultiDerivativeBlowup
