import Hironaka.Resolution.HironakaG1ClosedNormalJet
import Hironaka.Resolution.HironakaG1ClosedNormalSelector

/-! Native historical laws for adjoining the literal degree-one normal equation. -/
set_option autoImplicit false
open Set Classical

namespace Hironaka.HironakaG1ClosedNormalLaws
noncomputable section

open HolGerm HironakaActualCauchyMonomialDivision
  HironakaActualHistoricalWholeJetFrames HironakaActualFixedInheritedSelector
  HironakaActualHistoricalNormalizedWeakPresentation HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualOriginalFormalHSTransfer
  HironakaG11PresLineFormal HironakaG11PresLineContact
  HironakaG1ClosedNormalDivision HironakaG1ClosedNormalJet HironakaG1ClosedNormalSelector
  HironakaActualWeightedCoefficientCompression

variable {n k : ℕ} {V : Finset (Fin n →₀ ℕ)}

/-- Enumerate the new degree-one equation first and retain the old enumeration. -/
def normalEnumeration (a : Fin k ≃ V) : Fin (k+1) ≃ normalVertices V := by
  let f : Fin (k+1) → normalVertices V := Fin.cons (normalVertex V) (fun j => oldVertex (a j))
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    revert y
    refine Fin.cases ?_ (fun i => ?_) x
    · intro y
      refine Fin.cases (fun _ => rfl) (fun j hj => ?_) y
      exact (normalVertex_ne_old (a j) hj).elim
    · intro y
      refine Fin.cases (fun hi => ?_) (fun j hij => ?_) y
      · exact (normalVertex_ne_old (a i) hi.symm).elim
      · exact congrArg Fin.succ (a.injective (Subtype.ext
          (liftExp_injective (congrArg Subtype.val hij))))
  · intro v
    rcases normalVertices_cases v with rfl | ⟨x,rfl⟩
    · exact ⟨0,rfl⟩
    · exact ⟨(a.symm x).succ, congrArg oldVertex (a.apply_symm_apply x)⟩

@[simp] theorem normalEnumeration_zero (a : Fin k ≃ V) :
    normalEnumeration a 0 = normalVertex V := rfl

@[simp] theorem normalEnumeration_succ (a : Fin k ≃ V) (j : Fin k) :
    normalEnumeration a j.succ = oldVertex (a j) := rfl

theorem normalVertices_positive (hPos : ∀ v : V, 0 < normalExponentDegree v.val) :
    ∀ v : normalVertices V, 0 < normalExponentDegree v.val := by
  intro v
  rcases normalVertices_cases v with rfl | ⟨x,rfl⟩
  · simp only [normalVertex, normalExponent_degree, Nat.zero_lt_one]
  · simpa only [oldVertex, normalExponentDegree_liftExp] using hPos x

theorem normalEnumeration_words (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (hw : ∀ i, wordExponent (w i) = (a i).val) :
    ∀ j, wordExponent (normalWords w j) = (normalEnumeration a j).val := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · exact wordExponent_wordOfExponent _
  · change wordExponent (liftWord (w i)) = liftExp (a i).val
    rw [wordExponent_liftWord, hw i]

theorem normalWords_owner (w : Fin k → CoordinateWord n)
    (hOwn : ∀ i, historicalOwner w (wordExponent (w i)) = some i) :
    ∀ j, historicalOwner (normalWords w) (wordExponent (normalWords w j)) = some j := by
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · refine normalOwner_of_one_le w _ ?_
    change 1 ≤ wordExponent (normalWord n) (Fin.last n)
    rw [normalWord, wordExponent_wordOfExponent, Finsupp.single_eq_same]
  · change historicalOwner (normalWords w) (wordExponent (liftWord (w i))) = some i.succ
    rw [wordExponent_liftWord]
    exact (normalOwner_liftExp_iff w _ i).mpr (hOwn i)

private theorem normalTaylor_family (a : Fin k ≃ V) (Γ : V → HolGerm (ComplexModel n)) :
    (fun j => actualUnshiftedTaylorAlgHom (n+1) (normalGerms Γ (normalEnumeration a j))) =
      normalFamily (fun i => actualUnshiftedTaylorAlgHom n (Γ (a i))) := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [normalEnumeration_zero, normalGerms_normal, actualUnshiftedTaylor_coordinate]
    rfl
  · rw [normalEnumeration_succ, normalGerms_old, actualTaylor_tangentPullback_one]
    rfl

/-- All historical laws for the actual analytic extension. The inputs are the
original analytic germs with their inherited words, positive degrees and
existing whole and prefix laws. The target laws are produced internally. -/
theorem actualHistoricalFivePointLaws_closedNormal
    (S : ActualFixedInheritedSelector V) (a : Fin k ≃ V) (w : Fin k → CoordinateWord n)
    (Γ : V → HolGerm (ComplexModel n)) (hw : ∀ i, wordExponent (w i) = (a i).val)
    (hPos : ∀ v : V, 0 < normalExponentDegree v.val)
    (h : ActualHistoricalFivePointLaws S a w Γ) :
    ActualHistoricalFivePointLaws (normalSelector S) (normalEnumeration a)
      (normalWords w) (normalGerms Γ) := by
  obtain ⟨hOrders,hWhole,hPrefix,hDivision,hSelector,hSupport⟩ := h
  let G := fun i => actualUnshiftedTaylorAlgHom n (Γ (a i))
  have hG := normalTaylor_family a Γ
  refine ⟨?_, ?_, ?_, ?_, ?_, historicalWholePrefixSupport_normalGerms Γ hPos hSupport⟩
  · intro j
    have hGj := congrFun hG j
    rw [hGj]
    refine Fin.cases ?_ (fun i => ?_) j
    · change MvPowerSeries.X (Fin.last n) ∈ genuineFormalVariables (n+1) ^
        normalExponentDegree (wordExponent (normalWord n)) ∧
        MvPowerSeries.X (Fin.last n) ∉ genuineFormalVariables (n+1) ^
          (normalExponentDegree (wordExponent (normalWord n))+1)
      rw [normalWord, wordExponent_wordOfExponent, normalExponent_degree]
      refine ⟨?_, ?_⟩
      · rw [pow_one]
        exact Ideal.subset_span ⟨Fin.last n,rfl⟩
      · intro hm
        have hz := (mem_genuineFormalVariables_pow_iff_coefficients_zero (n+1) 2 _).mp hm
          (normalExponent n) (by rw [normalExponent_degree]; omega)
        simp [MvPowerSeries.coeff_X] at hz
    · change MvPowerSeries.rename (Fin.castAdd 1) (G i) ∈ genuineFormalVariables (n+1) ^
        normalExponentDegree (wordExponent (liftWord (w i))) ∧
        MvPowerSeries.rename (Fin.castAdd 1) (G i) ∉ genuineFormalVariables (n+1) ^
          (normalExponentDegree (wordExponent (liftWord (w i)))+1)
      simp only [wordExponent_liftWord, normalExponentDegree_liftExp,
        rename_mem_genuineFormalVariables_pow_iff]
      exact hOrders i
  · rw [hG]
    intro q
    exact historicalWholeJetMap_closedNormal_bijective w G q (hWhole q)
  · rw [hG]
    apply historicalDegreePrefixFrames_closedNormal w G
    · intro i
      rw [hw]
      exact hPos (a i)
    · exact fun i => (hOrders i).1
    · exact hPrefix
  · rw [hG]
    exact historicalWholeSupportedDivision_closedNormal w G hDivision
  · intro q
    refine ⟨normalSelector_contact S Γ q (hSelector q).1, ?_⟩
    rw [normalSelector_jacobian_det S Γ q hPos]
    exact (hSelector q).2

/-- The closed extension preserves the literal product common mark. -/
theorem weightedCommonMark_closedNormal (a : Fin k ≃ V) :
    weightedCommonMark (fun v : normalVertices V => normalExponentDegree v.val) =
      weightedCommonMark (fun v : V => normalExponentDegree v.val) := by
  unfold weightedCommonMark
  rw [← (normalEnumeration a).prod_comp (fun v => normalExponentDegree v.val),
    ← a.prod_comp (fun v => normalExponentDegree v.val), Fin.prod_univ_succ]
  simp only [normalEnumeration_zero, normalVertex, normalExponent_degree, one_mul,
    normalEnumeration_succ, oldVertex, normalExponentDegree_liftExp]

open HironakaRelativeNormalIdeal in
/-- The whole analytic compression is the inherited entire ideal extended by
the actual linear normal equation to the unchanged common mark. -/
theorem weightedCompression_closedNormal (a : Fin k ≃ V) (Γ : V → HolGerm (ComplexModel n)) :
    weightedCompression (fun v : normalVertices V => normalExponentDegree v.val) (normalGerms Γ) =
      Ideal.map (tangentPullback n 1).toRingHom
        (weightedCompression (fun v : V => normalExponentDegree v.val) Γ) ⊔
        Ideal.span {(HironakaHolomorphicJetMonomialSpan.coordinateGerm (Fin.last n)) ^
          weightedCommonMark (fun v : V => normalExponentDegree v.val)} := by
  let d := weightedCommonMark (fun v : V => normalExponentDegree v.val)
  have hg₀ : normalGerms Γ (normalVertex V) ^
      (d / normalExponentDegree (normalVertex V).val) =
      (HironakaHolomorphicJetMonomialSpan.coordinateGerm (Fin.last n)) ^ d := by
    rw [normalGerms_normal]
    simp only [normalVertex, normalExponent_degree, Nat.div_one]
  have hg (v : V) : normalGerms Γ (oldVertex v) ^
      (d / normalExponentDegree (oldVertex v).val) =
      tangentPullback n 1 (Γ v ^ (d / normalExponentDegree v.val)) := by
    rw [normalGerms_old, map_pow]
    simp only [oldVertex, normalExponentDegree_liftExp]
  unfold weightedCompression
  rw [weightedCommonMark_closedNormal a, Ideal.map_span, ← Set.range_comp, ← Ideal.span_union]
  apply congrArg Ideal.span
  ext F
  constructor
  · rintro ⟨v,rfl⟩
    rcases normalVertices_cases v with rfl | ⟨x,rfl⟩
    · exact Or.inr (Set.mem_singleton_iff.mpr hg₀)
    · exact Or.inl ⟨x,(hg x).symm⟩
  · rintro (⟨v,rfl⟩ | h)
    · exact ⟨oldVertex v,hg v⟩
    · exact ⟨normalVertex V,hg₀.trans (Set.mem_singleton_iff.mp h).symm⟩

#print axioms actualHistoricalFivePointLaws_closedNormal
#print axioms weightedCompression_closedNormal

end
end Hironaka.HironakaG1ClosedNormalLaws
