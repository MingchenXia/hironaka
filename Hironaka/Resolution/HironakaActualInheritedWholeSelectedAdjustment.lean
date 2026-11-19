import Hironaka.Resolution.HironakaActualInheritedSelectedAnalyticDivision

/-! The specified whole Cauchy quotients keep their genuine disjoint owner
parts. This proves actual head preservation without assuming a selected
prefix ideal is a standard basis. Every selected germ stays literally fixed. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualInheritedWholeSelectedAdjustment
noncomputable section
attribute [local instance] Classical.propDecidable
open HolGerm HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualFormalInitialDiagram
  HironakaActualSelectedVertexHomogeneousBasis HironakaActualReducedFormalStandardBasis
  HironakaActualCauchyMonomialDivision HironakaActualCauchyDiagramPartition
  HironakaActualCauchyEnumeratedPartition HironakaActualRelativeNormalJetDivision
  HironakaActualInheritedSelectedAnalyticDivision
variable {d t : ℕ} {K : Ideal (MvPowerSeries (Fin (d+t)) ℂ)}

private theorem initialExponent_sum_of_strict_minimum {n : ℕ} {ι : Type*} [Fintype ι]
    (m : MonomialOrder (Fin n)) (S : ι → MvPowerSeries (Fin n) ℂ)
    (a : ι) (ha : S a ≠ 0)
    (hmin : ∀ b : ι, b ≠ a → ∀ hb : S b ≠ 0,
      m.toSyn (actualInitialExponent m (S a) ha) < m.toSyn (actualInitialExponent m (S b) hb)) :
    ∃ hsum : (∑ b : ι, S b) ≠ 0,
      actualInitialExponent m (∑ b : ι, S b) hsum = actualInitialExponent m (S a) ha := by
  let α := actualInitialExponent m (S a) ha
  have hc : MvPowerSeries.coeff α (∑ b : ι, S b) = MvPowerSeries.coeff α (S a) := by
    rw [map_sum]
    apply Finset.sum_eq_single a
    · intro b _ hba
      by_cases hb : S b = 0
      · rw [hb, map_zero]
      · exact coeff_eq_zero_of_lt_actualInitialExponent m (S b) hb α (hmin b hba hb)
    · intro hnot
      exact (hnot (Finset.mem_univ a)).elim
  have hlow : ∀ β, m.toSyn β < m.toSyn α → MvPowerSeries.coeff β (∑ b : ι, S b) = 0 := by
    intro β hβ
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro b _
    by_cases hb : S b = 0
    · rw [hb, map_zero]
    · by_cases hba : b = a
      · subst b
        exact coeff_eq_zero_of_lt_actualInitialExponent m (S a) ha β hβ
      · exact coeff_eq_zero_of_lt_actualInitialExponent m (S b) hb β
          (lt_trans hβ (hmin b hba hb))
  have hsum : (∑ b : ι, S b) ≠ 0 := by
    intro hz
    have h := hc
    rw [hz, map_zero] at h
    exact (actualInitialExponent_spec m (S a) ha).1 h.symm
  refine ⟨hsum, ?_⟩
  exact actualInitialExponent_eq_of_coefficients m _ hsum α
    (by rw [hc]; exact (actualInitialExponent_spec m (S a) ha).1) hlow

def actualInheritedSelectedQuotient (G : ActualAnalyticInheritedFamily d t K)
    (S : Set (actualInitialVertices MonomialOrder.degLex K))
    (a : actualInitialVertices MonomialOrder.degLex K) :
    Fin (inheritedSelectedCount K S) → HolGerm (ComplexModel (d+t)) :=
  (exists_actual_inherited_selected_analytic_division G S a).choose

def actualInheritedSelectedRemainder (G : ActualAnalyticInheritedFamily d t K)
    (S : Set (actualInitialVertices MonomialOrder.degLex K))
    (a : actualInitialVertices MonomialOrder.degLex K) : HolGerm (ComplexModel (d+t)) :=
  (exists_actual_inherited_selected_analytic_division G S a).choose_spec.choose

theorem actualInheritedSelectedDivision_spec (G : ActualAnalyticInheritedFamily d t K)
    (S : Set (actualInitialVertices MonomialOrder.degLex K))
    (a : actualInitialVertices MonomialOrder.degLex K) :
    G.germs a = (∑ j, actualInheritedSelectedQuotient G S a j *
      G.germs (inheritedSelectedEnumeration K S j).val) + actualInheritedSelectedRemainder G S a ∧
    (∀ j β, ¬ AvoidsCones ((List.ofFn (inheritedSelectedWords K S)).take j.val)
      (β + (inheritedSelectedEnumeration K S j).val.val) →
        MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t)
          (actualInheritedSelectedQuotient G S a j)) = 0) ∧
    ∀ β ∈ actualSelectedVertexDiagram K S,
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t)
        (actualInheritedSelectedRemainder G S a)) = 0 :=
  (exists_actual_inherited_selected_analytic_division G S a).choose_spec.choose_spec

def actualInheritedSelectedCorrection (G : ActualAnalyticInheritedFamily d t K)
    (S : Set (actualInitialVertices MonomialOrder.degLex K))
    (a : actualInitialVertices MonomialOrder.degLex K) : HolGerm (ComplexModel (d+t)) :=
  ∑ j, actualInheritedSelectedQuotient G S a j * G.germs (inheritedSelectedEnumeration K S j).val

private theorem word_mem_take_of_lt {n k : ℕ} (w : Fin k → CoordinateWord n)
    (i j : Fin k) (hij : i < j) : w i ∈ (List.ofFn w).take j.val := by
  apply List.mem_take_iff_getElem.mpr
  refine ⟨i.val, ?_, ?_⟩
  · simp only [List.length_ofFn]
    exact lt_min hij i.isLt
  · simp only [List.getElem_ofFn, Fin.eta]

private theorem inherited_germ_initial (G : ActualAnalyticInheritedFamily d t K)
    (a : actualInitialVertices MonomialOrder.degLex K) :
    ∃ hne : actualUnshiftedTaylorAlgHom (d+t) (G.germs a) ≠ 0,
      actualInitialExponent MonomialOrder.degLex (actualUnshiftedTaylorAlgHom (d+t) (G.germs a)) hne = a.val := by
  have hne : actualUnshiftedTaylorAlgHom (d+t) (G.germs a) ≠ 0 := by
    intro hz
    have hc := G.monic a
    rw [hz, map_zero] at hc
    exact zero_ne_one hc
  exact ⟨hne, actualInitialExponent_eq_of_coefficients MonomialOrder.degLex _ hne a.val
    (by rw [G.monic]; exact one_ne_zero) (G.lower a)⟩

private theorem correction_product_initial (G : ActualAnalyticInheritedFamily d t K)
    (S : Set (actualInitialVertices MonomialOrder.degLex K))
    (a : actualInitialVertices MonomialOrder.degLex K) (j : Fin (inheritedSelectedCount K S))
    (hj : actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedQuotient G S a j *
      G.germs (inheritedSelectedEnumeration K S j).val) ≠ 0) :
    ∃ hq : actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedQuotient G S a j) ≠ 0,
      actualInitialExponent MonomialOrder.degLex
        (actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedQuotient G S a j *
          G.germs (inheritedSelectedEnumeration K S j).val)) hj =
        actualInitialExponent MonomialOrder.degLex
          (actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedQuotient G S a j)) hq +
            (inheritedSelectedEnumeration K S j).val.val := by
  have hq : actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedQuotient G S a j) ≠ 0 := by
    intro hz
    apply hj
    rw [map_mul, hz, zero_mul]
  obtain ⟨hg, hhead⟩ := inherited_germ_initial G (inheritedSelectedEnumeration K S j).val
  refine ⟨hq, ?_⟩
  simpa only [map_mul, hhead] using actualInitialExponent_mul MonomialOrder.degLex
    (actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedQuotient G S a j))
    (actualUnshiftedTaylorAlgHom (d+t) (G.germs (inheritedSelectedEnumeration K S j).val)) hq hg

/-- The WHOLE actual quotient partition, rather than ideal membership, forces
distinct leading products. Their genuine finite minimum cannot cancel. -/
theorem actualInheritedSelectedCorrection_initial (G : ActualAnalyticInheritedFamily d t K)
    (S : Set (actualInitialVertices MonomialOrder.degLex K))
    (a : actualInitialVertices MonomialOrder.degLex K)
    (hC : actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedCorrection G S a) ≠ 0) :
    actualInitialExponent MonomialOrder.degLex
      (actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedCorrection G S a)) hC ∈
        actualSelectedVertexDiagram K S := by
  let m : MonomialOrder (Fin (d+t)) := MonomialOrder.degLex
  let T (j : Fin (inheritedSelectedCount K S)) := actualUnshiftedTaylorAlgHom (d+t)
    (actualInheritedSelectedQuotient G S a j * G.germs (inheritedSelectedEnumeration K S j).val)
  have hsum : actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedCorrection G S a) = ∑ j, T j := by
    rw [actualInheritedSelectedCorrection, map_sum]
  have hdistinct : ∀ i j : Fin (inheritedSelectedCount K S), i < j → ∀ hi : T i ≠ 0, ∀ hj : T j ≠ 0,
      actualInitialExponent m (T i) hi ≠ actualInitialExponent m (T j) hj := by
    intro i j hij hi hj heq
    obtain ⟨hqi, hpi⟩ := correction_product_initial G S a i hi
    obtain ⟨hqj, hpj⟩ := correction_product_initial G S a j hj
    let β := actualInitialExponent m (actualUnshiftedTaylorAlgHom (d+t)
      (actualInheritedSelectedQuotient G S a j)) hqj
    have hbad : ¬ AvoidsCones ((List.ofFn (inheritedSelectedWords K S)).take j.val)
        (β + (inheritedSelectedEnumeration K S j).val.val) := by
      intro havoid
      apply havoid (inheritedSelectedWords K S i)
        (word_mem_take_of_lt (inheritedSelectedWords K S) i j hij)
      rw [inheritedSelectedWords, wordExponent_wordOfExponent]
      have he : actualInitialExponent m (actualUnshiftedTaylorAlgHom (d+t)
          (actualInheritedSelectedQuotient G S a i)) hqi + (inheritedSelectedEnumeration K S i).val.val =
            β + (inheritedSelectedEnumeration K S j).val.val := by
        have he := heq
        change actualInitialExponent MonomialOrder.degLex
            (actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedQuotient G S a i *
              G.germs (inheritedSelectedEnumeration K S i).val)) hi =
          actualInitialExponent MonomialOrder.degLex
            (actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedQuotient G S a j *
              G.germs (inheritedSelectedEnumeration K S j).val)) hj at he
        rw [hpi, hpj] at he
        exact he
      rw [← he]
      intro p
      change (inheritedSelectedEnumeration K S i).val.val p ≤ _ + _
      omega
    have hz := (actualInheritedSelectedDivision_spec G S a).2.1 j β hbad
    exact (actualInitialExponent_spec m _ hqj).1 hz
  have hsome : ∃ j, T j ≠ 0 := by
    by_contra h
    push Not at h
    apply hC
    rw [hsum]
    exact Finset.sum_eq_zero (fun j _ => h j)
  let J := {j : Fin (inheritedSelectedCount K S) // T j ≠ 0}
  let : Fintype J := Fintype.ofFinite J
  have hJ : (Finset.univ : Finset J).Nonempty := by
    obtain ⟨j, hj⟩ := hsome
    exact ⟨⟨j, hj⟩, Finset.mem_univ _⟩
  let weight (j : J) := m.toSyn (actualInitialExponent m (T j.val) j.property)
  obtain ⟨j, _hj, hmin⟩ := (Finset.univ : Finset J).exists_min_image weight hJ
  have hstrict : ∀ i, i ≠ j.val → ∀ hi : T i ≠ 0,
      m.toSyn (actualInitialExponent m (T j.val) j.property) < m.toSyn (actualInitialExponent m (T i) hi) := by
    intro i hij hi
    have hle := hmin (⟨i, hi⟩ : J) (Finset.mem_univ _)
    apply lt_of_le_of_ne hle
    intro he
    have hexp := m.toSyn.injective he
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact hdistinct i j.val hlt hi j.property hexp.symm
    · exact hdistinct j.val i hgt j.property hi hexp
  obtain ⟨hne, hhead⟩ := initialExponent_sum_of_strict_minimum m T j.val j.property hstrict
  have hheadC : actualInitialExponent m
      (actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedCorrection G S a)) hC =
        actualInitialExponent m (T j.val) j.property := by
    simpa only [← hsum] using hhead
  obtain ⟨hq, hp⟩ := correction_product_initial G S a j.val j.property
  rw [hheadC, hp]
  refine ⟨(inheritedSelectedEnumeration K S j.val).val,
    (inheritedSelectedEnumeration K S j.val).property, ?_⟩
  intro p
  simp only [Finsupp.add_apply]
  omega

def actualInheritedWholeSelectedMember (G : ActualAnalyticInheritedFamily d t K)
    (S : Set (actualInitialVertices MonomialOrder.degLex K))
    (a : actualInitialVertices MonomialOrder.degLex K) : HolGerm (ComplexModel (d+t)) :=
  if a ∈ S then G.germs a else actualInheritedSelectedRemainder G S a

private theorem vertex_outside_selected_diagram
    (S : Set (actualInitialVertices MonomialOrder.degLex K))
    (a : actualInitialVertices MonomialOrder.degLex K) (ha : a ∉ S) :
    a.val ∉ actualSelectedVertexDiagram K S := by
  rintro ⟨b, hb, hba⟩
  have hbD : b.val ∈ actualInitialDiagram MonomialOrder.degLex K :=
    (mem_actualInitialDiagram_iff_vertex_le MonomialOrder.degLex K b.val).mpr ⟨b.val, b.property, le_rfl⟩
  have hmin : Minimal (· ∈ actualInitialDiagram MonomialOrder.degLex K) a.val := by
    simpa only [actualInitialVertices, Set.Finite.mem_toFinset, Set.mem_ofPred_eq] using a.property
  have hab := hmin.2 hbD hba
  have heq : b = a := Subtype.ext (le_antisymm hba hab)
  exact ha (heq ▸ hb)

/-- Genuine leading separation retains the SAME outside vertex head. -/
theorem actualInheritedWholeSelectedMember_initial (G : ActualAnalyticInheritedFamily d t K)
    (S : Set (actualInitialVertices MonomialOrder.degLex K))
    (a : actualInitialVertices MonomialOrder.degLex K) :
    ∃ hne : actualUnshiftedTaylorAlgHom (d+t) (actualInheritedWholeSelectedMember G S a) ≠ 0,
      actualInitialExponent MonomialOrder.degLex
        (actualUnshiftedTaylorAlgHom (d+t) (actualInheritedWholeSelectedMember G S a)) hne = a.val ∧
      MvPowerSeries.coeff a.val
        (actualUnshiftedTaylorAlgHom (d+t) (actualInheritedWholeSelectedMember G S a)) = 1 := by
  by_cases ha : a ∈ S
  · rw [actualInheritedWholeSelectedMember, if_pos ha]
    obtain ⟨hne, hhead⟩ := inherited_germ_initial G a
    exact ⟨hne, hhead, G.monic a⟩
  · rw [actualInheritedWholeSelectedMember, if_neg ha]
    let C := actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedCorrection G S a)
    let R := actualUnshiftedTaylorAlgHom (d+t) (actualInheritedSelectedRemainder G S a)
    have he : actualUnshiftedTaylorAlgHom (d+t) (G.germs a) = C + R := by
      simpa only [C, R, actualInheritedSelectedCorrection, map_add] using
        congrArg (actualUnshiftedTaylorAlgHom (d+t)) (actualInheritedSelectedDivision_spec G S a).1
    have hCzero : ∀ β, MonomialOrder.degLex.toSyn β ≤ MonomialOrder.degLex.toSyn a.val →
        MvPowerSeries.coeff β C = 0 := by
      intro β hβ
      by_cases hC : C = 0
      · rw [hC, map_zero]
      · have hD := actualInheritedSelectedCorrection_initial G S a hC
        have hheadgt : MonomialOrder.degLex.toSyn a.val <
            MonomialOrder.degLex.toSyn (actualInitialExponent MonomialOrder.degLex C hC) := by
          apply lt_of_not_ge
          intro hle
          rcases lt_or_eq_of_le hle with hlt | heq
          · have hgzero := G.lower a _ hlt
            have hrzero := (actualInheritedSelectedDivision_spec G S a).2.2 _ hD
            have hc := congrArg (MvPowerSeries.coeff (actualInitialExponent MonomialOrder.degLex C hC)) he
            rw [map_add, hgzero, hrzero, add_zero] at hc
            exact (actualInitialExponent_spec MonomialOrder.degLex C hC).1 hc.symm
          · have heq' := MonomialOrder.degLex.toSyn.injective heq
            exact vertex_outside_selected_diagram S a ha (by rwa [heq'] at hD)
        exact coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex C hC β (hβ.trans_lt hheadgt)
    have hcoeff : MvPowerSeries.coeff a.val R = 1 := by
      have hc := congrArg (MvPowerSeries.coeff a.val) he
      rw [map_add, G.monic, hCzero a.val le_rfl, zero_add] at hc
      exact hc.symm
    have hlower : ∀ β, MonomialOrder.degLex.toSyn β < MonomialOrder.degLex.toSyn a.val →
        MvPowerSeries.coeff β R = 0 := by
      intro β hβ
      have hc := congrArg (MvPowerSeries.coeff β) he
      rw [map_add, G.lower a β hβ, hCzero β hβ.le, zero_add] at hc
      exact hc.symm
    have hne : R ≠ 0 := by
      intro hz
      have hc := hcoeff
      rw [hz, map_zero] at hc
      exact zero_ne_one hc
    exact ⟨hne, actualInitialExponent_eq_of_coefficients MonomialOrder.degLex R hne a.val
      (by rw [hcoeff]; exact one_ne_zero) hlower, hcoeff⟩

/-- The SAME literal label type and actual monic/lower data are retained. -/
def actualInheritedWholeSelectedFamily (G : ActualAnalyticInheritedFamily d t K)
    (S : Set (actualInitialVertices MonomialOrder.degLex K)) : ActualAnalyticInheritedFamily d t K where
  germs := actualInheritedWholeSelectedMember G S
  monic := fun a => (actualInheritedWholeSelectedMember_initial G S a).choose_spec.2
  lower := by
    intro a β hβ
    obtain ⟨hne, hhead, _⟩ := actualInheritedWholeSelectedMember_initial G S a
    apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex _ hne β
    rwa [hhead]

/-- Selected germs are literally fixed. Every higher remainder avoids the
ENTIRE selected cone union, and both whole analytic spans coincide. -/
theorem actual_inherited_whole_selected_adjustment (G : ActualAnalyticInheritedFamily d t K)
    (S : Set (actualInitialVertices MonomialOrder.degLex K)) :
    (∀ a ∈ S, (actualInheritedWholeSelectedFamily G S).germs a = G.germs a) ∧
    Ideal.span (range (actualInheritedWholeSelectedFamily G S).germs) = Ideal.span (range G.germs) ∧
    ∀ a ∉ S, ∀ β ∈ actualSelectedVertexDiagram K S,
      MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t)
        ((actualInheritedWholeSelectedFamily G S).germs a)) = 0 := by
  have hfixed : ∀ a ∈ S, (actualInheritedWholeSelectedFamily G S).germs a = G.germs a := by
    intro a ha
    exact if_pos ha
  refine ⟨hfixed, ?_, ?_⟩
  · let I := Ideal.span (range G.germs)
    let J := Ideal.span (range (actualInheritedWholeSelectedFamily G S).germs)
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro F ⟨a, rfl⟩
      by_cases ha : a ∈ S
      · rw [hfixed a ha]
        exact Ideal.subset_span ⟨a, rfl⟩
      · have hcorr : actualInheritedSelectedCorrection G S a ∈ I := by
          apply I.sum_mem
          intro j _
          exact I.mul_mem_left _ (Ideal.subset_span ⟨(inheritedSelectedEnumeration K S j).val, rfl⟩)
        have hm := I.sub_mem (Ideal.subset_span ⟨a, rfl⟩) hcorr
        have he := (actualInheritedSelectedDivision_spec G S a).1
        change G.germs a = actualInheritedSelectedCorrection G S a + actualInheritedSelectedRemainder G S a at he
        have hr : G.germs a - actualInheritedSelectedCorrection G S a = actualInheritedSelectedRemainder G S a := by
          rw [he]
          ring
        rw [hr] at hm
        change actualInheritedWholeSelectedMember G S a ∈ I
        rw [actualInheritedWholeSelectedMember, if_neg ha]
        exact hm
    · apply Ideal.span_le.mpr
      rintro F ⟨a, rfl⟩
      by_cases ha : a ∈ S
      · rw [← hfixed a ha]
        exact Ideal.subset_span ⟨a, rfl⟩
      · have hcorr : actualInheritedSelectedCorrection G S a ∈ J := by
          apply J.sum_mem
          intro j _
          rw [← hfixed _ (inheritedSelectedEnumeration K S j).property]
          exact J.mul_mem_left _ (Ideal.subset_span ⟨(inheritedSelectedEnumeration K S j).val, rfl⟩)
        have he := (actualInheritedSelectedDivision_spec G S a).1
        rw [he]
        apply J.add_mem hcorr
        have hnew := Ideal.subset_span (show (actualInheritedWholeSelectedFamily G S).germs a ∈
          range (actualInheritedWholeSelectedFamily G S).germs from ⟨a, rfl⟩)
        change actualInheritedWholeSelectedMember G S a ∈ J at hnew
        rwa [actualInheritedWholeSelectedMember, if_neg ha] at hnew
  · intro a ha β hβ
    change MvPowerSeries.coeff β (actualUnshiftedTaylorAlgHom (d+t)
      (actualInheritedWholeSelectedMember G S a)) = 0
    rw [actualInheritedWholeSelectedMember, if_neg ha]
    exact (actualInheritedSelectedDivision_spec G S a).2.2 β hβ

end
end Hironaka.HironakaActualInheritedWholeSelectedAdjustment
