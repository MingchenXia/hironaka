import Hironaka.Resolution.HironakaActualExceptionalFibreJetClasses

/-! Actual bounded normal tails are separated by the SAME literal exceptional jet map. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualExceptionalNormalJetSeparation
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalStandardMonomialHS
  HironakaActualExceptionalFibreJetClasses
variable {n : ℕ}

/-- The true exceptional/source index equivalence retains the literal monomial numerator. -/
theorem actualExceptionalJetVector_eq_source_monomial
    (I K J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (q : ℕ)
    (hCyl : ∀ α : Fin n →₀ ℕ,
      α ∉ actualInitialDiagram MonomialOrder.degLex K ↔
        α.erase e ∉ actualInitialDiagram MonomialOrder.degLex (actualExceptionalFibreIdeal J e))
    (a : actualExceptionalJetIndex J e q) :
    actualExceptionalJetVector I J e q a=
      Ideal.Quotient.mk (I ⊔ genuineFormalVariables n ^ q)
        (MvPowerSeries.monomial
          (actualExceptionalJetIndexEquivSource K J e q hCyl a).val.val 1) := by
  change Ideal.Quotient.mk _ ((MvPowerSeries.X e)^a.1.val *
      MvPowerSeries.monomial a.2.val.val 1)=
    Ideal.Quotient.mk _ (MvPowerSeries.monomial (Finsupp.single e a.1.val+a.2.val.val) 1)
  rw [MvPowerSeries.X_pow_eq,MvPowerSeries.monomial_mul_monomial,one_mul]

private theorem standardLift_eq_of_bounded_normal_support
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) (P : MvPowerSeries (Fin n) ℂ)
    (hP : ∀ α, MvPowerSeries.coeff α P ≠ 0 →
      normalExponentDegree α < q ∧ α ∉ actualInitialDiagram MonomialOrder.degLex K) :
    actualStandardLift n K q (fun a => MvPowerSeries.coeff a.val.val P)=P := by
  apply MvPowerSeries.ext
  intro α
  by_cases hd : normalExponentDegree α < q
  · by_cases hn : α ∉ actualInitialDiagram MonomialOrder.degLex K
    · let a : actualStandardIndex n K q := ⟨⟨α,hd⟩,hn⟩
      exact actualStandardLift_coefficient K q (fun a => MvPowerSeries.coeff a.val.val P) a
    · have hmem : α ∈ actualInitialDiagram MonomialOrder.degLex K := not_not.mp hn
      rw [actualStandardLift_coefficient_outside K q _ α (Or.inr hmem)]
      symm
      by_contra hne
      exact (hP α hne).2 hmem
  · rw [actualStandardLift_coefficient_outside K q _ α (Or.inl hd)]
    symm
    by_contra hne
    exact hd (hP α hne).1

/-- Injectivity of the SAME actual class map separates every genuine bounded normal tail. -/
theorem bounded_diagram_avoiding_eq_zero_of_exceptional_jet_injective
    (I K J : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (q : ℕ)
    (hCyl : ∀ α : Fin n →₀ ℕ,
      α ∉ actualInitialDiagram MonomialOrder.degLex K ↔
        α.erase e ∉ actualInitialDiagram MonomialOrder.degLex (actualExceptionalFibreIdeal J e))
    (hinj : Function.Injective (actualExceptionalJetMap I J e q))
    (P : MvPowerSeries (Fin n) ℂ)
    (hP : ∀ α, MvPowerSeries.coeff α P ≠ 0 →
      normalExponentDegree α < q ∧ α ∉ actualInitialDiagram MonomialOrder.degLex K)
    (hmem : P ∈ I ⊔ genuineFormalVariables n ^ q) : P=0 := by
  let E := actualExceptionalJetIndexEquivSource K J e q hCyl
  let c : actualExceptionalJetIndex J e q →₀ ℂ :=
    Finsupp.equivFunOnFinite.symm (fun a => MvPowerSeries.coeff (E a).val.val P)
  let Q := (Ideal.Quotient.mkₐ ℂ (I ⊔ genuineFormalVariables n ^ q)).toLinearMap
  have hsum : (∑ a : actualExceptionalJetIndex J e q,
      c a • MvPowerSeries.monomial (E a).val.val (1 : ℂ))=P := by
    calc
      _=∑ a : actualExceptionalJetIndex J e q,
          MvPowerSeries.monomial (E a).val.val (MvPowerSeries.coeff (E a).val.val P) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← map_smul,smul_eq_mul,mul_one]
        simp only [c,Finsupp.equivFunOnFinite_symm_apply_apply]
      _=∑ a : actualStandardIndex n K q,
          MvPowerSeries.monomial a.val.val (MvPowerSeries.coeff a.val.val P) :=
        Equiv.sum_comp E (fun a : actualStandardIndex n K q =>
          MvPowerSeries.monomial a.val.val (MvPowerSeries.coeff a.val.val P))
      _=P := standardLift_eq_of_bounded_normal_support K q P hP
  have hmap : actualExceptionalJetMap I J e q c=Q P := by
    rw [actualExceptionalJetMap,Finsupp.linearCombination_apply,
      c.sum_fintype (fun a z => z • actualExceptionalJetVector I J e q a)
        (fun _ => zero_smul _ _)]
    simp_rw [actualExceptionalJetVector_eq_source_monomial I K J e q hCyl]
    change (∑ a : actualExceptionalJetIndex J e q,
      c a • Q (MvPowerSeries.monomial (E a).val.val 1))=Q P
    rw [← hsum,map_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact (map_smul Q (c a) (MvPowerSeries.monomial (E a).val.val 1)).symm
  have hzero : actualExceptionalJetMap I J e q c=0 := by
    rw [hmap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hc : c=0 := by
    apply hinj
    simpa only [map_zero] using hzero
  apply MvPowerSeries.ext
  intro α
  rw [map_zero]
  by_contra hne
  have hα := hP α hne
  let a : actualStandardIndex n K q := ⟨⟨α,hα.1⟩,hα.2⟩
  have hentry := DFunLike.congr_fun hc (E.symm a)
  have hentry' : MvPowerSeries.coeff α P=0 := by
    simpa only [c,Finsupp.equivFunOnFinite_symm_apply_apply,E.apply_symm_apply,Finsupp.zero_apply]
      using hentry
  exact hne hentry'

end
end Hironaka.HironakaActualExceptionalNormalJetSeparation
