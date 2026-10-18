/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Support.FormalStandardMonomialHSComplementExact

/-! Genuine homogeneous initial forms, original ideal degree lifts, and actual Hilbert--Samuel equality. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualHomogeneousInitialHS
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalStandardMonomialHS
variable {n : ℕ}

private theorem degree_add (a b : Fin n →₀ ℕ) :
    Finsupp.degree (a+b)=Finsupp.degree a+Finsupp.degree b := by
  simp only [Finsupp.degree_eq_weight_one,map_add]

/-- Actual least degree-first coefficient exponent supplies its true original total degree. -/
def actualHomogeneousInitialDegree (F : MvPowerSeries (Fin n) ℂ) (hne : F ≠ 0) : ℕ :=
  normalExponentDegree (actualInitialExponent MonomialOrder.degLex F hne)

private theorem coeff_below_actualHomogeneousInitialDegree (F : MvPowerSeries (Fin n) ℂ)
    (hne : F ≠ 0) (a : Fin n →₀ ℕ) (ha : Finsupp.degree a < actualHomogeneousInitialDegree F hne) :
    MvPowerSeries.coeff a F=0 := by
  apply coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex F hne a
  apply MonomialOrder.degLex_lt_iff.mpr
  apply Finsupp.DegLex.lt_iff.mpr
  left
  simpa only [ofDegLex_toDegLex,Finsupp.degree_eq_sum,actualHomogeneousInitialDegree,normalExponentDegree] using ha

/-- The true least coefficient degree is exactly the existing genuine formal total order. -/
theorem actualHomogeneousInitialDegree_eq_order (F : MvPowerSeries (Fin n) ℂ) (hne : F ≠ 0) :
    (actualHomogeneousInitialDegree F hne : ℕ∞)=F.order := by
  symm
  apply MvPowerSeries.order_eq_nat.mpr
  refine ⟨⟨actualInitialExponent MonomialOrder.degLex F hne,
    (actualInitialExponent_spec MonomialOrder.degLex F hne).1,?_⟩,?_⟩
  · simp [actualHomogeneousInitialDegree,normalExponentDegree,Finsupp.degree_eq_sum]
  · intro a ha
    exact coeff_below_actualHomogeneousInitialDegree F hne a ha

/-- The SAME original series' genuine lowest homogeneous component, without any supplied initial-form model. -/
def actualHomogeneousInitialForm (F : MvPowerSeries (Fin n) ℂ) (hne : F ≠ 0) :
    MvPowerSeries (Fin n) ℂ := MvPowerSeries.homogeneousComponent (actualHomogeneousInitialDegree F hne) F

/-- The genuine initial form is nonzero by its ACTUAL least original coefficient. -/
theorem actualHomogeneousInitialForm_ne_zero (F : MvPowerSeries (Fin n) ℂ) (hne : F ≠ 0) :
    actualHomogeneousInitialForm F hne ≠ 0 :=
  MvPowerSeries.homogeneousComponent_of_order (actualHomogeneousInitialDegree_eq_order F hne)

/-- The literal homogeneous initial form retains exactly the SAME actual minimum exponent. -/
theorem actualHomogeneousInitialForm_initialExponent (F : MvPowerSeries (Fin n) ℂ) (hne : F ≠ 0) :
    actualInitialExponent MonomialOrder.degLex (actualHomogeneousInitialForm F hne)
      (actualHomogeneousInitialForm_ne_zero F hne)=actualInitialExponent MonomialOrder.degLex F hne := by
  apply actualInitialExponent_eq_of_coefficients
  · rw [actualHomogeneousInitialForm,MvPowerSeries.coeff_homogeneousComponent,if_pos]
    · exact (actualInitialExponent_spec MonomialOrder.degLex F hne).1
    · simp [actualHomogeneousInitialDegree,normalExponentDegree,Finsupp.degree_eq_sum]
  · intro b hb
    rw [actualHomogeneousInitialForm,MvPowerSeries.coeff_homogeneousComponent]
    split_ifs
    · exact coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex F hne b hb
    · rfl

/-- True finite-antidiagonal convolution extracts exactly the complementary homogeneous coefficient of an ACTUAL homogeneous factor. -/
theorem homogeneousComponent_mul_homogeneous_of_le (q d : ℕ)
    (H B : MvPowerSeries (Fin n) ℂ) (hB : B.IsHomogeneous d) (hd : d ≤ q) :
    MvPowerSeries.homogeneousComponent q (H*B)=MvPowerSeries.homogeneousComponent (q-d) H*B := by
  apply MvPowerSeries.ext
  intro a
  by_cases ha : Finsupp.degree a=q
  · rw [MvPowerSeries.coeff_homogeneousComponent,if_pos ha,MvPowerSeries.coeff_mul,MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨u,v⟩ huv
    by_cases hv : Finsupp.degree v=d
    · have he := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp huv)
      change Finsupp.degree (u+v)=Finsupp.degree a at he
      rw [degree_add,ha,hv] at he
      have hu : Finsupp.degree u=q-d := by omega
      rw [MvPowerSeries.coeff_homogeneousComponent,if_pos hu]
    · rw [hB.coeff_eq_zero hv,mul_zero,mul_zero]
  · rw [MvPowerSeries.coeff_homogeneousComponent,if_neg ha]
    symm
    have hprod : (MvPowerSeries.homogeneousComponent (q-d) H*B).IsHomogeneous ((q-d)+d) :=
      MvPowerSeries.IsHomogeneous.mul (MvPowerSeries.isHomogeneous_homogeneousComponent H (q-d)) hB
    rw [show q-d+d=q by omega] at hprod
    exact hprod.coeff_eq_zero ha

/-- Genuine convolution has no low component below the actual degree of its homogeneous factor. -/
theorem homogeneousComponent_mul_homogeneous_of_lt (q d : ℕ)
    (H B : MvPowerSeries (Fin n) ℂ) (hB : B.IsHomogeneous d) (hd : q < d) :
    MvPowerSeries.homogeneousComponent q (H*B)=0 := by
  apply MvPowerSeries.ext
  intro a
  rw [map_zero,MvPowerSeries.coeff_homogeneousComponent]
  split_ifs with ha
  · rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨u,v⟩ huv
    have he := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp huv)
    change Finsupp.degree (u+v)=Finsupp.degree a at he
    rw [degree_add,ha] at he
    have hv : Finsupp.degree v ≠ d := by omega
    rw [hB.coeff_eq_zero hv,mul_zero]
  · rfl

private theorem homogeneous_le_order {p : ℕ} {F : MvPowerSeries (Fin n) ℂ}
    (hF : F.IsHomogeneous p) : (p : ℕ∞) ≤ F.order := by
  apply MvPowerSeries.nat_le_order
  intro a ha
  exact MvPowerSeries.IsHomogeneous.coeff_eq_zero hF (Nat.ne_of_lt ha)

/-- Only ACTUAL nonzero original ideal members index the true source homogeneous generators. -/
abbrev actualHomogeneousInitialIdealIndex (I : Ideal (MvPowerSeries (Fin n) ℂ)) :=
  {F : MvPowerSeries (Fin n) ℂ // F ∈ I ∧ F ≠ 0}

/-- The GENUINE source homogeneous initial ideal is spanned by the literal initial forms of ALL actual original ideal members. -/
def actualHomogeneousInitialIdeal (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Ideal (MvPowerSeries (Fin n) ℂ) :=
  Ideal.span (range (fun F : actualHomogeneousInitialIdealIndex I => actualHomogeneousInitialForm F.val F.property.2))

attribute [local instance 2000] IsOrderedRing.toIsOrderedAddMonoid in
/-- Genuine convolution constructs the original ideal degree lift of EACH actual coefficient-times-initial-form product. -/
theorem actual_initial_product_degree_lift (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (F : MvPowerSeries (Fin n) ℂ) (hI : F ∈ I) (hne : F ≠ 0)
    (H : MvPowerSeries (Fin n) ℂ) (q : ℕ) :
    ∃ L : MvPowerSeries (Fin n) ℂ, L ∈ I ∧ L ∈ genuineFormalVariables n ^ q ∧
      MvPowerSeries.homogeneousComponent q L=
        MvPowerSeries.homogeneousComponent q (H*actualHomogeneousInitialForm F hne) := by
  let d := actualHomogeneousInitialDegree F hne
  have hinit : (actualHomogeneousInitialForm F hne).IsHomogeneous d :=
    MvPowerSeries.isHomogeneous_homogeneousComponent F d
  by_cases hd : d ≤ q
  · let p := q-d
    let C := MvPowerSeries.homogeneousComponent p H
    have hpq : p+d=q := by dsimp only [p]; omega
    have hChom : C.IsHomogeneous p := MvPowerSeries.isHomogeneous_homogeneousComponent H p
    have hCo : (p : ℕ∞) ≤ C.order := homogeneous_le_order hChom
    have hFo : (d : ℕ∞) ≤ F.order := le_of_eq (actualHomogeneousInitialDegree_eq_order F hne)
    have hLorder : (p : ℕ∞)+(d : ℕ∞) ≤ (C*F).order :=
      (add_le_add hCo hFo).trans MvPowerSeries.le_order_mul
    have hLq : (q : ℕ∞) ≤ (C*F).order := by
      simpa only [← Nat.cast_add,hpq] using hLorder
    refine ⟨C*F,I.mul_mem_left C hI,?_,?_⟩
    · apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
      intro a ha
      apply MvPowerSeries.coeff_of_lt_order
      have ha' : Finsupp.degree a < q := by
        simpa only [Finsupp.degree_eq_sum,normalExponentDegree] using ha
      exact (by exact_mod_cast ha' : ((Finsupp.degree a : ℕ) : ℕ∞) < (q : ℕ∞)).trans_le hLq
    · have hp : MvPowerSeries.homogeneousComponent (p+d) (C*F)=
          MvPowerSeries.homogeneousComponent p C*MvPowerSeries.homogeneousComponent d F :=
        MvPowerSeries.homogeneousComponent_mul_of_le_order hCo hFo
      rw [hpq,← MvPowerSeries.isHomogeneous_iff_eq_homogeneousComponent.mp hChom] at hp
      exact hp.trans (homogeneousComponent_mul_homogeneous_of_le q d H
        (actualHomogeneousInitialForm F hne) hinit hd).symm
  · refine ⟨0,I.zero_mem,(genuineFormalVariables n ^ q).zero_mem,?_⟩
    rw [map_zero,homogeneousComponent_mul_homogeneous_of_lt q d H
      (actualHomogeneousInitialForm F hne) hinit (lt_of_not_ge hd)]

/-- Actual finite original coefficients internally construct EVERY homogeneous initial-ideal component's true original ideal lift. -/
theorem actual_homogeneous_initial_ideal_degree_lift (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (G : MvPowerSeries (Fin n) ℂ) (hG : G ∈ actualHomogeneousInitialIdeal I) (q : ℕ) :
    ∃ L : MvPowerSeries (Fin n) ℂ, L ∈ I ∧ L ∈ genuineFormalVariables n ^ q ∧
      MvPowerSeries.homogeneousComponent q L=MvPowerSeries.homogeneousComponent q G := by
  obtain ⟨c,hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp hG
  let L (i : actualHomogeneousInitialIdealIndex I) := Classical.choose
    (actual_initial_product_degree_lift I i.val i.property.1 i.property.2 (c i) q)
  have hL (i : actualHomogeneousInitialIdealIndex I) :
      L i ∈ I ∧ L i ∈ genuineFormalVariables n ^ q ∧
        MvPowerSeries.homogeneousComponent q (L i)=
          MvPowerSeries.homogeneousComponent q (c i*actualHomogeneousInitialForm i.val i.property.2) :=
    Classical.choose_spec (actual_initial_product_degree_lift I i.val i.property.1 i.property.2 (c i) q)
  refine ⟨∑ i ∈ c.support, L i,I.sum_mem (fun i _ => (hL i).1),
    (genuineFormalVariables n ^ q).sum_mem (fun i _ => (hL i).2.1),?_⟩
  rw [← hc]
  change MvPowerSeries.homogeneousComponent q (∑ i ∈ c.support, L i)=
    MvPowerSeries.homogeneousComponent q (∑ i ∈ c.support,c i*actualHomogeneousInitialForm i.val i.property.2)
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (hL i).2.2

/-- BOTH WHOLE genuine degree-first diagrams coincide, from actual original ideal degree lifts. -/
theorem actual_homogeneous_initial_ideal_diagram (I : Ideal (MvPowerSeries (Fin n) ℂ)) :
    actualInitialDiagram MonomialOrder.degLex (actualHomogeneousInitialIdeal I)=
      actualInitialDiagram MonomialOrder.degLex I := by
  apply Set.Subset.antisymm
  · rintro a ⟨G,hG,hne,he⟩
    let b := actualInitialExponent MonomialOrder.degLex G hne
    let q := actualHomogeneousInitialDegree G hne
    have hbq : Finsupp.degree b=q := by
      simp [b,q,actualHomogeneousInitialDegree,normalExponentDegree,Finsupp.degree_eq_sum]
    obtain ⟨F,hFI,hFP,hcomp⟩ := actual_homogeneous_initial_ideal_degree_lift I G hG q
    have hc : MvPowerSeries.coeff b F=MvPowerSeries.coeff b G := by
      have h := congrArg (MvPowerSeries.coeff b) hcomp
      simpa only [MvPowerSeries.coeff_homogeneousComponent,if_pos hbq] using h
    have hcoef : MvPowerSeries.coeff b F ≠ 0 := by
      rw [hc]
      exact (actualInitialExponent_spec MonomialOrder.degLex G hne).1
    have hFne : F ≠ 0 := by intro h; rw [h,map_zero] at hcoef; exact hcoef rfl
    refine ⟨F,hFI,hFne,?_⟩
    have hmin : actualInitialExponent MonomialOrder.degLex F hFne=b := by
      apply actualInitialExponent_eq_of_coefficients _ _ _ b hcoef
      intro u hu
      have hdeg : normalExponentDegree u ≤ q := actual_degree_le_of_deglex_lt u b hu
      by_cases hlt : normalExponentDegree u < q
      · exact (mem_genuineFormalVariables_pow_iff_coefficients_zero n q F).mp hFP u hlt
      · have heq : Finsupp.degree u=q := by
          have hd : normalExponentDegree u=q := by omega
          simpa only [Finsupp.degree_eq_sum,normalExponentDegree] using hd
        have h := congrArg (MvPowerSeries.coeff u) hcomp
        simp only [MvPowerSeries.coeff_homogeneousComponent,if_pos heq] at h
        exact h.trans (coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex G hne u hu)
    exact hmin.trans he
  · rintro a ⟨F,hF,hne,he⟩
    refine ⟨actualHomogeneousInitialForm F hne,?_,actualHomogeneousInitialForm_ne_zero F hne,
      (actualHomogeneousInitialForm_initialExponent F hne).trans he⟩
    exact Ideal.subset_span ⟨⟨F,hF,hne⟩,rfl⟩

/-- Every genuine formal Hilbert--Samuel value of the ACTUAL homogeneous initial ideal equals that of the original whole ideal. -/
theorem genuineFormalHilbertSamuelValue_homogeneous_initial (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (ell : ℕ) :
    genuineFormalHilbertSamuelValue n I ell=
      genuineFormalHilbertSamuelValue n (actualHomogeneousInitialIdeal I) ell := by
  rw [genuineFormalHilbertSamuelValue_eq_card_standardIndex,genuineFormalHilbertSamuelValue_eq_card_standardIndex]
  apply Fintype.card_congr
  exact {
    toFun := fun a => ⟨a.val,by
      rw [actual_homogeneous_initial_ideal_diagram]
      exact a.property⟩
    invFun := fun a => ⟨a.val,by
      rw [← actual_homogeneous_initial_ideal_diagram I]
      exact a.property⟩
    left_inv := fun a => rfl
    right_inv := fun a => rfl }

end
end Hironaka.HironakaActualHomogeneousInitialHS
