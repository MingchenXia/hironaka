import TranscendentalNakamaye.Pending.HironakaActualFormalVertexDivision

/-! Actual diagram-complement monomials give the genuine whole formal jet quotient and HS count. -/
set_option autoImplicit false
open Set Classical
namespace TranscendentalNakamaye.Pending.HironakaActualFormalStandardMonomialHS
noncomputable section
open FirstPass HolGerm HironakaHolomorphicPointJets HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalFormalTaylor HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision

variable {n : ℕ}

/-- The genuine degree-first order is compatible with the actual total exponent degree. -/
theorem actual_degree_le_of_deglex_lt (a b : Fin n →₀ ℕ)
    (h : MonomialOrder.degLex.toSyn a < MonomialOrder.degLex.toSyn b) :
    normalExponentDegree a ≤ normalExponentDegree b := by
  have hd := Finsupp.DegLex.monotone_degree (MonomialOrder.degLex_lt_iff.mp h).le
  simpa only [ofDegLex_toDegLex,Finsupp.degree_eq_sum,normalExponentDegree] using hd

/-- Genuine bounded diagram-avoiding series are separated by the WHOLE actual formal jet quotient. -/
theorem bounded_diagram_avoiding_series_eq_zero (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (q : ℕ) (P : MvPowerSeries (Fin n) ℂ)
    (hP : ∀ a, MvPowerSeries.coeff a P ≠ 0 →
      normalExponentDegree a < q ∧ a ∉ actualInitialDiagram MonomialOrder.degLex I)
    (hmem : P ∈ I ⊔ genuineFormalVariables n ^ q) : P=0 := by
  obtain ⟨G,hG,Z,hZ,he⟩ := Submodule.mem_sup.mp hmem
  have hz := (mem_genuineFormalVariables_pow_iff_coefficients_zero n q Z).mp hZ
  by_contra hne
  let a := actualInitialExponent MonomialOrder.degLex P hne
  have ha : MvPowerSeries.coeff a P ≠ 0 := (actualInitialExponent_spec _ P hne).1
  have hs := hP a ha
  have hGa : MvPowerSeries.coeff a G=MvPowerSeries.coeff a P := by
    have hc := congrArg (MvPowerSeries.coeff a) he
    rw [map_add,hz a hs.1,add_zero] at hc
    exact hc
  have hGne : G ≠ 0 := by
    intro hzero
    have hc : MvPowerSeries.coeff a G=0 := by rw [hzero,map_zero]
    exact ha (hGa.symm.trans hc)
  have hgexp : actualInitialExponent MonomialOrder.degLex G hGne=a := by
    apply actualInitialExponent_eq_of_coefficients
    · rwa [hGa]
    · intro b hb
      have hdb : normalExponentDegree b < q :=
        lt_of_le_of_lt (actual_degree_le_of_deglex_lt b a hb) hs.1
      have hp := coeff_eq_zero_of_lt_actualInitialExponent MonomialOrder.degLex P hne b hb
      have hc := congrArg (MvPowerSeries.coeff b) he
      rw [map_add,hz b hdb,add_zero,hp] at hc
      exact hc
  exact hs.2 ⟨G,hG,hGne,hgexp⟩

/-- The finite genuine diagram complement within the ORIGINAL actual bounded exponent index. -/
abbrev actualStandardIndex (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :=
  {a : normalExponentIndex n q // (a : Fin n →₀ ℕ) ∉ actualInitialDiagram MonomialOrder.degLex I}

/-- The actual bounded exponent construction internally makes its genuine diagram complement finite. -/
instance actualStandardIndexFintype (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :
    Fintype (actualStandardIndex n I q) := by
  classical
  letI := normalExponentFintype n q
  exact inferInstance

/-- The literal finite sum of ACTUAL formal monomials, using the genuine complex action. -/
def actualStandardLift (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :
    (actualStandardIndex n I q → ℂ) →ₗ[ℂ] MvPowerSeries (Fin n) ℂ where
  toFun c := ∑ a : actualStandardIndex n I q, MvPowerSeries.monomial a.val.val (c a)
  map_add' c d := by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' c d := by simp only [Pi.smul_apply,map_smul,Finset.smul_sum,RingHom.id_apply]

/-- Every actual displayed monomial retains precisely its original complex coefficient. -/
theorem actualStandardLift_coefficient (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ)
    (c : actualStandardIndex n I q → ℂ) (a : actualStandardIndex n I q) :
    MvPowerSeries.coeff a.val.val (actualStandardLift n I q c)=c a := by
  change MvPowerSeries.coeff a.val.val
    (∑ b : actualStandardIndex n I q, MvPowerSeries.monomial b.val.val (c b))=c a
  rw [map_sum,Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
  · exact MvPowerSeries.coeff_monomial_same _ _
  · intro b _ hne
    have he : a.val.val ≠ b.val.val := fun h => hne (Subtype.ext (Subtype.ext h.symm))
    simp only [MvPowerSeries.coeff_monomial,if_neg he]

/-- Every actual coefficient outside the true bounded diagram complement is zero. -/
theorem actualStandardLift_coefficient_outside (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ)
    (c : actualStandardIndex n I q → ℂ) (b : Fin n →₀ ℕ)
    (hb : ¬normalExponentDegree b < q ∨ b ∈ actualInitialDiagram MonomialOrder.degLex I) :
    MvPowerSeries.coeff b (actualStandardLift n I q c)=0 := by
  change MvPowerSeries.coeff b
    (∑ a : actualStandardIndex n I q, MvPowerSeries.monomial a.val.val (c a))=0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro a _
  have he : b ≠ a.val.val := by
    intro he
    rcases hb with hd | hi
    · exact hd (he ▸ a.val.property)
    · exact a.property (he ▸ hi)
  simp only [MvPowerSeries.coeff_monomial,if_neg he]

/-- The true finite standard lift has exactly the actual bounded diagram-complement support. -/
theorem actualStandardLift_support (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ)
    (c : actualStandardIndex n I q → ℂ) (b : Fin n →₀ ℕ)
    (hb : MvPowerSeries.coeff b (actualStandardLift n I q c) ≠ 0) :
    normalExponentDegree b < q ∧ b ∉ actualInitialDiagram MonomialOrder.degLex I := by
  constructor
  · by_contra h
    exact hb (actualStandardLift_coefficient_outside I q c b (Or.inl h))
  · intro h
    exact hb (actualStandardLift_coefficient_outside I q c b (Or.inr h))

/-- The literal actual standard monomial map into the WHOLE genuine formal jet quotient. -/
def actualStandardQuotientMap (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :
    (actualStandardIndex n I q → ℂ) →ₗ[ℂ]
      (MvPowerSeries (Fin n) ℂ ⧸ (I ⊔ genuineFormalVariables n ^ q)) :=
  (Ideal.Quotient.mkₐ ℂ (I ⊔ genuineFormalVariables n ^ q)).toLinearMap.comp (actualStandardLift n I q)

/-- EVERY actual coefficient vector retains its genuine literal finite monomial numerator. -/
theorem actualStandardQuotientMap_apply (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ)
    (c : actualStandardIndex n I q → ℂ) :
    actualStandardQuotientMap n I q c=
      Ideal.Quotient.mk (I ⊔ genuineFormalVariables n ^ q) (actualStandardLift n I q c) := rfl

/-- Actual whole jet separation internally proves genuine monomial map injectivity. -/
theorem actualStandardQuotientMap_injective (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :
    Function.Injective (actualStandardQuotientMap n I q) := by
  intro c d hcd
  have hz : actualStandardQuotientMap n I q (c-d)=0 := by rw [map_sub,hcd,sub_self]
  rw [actualStandardQuotientMap_apply,Ideal.Quotient.eq_zero_iff_mem] at hz
  have he := bounded_diagram_avoiding_series_eq_zero I q (actualStandardLift n I q (c-d))
    (actualStandardLift_support I q (c-d)) hz
  have hvec : c-d=0 := by
    funext a
    have hc := congrArg (MvPowerSeries.coeff a.val.val) he
    rw [actualStandardLift_coefficient,map_zero] at hc
    exact hc
  exact sub_eq_zero.mp hvec

/-- Genuine formal division and the actual formal power kernel reach EVERY whole quotient class. -/
theorem actualStandardQuotientMap_surjective (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :
    Function.Surjective (actualStandardQuotientMap n I q) := by
  intro z
  obtain ⟨F,rfl⟩ := Ideal.Quotient.mk_surjective z
  let R := actualFormalRemainder MonomialOrder.degLex I F
  let c : actualStandardIndex n I q → ℂ := fun a => MvPowerSeries.coeff a.val.val R
  have hrem : R-actualStandardLift n I q c ∈ genuineFormalVariables n ^ q := by
    apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
    intro b hb
    rw [map_sub]
    apply sub_eq_zero.mpr
    by_cases hi : b ∈ actualInitialDiagram MonomialOrder.degLex I
    · change MvPowerSeries.coeff b (actualFormalRemainder MonomialOrder.degLex I F)=_
      rw [actualFormalRemainder_coefficient_diagram MonomialOrder.degLex I F b hi,
        actualStandardLift_coefficient_outside I q c b (Or.inr hi)]
    · exact (actualStandardLift_coefficient I q c ⟨⟨b,hb⟩,hi⟩).symm
  have hdiff : F-R ∈ I := by
    have he : F-R=∑ a : actualInitialVertices MonomialOrder.degLex I,
        actualFormalQuotient MonomialOrder.degLex I F a*actualVertexSeries MonomialOrder.degLex I a :=
      sub_eq_iff_eq_add.mpr (actual_formal_vertex_division MonomialOrder.degLex I F)
    rw [he]
    exact I.sum_mem (fun a _ => I.mul_mem_left _ (actualVertexSeries_spec MonomialOrder.degLex I a).1)
  have htotal : F-actualStandardLift n I q c ∈ I ⊔ genuineFormalVariables n ^ q := by
    have he : F-actualStandardLift n I q c=(F-R)+(R-actualStandardLift n I q c) := by abel
    rw [he]
    exact Ideal.add_mem _ (Ideal.mem_sup_left hdiff) (Ideal.mem_sup_right hrem)
  refine ⟨c,?_⟩
  rw [actualStandardQuotientMap_apply]
  apply Ideal.Quotient.eq.mpr
  have he : actualStandardLift n I q c-F=-(F-actualStandardLift n I q c) := by abel
  rw [he]
  exact (I ⊔ genuineFormalVariables n ^ q).neg_mem htotal

/-- The internally proved genuine monomial bijection retains the EXISTING complex action. -/
def actualStandardQuotientLinearEquiv (n : ℕ) (I : Ideal (MvPowerSeries (Fin n) ℂ)) (q : ℕ) :
    (actualStandardIndex n I q → ℂ) ≃ₗ[ℂ]
      (MvPowerSeries (Fin n) ℂ ⧸ (I ⊔ genuineFormalVariables n ^ q)) :=
  LinearEquiv.ofBijective (actualStandardQuotientMap n I q)
    ⟨actualStandardQuotientMap_injective I q,actualStandardQuotientMap_surjective I q⟩

/-- EVERY actual formal HS value is the true cardinality of its bounded initial diagram complement. -/
theorem genuineFormalHilbertSamuelValue_eq_card_standardIndex (I : Ideal (MvPowerSeries (Fin n) ℂ))
    (ℓ : ℕ) :
    genuineFormalHilbertSamuelValue n I ℓ=Fintype.card (actualStandardIndex n I (ℓ+1)) := by
  rw [genuineFormalHilbertSamuelValue,← (actualStandardQuotientLinearEquiv n I (ℓ+1)).finrank_eq,
    Module.finrank_fintype_fun_eq_card]

/-- EVERY EXISTING original HS value is computed by the actual diagram of its GENUINE whole Taylor extension. -/
theorem hilbertSamuelValue_eq_card_actual_formal_standardIndex
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (ℓ : ℕ) :
    hilbertSamuelValue J ℓ=Fintype.card (actualStandardIndex n
      (Ideal.map (originalTaylorAlgHom n).toRingHom J) (ℓ+1)) :=
  (hilbertSamuelValue_eq_genuine_formal_extension n J ℓ).trans
    (genuineFormalHilbertSamuelValue_eq_card_standardIndex _ ℓ)

end
end TranscendentalNakamaye.Pending.HironakaActualFormalStandardMonomialHS
