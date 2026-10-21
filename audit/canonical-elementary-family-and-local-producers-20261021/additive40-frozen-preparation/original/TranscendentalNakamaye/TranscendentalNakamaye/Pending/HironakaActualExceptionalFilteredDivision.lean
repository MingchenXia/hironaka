import TranscendentalNakamaye.Pending.HironakaActualFormalCoordinatePowerDivision
import Mathlib.RingTheory.MvPowerSeries.Rename
import TranscendentalNakamaye.Pending.HironakaActualPointTangentCoefficientHSDrop
import TranscendentalNakamaye.Pending.HironakaActualTaylorFaithfullyFlat

/-!
# Actual exceptional saturation produces strict maximal-ideal filtration

Literal coefficient truncation and a genuine pivot retraction construct whole
shifted filtered representations and all exceptional initial-symbol colon
identities. An original analytic ideal and point chart choose ONE canonical
normalized family before all current-order bounds and jets; actual Taylor-flat
syzygies and exact source polynomial coefficients discharge every auxiliary
saturation and homogeneous-shadow condition internally.
No fixed-coordinate diagram inclusion or HS equality certificate is assumed.
Blueprint: `hironaka-actual-exceptional-filtered-division-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace TranscendentalNakamaye.Pending.HironakaActualExceptionalFilteredDivision
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualFormalCoordinatePowerDivision
variable {n : ℕ}

private def highPart (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) : MvPowerSeries (Fin n) ℂ :=
  fun α => if q≤α.degree then MvPowerSeries.coeff α F else 0

private theorem point_power_iff (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    F∈actualFormalCoordinateIdeal n univ^q ↔
      ∀ α : Fin n →₀ ℕ,α.degree<q→MvPowerSeries.coeff α F=0 := by
  rw [mem_actualFormalCoordinateIdeal_pow_iff]
  have hw (α : Fin n →₀ ℕ) : Finsupp.weight (actualCoordinateWeight (univ : Set (Fin n))) α=α.degree := by
    simp [Finsupp.weight_eq_sum,actualCoordinateWeight,Finsupp.degree_eq_sum]
  simp only [hw]

private theorem highPart_mem (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    highPart q F∈actualFormalCoordinateIdeal n univ^q := by
  apply (point_power_iff q _).mpr
  intro α hα
  change (if q≤α.degree then _ else 0)=0
  rw [if_neg (by omega)]

private theorem coeff_mul_highPart (P A : MvPowerSeries (Fin n) ℂ) (d q : ℕ)
    (hP : P.IsHomogeneous d) (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α (P*highPart (q-d) A)=
      if q≤α.degree then MvPowerSeries.coeff α (P*A) else 0 := by
  rw [MvPowerSeries.coeff_mul]
  split_ifs with hα
  · rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_congr rfl
    rintro ⟨u,v⟩ huv
    by_cases hu : MvPowerSeries.coeff u P=0
    · rw [hu,zero_mul,zero_mul]
    · have hd : u.degree=d := by
        by_contra h
        exact hu (hP.coeff_eq_zero h)
      have hs : u.degree+v.degree=α.degree := by
        rw [←map_add]
        exact congrArg (fun a : Fin n →₀ ℕ => a.degree) (Finset.mem_antidiagonal.mp huv)
      change _*(if q-d≤v.degree then _ else 0)=_
      rw [if_pos (by omega)]
  · apply Finset.sum_eq_zero
    rintro ⟨u,v⟩ huv
    by_cases hu : MvPowerSeries.coeff u P=0
    · rw [hu,zero_mul]
    · have hd : u.degree=d := by
        by_contra h
        exact hu (hP.coeff_eq_zero h)
      have hs : u.degree+v.degree=α.degree := by
        rw [←map_add]
        exact congrArg (fun a : Fin n →₀ ℕ => a.degree) (Finset.mem_antidiagonal.mp huv)
      change _*(if q-d≤v.degree then _ else 0)=0
      rw [if_neg (by omega),mul_zero]

/-- Literal homogeneous generators give exact WHOLE shifted power coefficients,
by genuine coefficient truncation of any finite span representation. -/
theorem exists_homogeneous_filtered_representation {ι : Type*} [Fintype ι]
    (P : ι → MvPowerSeries (Fin n) ℂ) (d : ι → ℕ)
    (hP : ∀ i,(P i).IsHomogeneous (d i))
    (F : MvPowerSeries (Fin n) ℂ) (hF : F∈Ideal.span (range P)) (q : ℕ)
    (hFq : F∈actualFormalCoordinateIdeal n univ^q) :
    ∃ Q : ι → MvPowerSeries (Fin n) ℂ,
      F=(∑ i,P i*Q i) ∧ ∀ i,Q i∈actualFormalCoordinateIdeal n univ^(q-d i) := by
  obtain ⟨A,hA⟩ := Ideal.mem_span_range_iff_exists_fun.mp hF
  refine ⟨fun i => highPart (q-d i) (A i),?_,fun i => highPart_mem _ _⟩
  apply MvPowerSeries.ext
  intro α
  rw [map_sum]
  simp_rw [coeff_mul_highPart _ _ _ _ (hP _) α]
  by_cases hα : q≤α.degree
  · simp only [if_pos hα]
    have hc := congrArg (MvPowerSeries.coeff α) hA
    simpa only [map_sum,mul_comm] using hc.symm
  · simp only [if_neg hα,Finset.sum_const_zero]
    exact (point_power_iff q F).mp hFq α (by omega)


/-- Discard the actual pivot variable and literally reinclude all others. -/
def pivotZeroProjection (e : Fin n) :
    MvPowerSeries (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  (MvPowerSeries.rename (Function.Embedding.subtype (fun i : Fin n => i≠e))).comp
    (MvPowerSeries.killCompl (Function.Embedding.subtype (fun i : Fin n => i≠e)))

private theorem pivot_exponent_range_iff (e : Fin n) (α : Fin n →₀ ℕ) :
    α∈range (Finsupp.embDomain (Function.Embedding.subtype (fun i : Fin n => i≠e))) ↔ α e=0 := by
  rw [Finsupp.mem_range_embDomain_iff]
  constructor
  · intro h
    by_contra he
    have hh := h (Finsupp.mem_support_iff.mpr he)
    simp at hh
  · intro he i hi
    refine ⟨⟨i,?_⟩,rfl⟩
    intro hie
    subst i
    exact (Finsupp.mem_support_iff.mp hi) he

/-- The actual endomorphism retains exactly the pure nonpivot coefficients. -/
theorem pivotZeroProjection_coefficient (e : Fin n) (F : MvPowerSeries (Fin n) ℂ)
    (α : Fin n →₀ ℕ) :
    MvPowerSeries.coeff α (pivotZeroProjection e F)=
      if α e=0 then MvPowerSeries.coeff α F else 0 := by
  simp only [←pivot_exponent_range_iff e α]
  by_cases ha : α∈range (Finsupp.embDomain (Function.Embedding.subtype (fun i : Fin n => i≠e)))
  · rw [if_pos ha]
    obtain ⟨γ,rfl⟩ := ha
    change MvPowerSeries.coeff (Finsupp.embDomain (Function.Embedding.subtype (fun i : Fin n => i≠e)) γ)
      (MvPowerSeries.rename (Function.Embedding.subtype (fun i : Fin n => i≠e))
        (MvPowerSeries.killCompl (Function.Embedding.subtype (fun i : Fin n => i≠e)) F))=_
    rw [MvPowerSeries.coeff_embDomain_rename,MvPowerSeries.coeff_killCompl]
  · rw [if_neg ha]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨γ,hγ⟩
    apply ha
    refine ⟨γ,?_⟩
    rw [Finsupp.embDomain_eq_mapDomain]
    exact hγ

/-- Idempotence is a whole coefficient identity of the actual projection. -/
theorem pivotZeroProjection_idempotent (e : Fin n) (F : MvPowerSeries (Fin n) ℂ) :
    pivotZeroProjection e (pivotZeroProjection e F)=pivotZeroProjection e F := by
  apply MvPowerSeries.ext
  intro α
  simp only [pivotZeroProjection_coefficient]
  split_ifs <;> rfl

/-- Its actual whole kernel is precisely divisibility by the actual pivot variable. -/
theorem pivotZeroProjection_eq_zero_iff (e : Fin n) (F : MvPowerSeries (Fin n) ℂ) :
    pivotZeroProjection e F=0 ↔ (MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ)∣F := by
  rw [MvPowerSeries.X_dvd_iff]
  constructor
  · intro h α hα
    have hc := congrArg (MvPowerSeries.coeff α) h
    simpa only [pivotZeroProjection_coefficient,if_pos hα,map_zero] using hc
  · intro h
    apply MvPowerSeries.ext
    intro α
    rw [pivotZeroProjection_coefficient,map_zero]
    split_ifs with hα
    · exact h α hα
    · rfl

/-- All ordinary maximal powers are genuinely preserved by the actual projection. -/
theorem pivotZeroProjection_mem_point_power (e : Fin n) (q : ℕ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F∈actualFormalCoordinateIdeal n univ^q) :
    pivotZeroProjection e F∈actualFormalCoordinateIdeal n univ^q := by
  apply (point_power_iff q _).mpr
  intro α hα
  rw [pivotZeroProjection_coefficient]
  split_ifs
  · exact (point_power_iff q F).mp hF α hα
  · rfl

/-- Actual monomial coefficient shifting reflects the full ordinary powers. -/
theorem point_power_of_X_mul_mem (e : Fin n) (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : MvPowerSeries.X e*F∈actualFormalCoordinateIdeal n univ^(q+1)) :
    F∈actualFormalCoordinateIdeal n univ^q := by
  apply (point_power_iff q F).mpr
  intro α hα
  have hdeg : (Finsupp.single e 1+α).degree<q+1 := by
    simp only [map_add,Finsupp.degree_single]
    omega
  have hc := (point_power_iff (q+1) _).mp hF (Finsupp.single e 1+α) hdeg
  simpa only [MvPowerSeries.X,MvPowerSeries.coeff_add_monomial_mul,one_mul] using hc


private theorem product_mem_point_power (F G : MvPowerSeries (Fin n) ℂ) (p q r : ℕ)
    (hF : F∈actualFormalCoordinateIdeal n univ^p)
    (hG : G∈actualFormalCoordinateIdeal n univ^q) (hr : r≤p+q) :
    F*G∈actualFormalCoordinateIdeal n univ^r := by
  apply Ideal.pow_le_pow_right hr
  rw [pow_add]
  exact Ideal.mul_mem_mul hF hG

/-- GENUINE exceptional saturation and literal homogeneous fibre generators
construct exact whole shifted maximal-power division for EVERY order. -/
theorem exists_exceptional_filtered_representation {ι : Type*} [Fintype ι]
    (H : ι → MvPowerSeries (Fin n) ℂ) (d : ι → ℕ) (e : Fin n)
    (hH : ∀ i,H i∈actualFormalCoordinateIdeal n univ^(d i))
    (hShadow : ∀ i,(pivotZeroProjection e (H i)).IsHomogeneous (d i))
    (hReg : ∀ F : MvPowerSeries (Fin n) ℂ,
      MvPowerSeries.X e*F∈Ideal.span (range H)→F∈Ideal.span (range H))
    (q : ℕ) (F : MvPowerSeries (Fin n) ℂ)
    (hF : F∈Ideal.span (range H)) (hFq : F∈actualFormalCoordinateIdeal n univ^q) :
    ∃ Q : ι → MvPowerSeries (Fin n) ℂ,
      F=(∑ i,H i*Q i) ∧ ∀ i,Q i∈actualFormalCoordinateIdeal n univ^(q-d i) := by
  induction q generalizing F with
  | zero =>
      obtain ⟨A,hA⟩ := Ideal.mem_span_range_iff_exists_fun.mp hF
      refine ⟨A,?_,?_⟩
      · simpa only [mul_comm] using hA.symm
      · intro i
        simp
  | succ q ih =>
      let ρ := pivotZeroProjection e
      let P : ι → MvPowerSeries (Fin n) ℂ := fun i => ρ (H i)
      have hPF : ρ F∈Ideal.span (range P) := by
        have hm := Ideal.mem_map_of_mem ρ.toRingHom hF
        rw [Ideal.map_span,←range_comp] at hm
        exact hm
      have hPFq : ρ F∈actualFormalCoordinateIdeal n univ^(q+1) :=
        pivotZeroProjection_mem_point_power e _ F hFq
      obtain ⟨A,hA,hApow⟩ := exists_homogeneous_filtered_representation P d hShadow (ρ F) hPF (q+1) hPFq
      have hprojected : ρ F=(∑ i,ρ (H i)*ρ (A i)) := by
        have he := congrArg ρ hA
        simpa only [map_sum,map_mul,pivotZeroProjection_idempotent,P,ρ] using he
      let S := ∑ i,H i*ρ (A i)
      have hS : S∈Ideal.span (range H) := by
        apply Ideal.sum_mem
        intro i _
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_range_self (x := i))
      have hSq : S∈actualFormalCoordinateIdeal n univ^(q+1) := by
        apply Ideal.sum_mem
        intro i _
        apply product_mem_point_power (H i) (ρ (A i)) (d i) (q+1-d i) (q+1) (hH i)
          (pivotZeroProjection_mem_point_power e _ (A i) (hApow i))
        omega
      have hDproj : ρ (F-S)=0 := by
        rw [map_sub]
        change ρ F-ρ (∑ i,H i*ρ (A i))=0
        rw [map_sum]
        simp_rw [map_mul]
        change ρ F-(∑ i,ρ (H i)*pivotZeroProjection e (pivotZeroProjection e (A i)))=0
        simp_rw [pivotZeroProjection_idempotent]
        exact sub_eq_zero.mpr hprojected
      obtain ⟨K,hK⟩ := (pivotZeroProjection_eq_zero_iff e (F-S)).mp hDproj
      have hKI : K∈Ideal.span (range H) := by
        apply hReg K
        rw [←hK]
        exact Ideal.sub_mem _ hF hS
      have hKq : K∈actualFormalCoordinateIdeal n univ^q := by
        apply point_power_of_X_mul_mem e q
        rw [←hK]
        exact Ideal.sub_mem _ hFq hSq
      obtain ⟨B,hB,hBpow⟩ := ih K hKI hKq
      refine ⟨fun i => ρ (A i)+MvPowerSeries.X e*B i,?_,?_⟩
      · calc
          F=S+MvPowerSeries.X e*K := by rw [←hK];ring
          _=(∑ i,H i*ρ (A i))+MvPowerSeries.X e*(∑ i,H i*B i) := by rw [hB]
          _=(∑ i,H i*(ρ (A i)+MvPowerSeries.X e*B i)) := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib,Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            ring
      · intro i
        apply Ideal.add_mem
        · exact pivotZeroProjection_mem_point_power e _ (A i) (hApow i)
        · have he : (MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ)∈actualFormalCoordinateIdeal n univ^1 := by
            rw [pow_one]
            exact Ideal.subset_span ⟨e,mem_univ e,rfl⟩
          exact product_mem_point_power _ _ 1 (q-d i) (q+1-d i) he (hBpow i) (by omega)


open FirstPass HolGerm HironakaActualOriginalFormalTaylor HironakaActualTaylorFaithfullyFlat
  HironakaActualPointNormalizedSaturation HironakaActualPointTangentCoefficientHSDrop
  HironakaActualOriginalReducedVertexBasis HironakaActualFormalInitialDiagram
  HironakaActualPointDehomogenizedInitial HironakaActualPointExceptionalInitialForm
  HironakaActualReducedFormalStandardBasis HironakaRelativeNormalIdeal
  HironakaRelativeNormalActualBaseJetDimension HironakaActualAnalyticBlowupTaylor
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticStrictGenerators
  HironakaHolomorphicJetMonomialSpan

private theorem formal_syzygies_finite {ι : Type*} [Fintype ι]
    (G : ι → HolGerm (ComplexModel (0+n))) (A : ι → MvPowerSeries (Fin n) ℂ)
    (hRel : (∑ i,originalTaylorAlgHom n (G i)*A i)=0) :
    ∃ (k : ℕ) (c : ι → Fin k → HolGerm (ComplexModel (0+n)))
      (B : Fin k → MvPowerSeries (Fin n) ℂ),
      (∀ i,A i=∑ l,originalTaylorAlgHom n (c i l)*B l) ∧
      ∀ l,(∑ i,G i*c i l)=0 := by
  let e := Fintype.equivFin ι
  have hs : (∑ i : Fin (Fintype.card ι),originalTaylorAlgHom n (G (e.symm i))*A (e.symm i))=0 := by
    rw [e.symm.sum_comp (fun i => originalTaylorAlgHom n (G i)*A i)]
    exact hRel
  obtain ⟨k,c,B,hA,hc⟩ := (actual_formal_relation_iff_original_syzygies n (Fintype.card ι)
    (fun i => G (e.symm i)) (fun i => A (e.symm i))).mp hs
  refine ⟨k,fun i l => c (e i) l,B,?_,?_⟩
  · intro i
    simpa only [Equiv.symm_apply_apply] using hA (e i)
  · intro l
    have h := hc l
    rw [←e.sum_comp (fun i => G (e.symm i)*c i l)] at h
    simpa only [Equiv.symm_apply_apply] using h

private theorem taylor_span_exceptional_regular {ι : Type*} [Fintype ι]
    (H : ι → HolGerm (ComplexModel (0+n))) (j : Fin n)
    (hReg : ∀ g : HolGerm (ComplexModel (0+n)),
      normalCoordinate 0 n j*g∈Ideal.span (range H)→g∈Ideal.span (range H))
    (F : MvPowerSeries (Fin n) ℂ)
    (hF : MvPowerSeries.X j*F∈Ideal.span (range (fun i => originalTaylorAlgHom n (H i)))) :
    F∈Ideal.span (range (fun i => originalTaylorAlgHom n (H i))) := by
  obtain ⟨A,hA⟩ := Ideal.mem_span_range_iff_exists_fun.mp hF
  let G : Option ι → HolGerm (ComplexModel (0+n)) := fun o => o.elim (normalCoordinate 0 n j) H
  let C : Option ι → MvPowerSeries (Fin n) ℂ := fun o => o.elim (-F) A
  have hRel : (∑ o : Option ι,originalTaylorAlgHom n (G o)*C o)=0 := by
    rw [Fintype.sum_option]
    change originalTaylorAlgHom n (normalCoordinate 0 n j)*(-F)+(∑ i,originalTaylorAlgHom n (H i)*A i)=0
    rw [originalTaylorAlgHom_coordinate]
    have hs : (∑ i,originalTaylorAlgHom n (H i)*A i)=MvPowerSeries.X j*F := by
      simpa only [mul_comm] using hA
    rw [hs]
    ring
  obtain ⟨k,c,B,hC,hc⟩ := formal_syzygies_finite G C hRel
  have hcn (l : Fin k) : c none l∈Ideal.span (range H) := by
    apply hReg
    have hr := hc l
    rw [Fintype.sum_option] at hr
    change normalCoordinate 0 n j*c none l+(∑ i,H i*c (some i) l)=0 at hr
    have he : normalCoordinate 0 n j*c none l= -(∑ i,H i*c (some i) l) := eq_neg_of_add_eq_zero_left hr
    rw [he]
    apply (Ideal.span (range H)).neg_mem
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_range_self (x := i))
  have hm : -F∈Ideal.span (range (fun i => originalTaylorAlgHom n (H i))) := by
    change C none∈_
    rw [hC none]
    apply Ideal.sum_mem
    intro l _
    apply Ideal.mul_mem_right
    have h := Ideal.mem_map_of_mem (originalTaylorAlgHom n).toRingHom (hcn l)
    rw [Ideal.map_span,←range_comp] at h
    exact h
  simpa only [neg_neg] using (Ideal.span (range (fun i => originalTaylorAlgHom n (H i)))).neg_mem hm

private theorem dehom_pivot_independent (e : Fin n) (b : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ)
    (α : Fin n →₀ ℕ) (hα : α∈(actualPointDehomogenization e b f).support) : α e=0 := by
  apply MvPolynomial.mem_support_notMem_vars_zero hα
  intro he
  change e∈(MvPolynomial.aeval (fun i => if i=e then 1 else MvPolynomial.C (b i)+MvPolynomial.X i) f).vars at he
  rw [MvPolynomial.aeval_eq_bind₁] at he
  obtain ⟨i,_hi,hvar⟩ := MvPolynomial.mem_vars_bind₁ _ _ he
  by_cases hie : i=e
  · simp [hie] at hvar
  · have hx : e∈(MvPolynomial.C (b i)+MvPolynomial.X i).vars := by simpa [hie] using hvar
    have heq : e=i := by simpa using MvPolynomial.vars_add_subset (MvPolynomial.C (b i)) (MvPolynomial.X i) hx
    exact hie heq.symm

private theorem dehom_totalDegree_le (e : Fin n) (b : Fin n → ℂ) (f : MvPolynomial (Fin n) ℂ) :
    (actualPointDehomogenization e b f).totalDegree≤f.totalDegree := by
  have hlin (i : Fin n) :
      (if i=e then (1 : MvPolynomial (Fin n) ℂ) else MvPolynomial.C (b i)+MvPolynomial.X i).totalDegree≤1 := by
    split_ifs
    · simp
    · exact (MvPolynomial.totalDegree_add _ _).trans (by simp)
  conv_lhs => rw [←f.support_sum_monomial_coeff,map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro α hα
  change (MvPolynomial.aeval (fun i => if i=e then 1 else MvPolynomial.C (b i)+MvPolynomial.X i)
    (MvPolynomial.monomial α (MvPolynomial.coeff α f))).totalDegree≤_
  rw [MvPolynomial.aeval_monomial]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  change (MvPolynomial.C (MvPolynomial.coeff α f)).totalDegree+_≤_
  rw [MvPolynomial.totalDegree_C,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ => (MvPolynomial.totalDegree_pow _ _).trans
    (by simpa using Nat.mul_le_mul_left (α i) (hlin i))))
  exact MvPolynomial.le_totalDegree hα


private theorem canonical_point_power
    (J : Ideal (HolGerm (ComplexModel (0+n))))
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
    originalReducedVertexBasis J a∈normalIdeal 0 n^(normalExponentDegree a.val) := by
  rw [zeroTangentNormalIdeal_eq_maximalIdeal]
  apply (mem_original_maximal_pow_iff_formal_coefficients_zero n _ _).mpr
  intro α hα
  rw [originalReducedVertexBasis_taylor]
  apply actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex _ a α
  apply MonomialOrder.degLex_lt_iff.mpr
  apply Finsupp.DegLex.lt_iff.mpr
  left
  simpa only [ofDegLex_toDegLex,Finsupp.degree_eq_sum,normalExponentDegree] using hα

private theorem canonical_quotient_shadow_homogeneous
    (J : Ideal (HolGerm (ComplexModel (0+n))))
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J))
    (j : Fin n) (b : Fin (0+n) → ℂ) (H : HolGerm (ComplexModel (0+n)))
    (hH : (coordinateGerm (j.natAdd 0))^(normalExponentDegree a.val)*H=
      actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b (originalReducedVertexBasis J a))
    (hOrd : H∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(normalExponentDegree a.val)) :
    (pivotZeroProjection j (originalTaylorAlgHom n H)).IsHomogeneous (normalExponentDegree a.val) := by
  let f := actualPointHomogeneousPolynomial (normalExponentDegree a.val)
    (originalTaylorAlgHom n (originalReducedVertexBasis J a))
  let p := actualPointDehomogenization j (fun i => b (i.natAdd 0)) f
  have hEq : pivotZeroProjection j (originalTaylorAlgHom n H)=(p : MvPowerSeries (Fin n) ℂ) := by
    apply MvPowerSeries.ext
    intro γ
    rw [pivotZeroProjection_coefficient,MvPolynomial.coeff_coe]
    split_ifs with hγ
    · exact canonical_point_quotient_pure_coefficient J a j b H hH γ hγ
    · symm
      by_contra hc
      exact hγ (dehom_pivot_independent j (fun i => b (i.natAdd 0)) f γ
        (MvPolynomial.mem_support_iff.mpr hc))
  have hBound : p.totalDegree≤normalExponentDegree a.val :=
    (dehom_totalDegree_le j (fun i => b (i.natAdd 0)) f).trans
      (actualPointHomogeneousPolynomial_isHomogeneous _ _).totalDegree_le
  have hPower : originalTaylorAlgHom n H∈actualFormalCoordinateIdeal n univ^(normalExponentDegree a.val) := by
    apply (point_power_iff _ _).mpr
    intro γ hγ
    exact (mem_original_maximal_pow_iff_formal_coefficients_zero n _ H).mp hOrd γ
      (by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hγ)
  have hShadowPower := pivotZeroProjection_mem_point_power j _ _ hPower
  intro γ hc
  have hUp : γ.degree≤normalExponentDegree a.val := by
    have hcp : MvPolynomial.coeff γ p≠0 := by simpa only [hEq,MvPolynomial.coeff_coe] using hc
    have hd : γ.degree≤p.totalDegree := by
      simpa only [Finsupp.degree_apply,Finsupp.sum] using (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hcp))
    exact hd.trans hBound
  have hLow : normalExponentDegree a.val≤γ.degree := by
    by_contra h
    exact hc ((point_power_iff _ _).mp hShadowPower γ (by omega))
  simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using le_antisymm hUp hLow

/-- ONE original canonical normalized family is fixed BEFORE all order bounds
and jets. Its whole normalized ideal then has genuine strict formal maximal
filtration, with all auxiliary natural algebra hypotheses proved internally. -/
theorem exists_original_point_canonical_filtered_family
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (j : Fin n) (b : Fin (0+n) → ℂ) :
    ∃ H : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)),
      (∀ a,(coordinateGerm (j.natAdd 0))^(normalExponentDegree a.val)*H a=
        actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b (originalReducedVertexBasis J a)) ∧
      actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b=Ideal.span (range H) ∧
      ∀ (_hOrder : ∀ a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(normalExponentDegree a.val))
        (q : ℕ) (F : MvPowerSeries (Fin n) ℂ),
        F∈Ideal.map (originalTaylorAlgHom n).toRingHom
          (actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b) →
        F∈actualFormalCoordinateIdeal n univ^q →
        ∃ Q : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
            (Ideal.map (originalTaylorAlgHom n).toRingHom J) → MvPowerSeries (Fin n) ℂ,
          F=(∑ a,originalTaylorAlgHom n (H a)*Q a) ∧
            ∀ a,Q a∈actualFormalCoordinateIdeal n univ^(q-normalExponentDegree a.val) := by
  obtain ⟨H,hH,hReg⟩ := exists_original_point_exceptional_regular_canonical_family J j b
  let e : HolGerm (ComplexModel (0+n)) := coordinateGerm (j.natAdd 0)
  let N := Ideal.span (range H)
  let π := actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b
  have hTotal : Ideal.map π.toRingHom J≤N := by
    rw [Ideal.map_le_iff_le_comap,←originalReducedVertexBasis_span J]
    apply Ideal.span_le.mpr
    rintro _ ⟨a,rfl⟩
    change π (originalReducedVertexBasis J a)∈N
    rw [←hH a]
    exact N.mul_mem_left _ (Ideal.subset_span ⟨a,rfl⟩)
  have hPower (q : ℕ) (g : HolGerm (ComplexModel (0+n))) : e^q*g∈N ↔ g∈N := by
    induction q with
    | zero => simp only [pow_zero,one_mul]
    | succ q ih => rw [pow_succ',mul_assoc,hReg,ih]
  have hNamed : actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b=N := by
    apply le_antisymm
    · intro g hg
      obtain ⟨q,hq⟩ := ((actual_point_normalized_member_iff_total_saturation J j b).1 g).mp hg
      exact (hPower q g).mp (hTotal hq)
    · apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      apply Ideal.subset_span
      refine ⟨normalExponentDegree a.val,originalReducedVertexBasis J a,
        originalReducedVertexBasis_mem J a,?_,hH a⟩
      rw [actualAnalyticCoordinateIdeal_normal]
      exact canonical_point_power J a
  refine ⟨H,hH,hNamed,?_⟩
  intro hOrder q F hF hFq
  have hFspan : F∈Ideal.span (range (fun a => originalTaylorAlgHom n (H a))) := by
    rw [hNamed,Ideal.map_span,←range_comp] at hF
    exact hF
  have hOrd (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
      originalTaylorAlgHom n (H a)∈actualFormalCoordinateIdeal n univ^(normalExponentDegree a.val) := by
    apply (point_power_iff _ _).mpr
    intro γ hγ
    exact (mem_original_maximal_pow_iff_formal_coefficients_zero n _ (H a)).mp (hOrder a) γ
      (by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hγ)
  exact exists_exceptional_filtered_representation (fun a => originalTaylorAlgHom n (H a))
    (fun a => normalExponentDegree a.val) j hOrd
    (fun a => canonical_quotient_shadow_homogeneous J a j b (H a) (hH a) (hOrder a))
    (taylor_span_exceptional_regular H j (fun g hg => (hReg g).mp hg)) q F hFspan hFq


/-- Actual whole saturation and homogeneous shadows PRODUCE all ordinary
exceptional-symbol colon identities, rather than assuming graded regularity. -/
theorem exceptional_point_power_colon_eq {ι : Type*} [Fintype ι]
    (H : ι → MvPowerSeries (Fin n) ℂ) (d : ι → ℕ) (e : Fin n)
    (hH : ∀ i,H i∈actualFormalCoordinateIdeal n univ^(d i))
    (hShadow : ∀ i,(pivotZeroProjection e (H i)).IsHomogeneous (d i))
    (hReg : ∀ F : MvPowerSeries (Fin n) ℂ,
      MvPowerSeries.X e*F∈Ideal.span (range H)→F∈Ideal.span (range H)) (q : ℕ) :
    (Ideal.span (range H) ⊔ actualFormalCoordinateIdeal n univ^(q+1)).colon {MvPowerSeries.X e}=
      Ideal.span (range H) ⊔ actualFormalCoordinateIdeal n univ^q := by
  let ρ := pivotZeroProjection e
  have hxe : ρ (MvPowerSeries.X e)=0 :=
    (pivotZeroProjection_eq_zero_iff e _).mpr dvd_rfl
  ext F
  rw [Submodule.mem_colon_singleton]
  change F*MvPowerSeries.X e∈_ ↔ F∈_
  constructor
  · intro hF
    obtain ⟨A,hAI,B,hB,hAB⟩ := Submodule.mem_sup.mp hF
    have hφA : ρ A= -ρ B := by
      have hh := congrArg ρ hAB
      rw [map_add,map_mul,hxe,mul_zero] at hh
      exact eq_neg_of_add_eq_zero_left hh
    have hAq : ρ A∈actualFormalCoordinateIdeal n univ^(q+1) := by
      rw [hφA]
      exact (actualFormalCoordinateIdeal n univ^(q+1)).neg_mem (pivotZeroProjection_mem_point_power e _ B hB)
    have hAsp : ρ A∈Ideal.span (range (fun i => ρ (H i))) := by
      have hm := Ideal.mem_map_of_mem ρ.toRingHom hAI
      rw [Ideal.map_span,←range_comp] at hm
      exact hm
    obtain ⟨C,hC,hCpow⟩ := exists_homogeneous_filtered_representation
      (fun i => ρ (H i)) d hShadow (ρ A) hAsp (q+1) hAq
    have hprojected : ρ A=(∑ i,ρ (H i)*ρ (C i)) := by
      have hh := congrArg ρ hC
      simpa only [map_sum,map_mul,pivotZeroProjection_idempotent,ρ] using hh
    let A' := ∑ i,H i*ρ (C i)
    have hA'I : A'∈Ideal.span (range H) := by
      apply Ideal.sum_mem
      intro i _
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_range_self (x := i))
    have hA'q : A'∈actualFormalCoordinateIdeal n univ^(q+1) := by
      apply Ideal.sum_mem
      intro i _
      exact product_mem_point_power _ _ (d i) (q+1-d i) (q+1) (hH i)
        (pivotZeroProjection_mem_point_power e _ _ (hCpow i)) (by omega)
    have hz : ρ (A-A')=0 := by
      rw [map_sub]
      change ρ A-ρ (∑ i,H i*ρ (C i))=0
      rw [map_sum]
      simp_rw [map_mul]
      change ρ A-(∑ i,ρ (H i)*pivotZeroProjection e (pivotZeroProjection e (C i)))=0
      simp_rw [pivotZeroProjection_idempotent]
      exact sub_eq_zero.mpr hprojected
    obtain ⟨K,hK⟩ := (pivotZeroProjection_eq_zero_iff e (A-A')).mp hz
    have hKI : K∈Ideal.span (range H) := by
      apply hReg
      rw [←hK]
      exact (Ideal.span (range H)).sub_mem hAI hA'I
    have hRem : F-K∈actualFormalCoordinateIdeal n univ^q := by
      apply point_power_of_X_mul_mem e q
      have heq : MvPowerSeries.X e*(F-K)=B+A' := by
        linear_combination hK-hAB
      rw [heq]
      exact (actualFormalCoordinateIdeal n univ^(q+1)).add_mem hB hA'q
    exact Submodule.mem_sup.mpr ⟨K,hKI,F-K,hRem,by ring⟩
  · intro hF
    obtain ⟨A,hAI,B,hB,rfl⟩ := Submodule.mem_sup.mp hF
    rw [add_mul]
    apply (Ideal.span (range H) ⊔ actualFormalCoordinateIdeal n univ^(q+1)).add_mem
    · exact (le_sup_left : Ideal.span (range H)≤_)
        ((Ideal.span (range H)).mul_mem_right _ hAI)
    · apply (le_sup_right : actualFormalCoordinateIdeal n univ^(q+1)≤_)
      have he : (MvPowerSeries.X e : MvPowerSeries (Fin n) ℂ)∈actualFormalCoordinateIdeal n univ^1 := by
        rw [pow_one]
        exact Ideal.subset_span ⟨e,mem_univ e,rfl⟩
      exact product_mem_point_power _ _ q 1 (q+1) hB he (by omega)

/-- The SAME original canonical family retains exact filtered division AND
all genuine exceptional initial-symbol colon identities before every order. -/
theorem exists_original_point_canonical_strict_symbol_family
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (j : Fin n) (b : Fin (0+n) → ℂ) :
    ∃ H : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)),
      (∀ a,(coordinateGerm (j.natAdd 0))^(normalExponentDegree a.val)*H a=
        actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b (originalReducedVertexBasis J a)) ∧
      actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b=Ideal.span (range H) ∧
      ∀ (_hOrder : ∀ a,H a∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (0+n)))^(normalExponentDegree a.val)),
        (∀ (q : ℕ) (F : MvPowerSeries (Fin n) ℂ),
          F∈Ideal.map (originalTaylorAlgHom n).toRingHom
            (actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b) →
          F∈actualFormalCoordinateIdeal n univ^q →
          ∃ Q : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
              (Ideal.map (originalTaylorAlgHom n).toRingHom J) → MvPowerSeries (Fin n) ℂ,
            F=(∑ a,originalTaylorAlgHom n (H a)*Q a) ∧
              ∀ a,Q a∈actualFormalCoordinateIdeal n univ^(q-normalExponentDegree a.val)) ∧
        ∀ q : ℕ,(Ideal.map (originalTaylorAlgHom n).toRingHom
          (actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b) ⊔
          actualFormalCoordinateIdeal n univ^(q+1)).colon {MvPowerSeries.X j}=
          Ideal.map (originalTaylorAlgHom n).toRingHom
            (actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b) ⊔
          actualFormalCoordinateIdeal n univ^q := by
  obtain ⟨H,hH,hNamed,hFiltered⟩ := exists_original_point_canonical_filtered_family J j b
  refine ⟨H,hH,hNamed,?_⟩
  intro hOrder
  refine ⟨hFiltered hOrder,?_⟩
  intro q
  rw [hNamed,Ideal.map_span,←range_comp]
  apply exceptional_point_power_colon_eq (fun a => originalTaylorAlgHom n (H a))
    (fun a => normalExponentDegree a.val) j
  · intro a
    apply (point_power_iff _ _).mpr
    intro γ hγ
    exact (mem_original_maximal_pow_iff_formal_coefficients_zero n _ (H a)).mp (hOrder a) γ
      (by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hγ)
  · exact fun a => canonical_quotient_shadow_homogeneous J a j b (H a) (hH a) (hOrder a)
  · apply taylor_span_exceptional_regular H j
    intro g hg
    have hr := (actual_point_normalized_member_iff_total_saturation J j b).2.1 g
    rw [hNamed] at hr
    exact hr.mp hg

end
end TranscendentalNakamaye.Pending.HironakaActualExceptionalFilteredDivision
