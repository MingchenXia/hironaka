import Hironaka.Resolution.HironakaActualUnshiftedInitialHSTransfer
import Hironaka.Resolution.HironakaActualPointExceptionalFibre
import Hironaka.Resolution.HironakaActualFormalStandardMonomialHS
import Hironaka.Resolution.HironakaActualExceptionalFibreJetClasses
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Directional stability from actual cone-point HS equality, through genuine
bounded polynomial vector spaces. Nonzero translation is applied only to finite
polynomials. The origin jet quotient is never formally translated. -/

set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualConeEqualityDirectionalStability
noncomputable section
open HironakaRelativeNormalMonomialBasis HironakaActualOriginalFormalHSTransfer
  HironakaActualHomogeneousInitialHS HironakaActualFiniteInitialGeneration
  HironakaActualTranslatedInitialHS HironakaActualUnshiftedInitialHSTransfer
  HironakaActualPointExceptionalFibre HironakaActualFormalInitialDiagram
  HironakaActualPointExceptionalFibreRadial HironakaActualExceptionalFibreJetClasses
  HironakaActualPointNormalizedBennett HironakaActualPointUnitCoordinateChange

attribute [local instance] MvPolynomial.gradedAlgebra
variable {n : ℕ}

private def polynomialFormalInclusion :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  { MvPolynomial.coeToMvPowerSeries.ringHom with
    commutes' := by
      intro c
      simp [MvPowerSeries.c_eq_algebraMap] }

/-- A nonzero translation is defined on finite polynomials, never on arbitrary formal series. -/
def actualPolynomialTranslation (v : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  MvPolynomial.aeval (fun i => MvPolynomial.X i + MvPolynomial.C (v i))

private theorem polynomialTranslation_X (v : Fin n → ℂ) (i : Fin n) :
    actualPolynomialTranslation v (MvPolynomial.X i)=MvPolynomial.X i+MvPolynomial.C (v i) :=
  MvPolynomial.aeval_X _ _

/-- The true finite polynomial translations are inverse on the entire polynomial ring. -/
theorem actualPolynomialTranslation_inverse (v : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) :
    actualPolynomialTranslation v (actualPolynomialTranslation (-v) P)=P := by
  have h : (actualPolynomialTranslation v).comp (actualPolynomialTranslation (-v))=
      AlgHom.id ℂ (MvPolynomial (Fin n) ℂ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [actualPolynomialTranslation,AlgHom.comp_apply]
  exact DFunLike.congr_fun h P

private theorem translated_monomial_totalDegree_le (v : Fin n → ℂ)
    (α : Fin n →₀ ℕ) (c : ℂ) :
    (actualPolynomialTranslation v (MvPolynomial.monomial α c)).totalDegree ≤ α.degree := by
  rw [actualPolynomialTranslation,MvPolynomial.aeval_monomial]
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.algebraMap_eq,MvPolynomial.totalDegree_C,zero_add]
  change (∏ i ∈ α.support, (MvPolynomial.X i + MvPolynomial.C (v i)) ^ α i).totalDegree ≤ _
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ i ∈ α.support, α i * 1 := by
      apply Finset.sum_le_sum
      intro i _
      apply (MvPolynomial.totalDegree_pow _ _).trans
      apply Nat.mul_le_mul_left
      apply (MvPolynomial.totalDegree_add _ _).trans
      simp
    _ = α.degree := by
      simp only [mul_one,Finsupp.degree_eq_sum]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact Finsupp.notMem_support_iff.mp hi

/-- Literal affine polynomial substitution cannot increase the actual total degree. -/
theorem totalDegree_actualPolynomialTranslation_le (v : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) : (actualPolynomialTranslation v P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [← P.support_sum_monomial_coeff,map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro α hα
  exact (translated_monomial_totalDegree_le v α _).trans (MvPolynomial.le_totalDegree hα)

/-- The actual finite bounded polynomial vector space. It is not a subring. -/
def actualBoundedPolynomials (n q : ℕ) : Submodule ℂ (MvPolynomial (Fin n) ℂ) where
  carrier := {P | ∀ α : Fin n →₀ ℕ, q ≤ α.degree → MvPolynomial.coeff α P=0}
  zero_mem' := by simp
  add_mem' := by intro P Q hP hQ α hα; simp [hP α hα,hQ α hα]
  smul_mem' := by intro c P hP α hα; simp [hP α hα]

private theorem bounded_of_totalDegree_lt (P : MvPolynomial (Fin n) ℂ) (q : ℕ)
    (hP : P.totalDegree < q) : P ∈ actualBoundedPolynomials n q := by
  intro α hα
  exact MvPolynomial.coeff_eq_zero_of_totalDegree_lt (lt_of_lt_of_le hP hα)

private theorem bounded_totalDegree_lt_of_ne_zero (q : ℕ)
    (P : actualBoundedPolynomials n q) (hne : P.val ≠ 0) : P.val.totalDegree < q := by
  have hpos : 0 < q := by
    obtain ⟨α,hα⟩ := MvPolynomial.exists_coeff_ne_zero hne
    by_contra h
    exact hα (P.property α (by omega))
  apply (Finset.sup_lt_iff hpos).mpr
  intro α hα
  by_contra h
  exact (MvPolynomial.mem_support_iff.mp hα) (P.property α (not_lt.mp h))

private theorem bounded_translation (v : Fin n → ℂ) (q : ℕ)
    (P : actualBoundedPolynomials n q) : actualPolynomialTranslation v P.val ∈ actualBoundedPolynomials n q := by
  by_cases hP : P.val=0
  · rw [hP,map_zero]
    exact (actualBoundedPolynomials n q).zero_mem
  · exact bounded_of_totalDegree_lt _ q
      (lt_of_le_of_lt (totalDegree_actualPolynomialTranslation_le v P.val)
        (bounded_totalDegree_lt_of_ne_zero q P hP))

private theorem bounded_truncTotal (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    MvPowerSeries.truncTotal q F ∈ actualBoundedPolynomials n q := by
  intro α hα
  exact MvPowerSeries.coeff_truncTotal_eq_zero F hα

private theorem formal_truncation_remainder (q : ℕ) (F : MvPowerSeries (Fin n) ℂ) :
    F - (MvPowerSeries.truncTotal q F : MvPowerSeries (Fin n) ℂ) ∈ genuineFormalVariables n ^ q := by
  apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mpr
  intro α hα
  rw [map_sub,MvPolynomial.coeff_coe,MvPowerSeries.coeff_truncTotal]
  · exact sub_self _
  · simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hα

private theorem coe_homogeneousComponent (q : ℕ) (P : MvPolynomial (Fin n) ℂ) :
    (MvPolynomial.homogeneousComponent q P : MvPowerSeries (Fin n) ℂ)=
      MvPowerSeries.homogeneousComponent q (P : MvPowerSeries (Fin n) ℂ) := by
  apply MvPowerSeries.ext
  intro α
  simp only [MvPolynomial.coeff_coe,MvPolynomial.coeff_homogeneousComponent,
    MvPowerSeries.coeff_homogeneousComponent]

private theorem truncation_polynomial_mem_of_homogeneous
    (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (q : ℕ) (P : MvPolynomial (Fin n) ℂ) (hP : P ∈ J) :
    MvPowerSeries.truncTotal q (P : MvPowerSeries (Fin n) ℂ) ∈ J := by
  have hsum : MvPowerSeries.truncTotal q (P : MvPowerSeries (Fin n) ℂ)=
      ∑ k ∈ Finset.range q, MvPolynomial.homogeneousComponent k P := by
    apply MvPolynomial.ext
    intro α
    rw [MvPowerSeries.coeff_truncTotal_eq_ite,MvPolynomial.coeff_sum]
    simp [MvPolynomial.coeff_homogeneousComponent]
  rw [hsum]
  exact J.sum_mem (fun k _ => MvPolynomial.homogeneousComponent_mem_of_mem hJ hP k)

/-- The homogeneous whole polynomial ideal is the exact bounded formal-jet kernel. -/
theorem bounded_polynomial_mem_formal_jet_iff
    (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (q : ℕ) (P : actualBoundedPolynomials n q) :
    (P.val : MvPowerSeries (Fin n) ℂ) ∈
      Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom J ⊔ genuineFormalVariables n ^ q ↔ P.val ∈ J := by
  constructor
  · intro hP
    obtain ⟨F,hF,Z,hZ,he⟩ := Submodule.mem_sup.mp hP
    obtain ⟨m,A,V,hV⟩ := Submodule.mem_span_set'.mp hF
    have hgen (i : Fin m) : ∃ R ∈ J, (R : MvPowerSeries (Fin n) ℂ)=(V i).val :=
      (V i).property
    choose R hRJ hRV using hgen
    have hFsum : F=∑ i : Fin m, A i * (R i : MvPowerSeries (Fin n) ℂ) := by
      calc
        _=∑ i : Fin m, A i * (V i).val := by simpa only [smul_eq_mul] using hV.symm
        _=_ := Finset.sum_congr rfl (fun i _ => by rw [hRV i])
    let T : MvPolynomial (Fin n) ℂ := ∑ i : Fin m, MvPowerSeries.truncTotal q (A i) * R i
    have hTJ : T ∈ J := J.sum_mem (fun i _ => J.mul_mem_left _ (hRJ i))
    have hFT : F-(T : MvPowerSeries (Fin n) ℂ) ∈ genuineFormalVariables n ^ q := by
      have h := (genuineFormalVariables n ^ q).sum_mem (fun i (_ : i ∈ Finset.univ) =>
        (genuineFormalVariables n ^ q).mul_mem_right (R i : MvPowerSeries (Fin n) ℂ)
          (formal_truncation_remainder q (A i)))
      have hcoeT : (T : MvPowerSeries (Fin n) ℂ)=
          ∑ i : Fin m, (MvPowerSeries.truncTotal q (A i) : MvPowerSeries (Fin n) ℂ) *
            (R i : MvPowerSeries (Fin n) ℂ) := by
        change MvPolynomial.coeToMvPowerSeries.ringHom
          (∑ i : Fin m, MvPowerSeries.truncTotal q (A i) * R i)=_
        simp only [map_sum,map_mul,MvPolynomial.coeToMvPowerSeries.ringHom_apply]
      rw [hcoeT]
      simpa only [sub_mul,Finset.sum_sub_distrib,← hFsum] using h
    have hPT : (P.val : MvPowerSeries (Fin n) ℂ)-(T : MvPowerSeries (Fin n) ℂ) ∈
        genuineFormalVariables n ^ q := by
      have h := (genuineFormalVariables n ^ q).add_mem hFT hZ
      have he' : F-(T : MvPowerSeries (Fin n) ℂ)+Z=
          (P.val : MvPowerSeries (Fin n) ℂ)-(T : MvPowerSeries (Fin n) ℂ) := by rw [← he]; abel
      rwa [he'] at h
    have hEq : MvPowerSeries.truncTotal q (T : MvPowerSeries (Fin n) ℂ)=P.val := by
      apply MvPolynomial.ext
      intro α
      by_cases hα : α.degree < q
      · rw [MvPowerSeries.coeff_truncTotal _ hα]
        have hc := (mem_genuineFormalVariables_pow_iff_coefficients_zero n q _).mp hPT α
          (by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hα)
        have hc' : MvPolynomial.coeff α P.val=MvPolynomial.coeff α T := by
          simpa only [map_sub,MvPolynomial.coeff_coe,sub_eq_zero] using hc
        exact hc'.symm
      · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (not_lt.mp hα),P.property α (not_lt.mp hα)]
    rw [← hEq]
    exact truncation_polynomial_mem_of_homogeneous J hJ q T hTJ
  · intro hP
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hP)

/-- The literal bounded polynomial map to the source whole formal jet. -/
def actualBoundedOriginJetMap (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : ℕ) :
    actualBoundedPolynomials n q →ₗ[ℂ]
      MvPowerSeries (Fin n) ℂ ⧸
        (Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom J ⊔ genuineFormalVariables n ^ q) :=
  (Ideal.Quotient.mkₐ ℂ _).toLinearMap.comp
    (polynomialFormalInclusion.toLinearMap.comp (actualBoundedPolynomials n q).subtype)

/-- The target map evaluates the same bounded polynomial after its genuine finite translation. -/
def actualBoundedTranslatedJetMap (J : Ideal (MvPolynomial (Fin n) ℂ))
    (v : Fin n → ℂ) (q : ℕ) :
    actualBoundedPolynomials n q →ₗ[ℂ]
      MvPowerSeries (Fin n) ℂ ⧸
        (Ideal.map (MvPolynomial.coeToMvPowerSeries.ringHom.comp (actualPolynomialTranslation v).toRingHom) J ⊔
          genuineFormalVariables n ^ q) :=
  (Ideal.Quotient.mkₐ ℂ _).toLinearMap.comp
    (polynomialFormalInclusion.toLinearMap.comp
      ((actualPolynomialTranslation v).toLinearMap.comp (actualBoundedPolynomials n q).subtype))

/-- Actual total truncation supplies source surjectivity before HS equality. -/
theorem actualBoundedOriginJetMap_surjective (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : ℕ) :
    Function.Surjective (actualBoundedOriginJetMap J q) := by
  intro z
  obtain ⟨F,rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨⟨MvPowerSeries.truncTotal q F,bounded_truncTotal q F⟩,?_⟩
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_sup_right
  change (MvPowerSeries.truncTotal q F : MvPowerSeries (Fin n) ℂ)-F ∈ genuineFormalVariables n ^ q
  simpa only [neg_sub] using
    (genuineFormalVariables n ^ q).neg_mem (formal_truncation_remainder q F)

/-- Inverse translation acts only on the finite truncation and supplies genuine target surjectivity. -/
theorem actualBoundedTranslatedJetMap_surjective
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (v : Fin n → ℂ) (q : ℕ) :
    Function.Surjective (actualBoundedTranslatedJetMap J v q) := by
  intro z
  obtain ⟨F,rfl⟩ := Ideal.Quotient.mk_surjective z
  let P : actualBoundedPolynomials n q := ⟨MvPowerSeries.truncTotal q F,bounded_truncTotal q F⟩
  refine ⟨⟨actualPolynomialTranslation (-v) P.val,bounded_translation (-v) q P⟩,?_⟩
  change Ideal.Quotient.mk _ ((actualPolynomialTranslation v
    (actualPolynomialTranslation (-v) P.val) : MvPolynomial (Fin n) ℂ) : MvPowerSeries (Fin n) ℂ)=_
  rw [actualPolynomialTranslation_inverse]
  apply Ideal.Quotient.eq.mpr
  apply Ideal.mem_sup_right
  simpa only [neg_sub] using
    (genuineFormalVariables n ^ q).neg_mem (formal_truncation_remainder q F)

private theorem finite_actualBoundedPolynomials (n q : ℕ) :
    Module.Finite ℂ (actualBoundedPolynomials n q) := by
  let := normalExponentFintype n q
  let f : actualBoundedPolynomials n q →ₗ[ℂ] (normalExponentIndex n q → ℂ) := {
    toFun P α := MvPolynomial.coeff α.val P.val
    map_add' P Q := by ext α; simp
    map_smul' c P := by ext α; simp }
  apply FiniteDimensional.of_injective f
  intro P Q h
  apply Subtype.ext
  apply MvPolynomial.ext
  intro α
  by_cases hα : α.degree < q
  · exact congrFun h ⟨α,by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hα⟩
  · rw [P.property α (not_lt.mp hα),Q.property α (not_lt.mp hα)]

/-- Genuine dimensions identify the two ACTUAL kernels on the same bounded polynomial space. -/
theorem bounded_polynomial_mem_of_translated_jet_zero_of_hs_eq
    (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ))
    (v : Fin n → ℂ) (ℓ : ℕ)
    (hHS : genuineFormalHilbertSamuelValue n
      (Ideal.map (MvPolynomial.coeToMvPowerSeries.ringHom.comp (actualPolynomialTranslation v).toRingHom) J) ℓ =
      genuineFormalHilbertSamuelValue n (Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom J) ℓ)
    (P : actualBoundedPolynomials n (ℓ+1))
    (hP : actualBoundedTranslatedJetMap J v (ℓ+1) P=0) : P.val ∈ J := by
  let := finite_actualBoundedPolynomials n (ℓ+1)
  let u := actualBoundedOriginJetMap J (ℓ+1)
  let w := actualBoundedTranslatedJetMap J v (ℓ+1)
  have hu := actualBoundedOriginJetMap_surjective J (ℓ+1)
  have hw := actualBoundedTranslatedJetMap_surjective J v (ℓ+1)
  have hle : LinearMap.ker u ≤ LinearMap.ker w := by
    intro P hP
    have hmem : P.val ∈ J := (bounded_polynomial_mem_formal_jet_iff J hJ (ℓ+1) P).mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hP)
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hmem)
  have hdu := u.finrank_range_add_finrank_ker
  have hdw := w.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hu,finrank_top] at hdu
  rw [LinearMap.range_eq_top.mpr hw,finrank_top] at hdw
  have hdim : Module.finrank ℂ (LinearMap.ker u)=Module.finrank ℂ (LinearMap.ker w) := by
    change genuineFormalHilbertSamuelValue n (Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom J) ℓ +
      Module.finrank ℂ (LinearMap.ker u)=_ at hdu
    change genuineFormalHilbertSamuelValue n
      (Ideal.map (MvPolynomial.coeToMvPowerSeries.ringHom.comp (actualPolynomialTranslation v).toRingHom) J) ℓ +
      Module.finrank ℂ (LinearMap.ker w)=_ at hdw
    omega
  have heq : LinearMap.ker u=LinearMap.ker w :=
    Submodule.eq_of_le_of_finrank_le hle (le_of_eq hdim.symm)
  have hPu : P ∈ LinearMap.ker u := by rw [heq]; exact hP
  exact (bounded_polynomial_mem_formal_jet_iff J hJ (ℓ+1) P).mp
    (Ideal.Quotient.eq_zero_iff_mem.mp hPu)

private theorem homogeneousComponent_mul_X_succ (q : ℕ) (i : Fin n)
    (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.homogeneousComponent (q+1) (P * MvPolynomial.X i)=
      MvPolynomial.homogeneousComponent q P * MvPolynomial.X i := by
  apply MvPolynomial.ext
  intro α
  by_cases hi : α i=0
  · simp [MvPolynomial.coeff_homogeneousComponent,MvPolynomial.coeff_mul_X',Finsupp.mem_support_iff,hi]
  · have hsingle : Finsupp.single i 1 ≤ α := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
    have he : (α-Finsupp.single i 1)+Finsupp.single i 1=α := tsub_add_cancel_of_le hsingle
    have hd : ((α-Finsupp.single i 1)+Finsupp.single i 1).degree=
        (α-Finsupp.single i 1).degree+1 := by simp
    rw [← he,MvPolynomial.coeff_homogeneousComponent,MvPolynomial.coeff_mul_X,
      MvPolynomial.coeff_mul_X,MvPolynomial.coeff_homogeneousComponent,hd]
    by_cases h : (α-Finsupp.single i 1).degree=q <;> simp [h]

private theorem homogeneousComponent_mul_X_zero (i : Fin n) (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.homogeneousComponent 0 (P * MvPolynomial.X i)=0 := by
  simp [MvPolynomial.homogeneousComponent_zero,MvPolynomial.coeff_mul_X']

private theorem monomial_translation_top (v : Fin n → ℂ)
    (α : Fin n →₀ ℕ) (c : ℂ) :
    MvPolynomial.homogeneousComponent α.degree
      (actualPolynomialTranslation v (MvPolynomial.monomial α c))=MvPolynomial.monomial α c := by
  generalize hd : α.degree=d
  induction d using Nat.strong_induction_on generalizing α with
  | h d ih =>
    cases d with
    | zero =>
      have hα : α=0 := (Finsupp.degree_eq_zero_iff α).mp hd
      subst α
      simp [actualPolynomialTranslation]
    | succ r =>
      have hα : α ≠ 0 := by intro hz; subst α; simp at hd
      obtain ⟨i,hi⟩ : ∃ i : Fin n, α i ≠ 0 := by
        by_contra h
        push Not at h
        exact hα (Finsupp.ext h)
      let β := α-Finsupp.single i 1
      have hsingle : Finsupp.single i 1 ≤ α :=
        Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
      have hsplit : β+Finsupp.single i 1=α := tsub_add_cancel_of_le hsingle
      have hβ : β.degree=r := by
        have he := congrArg Finsupp.degree hsplit
        simp only [map_add,Finsupp.degree_single,hd] at he
        omega
      have hmono : MvPolynomial.monomial α c=MvPolynomial.monomial β c * MvPolynomial.X i := by
        rw [MvPolynomial.X,MvPolynomial.monomial_mul,hsplit,mul_one]
      have htop := ih r (Nat.lt_succ_self r) β hβ
      have hhigh : MvPolynomial.homogeneousComponent (r+1)
          (actualPolynomialTranslation v (MvPolynomial.monomial β c))=0 :=
        MvPolynomial.homogeneousComponent_eq_zero (r+1) _ (lt_of_le_of_lt
          (translated_monomial_totalDegree_le v β c) (by omega))
      rw [hmono,map_mul,polynomialTranslation_X v i,
        mul_add,map_add,homogeneousComponent_mul_X_succ,htop]
      rw [mul_comm _ (MvPolynomial.C (v i)),MvPolynomial.homogeneousComponent_C_mul,hhigh,mul_zero,add_zero]

/-- The actual top homogeneous layer is unchanged by finite translation. -/
theorem homogeneousComponent_translation_top (v : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) (d : ℕ) (hP : P.IsHomogeneous d) :
    MvPolynomial.homogeneousComponent d (actualPolynomialTranslation v P)=P := by
  conv_lhs => rw [← P.support_sum_monomial_coeff,map_sum,map_sum]
  conv_rhs => rw [← P.support_sum_monomial_coeff]
  apply Finset.sum_congr rfl
  intro α hα
  have hdeg : α.degree=d := by
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hP (MvPolynomial.mem_support_iff.mp hα)
  rw [← hdeg,monomial_translation_top]

private theorem pderiv_translation (v : Fin n → ℂ) (i : Fin n)
    (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.pderiv i (actualPolynomialTranslation v P)=
      actualPolynomialTranslation v (MvPolynomial.pderiv i P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [actualPolynomialTranslation]
  | add P Q hP hQ => simp only [map_add,hP,hQ]
  | mul_X P j hP =>
    simp only [map_mul,Derivation.leibniz,smul_eq_mul,polynomialTranslation_X,
      map_add,MvPolynomial.pderiv_C,MvPolynomial.pderiv_X,hP]
    by_cases hij : i=j <;> simp [hij,eq_comm]

private theorem homogeneousComponent_pderiv (q : ℕ) (i : Fin n)
    (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.homogeneousComponent q (MvPolynomial.pderiv i P)=
      MvPolynomial.pderiv i (MvPolynomial.homogeneousComponent (q+1) P) := by
  apply MvPolynomial.ext
  intro α
  have hd : (α+Finsupp.single i 1).degree=α.degree+1 := by simp
  simp only [MvPolynomial.coeff_homogeneousComponent,MvPolynomial.coeff_pderiv,hd]
  by_cases h : α.degree=q <;> simp [h]

private theorem homogeneousComponent_X_pderiv (q : ℕ) (i : Fin n)
    (P : MvPolynomial (Fin n) ℂ) :
    MvPolynomial.homogeneousComponent q (MvPolynomial.X i * MvPolynomial.pderiv i P)=
      MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.homogeneousComponent q P) := by
  cases q with
  | zero =>
    calc
      MvPolynomial.homogeneousComponent 0 (MvPolynomial.X i * MvPolynomial.pderiv i P)=0 := by
        rw [mul_comm,homogeneousComponent_mul_X_zero]
      _=MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.homogeneousComponent 0 P) := by
        rw [MvPolynomial.homogeneousComponent_zero,MvPolynomial.pderiv_C,mul_zero]
  | succ q =>
    rw [mul_comm,homogeneousComponent_mul_X_succ,homogeneousComponent_pderiv,mul_comm]

/-- The actual next homogeneous layer is the same constant directional derivative. -/
theorem homogeneousComponent_translation_next (v : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) (q : ℕ) (hP : P.IsHomogeneous (q+1)) :
    MvPolynomial.homogeneousComponent q (actualPolynomialTranslation v P)=
      ∑ i : Fin n, v i • MvPolynomial.pderiv i P := by
  let T := actualPolynomialTranslation v P
  let Q := MvPolynomial.homogeneousComponent q T
  have he := congrArg (actualPolynomialTranslation v) hP.sum_X_mul_pderiv
  have hshift : ∑ i : Fin n, (MvPolynomial.X i+MvPolynomial.C (v i)) * MvPolynomial.pderiv i T =
      (q+1) • T := by
    simpa only [map_sum,map_mul,map_nsmul,← pderiv_translation,
      polynomialTranslation_X] using he
  have h := congrArg (MvPolynomial.homogeneousComponent q) hshift
  have htop : MvPolynomial.homogeneousComponent (q+1) T=P :=
    homogeneousComponent_translation_top v P (q+1) hP
  have hleft : MvPolynomial.homogeneousComponent q
      (∑ i : Fin n, (MvPolynomial.X i+MvPolynomial.C (v i)) * MvPolynomial.pderiv i T)=
      (∑ i : Fin n, MvPolynomial.X i * MvPolynomial.pderiv i Q) +
        ∑ i : Fin n, v i • MvPolynomial.pderiv i P := by
    rw [map_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [add_mul,map_add,homogeneousComponent_X_pderiv,
      MvPolynomial.homogeneousComponent_C_mul,homogeneousComponent_pderiv,htop]
    rw [MvPolynomial.smul_eq_C_mul]
  rw [hleft,map_nsmul,(MvPolynomial.homogeneousComponent_isHomogeneous q T).sum_X_mul_pderiv,
    succ_nsmul] at h
  exact (add_left_cancel h).symm

private def polynomialDirectionalMap (v : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin n) ℂ :=
  ∑ i : Fin n, v i • (MvPolynomial.pderiv i).toLinearMap

private theorem polynomialDirectionalMap_apply (v : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ) :
    polynomialDirectionalMap v P=∑ i : Fin n, v i • MvPolynomial.pderiv i P := by
  simp [polynomialDirectionalMap]

private theorem derivative_homogeneous_zero (v : Fin n → ℂ)
    (P : MvPolynomial (Fin n) ℂ) (hP : P.IsHomogeneous 0) : polynomialDirectionalMap v P=0 := by
  have hC : P=MvPolynomial.C (MvPolynomial.coeff 0 P) := by
    exact (MvPolynomial.homogeneousComponent_eq_self hP).symm.trans
      (MvPolynomial.homogeneousComponent_zero P)
  rw [hC,polynomialDirectionalMap_apply]
  simp

/-- Equality at the genuine translated cone point produces WHOLE polynomial directional stability. -/
theorem polynomial_directional_derivative_mem_of_hs_eq
    (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ)) (v : Fin n → ℂ)
    (hHS : ∀ ℓ : ℕ, genuineFormalHilbertSamuelValue n
      (Ideal.map (MvPolynomial.coeToMvPowerSeries.ringHom.comp (actualPolynomialTranslation v).toRingHom) J) ℓ =
      genuineFormalHilbertSamuelValue n (Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom J) ℓ)
    (F : MvPolynomial (Fin n) ℂ) (hF : F ∈ J) :
    (∑ i : Fin n, v i • MvPolynomial.pderiv i F) ∈ J := by
  have hhom (P : MvPolynomial (Fin n) ℂ) (hPJ : P ∈ J) (d : ℕ) (hP : P.IsHomogeneous d) :
      polynomialDirectionalMap v P ∈ J := by
    cases d with
    | zero => rw [derivative_homogeneous_zero v P hP]; exact J.zero_mem
    | succ r =>
      let Q := P-actualPolynomialTranslation (-v) P
      have hQbound : Q ∈ actualBoundedPolynomials n (r+1) := by
        intro α hα
        by_cases he : α.degree=r+1
        · have hc := congrArg (MvPolynomial.coeff α)
            (homogeneousComponent_translation_top (-v) P (r+1) hP)
          simp only [MvPolynomial.coeff_homogeneousComponent,he,ite_true] at hc
          simp only [Q,MvPolynomial.coeff_sub,hc,sub_self]
        · have hlt : r+1 < α.degree := by omega
          have h0 := MvPolynomial.coeff_eq_zero_of_totalDegree_lt
            (lt_of_le_of_lt hP.totalDegree_le hlt)
          have h1 := MvPolynomial.coeff_eq_zero_of_totalDegree_lt
            (lt_of_le_of_lt ((totalDegree_actualPolynomialTranslation_le (-v) P).trans hP.totalDegree_le) hlt)
          simp only [Q,MvPolynomial.coeff_sub,h0,h1,sub_self]
      have hQjet : actualBoundedTranslatedJetMap J v (r+1) ⟨Q,hQbound⟩=0 := by
        apply Ideal.Quotient.eq_zero_iff_mem.mpr
        change (actualPolynomialTranslation v Q : MvPowerSeries (Fin n) ℂ) ∈ _
        have hQ : actualPolynomialTranslation v Q=actualPolynomialTranslation v P-P := by
          dsimp only [Q]
          rw [map_sub,actualPolynomialTranslation_inverse]
        rw [hQ]
        change polynomialFormalInclusion (actualPolynomialTranslation v P-P) ∈ _
        rw [map_sub]
        apply Ideal.sub_mem _
        · exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hPJ)
        · apply Ideal.mem_sup_right
          change (P : MvPowerSeries (Fin n) ℂ) ∈ genuineFormalVariables n ^ (r+1)
          apply (mem_genuineFormalVariables_pow_iff_coefficients_zero n (r+1) _).mpr
          intro α hα
          rw [MvPolynomial.coeff_coe]
          apply hP.coeff_eq_zero
          have hd : α.degree < r+1 := by simpa only [normalExponentDegree,Finsupp.degree_eq_sum] using hα
          omega
      have hQJ := bounded_polynomial_mem_of_translated_jet_zero_of_hs_eq J hJ v r (hHS r)
        ⟨Q,hQbound⟩ hQjet
      have hQr := MvPolynomial.homogeneousComponent_mem_of_mem hJ hQJ r
      have hPr : MvPolynomial.homogeneousComponent r P=0 := by
        rw [MvPolynomial.homogeneousComponent_of_mem hP,if_neg (by omega : r ≠ r+1)]
      have hEq : MvPolynomial.homogeneousComponent r Q=polynomialDirectionalMap v P := by
        dsimp only [Q]
        rw [map_sub,hPr,homogeneousComponent_translation_next (-v) P r hP,
          zero_sub,polynomialDirectionalMap_apply]
        simp only [Pi.neg_apply,neg_smul,Finset.sum_neg_distrib,neg_neg]
      rwa [hEq] at hQr
  rw [← polynomialDirectionalMap_apply,← MvPolynomial.sum_homogeneousComponent F,map_sum]
  exact J.sum_mem (fun d _ => hhom _
    (MvPolynomial.homogeneousComponent_mem_of_mem hJ hF d) d
    (MvPolynomial.homogeneousComponent_isHomogeneous d F))

private def formalDirectionalMap (v : Fin n → ℂ) :
    MvPowerSeries (Fin n) ℂ →ₗ[ℂ] MvPowerSeries (Fin n) ℂ :=
  ∑ i : Fin n, v i • (MvPowerSeries.pderiv ℂ i).toLinearMap

private theorem formalDirectionalMap_apply (v : Fin n → ℂ) (F : MvPowerSeries (Fin n) ℂ) :
    formalDirectionalMap v F=∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F := by
  simp [formalDirectionalMap]

private theorem formalDirectionalMap_polynomial (v : Fin n → ℂ) (P : MvPolynomial (Fin n) ℂ) :
    formalDirectionalMap v (P : MvPowerSeries (Fin n) ℂ)=
      (polynomialDirectionalMap v P : MvPowerSeries (Fin n) ℂ) := by
  rw [formalDirectionalMap_apply,polynomialDirectionalMap_apply]
  change (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i (P : MvPowerSeries (Fin n) ℂ))=
    polynomialFormalInclusion (∑ i : Fin n, v i • MvPolynomial.pderiv i P)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul,MvPowerSeries.pderiv_coe]
  rfl

private theorem formalDirectionalMap_leibniz (v : Fin n → ℂ)
    (F G : MvPowerSeries (Fin n) ℂ) :
    formalDirectionalMap v (F*G)=F*formalDirectionalMap v G+G*formalDirectionalMap v F := by
  simp only [formalDirectionalMap_apply,Derivation.leibniz,smul_eq_mul,smul_add,
    Finset.sum_add_distrib,Finset.mul_sum,mul_smul_comm]

/-- The produced polynomial stability extends to every member of the unchanged whole formal ideal. -/
theorem formal_directional_derivative_mem_of_hs_eq
    (J : Ideal (MvPolynomial (Fin n) ℂ))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin n) ℂ)) (v : Fin n → ℂ)
    (hHS : ∀ ℓ : ℕ, genuineFormalHilbertSamuelValue n
      (Ideal.map (MvPolynomial.coeToMvPowerSeries.ringHom.comp (actualPolynomialTranslation v).toRingHom) J) ℓ =
      genuineFormalHilbertSamuelValue n (Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom J) ℓ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom J) :
    (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈ Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom J := by
  obtain ⟨m,A,V,hV⟩ := Submodule.mem_span_set'.mp hF
  have hgen (i : Fin m) : ∃ R ∈ J, (R : MvPowerSeries (Fin n) ℂ)=(V i).val := (V i).property
  choose R hRJ hRV using hgen
  have hFsum : F=∑ i : Fin m, A i * (R i : MvPowerSeries (Fin n) ℂ) := by
    calc
      _=∑ i : Fin m, A i * (V i).val := by simpa only [smul_eq_mul] using hV.symm
      _=_ := Finset.sum_congr rfl (fun i _ => by rw [hRV i])
  rw [← formalDirectionalMap_apply,hFsum,map_sum]
  apply Ideal.sum_mem
  intro i _
  rw [formalDirectionalMap_leibniz,formalDirectionalMap_polynomial]
  apply Ideal.add_mem
  · apply Ideal.mul_mem_left
    apply Ideal.mem_map_of_mem
    rw [polynomialDirectionalMap_apply]
    exact polynomial_directional_derivative_mem_of_hs_eq J hJ v hHS (R i) (hRJ i)
  · apply Ideal.mul_mem_right
    exact Ideal.mem_map_of_mem _ (hRJ i)

private def actualFiniteInitialPolynomialIdeal (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (range (actualInitialVertexPolynomial K))

private theorem actualFiniteInitialPolynomialIdeal_homogeneous
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    (actualFiniteInitialPolynomialIdeal K).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule (Fin n) ℂ) := by
  apply Ideal.homogeneous_span
  rintro P ⟨a,rfl⟩
  exact ⟨normalExponentDegree a.val,actualInitialVertexPolynomial_isHomogeneous K a⟩

private theorem map_actualFiniteInitialPolynomialIdeal
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) :
    Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom (actualFiniteInitialPolynomialIdeal K)=
      actualHomogeneousInitialIdeal K := by
  rw [actualFiniteInitialPolynomialIdeal,Ideal.map_span,← Set.range_comp,
    actualHomogeneousInitialIdeal_eq_initial_vertex_span,actualInitialVertexSpan]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact actualInitialVertexPolynomial_coe K a

private theorem map_translated_actualFiniteInitialPolynomialIdeal
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (v : Fin n → ℂ) :
    Ideal.map (MvPolynomial.coeToMvPowerSeries.ringHom.comp (actualPolynomialTranslation v).toRingHom)
      (actualFiniteInitialPolynomialIdeal K)=actualTranslatedInitialFormalIdeal K v := by
  have hm : polynomialFormalInclusion.comp (actualPolynomialTranslation v)=
      MvPolynomial.aeval (fun i => MvPowerSeries.X i+algebraMap ℂ _ (v i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [actualPolynomialTranslation,polynomialFormalInclusion,AlgHom.comp_apply,
      MvPowerSeries.c_eq_algebraMap]
  rw [actualFiniteInitialPolynomialIdeal,Ideal.map_span,← Set.range_comp,actualTranslatedInitialFormalIdeal]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext a
  exact DFunLike.congr_fun hm (actualInitialVertexPolynomial K a)

/-- Cone-point HS equality INTERNALIZES the actual direction as a derivation of the whole original initial ideal. -/
theorem actual_homogeneous_initial_directional_stable_of_translated_hs_eq
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (v : Fin n → ℂ)
    (hHS : ∀ ℓ : ℕ,
      HironakaHolomorphicPointJets.hilbertSamuelValue (actualUnshiftedTranslatedInitialIdeal K v) ℓ =
        genuineFormalHilbertSamuelValue n K ℓ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualHomogeneousInitialIdeal K) :
    (∑ i : Fin n, v i • MvPowerSeries.pderiv ℂ i F) ∈ actualHomogeneousInitialIdeal K := by
  have heq (ℓ : ℕ) : genuineFormalHilbertSamuelValue n
      (Ideal.map (MvPolynomial.coeToMvPowerSeries.ringHom.comp (actualPolynomialTranslation v).toRingHom)
        (actualFiniteInitialPolynomialIdeal K)) ℓ =
      genuineFormalHilbertSamuelValue n
        (Ideal.map MvPolynomial.coeToMvPowerSeries.ringHom (actualFiniteInitialPolynomialIdeal K)) ℓ := by
    rw [map_translated_actualFiniteInitialPolynomialIdeal,map_actualFiniteInitialPolynomialIdeal,
      ← actualUnshiftedTranslatedInitialIdeal_formal_extension,
      ← hilbertSamuelValue_eq_actual_unshifted_formal_extension]
    exact (hHS ℓ).trans (genuineFormalHilbertSamuelValue_homogeneous_initial K ℓ)
  rw [← map_actualFiniteInitialPolynomialIdeal K] at hF ⊢
  exact formal_directional_derivative_mem_of_hs_eq _
    (actualFiniteInitialPolynomialIdeal_homogeneous K) v heq F hF

/-- Original point strict/source equality PRODUCES its actual chart direction's whole initial stability. -/
theorem actual_homogeneous_initial_directional_stable_of_point_strict_hs_eq
    (K : Ideal (MvPowerSeries (Fin n) ℂ)) (e : Fin n) (b : Fin n → ℂ)
    (hHS : ∀ ℓ : ℕ, genuineFormalHilbertSamuelValue n
      (HironakaActualFormalStrictGenerators.actualFormalStrictTransform K Set.univ e (mem_univ e) b) ℓ =
        genuineFormalHilbertSamuelValue n K ℓ)
    (F : MvPowerSeries (Fin n) ℂ) (hF : F ∈ actualHomogeneousInitialIdeal K) :
    (∑ i : Fin n, (actualPointUnitBasePoint e b i) • MvPowerSeries.pderiv ℂ i F) ∈
      actualHomogeneousInitialIdeal K := by
  apply actual_homogeneous_initial_directional_stable_of_translated_hs_eq K
    (actualPointUnitBasePoint e b) ?_ F hF
  intro ℓ
  have hd : genuineFormalHilbertSamuelValue n (actualDehomogenizedPointInitialConeIdeal K e b) ℓ =
      genuineFormalHilbertSamuelValue n K ℓ := by
    rw [← card_actualExceptionalJetIndex_dehomogenized K e b ℓ]
    exact (actual_point_strict_exceptional_jet_source_dimension_eq_of_hs_eq K e b ℓ (hHS ℓ)).trans (hHS ℓ)
  rw [← hilbertSamuelValue_actualDehomogenizedInitialIdeal_eq_translated K e b ℓ,
    hilbertSamuelValue_eq_actual_unshifted_formal_extension,
    actualDehomogenizedInitialIdeal_formal_extension_whole_cone]
  exact hd

end
end Hironaka.HironakaActualConeEqualityDirectionalStability
