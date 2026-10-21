/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualNormalizedInitialRelations
import Hironaka.Resolution.HironakaActualExceptionalFibreRelations
import Hironaka.Resolution.HironakaActualPolynomialRehomogenization
import Hironaka.Resolution.HironakaActualStrictPullbackSaturation
import Mathlib.Algebra.MvPolynomial.Monad

/-!
# The whole actual point-normalized canonical ideal is exceptional saturation

Whole exceptional-fibre polynomial flatness, genuine finite rehomogenization
and actual analytic initial-syzygy lifts prove exceptional regularity for ONE
canonical normalized family. The independently defined entire normalized-member
ideal is the whole total-pullback saturation and, for original analytic subsets
in dimension at least two, the entire actual geometric strict ideal.

The centre is a point. Relative regular-centre extension, transformed maximal-
ideal standardness and reverse current Hilbert--Samuel persistence are separate.
Blueprint: `hironaka-actual-point-normalized-saturation-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualPointNormalizedSaturation
noncomputable section
open HolGerm HironakaActualOriginalTaylorPolynomial
  HironakaActualOriginalFormalTaylor HironakaActualOriginalReducedVertexBasis
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualNormalizedInitialRelations HironakaActualExceptionalFibreRelations
  HironakaActualPolynomialRehomogenization HironakaActualPointDehomogenizedInitial
  HironakaActualPointExceptionalInitialForm HironakaActualNormalAxisDehomogenization
  HironakaActualNormalQuotientExceptionalRestriction HironakaActualAnalyticBlowupTaylor
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis HironakaRelativeNormalActualBaseJetDimension
  HironakaHolomorphicJetMonomialSpan HironakaActualCoefficientPresentationCentrePower
variable {n : ℕ}

private theorem originalTaylor_polynomial (p : MvPolynomial (Fin n) ℂ) :
    originalTaylorAlgHom n (originalPolynomialEval n p)=(p : MvPowerSeries (Fin n) ℂ) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      rw [originalPolynomialEval,MvPolynomial.aeval_C,MvPolynomial.coe_C]
      exact (originalTaylorAlgHom n).commutes c
  | add p q hp hq => simpa only [map_add,MvPolynomial.coe_add] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
      simp only [map_mul,MvPolynomial.coe_mul,hp]
      rw [show originalPolynomialEval n (MvPolynomial.X i)=normalCoordinate 0 n i from MvPolynomial.aeval_X _ i,
        originalTaylorAlgHom_coordinate,MvPolynomial.coe_X]

private theorem polynomial_dehom_eval (j : Fin n) (b : Fin (0+n) → ℂ) (p : MvPolynomial (Fin n) ℂ) :
    originalPolynomialEval n (actualPointDehomogenization j (fun i => b (i.natAdd 0)) p)=
      actualDehomogenizedNormalPolynomialEval 0 n j b
        (p.map (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel 0))) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
      simp only [actualPointDehomogenization,MvPolynomial.aeval_C,originalPolynomialEval,
        MvPolynomial.map_C,actualDehomogenizedNormalPolynomialEval,MvPolynomial.eval₂Hom_C]
      rw [AlgHom.commutes]
      exact ((tangentPullback 0 n).commutes c).symm
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
      simp only [map_mul,hp]
      congr 1
      by_cases hi : i=j <;>
        simp [actualPointDehomogenization,originalPolynomialEval,
          actualDehomogenizedNormalPolynomialEval,hi]

private theorem fibre_polynomial_syzygies {ι : Type*} [Fintype ι]
    (j : Fin n) (p : ι → MvPolynomial (Fin n) ℂ) (A : ι → HolGerm (ComplexModel (0+n)))
    (hp : ∀ i α,α∈(p i).support→α j=0)
    (hRel : (∑ i,originalPolynomialEval n (p i)*A i)∈Ideal.span {coordinateGerm (j.natAdd 0)}) :
    ∃ (k : ℕ) (c : ι → Fin k → MvPolynomial (Fin n) ℂ)
      (B : Fin k → HolGerm (ComplexModel (0+n))),
      (∀ i,A i-(∑ l,originalPolynomialEval n (c i l)*B l)∈Ideal.span {coordinateGerm (j.natAdd 0)}) ∧
      (∀ l,∑ i,p i*c i l=0) ∧ ∀ i l α,α∈(c i l).support→α j=0 := by
  let e := Fintype.equivFin ι
  have hs : (∑ i : Fin (Fintype.card ι),originalPolynomialEval n (p (e.symm i))*A (e.symm i))∈
      Ideal.span {coordinateGerm (j.natAdd 0)} := by
    rw [e.symm.sum_comp (fun i => originalPolynomialEval n (p i)*A i)]
    exact hRel
  obtain ⟨k,c,B,hA,hc,hcp⟩ := exists_original_exceptional_polynomial_syzygies n (Fintype.card ι) j
    (fun i => p (e.symm i)) (fun i => A (e.symm i)) (fun i => hp (e.symm i)) hs
  refine ⟨k,fun i l => c (e i) l,B,?_,?_,?_⟩
  · intro i
    simpa only [Equiv.symm_apply_apply] using hA (e i)
  · intro l
    have h := hc l
    rw [← e.sum_comp (fun i => p (e.symm i)*c i l)] at h
    simpa only [Equiv.symm_apply_apply] using h
  · exact fun i l => hcp (e i) l



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

private theorem canonical_coefficient_lower_degree
    (J : Ideal (HolGerm (ComplexModel (0+n))))
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J))
    (α : Fin n →₀ ℕ) (hα : α.degree<normalExponentDegree a.val) :
    MvPowerSeries.coeff α (originalTaylorAlgHom n (originalReducedVertexBasis J a))=0 := by
  rw [originalReducedVertexBasis_taylor]
  apply actualReducedVertexSeries_coefficient_lower MonomialOrder.degLex _ a α
  apply MonomialOrder.degLex_lt_iff.mpr
  apply Finsupp.DegLex.lt_iff.mpr
  left
  simpa only [ofDegLex_toDegLex,Finsupp.degree_eq_sum,normalExponentDegree] using hα

private theorem canonical_point_power
    (J : Ideal (HolGerm (ComplexModel (0+n))))
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J)) :
    originalReducedVertexBasis J a∈normalIdeal 0 n^(normalExponentDegree a.val) := by
  rw [zeroTangentNormalIdeal_eq_maximalIdeal]
  apply (mem_original_maximal_pow_iff_formal_coefficients_zero n _ _).mpr
  intro α hα
  apply canonical_coefficient_lower_degree J a α
  simpa only [Finsupp.degree_eq_sum,normalExponentDegree] using hα

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- The SAME canonical actual analytic quotient has its literal finite polynomial exceptional initial value. -/
theorem canonical_point_quotient_initial_congruence
    (J : Ideal (HolGerm (ComplexModel (0+n))))
    (a : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map (originalTaylorAlgHom n).toRingHom J))
    (j : Fin n) (b : Fin (0+n) → ℂ) (H : HolGerm (ComplexModel (0+n)))
    (hH : (coordinateGerm (j.natAdd 0))^(normalExponentDegree a.val)*H=
      actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b (originalReducedVertexBasis J a)) :
    H-originalPolynomialEval n (actualPointDehomogenization j (fun i => b (i.natAdd 0))
      (actualPointHomogeneousPolynomial (normalExponentDegree a.val)
        (originalTaylorAlgHom n (originalReducedVertexBasis J a))))∈Ideal.span {coordinateGerm (j.natAdd 0)} := by
  let d := normalExponentDegree a.val
  let f := actualPointHomogeneousPolynomial d (originalTaylorAlgHom n (originalReducedVertexBasis J a))
  have hrem : originalReducedVertexBasis J a-originalPolynomialEval n f∈normalIdeal 0 n^(d+1) := by
    rw [zeroTangentNormalIdeal_eq_maximalIdeal]
    apply (mem_original_maximal_pow_iff_formal_coefficients_zero n _ _).mpr
    intro α hα
    rw [map_sub,originalTaylor_polynomial,map_sub]
    rw [show (f : MvPowerSeries (Fin n) ℂ)=MvPowerSeries.homogeneousComponent d
      (originalTaylorAlgHom n (originalReducedVertexBasis J a)) from actualPointHomogeneousPolynomial_coe _ _]
    rw [MvPowerSeries.coeff_homogeneousComponent]
    by_cases hαd : α.degree=d
    · rw [if_pos hαd,sub_self]
    · have hαlt : α.degree<d := by
        have he : α.degree=normalExponentDegree α := by simp only [Finsupp.degree_eq_sum,normalExponentDegree]
        rw [←he] at hα
        omega
      rw [if_neg hαd,sub_zero]
      exact canonical_coefficient_lower_degree J a α hαlt
  obtain ⟨K,hK,_hKT⟩ := exists_actualAnalyticBlowup_quotient (actualTangentCentreVariables 0 n)
    (j.natAdd 0) (show j.natAdd 0∈actualTangentCentreVariables 0 n from ⟨j,rfl⟩) b (d+1)
    (originalReducedVertexBasis J a-originalPolynomialEval n f)
    (by rw [actualAnalyticCoordinateIdeal_normal];exact hrem)
  have hf := (actualPointHomogeneousPolynomial_isHomogeneous d
    (originalTaylorAlgHom n (originalReducedVertexBasis J a))).map
      (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel 0))
  have hfactor := actualAnalyticBlowupPullback_normalPolynomial_homogeneous 0 n j b
    (f.map (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel 0))) d hf
  rw [normalPolynomialEval_original_coefficient_lift] at hfactor
  let D := actualDehomogenizedNormalPolynomialEval 0 n j b
    (f.map (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel 0)))
  have hfactor' : actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b
      (originalPolynomialEval n f)=(coordinateGerm (j.natAdd 0))^d*D := hfactor
  have hH' : (coordinateGerm (j.natAdd 0))^d*H=
      actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b (originalReducedVertexBasis J a) := hH
  have he0 : (coordinateGerm (j.natAdd 0) : HolGerm (ComplexModel (0+n)))≠0 :=
    HolomorphicGermReducednessBridge.coordinate_germ_ne_zero (j.natAdd 0)
  have hprod : (coordinateGerm (j.natAdd 0))^d*(H-D)=
      (coordinateGerm (j.natAdd 0))^d*(coordinateGerm (j.natAdd 0)*K) := by
    calc
      _=actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b
          (originalReducedVertexBasis J a-originalPolynomialEval n f) := by
        rw [map_sub,←hH',hfactor']
        ring
      _=(coordinateGerm (j.natAdd 0))^(d+1)*K := hK.symm
      _=_ := by rw [pow_succ];ring
  have heq : H-D=coordinateGerm (j.natAdd 0)*K := mul_left_cancel₀ (pow_ne_zero d he0) hprod
  change H-originalPolynomialEval n (actualPointDehomogenization j (fun i => b (i.natAdd 0)) f)∈_
  rw [polynomial_dehom_eval]
  rw [heq]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- ONE canonical normalized family has no exceptional torsion in its whole analytic quotient. -/
theorem exists_original_point_exceptional_regular_canonical_family
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (j : Fin n) (b : Fin (0+n) → ℂ) :
    ∃ H : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
        (Ideal.map (originalTaylorAlgHom n).toRingHom J) → HolGerm (ComplexModel (0+n)),
      (∀ a,(coordinateGerm (j.natAdd 0))^(normalExponentDegree a.val)*H a=
        actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b
          (originalReducedVertexBasis J a)) ∧
      ∀ g,coordinateGerm (j.natAdd 0)*g∈Ideal.span (Set.range H) ↔ g∈Ideal.span (Set.range H) := by
  obtain ⟨H,hH,hLift⟩ := exists_original_point_polynomial_relation_lifts J j b
  refine ⟨H,hH,?_⟩
  let V := actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
    (Ideal.map (originalTaylorAlgHom n).toRingHom J)
  let e : HolGerm (ComplexModel (0+n)) := coordinateGerm (j.natAdd 0)
  let E : Ideal (HolGerm (ComplexModel (0+n))) := Ideal.span {e}
  let f (a : V) := actualPointHomogeneousPolynomial (normalExponentDegree a.val)
    (originalTaylorAlgHom n (originalReducedVertexBasis J a))
  let p (a : V) := actualPointDehomogenization j (fun i => b (i.natAdd 0)) (f a)
  have hInit (a : V) : H a-originalPolynomialEval n (p a)∈E :=
    canonical_point_quotient_initial_congruence J a j b (H a) (hH a)
  have hp (a : V) (α : Fin n →₀ ℕ) (hα : α∈(p a).support) : α j=0 :=
    dehom_pivot_independent j (fun i => b (i.natAdd 0)) (f a) α hα
  have hf (a : V) : (f a).IsHomogeneous (normalExponentDegree a.val) :=
    actualPointHomogeneousPolynomial_isHomogeneous _ _
  intro g
  constructor
  · intro hg
    obtain ⟨A,hA⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg
    have hsum : (∑ a : V,H a*A a)=e*g := by simpa only [mul_comm] using hA
    have hdiff : (∑ a : V,(H a-originalPolynomialEval n (p a))*A a)∈E := by
      exact E.sum_mem (fun a _ => E.mul_mem_right (A a) (hInit a))
    have hpoly : (∑ a : V,originalPolynomialEval n (p a)*A a)∈E := by
      have heg : e*g∈E := E.mul_mem_right g (Ideal.mem_span_singleton_self e)
      convert E.sub_mem heg hdiff using 1
      rw [←hsum]
      simp_rw [sub_mul,Finset.sum_sub_distrib]
      ring
    obtain ⟨k,c,B,hAc,hc,hcp⟩ := fibre_polynomial_syzygies j p A hp hpoly
    have hcolumns (l : Fin k) : ∃ L : V → HolGerm (ComplexModel (0+n)),
        (∑ a,H a*L a)=0 ∧ ∀ a,L a-originalPolynomialEval n (c a l)∈E := by
      obtain ⟨D,P,hD,hP,hdehom,hrel⟩ := exists_homogeneous_polynomial_relation_lift j
        (fun i => b (i.natAdd 0)) f (fun a => c a l) (fun a => normalExponentDegree a.val)
        hf (fun a => hcp a l) (by simpa only [mul_comm] using hc l)
      have hformal : (∑ a : V,(P a : MvPowerSeries (Fin n) ℂ)*
          MvPowerSeries.homogeneousComponent (normalExponentDegree a.val)
            (originalTaylorAlgHom n (originalReducedVertexBasis J a)))=0 := by
        have ht := congrArg (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := ℂ)) hrel
        simpa only [map_sum,map_mul,map_zero,MvPolynomial.coeToMvPowerSeries.ringHom_apply,
          f,actualPointHomogeneousPolynomial_coe] using ht
      obtain ⟨L,R,hL,hLR⟩ := hLift D P hD hP hformal
      refine ⟨L,hL,?_⟩
      intro a
      rw [hLR a,←polynomial_dehom_eval,hdehom a]
      simp only [add_sub_cancel_left]
      exact E.mul_mem_right (R a) (Ideal.mem_span_singleton_self e)
    choose L hL hLc using hcolumns
    have hAL (a : V) : A a-(∑ l,L l a*B l)∈E := by
      have hdelta : (∑ l,(L l a-originalPolynomialEval n (c a l))*B l)∈E :=
        E.sum_mem (fun l _ => E.mul_mem_right (B l) (hLc l a))
      convert E.sub_mem (hAc a) hdelta using 1
      simp_rw [sub_mul,Finset.sum_sub_distrib]
      ring
    have hD (a : V) : ∃ d : HolGerm (ComplexModel (0+n)),d*e=A a-(∑ l,L l a*B l) :=
      Ideal.mem_span_singleton'.mp (hAL a)
    choose d hd using hD
    have hzero : (∑ a : V,H a*(∑ l,L l a*B l))=0 := by
      simp_rw [Finset.mul_sum,←mul_assoc]
      rw [Finset.sum_comm]
      simp only [←Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro l _
      rw [hL l,zero_mul]
    have heq : e*g=e*(∑ a : V,H a*d a) := by
      calc
        e*g=(∑ a : V,H a*A a) := hsum.symm
        _=(∑ a : V,H a*(A a-(∑ l,L l a*B l))) := by
          simp_rw [mul_sub,Finset.sum_sub_distrib]
          rw [hzero,sub_zero]
        _=(∑ a : V,H a*(d a*e)) := by simp_rw [hd]
        _=e*(∑ a : V,H a*d a) := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro a _;ring
    have he0 : e≠0 := HolomorphicGermReducednessBridge.coordinate_germ_ne_zero (j.natAdd 0)
    have hgEq := mul_left_cancel₀ he0 heq
    rw [hgEq]
    exact (Ideal.span (Set.range H)).sum_mem (fun a _ =>
      (Ideal.span (Set.range H)).mul_mem_right (d a) (Ideal.subset_span ⟨a,rfl⟩))
  · intro hg
    exact (Ideal.span (Set.range H)).mul_mem_left e hg


open HironakaActualAnalyticStrictGenerators

/-- The independently defined WHOLE actual point-normalized ideal is the whole exceptional saturation, with one finite colon and no exceptional torsion. -/
theorem actual_point_normalized_member_iff_total_saturation
    (J : Ideal (HolGerm (ComplexModel (0+n)))) (j : Fin n) (b : Fin (0+n) → ℂ) :
    let A := actualTangentCentreVariables 0 n
    let e := coordinateGerm (j.natAdd 0)
    let N := actualAnalyticNormalizedMemberIdeal J A (j.natAdd 0) b
    let T := Ideal.map (actualAnalyticBlowupPullback A (j.natAdd 0) b).toRingHom J
    (∀ g,g∈N ↔ ∃ q : ℕ,e^q*g∈T) ∧
    (∀ g,e*g∈N ↔ g∈N) ∧ ∃ D : ℕ,T.colon {e^D}=N := by
  dsimp only
  obtain ⟨H,hH,hreg⟩ := exists_original_point_exceptional_regular_canonical_family J j b
  let V := actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
    (Ideal.map (originalTaylorAlgHom n).toRingHom J)
  let e : HolGerm (ComplexModel (0+n)) := coordinateGerm (j.natAdd 0)
  let N := Ideal.span (Set.range H)
  let π := actualAnalyticBlowupPullback (actualTangentCentreVariables 0 n) (j.natAdd 0) b
  let T := Ideal.map π.toRingHom J
  have hpower (q : ℕ) (g : HolGerm (ComplexModel (0+n))) : e^q*g∈N ↔ g∈N := by
    induction q with
    | zero => simp only [pow_zero,one_mul]
    | succ q ih =>
      rw [pow_succ',mul_assoc,hreg,ih]
  have hTotal : T≤N := by
    rw [Ideal.map_le_iff_le_comap,←originalReducedVertexBasis_span J]
    apply Ideal.span_le.mpr
    rintro _ ⟨a,rfl⟩
    change π (originalReducedVertexBasis J a)∈N
    rw [←hH a]
    exact N.mul_mem_left _ (Ideal.subset_span ⟨a,rfl⟩)
  have hNamed : actualAnalyticNormalizedMemberIdeal J (actualTangentCentreVariables 0 n) (j.natAdd 0) b=N := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro g ⟨q,F,hF,_hFpower,hg⟩
      apply (hpower q g).mp
      rw [hg]
      exact hTotal (Ideal.mem_map_of_mem _ hF)
    · apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      apply Ideal.subset_span
      refine ⟨normalExponentDegree a.val,originalReducedVertexBasis J a,
        originalReducedVertexBasis_mem J a,?_,hH a⟩
      rw [actualAnalyticCoordinateIdeal_normal]
      exact canonical_point_power J a
  let D : ℕ := ∑ a : V,normalExponentDegree a.val
  have hD (a : V) : normalExponentDegree a.val≤D :=
    Finset.single_le_sum (fun (x : V) _ => Nat.zero_le (normalExponentDegree x.val)) (Finset.mem_univ a)
  have hclearGen (a : V) : e^D*H a∈T := by
    have heq : e^D*H a=e^(D-normalExponentDegree a.val)*(π (originalReducedVertexBasis J a)) := by
      rw [←hH a,←mul_assoc,←pow_add,Nat.sub_add_cancel (hD a)]
    rw [heq]
    exact T.mul_mem_left _ (Ideal.mem_map_of_mem _ (originalReducedVertexBasis_mem J a))
  have hclear (g : HolGerm (ComplexModel (0+n))) (hg : g∈N) : e^D*g∈T := by
    obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg
    rw [←hc,Finset.mul_sum]
    apply T.sum_mem
    intro a _
    have hm := T.mul_mem_left (c a) (hclearGen a)
    convert hm using 1
    ring
  rw [hNamed]
  refine ⟨?_,hreg,⟨D,?_⟩⟩
  · intro g
    exact ⟨fun hg => ⟨D,hclear g hg⟩,fun ⟨q,hq⟩ => (hpower q g).mp (hTotal hq)⟩
  · ext g
    rw [Submodule.mem_colon_singleton]
    change g*e^D∈T ↔ g∈N
    rw [mul_comm]
    exact ⟨fun hg => (hpower D g).mp (hTotal hg),hclear g⟩

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences HironakaRelativeNormalCoherentSaturation
  HironakaRelativeNormalDeformationInitialRelations
  HironakaActualStrictPullbackSaturation

/-- For an original analytic subset in dimension at least two, actual point-normalization gives its ENTIRE geometric strict ideal. -/
theorem actual_point_normalized_eq_geometric_strict (hn : 2≤n) (j : Fin n) (b : Fin (0+n) → ℂ)
    (W : Set (ComplexModel (0+n))) (hW : IsComplexAnalyticSubset (n := 0+n) W) :
    actualAnalyticNormalizedMemberIdeal (originalCoherentOriginIdeal (vanishingIdeal (n := 0+n) W))
      (actualTangentCentreVariables 0 n) (j.natAdd 0) b=
      originalCoherentOriginIdeal (vanishingIdeal (n := 0+n)
        (strictTransform (0+n) (actualAnalyticBlowupMap (actualTangentCentreVariables 0 n) (j.natAdd 0) b) W)) := by
  ext g
  exact ((actual_point_normalized_member_iff_total_saturation
    (originalCoherentOriginIdeal (vanishingIdeal (n := 0+n) W)) j b).1 g).trans
      (mem_original_analytic_strict_ideal_iff_exists_coordinate_power 0 n hn j b W hW g).symm

end
end Hironaka.HironakaActualPointNormalizedSaturation
