/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualNormalFilteredOwnerDivision
import Hironaka.Resolution.HironakaActualRelativeExceptionalFibreRelations
import Hironaka.Resolution.HironakaActualRelativePolynomialRehomogenization

/-!
# The whole relative canonical normalized ideal is exceptional saturation

Complete actual exceptional-fibre syzygies over the ORIGINAL analytic tangent
ring, genuine finite rehomogenization and source normal-filtered analytic
relation lifts prove exceptional regularity for the SAME prescribed canonical
normalized family. The independently defined entire normalized-member ideal
is the WHOLE total-pullback exceptional saturation with one finite colon.
Original regular-centre HSconstancy internally fixes one chart/canonical family
before ALL normal-pivot charts, with no family/power/regularity certificate.

Transformed maximal-ideal standardness, reverse current HS persistence and a
uniform history driver remain separate.
Blueprint: `hironaka-actual-relative-normalized-saturation-extension.tex`.
-/
set_option autoImplicit false
open Set Classical
open scoped BigOperators
namespace Hironaka.HironakaActualRelativeNormalizedSaturation
noncomputable section
open HolGerm HironakaActualOriginalFormalTaylor HironakaActualOriginalReducedVertexBasis HironakaHolomorphicJetMonomialSpan HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  HironakaActualFormalInitialDiagram HironakaActualReducedFormalStandardBasis
  HironakaActualCoefficientPresentationCentrePower HironakaActualAnalyticBlowupTaylor
  HironakaActualNormalHomogeneousComponents HironakaActualNormalQuotientExceptionalRestriction
  HironakaActualNormalAxisDehomogenization HironakaActualAnalyticFormalNormalPowers
  HironakaRelativeNormalPolynomialJetAlgebra HironakaActualNormalFilteredOwnerDivision
  HironakaActualRelativeExceptionalFibreRelations HironakaActualRelativePolynomialRehomogenization
  HironakaActualFormalCoordinatePowerDivision HironakaActualRelativeTaylorCoefficients
variable {d t : ℕ}
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Actual point powers, genuine exceptional quotients anw analytic-domain cancellation transport a whole weighted source syzygy. -/
private theorem exists_relative_normalized_syzygy {ι : Type*} [Fintype ι]
    (d t : ℕ) (G C H : ι → HolGerm (ComplexModel (d+t))) (w : ι → ℕ) (D : ℕ)
    (hd : ∀ a,w a≤D)
    (hC : ∀ a,C a∈normalIdeal d t^(D-w a))
    (hRel : (∑ a,G a*C a)=0)
    (j : Fin t) (b : Fin (d+t) → ℂ)
    (hH : ∀ a,(coordinateGerm (j.natAdd d))^(w a)*H a=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (G a)) :
    ∃ L : ι → HolGerm (ComplexModel (d+t)),
      (∀ a,(coordinateGerm (j.natAdd d))^(D-w a)*L a=
        actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (C a)) ∧
      (∑ a,H a*L a)=0 := by
  have hq (a : ι) := exists_actualAnalyticBlowup_quotient (actualTangentCentreVariables d t)
    (j.natAdd d) (show j.natAdd d∈actualTangentCentreVariables d t from ⟨j,rfl⟩) b (D-w a) (C a)
    (by rw [actualAnalyticCoordinateIdeal_normal];exact hC a)
  choose L hL using hq
  refine ⟨L,fun a => (hL a).1,?_⟩
  have he0 : (coordinateGerm (j.natAdd d) : HolGerm (ComplexModel (d+t)))≠0 :=
    HolomorphicGermReducednessBridge.coordinate_germ_ne_zero (j.natAdd d)
  apply mul_left_cancel₀ (pow_ne_zero D he0)
  rw [mul_zero,Finset.mul_sum]
  calc
    _=(∑ a,actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (G a*C a)) := by
      apply Finset.sum_congr rfl
      intro a _
      have hdeg : w a+(D-w a)=D := Nat.add_sub_of_le (hd a)
      calc
        _=(coordinateGerm (j.natAdd d))^(w a+(D-w a))*(H a*L a) := by rw [hdeg]
        _=((coordinateGerm (j.natAdd d))^(w a)*H a)*
            ((coordinateGerm (j.natAdd d))^(D-w a)*L a) := by rw [pow_add];ring
        _=_ := by rw [hH a,(hL a).1,map_mul]
    _=0 := by rw [←map_sum,hRel,map_zero]

private theorem homogeneous_normalPolynomialEval_mem (d t q : ℕ)
    (P : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (hP : P.IsHomogeneous q) :
    normalPolynomialEval d t P∈normalIdeal d t ^ q := by
  apply (normalPolynomialEval_mem_power_iff d t q P).mpr
  apply (actualPolynomialNormalIdeal_power_iff_coefficients d t q P).mpr
  intro α hα
  by_contra hc
  have hd := hP hc
  change Finsupp.weight (fun _ : Fin t => (1 : ℕ)) α=q at hd
  have heq : normalExponentDegree α=q := by
    simpa only [←Finsupp.degree_eq_weight_one,Finsupp.degree_eq_sum,normalExponentDegree] using hd
  omega

private theorem unshiftedTaylor_property (n : ℕ)
    (P : (m : ℕ) → (HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) → Prop)
    (h : P (0+n) (originalTaylorAlgHom n)) : P n (actualUnshiftedTaylorAlgHom n) := by
  have hc {m : ℕ} (hm : m=n)
      (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) (hf : P m f) :
      P n (cast (congrArg (fun j => HolGerm (ComplexModel j) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) hm) f) := by
    subst m
    exact hf
  exact hc (Nat.zero_add n) (originalTaylorAlgHom n) h

private theorem prescribed_canonical_span (n : ℕ) (I : Ideal (HolGerm (ComplexModel n)))
    (G : actualInitialVertices (MonomialOrder.degLex (σ := Fin n))
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) → HolGerm (ComplexModel n))
    (hG : ∀ a,actualUnshiftedTaylorAlgHom n (G a)=actualReducedVertexSeries MonomialOrder.degLex
      (Ideal.map (actualUnshiftedTaylorAlgHom n).toRingHom I) a) : Ideal.span (range G)=I := by
  let P (m : ℕ) (f : HolGerm (ComplexModel m) →ₐ[ℂ] MvPowerSeries (Fin n) ℂ) : Prop :=
    ∀ (J : Ideal (HolGerm (ComplexModel m)))
      (B : actualInitialVertices (MonomialOrder.degLex (σ := Fin n)) (Ideal.map f.toRingHom J) →
        HolGerm (ComplexModel m)),
      (∀ a,f (B a)=actualReducedVertexSeries MonomialOrder.degLex (Ideal.map f.toRingHom J) a) →
        Ideal.span (range B)=J
  have h : P (0+n) (originalTaylorAlgHom n) := by
    intro J B hB
    have he : B=originalReducedVertexBasis J := by
      funext a
      apply originalTaylorAlgHom_injective n
      rw [hB,originalReducedVertexBasis_taylor]
    rw [he]
    exact originalReducedVertexBasis_span J
  exact unshiftedTaylor_property n P h I G hG

private abbrev relativeVertices (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t)))) :=
  actualInitialVertices (MonomialOrder.degLex (σ := Fin (d+t)))
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I)
private def relativeWeight (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
    (a : relativeVertices d t I) : ℕ :=
  Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val

private theorem dehom_pivot_independent (j : Fin t) (b : Fin (d+t) → ℂ)
    (f : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (α : Fin t →₀ ℕ) (hα : α∈(relativePolynomialDehomogenization j b f).support) : α j=0 := by
  apply MvPolynomial.mem_support_notMem_vars_zero hα
  intro hj
  change j∈(MvPolynomial.aeval (fun i => if i=j then 1 else
    MvPolynomial.C ((HolGerm.constHom (b (i.natAdd d)) : HolGerm (ComplexModel d)))+MvPolynomial.X i) f).vars at hj
  rw [MvPolynomial.aeval_eq_bind₁] at hj
  obtain ⟨i,_hi,hvar⟩ := MvPolynomial.mem_vars_bind₁ _ _ hj
  by_cases hie : i=j
  · simp [hie] at hvar
  · have hx : j∈(MvPolynomial.C ((HolGerm.constHom (b (i.natAdd d)) : HolGerm (ComplexModel d)))+MvPolynomial.X i).vars := by
      simpa [hie] using hvar
    have heq : j=i := by
      simpa using MvPolynomial.vars_add_subset
        (MvPolynomial.C ((HolGerm.constHom (b (i.natAdd d)) : HolGerm (ComplexModel d)))) (MvPolynomial.X i) hx
    exact hie heq.symm

variable (d t : ℕ) (I : Ideal (HolGerm (ComplexModel (d+t))))
variable (G : (relativeVertices d t I) → HolGerm (ComplexModel (d+t)))
  (hG : ∀ a,actualUnshiftedTaylorAlgHom (d+t) (G a)=actualReducedVertexSeries MonomialOrder.degLex
    (Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I) a)
  (hpower : ∀ a,G a∈normalIdeal d t ^((relativeWeight d t I) a))
include hG hpower

attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- Whole homogeneous relative source relations have actual normalized lifts for this SAME prescribed H. -/
theorem relative_normalized_polynomial_relation_lift (j : Fin t) (b : Fin (d+t) → ℂ)
    (H : (relativeVertices d t I) → HolGerm (ComplexModel (d+t)))
    (hH : ∀ a,(coordinateGerm (j.natAdd d))^((relativeWeight d t I) a)*H a=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (G a))
    (D : ℕ) (p : (relativeVertices d t I) → MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hD : ∀ a : (relativeVertices d t I),(relativeWeight d t I) a≤D) (hp : ∀ a,(p a).IsHomogeneous (D-(relativeWeight d t I) a))
    (hrel : (∑ a,p a*actualNormalHomogeneousPolynomial d t ((relativeWeight d t I) a) (G a))=0) :
    ∃ L : (relativeVertices d t I) → HolGerm (ComplexModel (d+t)),
      (∑ a,H a*L a)=0 ∧ ∀ a,L a-normalPolynomialEval d t (relativePolynomialDehomogenization j b (p a))∈
        Ideal.span {coordinateGerm (j.natAdd d)} := by
  obtain ⟨C,hRel,hCorr⟩ := exists_normal_homogeneous_initial_syzygy d t I G hG hpower D p hD hp hrel
  have hP (a : (relativeVertices d t I)) := homogeneous_normalPolynomialEval_mem d t (D-(relativeWeight d t I) a) (p a) (hp a)
  have hCorr' (a : (relativeVertices d t I)) : normalPolynomialEval d t (p a)-C a∈normalIdeal d t ^((D-(relativeWeight d t I) a)+1) := by
    have he : D+1-(relativeWeight d t I) a=(D-(relativeWeight d t I) a)+1 := by have := hD a;omega
    rw [←he]
    exact hCorr a
  have hC (a : (relativeVertices d t I)) : C a∈normalIdeal d t ^(D-(relativeWeight d t I) a) := by
    have hc := Ideal.pow_le_pow_right (Nat.le_succ (D-(relativeWeight d t I) a)) (hCorr' a)
    convert (normalIdeal d t ^(D-(relativeWeight d t I) a)).sub_mem (hP a) hc using 1
    ring
  obtain ⟨L,hL,hLRel⟩ := exists_relative_normalized_syzygy d t G C H (relativeWeight d t I) D hD hC hRel j b hH
  have hRq (a : (relativeVertices d t I)) := exists_actualAnalyticBlowup_quotient (actualTangentCentreVariables d t)
    (j.natAdd d) (show j.natAdd d∈actualTangentCentreVariables d t from ⟨j,rfl⟩) b
    ((D-(relativeWeight d t I) a)+1) (C a-normalPolynomialEval d t (p a))
    (by rw [actualAnalyticCoordinateIdeal_normal];simpa only [neg_sub] using
      (normalIdeal d t ^_).neg_mem (hCorr' a))
  choose R hR using hRq
  refine ⟨L,hLRel,?_⟩
  intro a
  have he0 : (coordinateGerm (j.natAdd d) : HolGerm (ComplexModel (d+t)))≠0 :=
    HolomorphicGermReducednessBridge.coordinate_germ_ne_zero (j.natAdd d)
  have hfactor := actualAnalyticBlowupPullback_normalPolynomial_homogeneous d t j b (p a) (D-(relativeWeight d t I) a) (hp a)
  change actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b
    (normalPolynomialEval d t (p a))=coordinateGerm (j.natAdd d)^(D-relativeWeight d t I a)*
      actualDehomogenizedNormalPolynomialEval d t j b (p a) at hfactor
  have heq : L a=actualDehomogenizedNormalPolynomialEval d t j b (p a)+coordinateGerm (j.natAdd d)*R a := by
    apply mul_left_cancel₀ (pow_ne_zero (D-(relativeWeight d t I) a) he0)
    rw [mul_add,hL a,←mul_assoc,←pow_succ,(hR a).1,map_sub]
    rw [←hfactor]
    ring
  rw [heq,relativePolynomialDehomogenization_eval,add_sub_cancel_left]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)


attribute [local instance 2000] SubsemiringClass.toAddSubmonoidClass in
/-- EVERY whole actual relative canonical normalized quotient is exceptional-regular. -/
theorem relative_normalized_family_exceptional_regular (j : Fin t) (b : Fin (d+t) → ℂ)
    (H : relativeVertices d t I → HolGerm (ComplexModel (d+t)))
    (hH : ∀ a,coordinateGerm (j.natAdd d)^(relativeWeight d t I a)*H a=
      actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b (G a)) :
    ∀ g,coordinateGerm (j.natAdd d)*g∈Ideal.span (range H) ↔ g∈Ideal.span (range H) := by
  let e : HolGerm (ComplexModel (d+t)) := coordinateGerm (j.natAdd d)
  let E : Ideal (HolGerm (ComplexModel (d+t))) := Ideal.span {e}
  let f (a : relativeVertices d t I) := actualNormalHomogeneousPolynomial d t (relativeWeight d t I a) (G a)
  let p (a : relativeVertices d t I) := relativePolynomialDehomogenization j b (f a)
  have hInit (a : relativeVertices d t I) : H a-normalPolynomialEval d t (p a)∈E := by
    rw [show p a=relativePolynomialDehomogenization j b (f a) from rfl,relativePolynomialDehomogenization_eval]
    exact actual_analytic_normal_quotient_initial_restriction d t j b (relativeWeight d t I a) (G a) (H a)
      (hpower a) (hH a)
  have hp (a : relativeVertices d t I) (α : Fin t →₀ ℕ) (hα : α∈(p a).support) : α j=0 :=
    dehom_pivot_independent j b (f a) α hα
  have hf (a : relativeVertices d t I) : (f a).IsHomogeneous (relativeWeight d t I a) :=
    actualNormalHomogeneousPolynomial_isHomogeneous d t _ _
  intro g
  constructor
  · intro hg
    obtain ⟨A,hA⟩ := Ideal.mem_span_range_iff_exists_fun.mp hg
    have hsum : (∑ a,H a*A a)=e*g := by simpa only [mul_comm] using hA
    have hdiff : (∑ a,(H a-normalPolynomialEval d t (p a))*A a)∈E :=
      E.sum_mem (fun a _ => E.mul_mem_right (A a) (hInit a))
    have hpoly : (∑ a,normalPolynomialEval d t (p a)*A a)∈E := by
      have heg : e*g∈E := E.mul_mem_right g (Ideal.mem_span_singleton_self e)
      convert E.sub_mem heg hdiff using 1
      rw [←hsum]
      simp_rw [sub_mul,Finset.sum_sub_distrib]
      ring
    obtain ⟨k,c,B,hAc,hc,hcp⟩ := exists_relative_exceptional_polynomial_syzygies d t j p A hp hpoly
    have hcolumns (l : Fin k) : ∃ L : relativeVertices d t I → HolGerm (ComplexModel (d+t)),
        (∑ a,H a*L a)=0 ∧ ∀ a,L a-normalPolynomialEval d t (c a l)∈E := by
      obtain ⟨D,P,hD,hP,hdehom,hrel⟩ := exists_relative_homogeneous_polynomial_relation_lift j b
        f (fun a => c a l) (relativeWeight d t I) hf (fun a => hcp a l)
        (by simpa only [mul_comm,p] using hc l)
      obtain ⟨L,hL,hLc⟩ := relative_normalized_polynomial_relation_lift d t I G hG hpower j b H hH D P hD hP hrel
      exact ⟨L,hL,fun a => by simpa only [hdehom] using hLc a⟩
    choose L hL hLc using hcolumns
    have hAL (a : relativeVertices d t I) : A a-(∑ l,L l a*B l)∈E := by
      have hdelta : (∑ l,(L l a-normalPolynomialEval d t (c a l))*B l)∈E :=
        E.sum_mem (fun l _ => E.mul_mem_right (B l) (hLc l a))
      convert E.sub_mem (hAc a) hdelta using 1
      simp_rw [sub_mul,Finset.sum_sub_distrib]
      ring
    have hD (a : relativeVertices d t I) : ∃ v : HolGerm (ComplexModel (d+t)),v*e=A a-(∑ l,L l a*B l) :=
      Ideal.mem_span_singleton'.mp (hAL a)
    choose v hv using hD
    have hzero : (∑ a,H a*(∑ l,L l a*B l))=0 := by
      simp_rw [Finset.mul_sum,←mul_assoc]
      rw [Finset.sum_comm]
      simp only [←Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro l _
      rw [hL l,zero_mul]
    have heq : e*g=e*(∑ a,H a*v a) := by
      calc
        e*g=(∑ a,H a*A a) := hsum.symm
        _=(∑ a,H a*(A a-(∑ l,L l a*B l))) := by
          simp_rw [mul_sub,Finset.sum_sub_distrib]
          rw [hzero,sub_zero]
        _=(∑ a,H a*(v a*e)) := by simp_rw [hv]
        _=e*(∑ a,H a*v a) := by rw [Finset.mul_sum];apply Finset.sum_congr rfl;intro a _;ring
    have he0 : e≠0 := HolomorphicGermReducednessBridge.coordinate_germ_ne_zero (j.natAdd d)
    have hgEq := mul_left_cancel₀ he0 heq
    rw [hgEq]
    exact (Ideal.span (range H)).sum_mem (fun a _ =>
      (Ideal.span (range H)).mul_mem_right (v a) (Ideal.subset_span ⟨a,rfl⟩))
  · intro hg
    exact (Ideal.span (range H)).mul_mem_left e hg

open HironakaActualAnalyticStrictGenerators

/-- The independently named WHOLE normalized-member ideal equals total exceptional saturation, with one finite colon. -/
theorem relative_normalized_member_iff_total_saturation (j : Fin t) (b : Fin (d+t) → ℂ) :
    let A := actualTangentCentreVariables d t
    let e := coordinateGerm (j.natAdd d)
    let N := actualAnalyticNormalizedMemberIdeal I A (j.natAdd d) b
    let T := Ideal.map (actualAnalyticBlowupPullback A (j.natAdd d) b).toRingHom I
    (∀ g,g∈N ↔ ∃ q : ℕ,e^q*g∈T) ∧
    (∀ g,e*g∈N ↔ g∈N) ∧ ∃ D : ℕ,T.colon {e^D}=N := by
  dsimp only
  have hq (a : relativeVertices d t I) := exists_actualAnalyticBlowup_quotient (actualTangentCentreVariables d t)
    (j.natAdd d) (show j.natAdd d∈actualTangentCentreVariables d t from ⟨j,rfl⟩) b
    (relativeWeight d t I a) (G a)
    (by rw [actualAnalyticCoordinateIdeal_normal];exact hpower a)
  choose H hH using hq
  have hreg := relative_normalized_family_exceptional_regular d t I G hG hpower j b H (fun a => (hH a).1)
  let e : HolGerm (ComplexModel (d+t)) := coordinateGerm (j.natAdd d)
  let N := Ideal.span (range H)
  let π := actualAnalyticBlowupPullback (actualTangentCentreVariables d t) (j.natAdd d) b
  let T := Ideal.map π.toRingHom I
  have hspan : Ideal.span (range G)=I := prescribed_canonical_span (d+t) I G hG
  have hGmem (a : relativeVertices d t I) : G a∈I := by rw [←hspan];exact Ideal.mem_span_range_self (x := a)
  have hpow (q : ℕ) (g : HolGerm (ComplexModel (d+t))) : e^q*g∈N ↔ g∈N := by
    induction q with
    | zero => simp only [pow_zero,one_mul]
    | succ q ih => rw [pow_succ',mul_assoc,hreg,ih]
  have hTotal : T≤N := by
    rw [Ideal.map_le_iff_le_comap,←hspan]
    apply Ideal.span_le.mpr
    rintro _ ⟨a,rfl⟩
    change π (G a)∈N
    rw [←(hH a).1]
    exact N.mul_mem_left _ (Ideal.subset_span ⟨a,rfl⟩)
  have hNamed : actualAnalyticNormalizedMemberIdeal I (actualTangentCentreVariables d t) (j.natAdd d) b=N := by
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro g ⟨q,F,hF,_hFpower,hg⟩
      apply (hpow q g).mp
      rw [hg]
      exact hTotal (Ideal.mem_map_of_mem _ hF)
    · apply Ideal.span_le.mpr
      rintro _ ⟨a,rfl⟩
      apply Ideal.subset_span
      refine ⟨relativeWeight d t I a,G a,hGmem a,?_,(hH a).1⟩
      rw [actualAnalyticCoordinateIdeal_normal]
      exact hpower a
  let D : ℕ := ∑ a : relativeVertices d t I,relativeWeight d t I a
  have hD (a : relativeVertices d t I) : relativeWeight d t I a≤D :=
    Finset.single_le_sum (fun (x : relativeVertices d t I) _ => Nat.zero_le (relativeWeight d t I x)) (Finset.mem_univ a)
  have hclearGen (a : relativeVertices d t I) : e^D*H a∈T := by
    have heq : e^D*H a=e^(D-relativeWeight d t I a)*(π (G a)) := by
      rw [←(hH a).1,←mul_assoc,←pow_add,Nat.sub_add_cancel (hD a)]
    rw [heq]
    exact T.mul_mem_left _ (Ideal.mem_map_of_mem _ (hGmem a))
  have hclear (g : HolGerm (ComplexModel (d+t))) (hg : g∈N) : e^D*g∈T := by
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
    exact ⟨fun hg => ⟨D,hclear g hg⟩,fun ⟨q,hq⟩ => (hpow q g).mp (hTotal hq)⟩
  · ext g
    rw [Submodule.mem_colon_singleton]
    change g*e^D∈T ↔ g∈N
    rw [mul_comm]
    exact ⟨fun hg => (hpow D g).mp (hTotal hg),hclear g⟩

omit hG hpower
section OriginalCentre
open Hironaka.HolomorphicIdealSheaves HironakaActualAnalyticVertexCoefficientData
  HironakaSmoothCentreCoherentDomain HironakaSmoothCentreNearbyStalks HironakaSmoothCentreNearbyIdeal
  HironakaSmoothCentreRealDomainActualAmbientHS HironakaRelativeNormalCoherentTranslatedJets
  HironakaRelativeNormalDeformationInitialRelations HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicPointJets HironakaHolomorphicJetRankLoci HironakaActualCanonicalNormalCoefficientData
variable {d t : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ComplexModel (d+t)) M] [IsComplexManifold (d+t) M]

/-- ORIGINAL regular-centre HSconstancy fixes ONE chart/family before ALL actual normal-pivot saturation laws. -/
theorem exists_original_hs_centre_normalized_saturation
    (C : Set M) (x : M) (hreg : RegularAtDim (n := d+t) C x d)
    (A : GermIdeal (d+t) M) (hA : A.IsCoherent)
    (hhs : ∀ y∈C,∀ ℓ : ℕ,hilbertSamuelAt A y ℓ=hilbertSamuelAt A x ℓ) :
    ∃ Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+t)) x x),
      ∃ _hsrc : Φ.source⊆(chartAt (ComplexModel (d+t)) x).target,
      ∃ _h0 : Φ.toFun (chartAt (ComplexModel (d+t)) x x)=0,
      (∀ {y : M}, y∈(chartAt (ComplexModel (d+t)) x).source →
        chartAt (ComplexModel (d+t)) x y∈Φ.source →
        (y∈C ↔ Φ.toFun (chartAt (ComplexModel (d+t)) x y)∈complexCoordinatePlane (d+t) d)) ∧
      let I0 := originalCoherentOriginIdeal (actualTranslatedOriginalSheaf
        (actualFlattenedOriginalSheaf A x Φ) 0)
      let K0 := Ideal.map (actualUnshiftedTaylorAlgHom (d+t)).toRingHom I0
      ∃ P : ActualAnalyticVertexCoefficientData d 0 t I0,
        (∀ a,actualUnshiftedTaylorAlgHom (d+t) (P.generator a)=actualReducedVertexSeries MonomialOrder.degLex K0 a) ∧
        (∀ a,P.generator a∈normalIdeal d t ^
          Finsupp.weight (actualCoordinateWeight (actualTangentCentreVariables d t)) a.val) ∧
        ∀ (j : Fin t) (b : Fin (d+t) → ℂ),
          let A := actualTangentCentreVariables d t
          let e := coordinateGerm (j.natAdd d)
          let N := actualAnalyticNormalizedMemberIdeal I0 A (j.natAdd d) b
          let T := Ideal.map (actualAnalyticBlowupPullback A (j.natAdd d) b).toRingHom I0
          (∀ g,g∈N ↔ ∃ q : ℕ,e^q*g∈T) ∧
          (∀ g,e*g∈N ↔ g∈N) ∧ ∃ D : ℕ,T.colon {e^D}=N := by
  obtain ⟨Φ,hsrc,h0,hflat,P,hPG,_hcoeff,hpower⟩ :=
    exists_original_hs_constant_centre_canonical_coefficient_data C x hreg A hA hhs
  refine ⟨Φ,hsrc,h0,hflat,P,hPG,hpower,?_⟩
  intro j b
  exact relative_normalized_member_iff_total_saturation d t _ P.generator hPG hpower j b

end OriginalCentre

end
end Hironaka.HironakaActualRelativeNormalizedSaturation
