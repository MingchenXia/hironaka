/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualFormalNormalSeries
import Hironaka.Resolution.HironakaActualExceptionalFibreRelations

/-!
# Every whole relative exceptional-fibre relation has actual polynomial syzygies

The proved entire B[z]-to-original-analytic flatness and genuine quotient tensor
base change generate every whole exceptional-fibre relation. Actual quotient
surjections and the literal kill-pivot algebra retraction give genuine pivot-free
polynomial syzygies over the unchanged original analytic tangent ring.
No relation-generation, exceptional regularity or normalization certificate is input.
Blueprint: `hironaka-actual-relative-exceptional-fibre-relations-extension.tex`.
-/
set_option autoImplicit false
open Set Classical TensorProduct
open scoped BigOperators
namespace Hironaka.HironakaActualRelativeExceptionalFibreRelations
noncomputable section
private theorem quotient_relation_witness (P R : Type*) [CommRing P] [CommRing R]
    [Algebra P R] [Module.Flat P R] {ι : Type*} [Fintype ι] (I : Ideal P)
    (p : ι → P) (A : ι → R) (hRel : (∑ i,algebraMap P R (p i)*A i)∈Ideal.map (algebraMap P R) I) :
    ∃ (k : ℕ) (cq : ι → Fin k → P⧸I) (Bq : Fin k → R⧸Ideal.map (algebraMap P R) I),
      (∀ i,Ideal.Quotient.mk (Ideal.map (algebraMap P R) I) (A i)=
        ∑ l,Ideal.quotientMap _ (algebraMap P R) Ideal.le_comap_map (cq i l)*Bq l) ∧
      ∀ l,∑ i,Ideal.Quotient.mk I (p i)*cq i l=0 := by
  let J := Ideal.map (algebraMap P R) I
  let f := Ideal.quotientMap J (algebraMap P R) Ideal.le_comap_map
  let : Algebra (P⧸I) (R⧸J) := f.toAlgebra
  let : Module.Flat (P⧸I) (R⧸J) := HironakaActualExceptionalFibreRelations.quotientMap_flat P R I
  have hs : (∑ i,(Ideal.Quotient.mk I (p i)) • (Ideal.Quotient.mk J (A i)))=0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hRel
    simp only [Algebra.smul_def]
    change (∑ i,Ideal.Quotient.mk J (algebraMap P R (p i))*Ideal.Quotient.mk J (A i))=0
    simpa only [map_sum,map_mul] using h
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hse : (∑ j,Ideal.Quotient.mk I (p (e j)) • Ideal.Quotient.mk J (A (e j)))=0 := by
    exact (e.sum_comp (fun i => Ideal.Quotient.mk I (p i) • Ideal.Quotient.mk J (A i))).trans hs
  have ht : Module.IsTrivialRelation (fun i : Fin (Fintype.card ι) => Ideal.Quotient.mk I (p (e i)))
      (fun i => Ideal.Quotient.mk J (A (e i))) :=
    (Module.Flat.iff_forall_isTrivialRelation (R := P⧸I) (M := R⧸J)).mp
    ‹Module.Flat (P⧸I) (R⧸J)› (f := fun i => Ideal.Quotient.mk I (p (e i)))
      (x := fun i => Ideal.Quotient.mk J (A (e i))) hse
  obtain ⟨k,cq,Bq,hc,hp⟩ := ht
  refine ⟨k,fun i l => cq (e.symm i) l,Bq,?_,?_⟩
  · intro i
    have hm (x : P⧸I) : algebraMap (P⧸I) (R⧸J) x=f x := rfl
    simpa only [Algebra.smul_def,hm,e.apply_symm_apply] using hc (e.symm i)
  · intro l
    have hh := (e.symm.sum_comp (fun i => Ideal.Quotient.mk I (p (e i))*cq i l)).trans (hp l)
    simpa only [e.apply_symm_apply] using hh

private theorem flat_quotient_relations (P R : Type*) [CommRing P] [CommRing R]
    [Algebra P R] [Module.Flat P R] {ι : Type*} [Fintype ι] (I : Ideal P)
    (p : ι → P) (A : ι → R) (hRel : (∑ i,algebraMap P R (p i)*A i)∈Ideal.map (algebraMap P R) I) :
    ∃ (k : ℕ) (c : ι → Fin k → P) (B : Fin k → R),
      (∀ i,A i-(∑ l,algebraMap P R (c i l)*B l)∈Ideal.map (algebraMap P R) I) ∧
      ∀ l,(∑ i,p i*c i l)∈I := by
  let J := Ideal.map (algebraMap P R) I
  let f := Ideal.quotientMap J (algebraMap P R) Ideal.le_comap_map
  obtain ⟨k,cq,Bq,hc,hp⟩ := quotient_relation_witness P R I p A hRel
  choose c hrep using fun i l => Ideal.Quotient.mk_surjective (cq i l)
  choose B hB using fun l => Ideal.Quotient.mk_surjective (Bq l)
  refine ⟨k,c,B,?_,?_⟩
  · intro i
    have hclasses : Ideal.Quotient.mk J (A i)=
        ∑ l,Ideal.Quotient.mk J (algebraMap P R (c i l))*Ideal.Quotient.mk J (B l) := by
      rw [hc i]
      apply Finset.sum_congr rfl
      intro l _
      rw [←hrep i l,←hB l]
      rfl
    exact Ideal.Quotient.eq.mp (by simpa only [map_sum,map_mul] using hclasses)
  · intro l
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := hp l
    simpa only [map_sum,map_mul,hrep] using h

open HolGerm HironakaActualFormalNormalSeries HironakaRelativeNormalMonomialBasis
  HironakaRelativeNormalIdeal HironakaHolomorphicJetMonomialSpan
variable {d t : ℕ}
local instance : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) := tangentAlgebra d t

private def relativePolynomialIdeal (d t : ℕ) (j : Fin t) :
    Ideal (MvPolynomial (Fin t) (HolGerm (ComplexModel d))) := Ideal.span {MvPolynomial.X j}

private theorem relativePolynomialIdealImage_eq_coordinate_span (d t : ℕ) (j : Fin t) :
    Ideal.map (normalPolynomialEval d t).toRingHom (relativePolynomialIdeal d t j)=
      Ideal.span {coordinateGerm (j.natAdd d)} := by
  rw [relativePolynomialIdeal,Ideal.map_span,Set.image_singleton]
  change Ideal.span {normalPolynomialEval d t (MvPolynomial.X j)}=_
  rw [normalPolynomialEval,MvPolynomial.aeval_X]
  rfl

private def killPivot (j : Fin t) : MvPolynomial (Fin t) (HolGerm (ComplexModel d)) →ₐ[HolGerm (ComplexModel d)] MvPolynomial (Fin t) (HolGerm (ComplexModel d)) :=
  (MvPolynomial.rename (Subtype.val : {i : Fin t // i≠j} → Fin t)).comp
    (MvPolynomial.killCompl (Subtype.val_injective : Function.Injective (Subtype.val : {i : Fin t // i≠j} → Fin t)))

private theorem killPivot_X (j i : Fin t) : killPivot (d := d) j (MvPolynomial.X i)=if i=j then 0 else MvPolynomial.X i := by
  change MvPolynomial.rename (Subtype.val : {i : Fin t // i≠j} → Fin t)
    (MvPolynomial.killCompl Subtype.val_injective (MvPolynomial.X i))=_
  by_cases hi : i=j
  · subst i
    have hne : j∉Set.range (Subtype.val : {i : Fin t // i≠j} → Fin t) := by
      rintro ⟨i,hi⟩
      exact i.property hi
    rw [MvPolynomial.killCompl,MvPolynomial.aeval_X,dif_neg hne,map_zero,if_pos rfl]
  · let i' : {i : Fin t // i≠j} := ⟨i,hi⟩
    have hx : MvPolynomial.X i=MvPolynomial.rename (Subtype.val : {i : Fin t // i≠j} → Fin t) (MvPolynomial.X i') :=
      (MvPolynomial.rename_X (R := HolGerm (ComplexModel d)) (Subtype.val : {i : Fin t // i≠j} → Fin t) i').symm
    rw [hx,MvPolynomial.killCompl_rename_app,MvPolynomial.rename_X,if_neg hi]

private theorem killPivot_independent (j : Fin t) (p : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (α : Fin t →₀ ℕ) (hα : α∈(killPivot (d := d) j p).support) : α j=0 := by
  apply MvPolynomial.mem_support_notMem_vars_zero hα
  intro hj
  have hh := MvPolynomial.vars_rename (Subtype.val : {i : Fin t // i≠j} → Fin t)
    (MvPolynomial.killCompl Subtype.val_injective p) hj
  obtain ⟨i,_hi,hij⟩ := Finset.mem_image.mp hh
  exact i.property hij

private theorem killPivot_fix (j : Fin t) (p : MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
    (hp : ∀ α∈p.support,α j=0) : killPivot (d := d) j p=p := by
  have he : killPivot (d := d) j=MvPolynomial.aeval (fun i : Fin t => if i≠j then MvPolynomial.X i else 0) := by
    ext i
    by_cases hi : i=j <;> simp [killPivot_X,hi]
  rw [he]
  apply MvPolynomial.aeval_ite_mem_eq_self (s := {i : Fin t | i≠j}) p
  intro i hi
  change i≠j
  intro hij
  subst i
  obtain ⟨α,hα,hj⟩ := (MvPolynomial.mem_vars_iff_mem_support j).mp hi
  exact (Finsupp.mem_support_iff.mp hj) (hp α hα)

private theorem killPivot_quotient (j : Fin t) (p : MvPolynomial (Fin t) (HolGerm (ComplexModel d))) :
    Ideal.Quotient.mk (relativePolynomialIdeal d t j) (killPivot (d := d) j p)=Ideal.Quotient.mk (relativePolynomialIdeal d t j) p := by
  have he : (Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (relativePolynomialIdeal d t j)).comp (killPivot (d := d) j)=
      Ideal.Quotient.mkₐ (HolGerm (ComplexModel d)) (relativePolynomialIdeal d t j) := by
    ext i
    rw [AlgHom.comp_apply,killPivot_X]
    by_cases hi : i=j
    · subst i
      rw [if_pos rfl,map_zero]
      symm
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact Ideal.mem_span_singleton_self _
    · rw [if_neg hi]
  exact DFunLike.congr_fun he p



/-- EVERY actual relative exceptional-fibre relation has WHOLE pivot-free polynomial syzygies over the original analytic tangent ring. -/
theorem exists_relative_exceptional_polynomial_syzygies {ι : Type*} [Fintype ι] (d t : ℕ) (j : Fin t)
    (p : ι → MvPolynomial (Fin t) (HolGerm (ComplexModel d))) (A : ι → HolGerm (ComplexModel (d+t)))
    (hp : ∀ i α,α∈(p i).support→α j=0)
    (hRel : (∑ i,normalPolynomialEval d t (p i)*A i)∈Ideal.span {coordinateGerm (j.natAdd d)}) :
    ∃ (k : ℕ) (c : ι → Fin k → MvPolynomial (Fin t) (HolGerm (ComplexModel d)))
      (B : Fin k → HolGerm (ComplexModel (d+t))),
      (∀ i,A i-(∑ l,normalPolynomialEval d t (c i l)*B l)∈Ideal.span {coordinateGerm (j.natAdd d)}) ∧
      (∀ l,∑ i,p i*c i l=0) ∧ ∀ i l α,α∈(c i l).support→α j=0 := by
  let P := MvPolynomial (Fin t) (HolGerm (ComplexModel d))
  let R := HolGerm (ComplexModel (d+t))
  let I := relativePolynomialIdeal d t j
  let J := Ideal.map (normalPolynomialEval d t).toRingHom I
  let : Algebra P R := (normalPolynomialEval d t).toRingHom.toAlgebra
  let : Module.Flat P R := normalPolynomialEval_flat d t
  have hRelJ : (∑ i,normalPolynomialEval d t (p i)*A i)∈J := by
    change (∑ i,normalPolynomialEval d t (p i)*A i)∈Ideal.map (normalPolynomialEval d t).toRingHom (relativePolynomialIdeal d t j)
    rw [relativePolynomialIdealImage_eq_coordinate_span]
    exact hRel
  obtain ⟨k,c,B,hA,hpoly⟩ := flat_quotient_relations P R I p A hRelJ
  have hkill : ∀ q∈I,killPivot (d := d) j q=0 := by
    have hi : I≤RingHom.ker (killPivot (d := d) j).toRingHom := by
      apply Ideal.span_le.mpr
      rintro q rfl
      change killPivot (d := d) j (MvPolynomial.X j)=0
      rw [killPivot_X,if_pos rfl]
    exact fun q hq => hi hq
  have hproj (q : P) : normalPolynomialEval d t (killPivot (d := d) j q)-normalPolynomialEval d t q∈J := by
    have hq := Ideal.Quotient.eq.mp (killPivot_quotient j q)
    have h := Ideal.mem_map_of_mem (normalPolynomialEval d t).toRingHom hq
    change (normalPolynomialEval d t (killPivot (d := d) j q - q))∈J at h
    simpa only [map_sub] using h
  have hA' (i : ι) : A i-(∑ l,normalPolynomialEval d t (c i l)*B l)∈J := hA i
  refine ⟨k,fun i l => killPivot (d := d) j (c i l),B,?_,?_,?_⟩
  · intro i
    rw [←relativePolynomialIdealImage_eq_coordinate_span d t j]
    have hdelta : (∑ l,(normalPolynomialEval d t (killPivot (d := d) j (c i l))-
        normalPolynomialEval d t (c i l))*B l)∈J :=
      J.sum_mem (fun l _ => J.mul_mem_right (B l) (hproj (c i l)))
    convert J.sub_mem (hA' i) hdelta using 1
    simp_rw [sub_mul,Finset.sum_sub_distrib]
    ring
  · intro l
    have h := hkill _ (hpoly l)
    simpa only [map_sum,map_mul,fun i => killPivot_fix j (p i) (hp i)] using h
  · intro i l α hα
    exact killPivot_independent j (c i l) α hα

end
end Hironaka.HironakaActualRelativeExceptionalFibreRelations
