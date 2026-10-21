/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualPolynomialAnalyticFlatness
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Actual exceptional-fibre flatness and complete polynomial relation generation

The genuine quotient tensor base change makes the whole induced
polynomial-to-original-analytic exceptional-fibre map flat. Its actual
finite equational criterion, quotient surjections and literal kill-pivot
algebra retraction internally generate EVERY whole analytic fibre relation
by genuine pivot-free polynomial syzygies with actual analytic multipliers.
No quotient identification, flatness or relation-generation certificate is
supplied at the original endpoint. Normalized-ideal regularity remains a
subsequent application.

Blueprint: `hironaka-actual-exceptional-fibre-relations-extension.tex`.
-/
set_option autoImplicit false
open Set Classical TensorProduct
open scoped BigOperators
namespace Hironaka.HironakaActualExceptionalFibreRelations
noncomputable section

/-- The true whole quotient of a flat map is the genuine flat quotient base change. -/
theorem quotientMap_flat (P R : Type*) [CommRing P] [CommRing R] [Algebra P R]
    [Module.Flat P R] (I : Ideal P) :
    (Ideal.quotientMap (Ideal.map (algebraMap P R) I) (algebraMap P R) Ideal.le_comap_map).Flat := by
  let J := Ideal.map (algebraMap P R) I
  let : Algebra (P⧸I) (R⧸J) := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
  let : IsScalarTower P (P⧸I) (R⧸J) := IsScalarTower.of_algebraMap_eq fun p => rfl
  let E : (R⧸J)≃ₗ[P] (P⧸I)⊗[P]R :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot R I).toLinearEquiv.restrictScalars P ≪≫ₗ
      TensorProduct.comm P R (P⧸I)
  let E' : (R⧸J)≃ₗ[P⧸I] (P⧸I)⊗[P]R :=
    E.extendScalarsOfSurjective (Ideal.Quotient.mk_surjective)
  change (algebraMap (P⧸I) (R⧸J)).Flat
  apply RingHom.flat_algebraMap_iff.mpr
  exact Module.Flat.of_linearEquiv E'



open HolGerm HironakaActualOriginalTaylorPolynomial
  HironakaActualPolynomialAnalyticFlatness HironakaRelativeNormalIdeal HironakaHolomorphicJetMonomialSpan
variable {n : ℕ}

/-- The literal polynomial exceptional coordinate ideal. -/
def pointPolynomialIdeal (n : ℕ) (j : Fin n) : Ideal (MvPolynomial (Fin n) ℂ) := Ideal.span {MvPolynomial.X j}

/-- The WHOLE image of this literal polynomial ideal under actual coordinate evaluation. -/
def pointPolynomialIdealImage (n : ℕ) (j : Fin n) : Ideal (HolGerm (ComplexModel (0+n))) :=
  Ideal.map (originalPolynomialEval n).toRingHom (pointPolynomialIdeal n j)

theorem pointPolynomialIdealImage_eq_coordinate_span (n : ℕ) (j : Fin n) :
    pointPolynomialIdealImage n j=Ideal.span {coordinateGerm (j.natAdd 0)} := by
  rw [pointPolynomialIdealImage,pointPolynomialIdeal,Ideal.map_span,Set.image_singleton]
  change Ideal.span {originalPolynomialEval n (MvPolynomial.X j)}=_
  rw [originalPolynomialEval,MvPolynomial.aeval_X]
  rfl

/-- The actual entire numerator-preserving polynomial exceptional-fibre map. -/
def pointFibrePolynomialEval (n : ℕ) (j : Fin n) :
    (MvPolynomial (Fin n) ℂ⧸pointPolynomialIdeal n j) →+*
      (HolGerm (ComplexModel (0+n))⧸pointPolynomialIdealImage n j) :=
  Ideal.quotientMap _ (originalPolynomialEval n).toRingHom Ideal.le_comap_map

theorem pointFibrePolynomialEval_flat (n : ℕ) (j : Fin n) : (pointFibrePolynomialEval n j).Flat := by
  let P := MvPolynomial (Fin n) ℂ
  let R := HolGerm (ComplexModel (0+n))
  let : Algebra P R := (originalPolynomialEval n).toRingHom.toAlgebra
  have : Module.Flat P R := originalPolynomialEval_flat n
  exact quotientMap_flat P R (pointPolynomialIdeal n j)

private def killPivot (j : Fin n) : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n) ℂ :=
  (MvPolynomial.rename (Subtype.val : {i : Fin n // i≠j} → Fin n)).comp
    (MvPolynomial.killCompl (Subtype.val_injective : Function.Injective (Subtype.val : {i : Fin n // i≠j} → Fin n)))

private theorem killPivot_X (j i : Fin n) : killPivot j (MvPolynomial.X i)=if i=j then 0 else MvPolynomial.X i := by
  change MvPolynomial.rename (Subtype.val : {i : Fin n // i≠j} → Fin n)
    (MvPolynomial.killCompl Subtype.val_injective (MvPolynomial.X i))=_
  by_cases hi : i=j
  · subst i
    have hne : j∉Set.range (Subtype.val : {i : Fin n // i≠j} → Fin n) := by
      rintro ⟨i,hi⟩
      exact i.property hi
    rw [MvPolynomial.killCompl,MvPolynomial.aeval_X,dif_neg hne,map_zero,if_pos rfl]
  · let i' : {i : Fin n // i≠j} := ⟨i,hi⟩
    have hx : MvPolynomial.X i=MvPolynomial.rename (Subtype.val : {i : Fin n // i≠j} → Fin n) (MvPolynomial.X i') :=
      (MvPolynomial.rename_X (R := ℂ) (Subtype.val : {i : Fin n // i≠j} → Fin n) i').symm
    rw [hx,MvPolynomial.killCompl_rename_app,MvPolynomial.rename_X,if_neg hi]

private theorem killPivot_independent (j : Fin n) (p : MvPolynomial (Fin n) ℂ)
    (α : Fin n →₀ ℕ) (hα : α∈(killPivot j p).support) : α j=0 := by
  apply MvPolynomial.mem_support_notMem_vars_zero hα
  intro hj
  have hh := MvPolynomial.vars_rename (Subtype.val : {i : Fin n // i≠j} → Fin n)
    (MvPolynomial.killCompl Subtype.val_injective p) hj
  obtain ⟨i,_hi,hij⟩ := Finset.mem_image.mp hh
  exact i.property hij

private theorem killPivot_fix (j : Fin n) (p : MvPolynomial (Fin n) ℂ)
    (hp : ∀ α∈p.support,α j=0) : killPivot j p=p := by
  have he : killPivot j=MvPolynomial.aeval (fun i : Fin n => if i≠j then MvPolynomial.X i else 0) := by
    ext i
    by_cases hi : i=j <;> simp [killPivot_X,hi]
  rw [he]
  apply MvPolynomial.aeval_ite_mem_eq_self (s := {i : Fin n | i≠j}) p
  intro i hi
  change i≠j
  intro hij
  subst i
  obtain ⟨α,hα,hj⟩ := (MvPolynomial.mem_vars_iff_mem_support j).mp hi
  exact (Finsupp.mem_support_iff.mp hj) (hp α hα)

private theorem killPivot_quotient (j : Fin n) (p : MvPolynomial (Fin n) ℂ) :
    Ideal.Quotient.mk (pointPolynomialIdeal n j) (killPivot j p)=Ideal.Quotient.mk (pointPolynomialIdeal n j) p := by
  have he : (Ideal.Quotient.mkₐ ℂ (pointPolynomialIdeal n j)).comp (killPivot j)=
      Ideal.Quotient.mkₐ ℂ (pointPolynomialIdeal n j) := by
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



/-- Every actual exceptional-fibre relation has genuine pivot-free WHOLE polynomial syzygies and actual holomorphic multipliers; no relation-generation input. -/
theorem exists_original_exceptional_polynomial_syzygies (n r : ℕ) (j : Fin n)
    (p : Fin r → MvPolynomial (Fin n) ℂ) (A : Fin r → HolGerm (ComplexModel (0+n)))
    (hp : ∀ i α,α∈(p i).support→α j=0)
    (hRel : (∑ i,originalPolynomialEval n (p i)*A i)∈Ideal.span {coordinateGerm (j.natAdd 0)}) :
    ∃ (k : ℕ) (c : Fin r → Fin k → MvPolynomial (Fin n) ℂ)
      (B : Fin k → HolGerm (ComplexModel (0+n))),
      (∀ i,A i-(∑ l,originalPolynomialEval n (c i l)*B l)∈Ideal.span {coordinateGerm (j.natAdd 0)}) ∧
      (∀ l,∑ i,p i*c i l=0) ∧ ∀ i l α,α∈(c i l).support→α j=0 := by
  let P := MvPolynomial (Fin n) ℂ
  let R := HolGerm (ComplexModel (0+n))
  let I := pointPolynomialIdeal n j
  let J := pointPolynomialIdealImage n j
  let : Algebra (P⧸I) (R⧸J) := (pointFibrePolynomialEval n j).toAlgebra
  have : Module.Flat (P⧸I) (R⧸J) := pointFibrePolynomialEval_flat n j
  have hRelJ : (∑ i,originalPolynomialEval n (p i)*A i)∈J := by
    change (∑ i,originalPolynomialEval n (p i)*A i)∈pointPolynomialIdealImage n j
    rw [pointPolynomialIdealImage_eq_coordinate_span]
    exact hRel
  have hs : (∑ i,(Ideal.Quotient.mk I (p i)) • (Ideal.Quotient.mk J (A i)))=0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hRelJ
    change (∑ i,Ideal.Quotient.mk J (originalPolynomialEval n (p i))*Ideal.Quotient.mk J (A i))=0
    simpa only [map_sum,map_mul] using h
  obtain ⟨k,cq,Bq,hc,hpRel⟩ := (Module.Flat.iff_forall_isTrivialRelation (R := P⧸I) (M := R⧸J)).mp
    ‹Module.Flat (P⧸I) (R⧸J)› (f := fun i => Ideal.Quotient.mk I (p i))
      (x := fun i => Ideal.Quotient.mk J (A i)) hs
  choose c hrep using fun i l => Ideal.Quotient.mk_surjective (cq i l)
  choose B hB using fun l => Ideal.Quotient.mk_surjective (Bq l)
  have hclasses (i : Fin r) : Ideal.Quotient.mk J (A i)=
      ∑ l,Ideal.Quotient.mk J (originalPolynomialEval n (killPivot j (c i l)))*Ideal.Quotient.mk J (B l) := by
    have hc' : Ideal.Quotient.mk J (A i)=∑ l,pointFibrePolynomialEval n j (cq i l)*Bq l := by
      simpa only [Algebra.smul_def,RingHom.algebraMap_toAlgebra] using hc i
    rw [hc']
    apply Finset.sum_congr rfl
    intro l _
    rw [hB l]
    apply congrArg (fun q => q*Bq l)
    calc
      _=pointFibrePolynomialEval n j (Ideal.Quotient.mk I (c i l)) := congrArg (pointFibrePolynomialEval n j) (hrep i l).symm
      _=pointFibrePolynomialEval n j (Ideal.Quotient.mk I (killPivot j (c i l))) :=
        congrArg (pointFibrePolynomialEval n j) (killPivot_quotient j (c i l)).symm
      _=_ := by rfl
  have hpoly (l : Fin k) : (∑ i,p i*c i l)∈I := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have h := hpRel l
    simpa only [map_sum,map_mul,hrep] using h
  have hkill : ∀ q∈I,killPivot j q=0 := by
    have hi : I≤RingHom.ker (killPivot j).toRingHom := by
      apply Ideal.span_le.mpr
      rintro q rfl
      change killPivot j (MvPolynomial.X j)=0
      rw [killPivot_X,if_pos rfl]
    exact fun q hq => hi hq
  refine ⟨k,fun i l => killPivot j (c i l),B,?_,?_,?_⟩
  · intro i
    rw [←pointPolynomialIdealImage_eq_coordinate_span n j]
    apply Ideal.Quotient.eq.mp
    simpa only [map_sum,map_mul] using hclasses i
  · intro l
    have h := hkill _ (hpoly l)
    simpa only [map_sum,map_mul,fun i => killPivot_fix j (p i) (hp i)] using h
  · intro i l α hα
    exact killPivot_independent j (c i l) α hα

end
end Hironaka.HironakaActualExceptionalFibreRelations
