import DeJongAlterations.Algebra.SteinCurveConstants
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Actual finite separable tensors over a relatively closed constant field

Smooth coefficient change of integral closure forces all idempotents
into the coefficient field.  The actual reduced Artinian decomposition
then proves that a finite separable scalar change is a field.
-/

noncomputable section

open TensorProduct Polynomial

namespace DeJongAlterations.Algebra.SteinTensor

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {K F E : Type u} [Field K] [Field F] [Algebra K F]

/-- Smooth coefficient change preserves the actual absence of algebraic constants. -/
theorem integralClosure_eq_bot_of_smooth [CommRing E] [Algebra K E] [Algebra.Smooth K E]
    (h : integralClosure K F = ⊥) :
    integralClosure E (E ⊗[K] F) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro x hx
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := K) (S := E) (B := F)).2 ⟨x, hx⟩
  have H : ∀ z : E ⊗[K] integralClosure K F,
      ((TensorProduct.toIntegralClosure K E F z) : E ⊗[K] F) ∈
        (⊥ : Subalgebra E (E ⊗[K] F)) := by
    intro z
    induction z with
    | zero => simp
    | add z w hz hw => simpa only [map_add, Subalgebra.coe_add] using add_mem hz hw
    | tmul e c =>
      have hc : (c : F) ∈ (⊥ : Subalgebra K F) := by
        rw [← h]; exact c.property
      obtain ⟨k, hk⟩ := Algebra.mem_bot.mp hc
      change e ⊗ₜ[K] (c : F) ∈ (⊥ : Subalgebra E (E ⊗[K] F))
      rw [← hk, Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul]
      exact (⊥ : Subalgebra E (E ⊗[K] F)).algebraMap_mem (k • e)
  simpa only [hy] using H y

/-- A reduced Artinian ring with no nontrivial idempotents is a field. -/
theorem isField_of_idempotents_trivial (A : Type u) [CommRing A] [Nontrivial A]
    [IsArtinianRing A] [IsReduced A]
    (h : ∀ a : A, IsIdempotentElem a → a = 0 ∨ a = 1) : IsField A := by
  classical
  let e := IsArtinianRing.equivPi A
  have hs : Subsingleton (MaximalSpectrum A) := by
    refine ⟨fun i j => ?_⟩
    by_contra hij
    let a := e.symm (Pi.single i 1)
    have ha : IsIdempotentElem a := by
      apply e.injective
      ext m
      by_cases hm : m = i
      · subst m; simp [a]
      · simp [a, Pi.single_eq_of_ne hm]
    rcases h a ha with ha | ha
    · have H := congrFun (congrArg e ha) i
      simp [a] at H
    · have H := congrFun (congrArg e ha) j
      simp [a, Ne.symm hij] at H
  let := hs
  let : Unique (MaximalSpectrum A) :=
    { default := Classical.choice inferInstance
      uniq := fun _ => Subsingleton.elim _ _ }
  exact e.toRingEquiv.trans (RingEquiv.piUnique _) |>.toMulEquiv.isField
    (Ideal.Quotient.field _).toIsField

variable [Field E] [Algebra K E]

/-- An actual finite separable tensor product over relatively closed constants is a field. -/
theorem isField_tensorProduct [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (h : integralClosure K F = ⊥) : IsField (E ⊗[K] F) := by
  let : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  let : Algebra.FinitePresentation K E := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  let : Algebra.Smooth K E := ⟨inferInstance, inferInstance⟩
  have hc := integralClosure_eq_bot_of_smooth (E := E) h
  have hi (a : E ⊗[K] F) (ha : IsIdempotentElem a) : a = 0 ∨ a = 1 := by
    have haI : IsIntegral E a :=
      ⟨X ^ 2 - X, Polynomial.monic_X_pow_sub (by simp),
        by simpa [pow_two] using sub_eq_zero.mpr ha.eq⟩
    have haC : a ∈ integralClosure E (E ⊗[K] F) := haI
    rw [hc] at haC
    obtain ⟨e, he⟩ := Algebra.mem_bot.mp haC
    have heI : IsIdempotentElem e := by
      apply (algebraMap E (E ⊗[K] F)).injective
      simpa only [map_mul, he] using ha.eq
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp heI with heI | heI
    · left; simpa [heI] using he.symm
    · right; rw [heI, map_one] at he; exact he.symm
  let : Algebra.FormallyEtale F (F ⊗[K] E) := inferInstance
  let : Algebra F (E ⊗[K] F) := Algebra.TensorProduct.rightAlgebra
  let : Algebra.FormallyEtale F (E ⊗[K] F) :=
    .of_equiv (Algebra.TensorProduct.commRight K F E)
  let : Module.Finite F (E ⊗[K] F) :=
    Module.Finite.of_surjective
      (Algebra.TensorProduct.commRight K F E).toLinearMap
      (Algebra.TensorProduct.commRight K F E).surjective
  let : IsArtinianRing (E ⊗[K] F) := .of_finite F _
  let : IsReduced (E ⊗[K] F) := Algebra.FormallyUnramified.isReduced_of_field F _
  exact isField_of_idempotents_trivial _ hi

/-- Both tensors descend to one actual finitely generated intermediate field. -/
theorem exists_pair_finite_stage (x y : E ⊗[K] F) :
    ∃ s : Finset E,
      ∃ x' y' : IntermediateField.adjoin K (s : Set E) ⊗[K] F,
        Algebra.TensorProduct.map (IntermediateField.adjoin K (s : Set E)).val
          (AlgHom.id K F) x' = x ∧
        Algebra.TensorProduct.map (IntermediateField.adjoin K (s : Set E)).val
          (AlgHom.id K F) y' = y := by
  classical
  obtain ⟨sx, hx⟩ := TensorProduct.exists_finset x
  obtain ⟨sy, hy⟩ := TensorProduct.exists_finset y
  let s := sx.image Prod.fst ∪ sy.image Prod.fst
  let L := IntermediateField.adjoin K (s : Set E)
  have hxL (p : E × F) (hp : p ∈ sx) : p.1 ∈ L :=
    IntermediateField.subset_adjoin K (s : Set E)
      (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp))
  have hyL (p : E × F) (hp : p ∈ sy) : p.1 ∈ L :=
    IntermediateField.subset_adjoin K (s : Set E)
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))
  refine ⟨s, ∑ p ∈ sx.attach, (⟨p.1.1, hxL p.1 p.2⟩ : L) ⊗ₜ[K] p.1.2,
    ∑ p ∈ sy.attach, (⟨p.1.1, hyL p.1 p.2⟩ : L) ⊗ₜ[K] p.1.2, ?_, ?_⟩
  · simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change (∑ p ∈ sx.attach, p.1.1 ⊗ₜ[K] p.1.2) = x
    rw [Finset.sum_attach sx (fun p : E × F => p.1 ⊗ₜ[K] p.2)]
    exact hx.symm
  · simp only [map_sum, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    change (∑ p ∈ sy.attach, p.1.1 ⊗ₜ[K] p.1.2) = y
    rw [Finset.sum_attach sy (fun p : E × F => p.1 ⊗ₜ[K] p.2)]
    exact hy.symm

/-- No finiteness assumption on the actual separable algebraic scalar extension is needed. -/
theorem isDomain_tensorProduct_of_isSeparable [Algebra.IsSeparable K E]
    (h : integralClosure K F = ⊥) : IsDomain (E ⊗[K] F) := by
  let : NoZeroDivisors (E ⊗[K] F) := by
    refine ⟨fun {x y} hxy => ?_⟩
    obtain ⟨s, x', y', hx, hy⟩ := exists_pair_finite_stage x y
    let L := IntermediateField.adjoin K (s : Set E)
    change L ⊗[K] F at x' y'
    let : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin
      (fun e _ => (Algebra.IsSeparable.isSeparable K e).isIntegral)
    let : Algebra.IsSeparable K L :=
      Algebra.IsSeparable.of_algHom (F := K) (E := L) (E' := E) L.val
    let hdom : IsDomain (L ⊗[K] F) := (isField_tensorProduct (E := L) h).isDomain
    have hnd : NoZeroDivisors (L ⊗[K] F) := @IsDomain.to_noZeroDivisors _ _ hdom
    let m := Algebra.TensorProduct.map L.val (AlgHom.id K F)
    change m x' = x at hx
    change m y' = y at hy
    have hm : Function.Injective m :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := F) L.val.toLinearMap
        Subtype.val_injective
    have hz : x' * y' = 0 := hm (by simpa only [map_mul, hx, hy, map_zero] using hxy)
    rcases @eq_zero_or_eq_zero_of_mul_eq_zero (L ⊗[K] F) _ _ hnd x' y' hz with hz | hz
    · left; rw [← hx, hz, map_zero]
    · right; rw [← hy, hz, map_zero]
  exact NoZeroDivisors.to_isDomain _

/-- All algebraic scalar changes have an actual irreducible tensor spectrum. -/
theorem irreducibleSpace_tensorSpectrum_of_isAlgebraic [Algebra.IsAlgebraic K E]
    (h : integralClosure K F = ⊥) : IrreducibleSpace (PrimeSpectrum (E ⊗[K] F)) := by
  let L := separableClosure K E
  let : IsDomain (L ⊗[K] F) := isDomain_tensorProduct_of_isSeparable h
  have he := PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
    L K F E
  exact (he.homeomorph _).irreducibleSpace_iff.mpr inferInstance

end DeJongAlterations.Algebra.SteinTensor
