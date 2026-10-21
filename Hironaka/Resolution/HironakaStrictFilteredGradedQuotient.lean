/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaStrictFilteredRegularElement
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Isomorphisms

set_option autoImplicit false
namespace Hironaka.HironakaStrictFilteredGradedQuotient
open HironakaStrictFilteredRegularElement
variable {R : Type*} [CommRing R]
noncomputable section

def adicLayer (I N : Ideal R) (q : ℕ) : Submodule R (R ⧸ (I ⊔ N^(q+1))) :=
  ((N^q).restrictScalars R).map (Ideal.Quotient.mkₐ R (I ⊔ N^(q+1))).toLinearMap

def adicLayerMap (I N : Ideal R) (v : R) (q : ℕ) :
    adicLayer I N q →ₗ[R] adicLayer (I ⊔ Ideal.span ({v} : Set R)) N q :=
  (((Ideal.Quotient.factorₐ R
    (sup_le_sup le_sup_left le_rfl : I ⊔ N^(q+1) ≤
      (I ⊔ Ideal.span ({v} : Set R)) ⊔ N^(q+1))).toLinearMap).comp
        (adicLayer I N q).subtype).codRestrict _ (by
    rintro ⟨x,hx⟩
    obtain ⟨a,ha,rfl⟩ := hx
    exact ⟨a,ha,rfl⟩)

theorem adicLayerMap_surjective (I N : Ideal R) (v : R) (q : ℕ) :
    Function.Surjective (adicLayerMap I N v q) := by
  rintro ⟨x,hx⟩
  obtain ⟨a,ha,rfl⟩ := hx
  exact ⟨⟨_,⟨a,ha,rfl⟩⟩,rfl⟩

private theorem mul_mem_successor (I N : Ideal R) (v : R) (hv : v ∈ N)
    (q : ℕ) (a : R) (ha : a ∈ I ⊔ N^(q+1)) : v*a ∈ I ⊔ N^(q+2) := by
  obtain ⟨i,hi,b,hb,rfl⟩ := Submodule.mem_sup.mp ha
  rw [mul_add]
  apply (I ⊔ N^(q+2)).add_mem
  · exact (le_sup_left : I ≤ I ⊔ N^(q+2)) (I.mul_mem_left v hi)
  · apply (le_sup_right : N^(q+2) ≤ I ⊔ N^(q+2))
    rw [show q+2=(q+1)+1 from rfl,pow_succ']
    exact Ideal.mul_mem_mul hv hb

def adicSymbolMul (I N : Ideal R) (v : R) (hv : v ∈ N) (q : ℕ) :
    adicLayer I N q →ₗ[R] adicLayer I N (q+1) :=
  let f : R →ₗ[R] R ⧸ (I ⊔ N^(q+2)) :=
    (Ideal.Quotient.mkₐ R (I ⊔ N^(q+2))).toLinearMap.comp (LinearMap.mulLeft R v)
  let F : (R ⧸ (I ⊔ N^(q+1))) →ₗ[R] R ⧸ (I ⊔ N^(q+2)) :=
    (I ⊔ N^(q+1)).liftQ f (by
      intro a ha
      change Ideal.Quotient.mk (I ⊔ N^(q+2)) (v*a)=0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (mul_mem_successor I N v hv q a ha))
  (F.comp (adicLayer I N q).subtype).codRestrict _ (by
    rintro ⟨x,hx⟩
    obtain ⟨a,ha,rfl⟩ := hx
    refine ⟨v*a,?_,rfl⟩
    rw [pow_succ']
    exact Ideal.mul_mem_mul hv ha)

theorem adicSymbolMul_apply (I N : Ideal R) (v : R) (hv : v ∈ N)
    (q : ℕ) (a : R) (ha : a ∈ N^q) :
    (adicSymbolMul I N v hv q
      ⟨Ideal.Quotient.mk (I ⊔ N^(q+1)) a,⟨a,ha,rfl⟩⟩).val =
        Ideal.Quotient.mk (I ⊔ N^(q+2)) (v*a) := rfl

theorem ker_adicLayerMap_eq_range_adicSymbolMul
    (I N : Ideal R) (v : R) (hv : v ∈ N)
    (hreg : ∀ q : ℕ, ∀ b ∈ N^q, v*b ∈ I ⊔ N^(q+2) → b ∈ I ⊔ N^(q+1))
    (q : ℕ) : LinearMap.ker (adicLayerMap I N v (q+1)) =
      LinearMap.range (adicSymbolMul I N v hv q) := by
  apply le_antisymm
  · rintro ⟨x,hx⟩ hk
    obtain ⟨b,hb,rfl⟩ := hx
    have hz : Ideal.Quotient.mk ((I ⊔ Ideal.span ({v} : Set R)) ⊔ N^(q+2)) b=0 :=
      congrArg Subtype.val (LinearMap.mem_ker.mp hk)
    have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hz
    obtain ⟨j,hj,c,hc,hbc⟩ := Submodule.mem_sup.mp hmem
    have hcLow : c ∈ N^(q+1) := Ideal.pow_le_pow_right (by omega) hc
    have hbcN : b-c ∈ I ⊔ N^(q+1) :=
      (I ⊔ N^(q+1)).sub_mem ((le_sup_right : N^(q+1) ≤ I ⊔ N^(q+1)) hb)
        ((le_sup_right : N^(q+1) ≤ I ⊔ N^(q+1)) hcLow)
    have hbcP : b-c ∈ I ⊔ Ideal.span ({v} : Set R) := by
      have he : b-c=j := by rw [←hbc,add_sub_cancel_right]
      rw [he]; exact hj
    have hstrict : b-c ∈ I ⊔ Ideal.span ({v} : Set R)*N^q := by
      rw [←sup_pow_inf_principal_of_regular_symbol I N v hv hreg q]
      exact ⟨hbcN,hbcP⟩
    obtain ⟨i,hi,k,hk,he⟩ := Submodule.mem_sup.mp hstrict
    obtain ⟨h,hh,rfl⟩ := Ideal.mem_span_singleton_mul.mp hk
    refine ⟨⟨Ideal.Quotient.mk (I ⊔ N^(q+1)) h,⟨h,hh,rfl⟩⟩,?_⟩
    apply Subtype.ext
    change Ideal.Quotient.mk (I ⊔ N^(q+2)) (v*h)=Ideal.Quotient.mk (I ⊔ N^(q+2)) b
    apply Ideal.Quotient.eq.mpr
    have hbEq : b=(i+v*h)+c := (sub_eq_iff_eq_add).mp he.symm
    have hdiff : b-v*h=i+c := by
      rw [hbEq,add_right_comm i (v*h) c,add_sub_cancel_right]
    have hm : b-v*h ∈ I ⊔ N^(q+2) := by
      rw [hdiff]
      exact (I ⊔ N^(q+2)).add_mem ((le_sup_left : I ≤ I ⊔ N^(q+2)) hi)
        ((le_sup_right : N^(q+2) ≤ I ⊔ N^(q+2)) hc)
    simpa only [neg_sub] using (I ⊔ N^(q+2)).neg_mem hm
  · rintro x ⟨⟨y,hy⟩,rfl⟩
    obtain ⟨a,ha,rfl⟩ := hy
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    change Ideal.Quotient.mk ((I ⊔ Ideal.span ({v} : Set R)) ⊔ N^(q+2)) (v*a)=0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (le_trans le_sup_right le_sup_left :
      Ideal.span ({v} : Set R) ≤ (I ⊔ Ideal.span ({v} : Set R)) ⊔ N^(q+2))
    exact Ideal.mul_mem_right a (Ideal.span ({v} : Set R)) (Ideal.mem_span_singleton_self v)

private def quotientByKnownKernelEquiv
    {M P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (S : Submodule R M) (f : M →ₗ[R] P) (hS : S=LinearMap.ker f)
    (hf : Function.Surjective f) : (M ⧸ S) ≃ₗ[R] P :=
  (Submodule.quotEquivOfEq S (LinearMap.ker f) hS).trans
    (f.quotKerEquivOfSurjective hf)

private theorem quotientByKnownKernelEquiv_apply
    {M P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (S : Submodule R M) (f : M →ₗ[R] P) (hS : S=LinearMap.ker f)
    (hf : Function.Surjective f) (x : M) :
    quotientByKnownKernelEquiv S f hS hf (Submodule.Quotient.mk x)=f x := rfl

def adicLayerQuotientEquiv
    (I N : Ideal R) (v : R) (hv : v ∈ N)
    (hreg : ∀ q : ℕ, ∀ b ∈ N^q, v*b ∈ I ⊔ N^(q+2) → b ∈ I ⊔ N^(q+1))
    (q : ℕ) :
    (adicLayer I N (q+1) ⧸ LinearMap.range (adicSymbolMul I N v hv q)) ≃ₗ[R]
      adicLayer (I ⊔ Ideal.span ({v} : Set R)) N (q+1) :=
  quotientByKnownKernelEquiv (LinearMap.range (adicSymbolMul I N v hv q))
    (adicLayerMap I N v (q+1))
    (ker_adicLayerMap_eq_range_adicSymbolMul I N v hv hreg q).symm
    (adicLayerMap_surjective I N v (q+1))

theorem adicLayerQuotientEquiv_apply
    (I N : Ideal R) (v : R) (hv : v ∈ N)
    (hreg : ∀ q : ℕ, ∀ b ∈ N^q, v*b ∈ I ⊔ N^(q+2) → b ∈ I ⊔ N^(q+1))
    (q : ℕ) (x : adicLayer I N (q+1)) :
    adicLayerQuotientEquiv I N v hv hreg q (Submodule.Quotient.mk x) =
      adicLayerMap I N v (q+1) x :=
  quotientByKnownKernelEquiv_apply _ _ _ _ x

theorem adicLayer_zero_denominator (I N : Ideal R) (v : R) (hv : v ∈ N) :
    (I ⊔ Ideal.span ({v} : Set R)) ⊔ N = I ⊔ N := by
  apply le_antisymm
  · exact sup_le (sup_le le_sup_left
      ((Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hv)).trans le_sup_right)) le_sup_right
  · exact sup_le (le_trans le_sup_left le_sup_left) le_sup_right

theorem adicLayerMap_zero_injective (I N : Ideal R) (v : R) (hv : v ∈ N) :
    Function.Injective (adicLayerMap I N v 0) := by
  rintro ⟨x,hx⟩ ⟨y,hy⟩ he
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  apply Subtype.ext
  apply Ideal.Quotient.eq.mpr
  have hEq : Ideal.Quotient.mk ((I ⊔ Ideal.span ({v} : Set R)) ⊔ N^(0+1)) a =
      Ideal.Quotient.mk ((I ⊔ Ideal.span ({v} : Set R)) ⊔ N^(0+1)) b :=
    congrArg Subtype.val he
  have hm := Ideal.Quotient.eq.mp hEq
  simpa only [zero_add,pow_one,adicLayer_zero_denominator I N v hv] using hm

end
end Hironaka.HironakaStrictFilteredGradedQuotient
