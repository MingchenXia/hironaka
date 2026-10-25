/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors
-/
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Nakayama
import Mathlib.Algebra.Regular.Basic

/-!
# The actual local kernel of an étale marking on a smooth relative curve

The original compatible maps and differential module give a principal regular
kernel internally. This is the local algebra step toward the original marked
Cartier divisor; no scheme Cartier or marked-dualizing-twist claim is made here.

Blueprint: `stable-marked-cartier-algebra.tex`.
-/

noncomputable section

open IsLocalRing TensorProduct KaehlerDifferential

namespace DeJongAlterations.StableModificationBridge.StableMarkedCartierAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v w

/-- The original étale marking quotient of a smooth local curve has an actual
principal regular kernel; neither its equation nor conormal comparison is supplied. -/
theorem exists_regular_kernel_generator
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [Nontrivial C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra.FormallySmooth A B] [Algebra.FormallyEtale A C]
    (hf : Function.Surjective (algebraMap B C)) (eΩ : Ω[B⁄A] ≃ₗ[B] B) :
    ∃ t : B, IsRegular t ∧ RingHom.ker (algebraMap B C) = Ideal.span {t} := by
  let I : Ideal B := RingHom.ker (algebraMap B C)
  have hinj : Function.Injective (kerCotangentToTensor A B C) :=
    (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff hf).mpr inferInstance
  have hsurj : Function.Surjective (kerCotangentToTensor A B C) := by
    intro z
    exact (exact_kerCotangentToTensor_mapBaseChange A B C hf z).mp
      (Subsingleton.elim _ _)
  let e : I.Cotangent ≃ₗ[B] C :=
    (LinearEquiv.ofBijective (kerCotangentToTensor A B C) ⟨hinj, hsurj⟩) ≪≫ₗ
      eΩ.lTensor C ≪≫ₗ TensorProduct.rid B C
  obtain ⟨t, ht⟩ := I.toCotangent_surjective (e.symm 1)
  have ht1 : e (I.toCotangent t) = 1 := by rw [ht, e.apply_symm_apply]
  have hI : I ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ I := h.symm ▸ (show (1 : B) ∈ (⊤ : Ideal B) from trivial)
    exact one_ne_zero (by simpa only [I, RingHom.mem_ker, map_one] using h1)
  have hle : I ≤ Ideal.span {(t : B)} ⊔ I * I := by
    intro x hx
    obtain ⟨b, hb⟩ := hf (e (I.toCotangent ⟨x, hx⟩))
    have hres : I.toCotangent (⟨x, hx⟩ - b • t) = 0 := by
      apply e.injective
      simp only [map_sub, map_smul, ht1, map_zero, Algebra.smul_def, mul_one, hb, sub_self]
    have hsq : x - b * t ∈ I * I := by
      have h := (I.toCotangent_eq_zero _).mp hres
      change x - b * (t : B) ∈ I ^ 2 at h
      simpa only [pow_two] using h
    exact Submodule.mem_sup.mpr
      ⟨b * t, (Ideal.span {(t : B)}).mul_mem_left b
        (Ideal.subset_span (Set.mem_singleton _)), x - b * t, hsq, by ring⟩
  have hprincipal : I = Ideal.span {(t : B)} := by
    apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I)
        ((le_maximalIdeal hI).trans (maximalIdeal_le_jacobson _))
      simpa only [Ideal.smul_eq_mul] using hle
    · exact Ideal.span_le.mpr fun x hx => Set.mem_singleton_iff.mp hx ▸ t.2
  have ht0 : (t : B) ≠ 0 := by
    intro h
    have h' : t = 0 := Subtype.ext h
    rw [h', map_zero, map_zero] at ht1
    exact zero_ne_one ht1
  exact ⟨t, IsRegular.of_ne_zero ht0, hprincipal⟩

end DeJongAlterations.StableModificationBridge.StableMarkedCartierAlgebra
