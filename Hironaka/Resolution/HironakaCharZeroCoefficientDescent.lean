/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaRelativeNormalCoefficientPolynomialBaseChange
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.FinitePresentation
import Mathlib.Algebra.Algebra.Rat
import Mathlib.RingTheory.Flat.Basic

/-! # Actual finite coefficient models in characteristic zero

Finite polynomial relations over an arbitrary characteristic-zero field
internally determine an actual finitely generated rational coefficient
subfield and an exact scalar-extension model. No complex embedding or
resolution data is assumed. Algebraization of centres, resolution descent
and resolution of abstract analytic spaces remain separate obligations.
-/

set_option autoImplicit false
open Set
open scoped TensorProduct

namespace Hironaka.HironakaCharZeroCoefficientDescent
noncomputable section

open HironakaRelativeNormalCoefficientPolynomialBaseChange

variable {K : Type*} [Field K] [CharZero K]

/-- Every finite original relation family descends to its actual finitely generated rational coefficient field. -/
theorem finite_relations_descend (n r : ℕ) (P : Fin r → MvPolynomial (Fin n) K) :
    ∃ L : IntermediateField ℚ K, L.FG ∧
      ∃ Q : Fin r → MvPolynomial (Fin n) L,
        (∀ i, MvPolynomial.map (algebraMap L K) (Q i) = P i) ∧
        Algebra.FinitePresentation L (MvPolynomial (Fin n) L ⧸ Ideal.span (Set.range Q)) ∧
        Nonempty ((K ⊗[L] (MvPolynomial (Fin n) L ⧸ Ideal.span (Set.range Q))) ≃ₐ[K]
          (MvPolynomial (Fin n) K ⧸ Ideal.span (Set.range P))) := by
  classical
  let S : Finset K := Finset.univ.biUnion fun i => (P i).coeffs
  let L : IntermediateField ℚ K := IntermediateField.adjoin ℚ (S : Set K)
  have hL : L.FG := IntermediateField.fg_adjoin_finset S
  have hcoeff (i : Fin r) : ((P i).coeffs : Set K) ⊆ Set.range (algebraMap L K) := by
    intro c hc
    have hcS : c ∈ S := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hc⟩
    have hcL : c ∈ L := IntermediateField.subset_adjoin ℚ (S : Set K) hcS
    exact ⟨⟨c, hcL⟩, rfl⟩
  have hQ (i : Fin r) : ∃ Q : MvPolynomial (Fin n) L,
      MvPolynomial.map (algebraMap L K) Q = P i :=
    (MvPolynomial.mem_range_map_iff_coeffs_subset).mpr (hcoeff i)
  choose Q hQ using hQ
  have hI : Ideal.map (MvPolynomial.map (algebraMap L K)) (Ideal.span (Set.range Q)) =
      Ideal.span (Set.range P) := by
    rw [Ideal.map_span, ← Set.range_comp]
    apply congrArg Ideal.span
    apply congrArg Set.range
    funext i
    exact hQ i
  have hFP : Algebra.FinitePresentation L
      (MvPolynomial (Fin n) L ⧸ Ideal.span (Set.range Q)) :=
    (Algebra.FinitePresentation.of_finiteType (R := L)
      (A := MvPolynomial (Fin n) L ⧸ Ideal.span (Set.range Q))).mp inferInstance
  have E := polynomialQuotientBaseChangeEquiv L K n (Ideal.span (Set.range Q))
  rw [hI] at E
  exact ⟨L, hL, Q, hQ, hFP, ⟨E⟩⟩

/-- A finite-type original algebra internally supplies a finite coefficient model and an exact tensor isomorphism. -/
theorem finite_type_algebra_descends (A : Type*) [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] :
    ∃ L : IntermediateField ℚ K, L.FG ∧
      ∃ (n r : ℕ) (Q : Fin r → MvPolynomial (Fin n) L),
        Algebra.FinitePresentation L (MvPolynomial (Fin n) L ⧸ Ideal.span (Set.range Q)) ∧
        Nonempty ((K ⊗[L] (MvPolynomial (Fin n) L ⧸ Ideal.span (Set.range Q))) ≃ₐ[K] A) := by
  classical
  let : Algebra.FinitePresentation K A :=
    (Algebra.FinitePresentation.of_finiteType (R := K)).mp inferInstance
  obtain ⟨n, f, hf, hker⟩ := Algebra.FinitePresentation.out (R := K) (A := A)
  obtain ⟨r, P, hP⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hker
  have hPI : Ideal.span (Set.range P) = RingHom.ker f.toRingHom := hP
  obtain ⟨L, hL, Q, _hQ, hFP, ⟨E⟩⟩ := finite_relations_descend n r P
  have F := Ideal.quotientKerAlgEquivOfSurjective hf
  change (MvPolynomial (Fin n) K ⧸ RingHom.ker f.toRingHom) ≃ₐ[K] A at F
  rw [← hPI] at F
  exact ⟨L, hL, n, r, Q, hFP, ⟨E.trans F⟩⟩

omit [CharZero K] in
private theorem model_isDomain_of_scalarExtension
    {L : Type*} [Field L] [Algebra L K]
    (A0 A : Type*) [CommRing A0] [Algebra L A0]
    [CommRing A] [Algebra K A] [IsDomain A]
    (E : (K ⊗[L] A0) ≃ₐ[K] A) : IsDomain A0 := by
  let f : A0 →+* A := E.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := L) (A := K) (B := A0)).toRingHom
  have hι : Function.Injective
      (Algebra.TensorProduct.includeRight (R := L) (A := K) (B := A0)) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap L K).injective
  exact Function.Injective.isDomain f (E.injective.comp hι)

/-- Integral finite-type algebras internally give actual integral finite coefficient models. -/
theorem finite_type_domain_descends (A : Type*) [CommRing A] [Algebra K A]
    [IsDomain A] [Algebra.FiniteType K A] :
    ∃ L : IntermediateField ℚ K, L.FG ∧
      ∃ (n r : ℕ) (Q : Fin r → MvPolynomial (Fin n) L),
        Algebra.FinitePresentation L (MvPolynomial (Fin n) L ⧸ Ideal.span (Set.range Q)) ∧
        IsDomain (MvPolynomial (Fin n) L ⧸ Ideal.span (Set.range Q)) ∧
        Nonempty ((K ⊗[L] (MvPolynomial (Fin n) L ⧸ Ideal.span (Set.range Q))) ≃ₐ[K] A) := by
  obtain ⟨L, hL, n, r, Q, hFP, ⟨E⟩⟩ := finite_type_algebra_descends (K := K) A
  exact ⟨L, hL, n, r, Q, hFP,
    model_isDomain_of_scalarExtension
      (MvPolynomial (Fin n) L ⧸ Ideal.span (Set.range Q)) A E, ⟨E⟩⟩

end
end Hironaka.HironakaCharZeroCoefficientDescent
