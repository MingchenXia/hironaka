import Hironaka.Algebra.NodeFamilyBaseChange
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Actual full node quotients along coefficient ideals -/

noncomputable section

open scoped TensorProduct

namespace Hironaka.Algebra.NodeQuotientBaseChange

open NodeBlowupChart

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] (I : Ideal A) (t : A)

/-- The original relation ideal maps literally through the native polynomial tensor equivalence. -/
theorem tensorRelationIdeal_map (S : Type u) [CommRing S] [Algebra A S] :
    ((NodeChart.uChartIdeal A t).map
      (Algebra.TensorProduct.includeRight (A := S) (R := A))).map
        (MvPolynomial.algebraTensorAlgEquiv A S).toRingHom =
      NodeChart.uChartIdeal S (algebraMap A S t) := by
  change Ideal.map (MvPolynomial.algebraTensorAlgEquiv A S).toRingHom
    (Ideal.map (Algebra.TensorProduct.includeRight (A := S) (R := A)).toRingHom
      (NodeChart.uChartIdeal A t)) = _
  rw [Ideal.map_map]
  have he : (MvPolynomial.algebraTensorAlgEquiv (σ := Fin 2) A S).toRingHom.comp
      (Algebra.TensorProduct.includeRight (A := S) (R := A)).toRingHom =
        MvPolynomial.map (algebraMap A S) := by
    apply RingHom.ext
    intro P
    change MvPolynomial.algebraTensorAlgEquiv A S (1 ⊗ₜ[A] P) = _
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  rw [he]
  exact NodeFamilyBaseChange.nodeIdeal_map S t

/-- Native tensor base change with the original relation and explicit generator formulas. -/
def tensorEquiv (S : Type u) [CommRing S] [Algebra A S] :
    S ⊗[A] Node A t ≃ₐ[S] Node S (algebraMap A S t) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := A) S
    (MvPolynomial (Fin 2) A) S (NodeChart.uChartIdeal A t)).trans
      (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv A S)
        (tensorRelationIdeal_map t S).symm)

/-- The actual tensor adapter preserves every original polynomial, not only its support. -/
theorem tensorEquiv_one_tmul (S : Type u) [CommRing S] [Algebra A S]
    (P : MvPolynomial (Fin 2) A) :
    tensorEquiv t S (1 ⊗ₜ[A] Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (MvPolynomial.map (algebraMap A S) P) := by
  simp [tensorEquiv, MvPolynomial.algebraTensorAlgEquiv_tmul]

/-- The actual full coefficient-ideal quotient is the literal quotient-coefficient node. -/
def quotientEquiv :
    (Node A t ⧸ I.map (algebraMap A (Node A t))) ≃ₐ[A ⧸ I]
      Node (A ⧸ I) (Ideal.Quotient.mk I t) :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (Node A t) I).trans
    (tensorEquiv t (A ⧸ I))

/-- The same actual coefficient-quotient equivalence over the original base ring. -/
def quotientEquivOverBase :
    (Node A t ⧸ I.map (algebraMap A (Node A t))) ≃ₐ[A]
      Node (A ⧸ I) (Ideal.Quotient.mk I t) :=
  (quotientEquiv I t).restrictScalars A

/-- The actual original coefficient map is retained by the full-ideal equivalence. -/
theorem quotientEquiv_coefficient (a : A) :
    quotientEquiv I t
      (Ideal.Quotient.mk _ (algebraMap A (Node A t) a)) =
        algebraMap (A ⧸ I) (Node (A ⧸ I) (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I a) := by
  simpa only [Ideal.Quotient.algebraMap_quotient_map_quotient] using
    (quotientEquiv I t).commutes (Ideal.Quotient.mk I a)

/-- Both literal original node coordinates survive the full coefficient quotient. -/
theorem quotientEquiv_coordinate (i : Fin 2) :
    quotientEquiv I t (Ideal.Quotient.mk _ (coordinate t i)) =
      coordinate (Ideal.Quotient.mk I t) i := by
  simp only [quotientEquiv, AlgEquiv.trans_apply,
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  simpa [coordinate] using
    tensorEquiv_one_tmul t (A ⧸ I) (MvPolynomial.X i)

end Hironaka.Algebra.NodeQuotientBaseChange
