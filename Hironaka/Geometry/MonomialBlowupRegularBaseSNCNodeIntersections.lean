import Hironaka.Algebra.NodeQuotientBaseChange
import Hironaka.Geometry.MonomialBlowupRegularBaseSNCQuotientNode
import Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeAlgebra

/-! Exact mixed node boundary quotient rings and their derived native regularity. -/

noncomputable section

open Polynomial AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeIntersections

open Algebra.NodeBlowupChart Algebra.NodeNormalCoordinates
open MonomialBlowupRegularBaseSNCNodeAlgebra MonomialBlowupRegularBaseSNCIntersection
open MonomialBlowupRegularBaseSNCQuotientParameters MonomialBlowupRegularBaseSNCQuotientNode
open SpecIdealSheaf Scheme.IdealSheafData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A]

/-- The actual sum of the full coefficient ideal with the selected original coordinate ideals. -/
def mixedIdeal (I : Ideal A) (t : A) (s : Finset (Fin 2)) : Ideal (Node A t) :=
  I.map (algebraMap A (Node A t)) ⊔ nodeIdeal t s

/-- The entire mixed quotient is the actual selected-coordinate quotient of the quotient-coefficient node. -/
def mixedQuotientEquiv (I : Ideal A) (t : A) (s : Finset (Fin 2)) :
    (Node A t ⧸ mixedIdeal I t s) ≃+*
      (Node (A ⧸ I) (Ideal.Quotient.mk I t) ⧸ nodeIdeal (Ideal.Quotient.mk I t) s) := by
  let K := I.map (algebraMap A (Node A t))
  let e := (Algebra.NodeQuotientBaseChange.quotientEquiv I t).toRingEquiv
  have hmap : nodeIdeal (Ideal.Quotient.mk I t) s =
      ((nodeIdeal t s).map (Ideal.Quotient.mk K)).map e.toRingHom := by
    rw [Ideal.map_map]
    simp only [nodeIdeal, Ideal.map_span, ← Set.image_comp]
    have hf : (e.toRingHom.comp (Ideal.Quotient.mk K)) ∘ coordinate t =
        coordinate (Ideal.Quotient.mk I t) := by
      funext i
      exact Algebra.NodeQuotientBaseChange.quotientEquiv_coordinate I t i
    rw [hf]
  exact (DoubleQuot.quotQuotEquivQuotSup K (nodeIdeal t s)).symm.trans
    (Ideal.quotientEquiv _ _ e hmap)

/-- The actual iterated parameter quotient is the original coefficient ideal sum quotient. -/
def parameterQuotientEquiv (I : Ideal A) (t : A) :
    ((A ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I t}) ≃+* A ⧸ I ⊔ Ideal.span {t} := by
  have hmap : Ideal.span {Ideal.Quotient.mk I t} = (Ideal.span {t}).map (Ideal.Quotient.mk I) := by
    rw [Ideal.map_span, Set.image_singleton]
  exact (Ideal.quotEquivOfEq hmap).trans (DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {t}))

/-- The actual mixed first-axis quotient is a polynomial ring over the original sum quotient. -/
def mixedAxis0QuotientEquiv (I : Ideal A) (t : A) :
    (Node A t ⧸ mixedIdeal I t {0}) ≃+* (A ⧸ I ⊔ Ideal.span {t})[X] :=
  (mixedQuotientEquiv I t {0}).trans
    ((Ideal.quotEquivOfEq (nodeIdeal_singleton (Ideal.Quotient.mk I t) 0)).trans
      ((coordinateQuotientEquiv (Ideal.Quotient.mk I t)).toRingEquiv.trans
        (Polynomial.mapEquiv (parameterQuotientEquiv I t))))

/-- The literal surviving second coordinate is exactly the original polynomial variable. -/
theorem mixedAxis0QuotientEquiv_coordinate1 (I : Ideal A) (t : A) :
    mixedAxis0QuotientEquiv I t
      (Ideal.Quotient.mk _ (coordinate t 1)) = X := by
  simp only [mixedAxis0QuotientEquiv, mixedQuotientEquiv, mixedIdeal, RingEquiv.trans_apply,
    DoubleQuot.quotQuotEquivQuotSup_symm_quotQuotMk, DoubleQuot.quotQuotMk, RingHom.comp_apply,
    Ideal.quotientEquiv_mk,
    Ideal.quotEquivOfEq_mk, Polynomial.mapEquiv_apply]
  change Polynomial.map (parameterQuotientEquiv I t).toRingHom
    (coordinateQuotientEquiv (Ideal.Quotient.mk I t)
      (mkCoordinate (Ideal.Quotient.mk I t)
        (Algebra.NodeQuotientBaseChange.quotientEquiv I t
          (Ideal.Quotient.mk _ (coordinate t 1))))) = X
  rw [Algebra.NodeQuotientBaseChange.quotientEquiv_coordinate,
    coordinateQuotientEquiv_coordinate1, Polynomial.map_X]

/-- The actual mixed second-axis quotient has the other surviving original polynomial coordinate. -/
def mixedAxis1QuotientEquiv (I : Ideal A) (t : A) :
    (Node A t ⧸ mixedIdeal I t {1}) ≃+* (A ⧸ I ⊔ Ideal.span {t})[X] :=
  (mixedQuotientEquiv I t {1}).trans
    ((Ideal.quotEquivOfEq (nodeIdeal_singleton (Ideal.Quotient.mk I t) 1)).trans
      ((quotientCoordinate1Equiv (Ideal.Quotient.mk I t)).toRingEquiv.trans
        (Polynomial.mapEquiv (parameterQuotientEquiv I t))))

/-- The actual double-axis intersection is exactly the original coefficient sum quotient. -/
def mixedPairQuotientEquiv (I : Ideal A) (t : A) :
    (Node A t ⧸ mixedIdeal I t Finset.univ) ≃+* A ⧸ I ⊔ Ideal.span {t} :=
  (mixedQuotientEquiv I t Finset.univ).trans
    ((quotientCoordinatesEquiv (Ideal.Quotient.mk I t)).trans (parameterQuotientEquiv I t))

variable [IsRegularRing A]

/-- Full SNC internally produces regularity of every actual mixed coefficient/coordinate intersection. -/
theorem mixed_quotient_isRegularRing
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (J : Finset (DivisorComponent D)) (hJ : J.Nonempty)
    (C : DivisorComponent D) (hC : C ∉ J) (t : A)
    (heq : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val) (s : Finset (Fin 2)) :
    IsRegularRing (Node A t ⧸ mixedIdeal (intersectionIdeal D J) t s) := by
  classical
  let I := intersectionIdeal D J
  let B := A ⧸ I ⊔ Ideal.span {t}
  let : IsRegularRing B := by
    have heqI : I ⊔ Ideal.span {t} = intersectionIdeal D (insert C J) := by
      rw [intersectionIdeal_insert_equation D J C t heq, sup_comm]
    let : IsRegularRing (A ⧸ intersectionIdeal D (insert C J)) :=
      SNCSubdivisorComponent.isRegularRing_quotient_of_specIdealSheaf _ (by
        rw [intersectionIdeal_spec]
        exact hD.intersectionsRegular _ (Finset.insert_nonempty C J))
    exact IsRegularRing.of_ringEquiv (Ideal.quotEquivOfEq heqI).symm
  by_cases h0 : 0 ∈ s <;> by_cases h1 : 1 ∈ s
  · have hs : s = Finset.univ := by ext i; fin_cases i <;> simp_all
    rw [hs]
    exact IsRegularRing.of_ringEquiv (mixedPairQuotientEquiv I t).symm
  · have hs : s = {0} := by ext i; fin_cases i <;> simp_all
    rw [hs]
    exact IsRegularRing.of_ringEquiv (mixedAxis0QuotientEquiv I t).symm
  · have hs : s = {1} := by ext i; fin_cases i <;> simp_all
    rw [hs]
    exact IsRegularRing.of_ringEquiv (mixedAxis1QuotientEquiv I t).symm
  · have hs : s = ∅ := by ext i; fin_cases i <;> simp_all
    rw [hs]
    let : IsRegularRing (Node (A ⧸ I) (Ideal.Quotient.mk I t)) :=
      remaining_node_isRegularRing D hD J hJ C hC t heq
    let e := (mixedQuotientEquiv I t ∅).trans
      ((Ideal.quotEquivOfEq (nodeIdeal_empty (Ideal.Quotient.mk I t))).trans
        (RingEquiv.quotientBot (Node (A ⧸ I) (Ideal.Quotient.mk I t))))
    exact IsRegularRing.of_ringEquiv e.symm

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeIntersections
