import Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeIntersections
import Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeBoundary

/-! The literal prime factors of a several-component native SNC node boundary. -/

noncomputable section

open Polynomial AlgebraicGeometry CategoryTheory

namespace Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeFactors

open Algebra.NodeBlowupChart Algebra.NodeNormalCoordinates
open MonomialBlowupRegularBaseSNCNodeAlgebra MonomialBlowupRegularBaseSNCParameters
open SpecIdealSheaf Scheme.IdealSheafData ReducedClosedSubscheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {A : Type u} [CommRing A]

/-- The full coefficient-principal quotient retains its literal node and both original coordinates. -/
def coefficientPrincipalQuotientEquiv (a t : A) :
    (Node A t ⧸ Ideal.span {algebraMap A (Node A t) a}) ≃+*
      Node (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk _ t) :=
  (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton] :
    Ideal.span {algebraMap A (Node A t) a} = (Ideal.span {a}).map (algebraMap A (Node A t)))).trans
      (Algebra.NodeQuotientBaseChange.quotientEquiv (Ideal.span {a}) t).toRingEquiv

/-- Its literal original coefficient formula. -/
theorem coefficientPrincipalQuotientEquiv_coefficient (a t b : A) :
    coefficientPrincipalQuotientEquiv a t
      (Ideal.Quotient.mk _ (algebraMap A (Node A t) b)) =
        algebraMap (A ⧸ Ideal.span {a}) _ (Ideal.Quotient.mk _ b) := by
  exact Algebra.NodeQuotientBaseChange.quotientEquiv_coefficient (Ideal.span {a}) t b

/-- The original coefficient in the actual first-axis quotient is its literal residue constant. -/
theorem coordinateQuotientEquiv_coefficient (t a : A) :
    coordinateQuotientEquiv t (mkCoordinate t (algebraMap A (Node A t) a)) =
      C (Ideal.Quotient.mk (Ideal.span {t}) a) := by
  exact (coordinateQuotientEquiv t).commutes a

/-- The original coefficient in the actual second-axis quotient is the same literal residue constant. -/
theorem quotientCoordinate1Equiv_coefficient (t a : A) :
    quotientCoordinate1Equiv t
      (Ideal.Quotient.mk (Ideal.span {coordinate t 1}) (algebraMap A (Node A t) a)) =
        Polynomial.C (Ideal.Quotient.mk (Ideal.span {t}) a) := by
  simp only [quotientCoordinate1Equiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlg_mk,
    AlgEquiv.commutes]
  exact coordinateQuotientEquiv_coefficient t a

variable [IsRegularRing A]

/-- Distinct actual SNC components have incomparable original principal ideals. -/
theorem component_equation_not_mem
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C B : DivisorComponent D) (hCB : C ≠ B) (t a : A)
    (ht : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (ha : specIdealSheaf A (Ideal.span {a}) = vanishingIdeal B.val) :
    a ∉ Ideal.span {t} := by
  obtain ⟨hp, hheight, _⟩ := component_equation_data D hD C t ht
  obtain ⟨hq, hheight', _⟩ := component_equation_data D hD B a ha
  let := hp
  let := hq
  intro hamem
  have hle : Ideal.span {a} ≤ Ideal.span {t} := Ideal.span_le.mpr (by simpa using hamem)
  have heq : Ideal.span {a} = Ideal.span {t} := by
    by_contra hne
    have h := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
    rw [hheight, hheight'] at h
    norm_num at h
  apply hCB
  apply Subtype.ext
  have hs : vanishingIdeal C.val = vanishingIdeal B.val := by rw [← ht, ← ha, heq]
  have h := congrArg Scheme.IdealSheafData.support hs
  simpa only [support_vanishingIdeal] using h

variable [IsDomain A]

/-- The genuine remaining component equation stays prime in the original node. -/
theorem coefficient_prime
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C B : DivisorComponent D) (hCB : C ≠ B) (t a : A)
    (ht : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (ha : specIdealSheaf A (Ideal.span {a}) = vanishingIdeal B.val) :
    Prime (algebraMap A (Node A t) a) := by
  have ht0 := component_equation_ne_zero D hD C t ht
  have ha0 := component_equation_ne_zero D hD B a ha
  let : IsDomain (Node A t) := Algebra.NodeDomain.nodeQuotient_isDomain t ht0
  have hpa := (component_equation_data D hD B a ha).1
  let := hpa
  have htb : Ideal.Quotient.mk (Ideal.span {a}) t ≠ 0 := by
    intro hz
    exact component_equation_not_mem D hD B C hCB.symm a t ha ht
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  let : IsDomain (Node (A ⧸ Ideal.span {a}) (Ideal.Quotient.mk _ t)) :=
    Algebra.NodeDomain.nodeQuotient_isDomain _ htb
  let : IsDomain (Node A t ⧸ Ideal.span {algebraMap A (Node A t) a}) :=
    MulEquiv.isDomain _ (coefficientPrincipalQuotientEquiv a t).toMulEquiv
  have hp : (Ideal.span {algebraMap A (Node A t) a}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  exact (Ideal.span_singleton_prime
    ((map_ne_zero_iff _ (Algebra.NodeDomain.algebraMap_nodeQuotient_injective t ht0)).mpr ha0)).mp hp

omit [IsDomain A] in
/-- A remaining genuine coefficient equation is not divisible by either original node coordinate. -/
theorem coordinate_not_dvd_coefficient
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C B : DivisorComponent D) (hCB : C ≠ B) (t a : A)
    (ht : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (ha : specIdealSheaf A (Ideal.span {a}) = vanishingIdeal B.val) (i : Fin 2) :
    ¬ coordinate t i ∣ algebraMap A (Node A t) a := by
  intro hdiv
  have hmem := Ideal.mem_span_singleton.mpr hdiv
  have hzero : Ideal.Quotient.mk (Ideal.span {coordinate t i}) (algebraMap A (Node A t) a) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  have hconst : Polynomial.C (Ideal.Quotient.mk (Ideal.span {t}) a) = (0 : (ParameterQuotient t)[X]) := by
    fin_cases i
    · have h := congrArg (coordinateQuotientEquiv t) hzero
      change coordinateQuotientEquiv t (mkCoordinate t (algebraMap A (Node A t) a)) = _ at h
      simpa only [coordinateQuotientEquiv_coefficient, map_zero] using h
    · have h := congrArg (quotientCoordinate1Equiv t) hzero
      have hz : quotientCoordinate1Equiv t
          (Ideal.Quotient.mk (Ideal.span {coordinate t 1}) (algebraMap A (Node A t) a)) = 0 :=
        h.trans (map_zero _)
      exact (quotientCoordinate1Equiv_coefficient t a).symm.trans hz
  have ha0 : Ideal.Quotient.mk (Ideal.span {t}) a = 0 := by
    apply Polynomial.C_injective
    simpa only [Polynomial.C_0] using hconst
  exact component_equation_not_mem D hD C B hCB t a ht ha
    (Ideal.Quotient.eq_zero_iff_mem.mp ha0)

omit [IsDomain A] in
/-- Distinct remaining original component equations remain nondividing under the actual coefficient map. -/
theorem coefficient_not_dvd_coefficient
    (D : (Spec (CommRingCat.of A)).IdealSheafData) (hD : IsStrictNormalCrossings D)
    (C B B' : DivisorComponent D) (hCB : C ≠ B) (hBB' : B ≠ B') (t a b : A)
    (ht : specIdealSheaf A (Ideal.span {t}) = vanishingIdeal C.val)
    (ha : specIdealSheaf A (Ideal.span {a}) = vanishingIdeal B.val)
    (hb : specIdealSheaf A (Ideal.span {b}) = vanishingIdeal B'.val) :
    ¬ algebraMap A (Node A t) a ∣ algebraMap A (Node A t) b := by
  have hpa := (component_equation_data D hD B a ha).1
  let := hpa
  have htb : Ideal.Quotient.mk (Ideal.span {a}) t ≠ 0 := by
    intro hz
    exact component_equation_not_mem D hD B C hCB.symm a t ha ht
      (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  intro hdiv
  have hz : Ideal.Quotient.mk (Ideal.span {algebraMap A (Node A t) a})
      (algebraMap A (Node A t) b) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton.mpr hdiv)
  have h := congrArg (coefficientPrincipalQuotientEquiv a t) hz
  rw [coefficientPrincipalQuotientEquiv_coefficient, map_zero] at h
  have hb0 : Ideal.Quotient.mk (Ideal.span {a}) b = 0 := by
    apply Algebra.NodeDomain.algebraMap_nodeQuotient_injective _ htb
    simpa only [map_zero] using h
  exact component_equation_not_mem D hD B B' hBB' a b ha hb
    (Ideal.Quotient.eq_zero_iff_mem.mp hb0)

end Hironaka.Geometry.MonomialBlowupRegularBaseSNCNodeFactors
