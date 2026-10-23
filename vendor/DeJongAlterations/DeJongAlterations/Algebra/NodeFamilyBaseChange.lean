import DeJongAlterations.Algebra.GenericFlatness
import DeJongAlterations.Algebra.NodeFamilyFlat
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! Actual coefficient base change and reduced field-valued node equations. -/

noncomputable section

open scoped TensorProduct
open MvPolynomial

namespace DeJongAlterations.Algebra.NodeFamilyBaseChange

open NodeBlowupChart

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [CommRing A] (S : Type u) [CommRing S] [Algebra A S]

/-- Actual extension of the original node relation ideal retains its entire literal equation. -/
theorem nodeIdeal_map (t : A) :
    (NodeChart.uChartIdeal A t).map (MvPolynomial.map (algebraMap A S)) =
      NodeChart.uChartIdeal S (algebraMap A S t) := by
  rw [NodeChart.uChartIdeal, NodeChart.uChartIdeal, Ideal.map_span, Set.image_singleton]
  simp only [map_sub, map_mul, MvPolynomial.map_X, MvPolynomial.map_C]

/-- The entire actual node quotient is preserved by arbitrary coefficient tensor base change. -/
def nodeBaseChangeEquiv (t : A) :
    S ⊗[A] Node A t ≃ₐ[S] Node S (algebraMap A S t) :=
  (GenericFlatness.polynomialQuotientBaseChangeEquiv A S 2 (NodeChart.uChartIdeal A t)).trans
    (Ideal.quotientEquivAlgOfEq S (nodeIdeal_map S t))

variable (K : Type u) [Field K]

/-- The zero-parameter node equation is genuinely radical over every field. -/
theorem nodeZeroIdeal_isRadical : (NodeChart.uChartIdeal K 0).IsRadical := by
  have hrad : (Ideal.span {∏ i ∈ (Finset.univ : Finset (Fin 2)), (X i : MvPolynomial (Fin 2) K)}).IsRadical := by
    apply isRadical_iff_span_singleton.mp
    apply Squarefree.isRadical
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i _ j _ hij
      apply (MvPolynomial.X_prime (R := K) (i := i)).irreducible.isRelPrime_iff_not_dvd.mpr
      intro hdiv
      exact hij (MvPolynomial.X_dvd_X.mp hdiv)
    · intro i _
      exact (MvPolynomial.X_prime (R := K) (i := i)).irreducible.squarefree
  simpa only [NodeChart.uChartIdeal, MvPolynomial.C_0, sub_zero, Fin.prod_univ_two] using hrad

/-- Every actual node algebra over a field is reduced, including the crossing fibre. -/
theorem node_isReduced (t : K) : _root_.IsReduced (Node K t) := by
  by_cases ht : t = 0
  · subst t
    exact (Ideal.isRadical_iff_quotient_reduced _).mp (nodeZeroIdeal_isRadical K)
  · let : IsDomain (Node K t) := NodeDomain.nodeQuotient_isDomain t ht
    infer_instance

/-- The actual tensor base change of the node to any field is reduced. -/
theorem fieldBaseChange_isReduced [Algebra A K] (t : A) :
    _root_.IsReduced (K ⊗[A] Node A t) := by
  let : _root_.IsReduced (Node K (algebraMap A K t)) := node_isReduced K _
  exact isReduced_of_injective (nodeBaseChangeEquiv K t).toRingHom
    (nodeBaseChangeEquiv K t).injective

end DeJongAlterations.Algebra.NodeFamilyBaseChange
