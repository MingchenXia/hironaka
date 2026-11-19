import Hironaka.Algebra.NodeSingularJacobian
import Hironaka.Algebra.NodeSingularNorm

/-!
# The actual norm-locus factor for the original formal Jacobian quotient

The finite map is built from the actual original norm and the actual quotient
isomorphism. No etaleness of the induced zero-locus map is asserted.
-/

noncomputable section

namespace Hironaka.Algebra.NodeSingular

open MvPowerSeries NodeNonsplit

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]

/-- The actual finite factor into the original formal derivative quotient. -/
def normJacobianLocusMap (Q : Quadratic S) (h : S) :
    R ⧸ Ideal.span {Algebra.norm R h} →+* Node Q h ⧸ jacobianIdeal Q h :=
  (jacobianQuotientEquiv Q h).symm.toRingHom.comp (normLocusMap (R := R) h)

/-- The actual original coefficient triangle commutes on every element. -/
@[simp]
theorem normJacobianLocusMap_coefficient (Q : Quadratic S) (h : S) (r : R) :
    normJacobianLocusMap (R := R) Q h (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk (jacobianIdeal Q h)
        (Ideal.Quotient.mk (equationIdeal Q h) (C (algebraMap R S r))) := by
  apply (jacobianQuotientEquiv Q h).injective
  change jacobianQuotientEquiv Q h
    ((jacobianQuotientEquiv Q h).symm (Ideal.Quotient.mk _ (algebraMap R S r))) = _
  rw [AlgEquiv.apply_symm_apply, jacobianQuotientEquiv_coefficient]

/-- Finiteness is proved for the actual original norm-locus factor. -/
theorem normJacobianLocusMap_finite (Q : Quadratic S) (h : S) :
    @RingHom.Finite (R ⧸ Ideal.span {Algebra.norm R h})
      (Node Q h ⧸ jacobianIdeal Q h) inferInstance inferInstance
      (normJacobianLocusMap (R := R) Q h) := by
  refine @RingHom.Finite.comp
    (R ⧸ Ideal.span {Algebra.norm R h}) (S ⧸ Ideal.span {h})
    (Node Q h ⧸ jacobianIdeal Q h) inferInstance inferInstance inferInstance
    (jacobianQuotientEquiv Q h).symm.toRingHom (normLocusMap (R := R) h)
    ?_ (normLocusMap_finite (R := R) h)
  exact @RingHom.Finite.of_surjective
    (S ⧸ Ideal.span {h}) (Node Q h ⧸ jacobianIdeal Q h) inferInstance inferInstance
    (jacobianQuotientEquiv Q h).symm.toRingHom (jacobianQuotientEquiv Q h).symm.surjective

/-- The literal original norm is killed in the actual original formal Jacobian quotient. -/
theorem coefficient_norm_eq_zero (Q : Quadratic S) (h : S) :
    Ideal.Quotient.mk (jacobianIdeal Q h)
      (Ideal.Quotient.mk (equationIdeal Q h) (C (algebraMap R S (Algebra.norm R h)))) = 0 := by
  rw [← normJacobianLocusMap_coefficient (R := R) Q h]
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), map_zero]

end Hironaka.Algebra.NodeSingular
