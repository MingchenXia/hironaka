import Hironaka.Algebra.NodeFittingRelativeClosedTrace
import Hironaka.Algebra.NodeSingularNorm

/-! # The ACTUAL original singular completion lies over the actual norm zero locus

This proves a finite factor of the SAME actual completed structural map. It
asserts neither quotient etaleness nor a schematic-image norm-ideal equality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Algebra.NodeFittingRelativeNormTrace

open NodeFittingRelativeClosedTrace Geometry.NodeCompletedLocalMap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
  [IsLocallyNoetherian S]

local notation "I" => NodeFittingOmegaGluing.idealSheaf f 1
variable (z : (NodeFittingOmegaGluing.idealSheaf f 1).subscheme)
local notation "x" => (I).subschemeι z
local notation "A" => S.completedLocalRing (f x)
local notation "C" => X.completedLocalRing x
local notation "D" => (I).subscheme.completedLocalRing z

variable (T : Type u) [CommRing T] [IsLocalRing T]
  [Algebra (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T]
  [Module.Free (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T]
  [Module.Finite (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T]

section Factor

local instance : Algebra A C := completedAlgebra f x

variable
  [Algebra T (X.completedLocalRing ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))]
  [IsScalarTower (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T
    (X.completedLocalRing ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))]
  [Algebra.FormallyUnramified
    (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T]
  (Q : NodeNonsplit.Quadratic T) (h : T)
  (e : X.completedLocalRing ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z) ≃ₐ[T]
    NodeSingular.Node Q h)

local instance : Algebra T D := singularCoefficientAlgebra f z T

/-- The norm factor targets the ACTUAL native original singular completed stalk. -/
def normLocusSingularMap : A ⧸ Ideal.span {Algebra.norm A h} →+* D :=
  (actualSingularCompletedEquiv f z T Q h e).symm.toRingHom.comp
    (NodeSingular.normLocusMap (R := A) h)

/-- EVERY completed original base representative follows precisely the SAME actual completed structural map. -/
theorem normLocusSingularMap_mk (a : S.completedLocalRing (f ((I).subschemeι z))) :
    normLocusSingularMap f z T Q h e
      (Ideal.Quotient.mk (Ideal.span {Algebra.norm A h}) a) =
        completedMap (NodeFittingOmegaGluing.fittingMorphism f 1) z a := by
  change (actualSingularCompletedEquiv f z T Q h e).symm
    (NodeSingular.normLocusMap (R := A) h (Ideal.Quotient.mk _ a)) = _
  rw [NodeSingular.normLocusMap_mk]
  apply (actualSingularCompletedEquiv f z T Q h e).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (actualSingularCompletedEquiv_completedBase f z T Q h e a).symm

/-- The actual norm-zero-locus factor is finite; no flatness or etaleness is claimed. -/
theorem normLocusSingularMap_finite : (normLocusSingularMap f z T Q h e).Finite :=
  (RingHom.Finite.of_surjective
    (actualSingularCompletedEquiv f z T Q h e).symm.toRingHom
    (actualSingularCompletedEquiv f z T Q h e).symm.surjective).comp
      (NodeSingular.normLocusMap_finite (R := A) h)

end Factor

variable [IsLocalHom
  (algebraMap (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T)]

/-- The actual norm smoothing parameter is in the SAME original completed-base maximal ideal. -/
theorem norm_mem_originalCompletedBase_maximalIdeal (h : T) (hh : h ∈ maximalIdeal T) :
    Algebra.norm A h ∈ maximalIdeal A :=
  NodeSingular.norm_mem_maximalIdeal (R := A) h hh

end Hironaka.Algebra.NodeFittingRelativeNormTrace
