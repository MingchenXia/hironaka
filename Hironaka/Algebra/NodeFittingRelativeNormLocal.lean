import Hironaka.Algebra.NodeFittingRelativeParameter

/-! # Native local structure of the SAME actual finite norm-zero-locus factor -/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Algebra.NodeFittingRelativeNormLocal

open NodeFittingRelativeClosedTrace NodeFittingRelativeParameter Geometry.NodeCompletedLocalMap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u

section Algebra

variable {R T : Type*} [CommRing R] [IsLocalRing R] [CommRing T] [IsLocalRing T]
  [Algebra R T] [IsLocalHom (algebraMap R T)] [Module.Free R T] [Module.Finite R T]
  (h : T) (hh : h ∈ maximalIdeal T)

include hh

/-- Native local structure of the original proper parameter quotient. -/
theorem parameterQuotientLocalRing : IsLocalRing (T ⧸ Ideal.span {h}) :=
  CompletionIdealQuotient.quotientLocalRing _ (Ideal.span_le.mpr (by
    rintro a rfl
    exact hh))

/-- Native local structure of the original proper norm quotient. -/
theorem normQuotientLocalRing : IsLocalRing (R ⧸ Ideal.span {Algebra.norm R h}) :=
  CompletionIdealQuotient.quotientLocalRing _ (Ideal.span_le.mpr (by
    rintro a rfl
    exact NodeSingular.norm_mem_maximalIdeal h hh))

/-- Locality of the SAME finite norm factor, proved from its actual original representatives. -/
theorem normLocusMap_isLocalHom :
    letI := parameterQuotientLocalRing h hh
    letI := normQuotientLocalRing (R := R) h hh
    IsLocalHom (NodeSingular.normLocusMap (R := R) h) := by
  let := parameterQuotientLocalRing h hh
  let := normQuotientLocalRing (R := R) h hh
  let : IsLocalHom (Ideal.Quotient.mk (Ideal.span {h})) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨?_⟩
  intro a ha
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [NodeSingular.normLocusMap_mk] at ha
  have ht : IsUnit (algebraMap R T r) :=
    isUnit_of_map_unit (Ideal.Quotient.mk (Ideal.span {h})) _ ha
  have hr : IsUnit r := isUnit_of_map_unit (algebraMap R T) r ht
  exact hr.map (Ideal.Quotient.mk (Ideal.span {Algebra.norm R h}))

end Algebra

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
  [IsLocallyNoetherian S]

local notation "I" => NodeFittingOmegaGluing.idealSheaf f 1
variable (z : (NodeFittingOmegaGluing.idealSheaf f 1).subscheme)
local notation "x" => (I).subschemeι z
local notation "A" => S.completedLocalRing (f x)
local notation "C" => X.completedLocalRing x
local notation "D" => (I).subscheme.completedLocalRing z

/-- The actual native singular completion is local, from its original Noetherian scheme stalk. -/
theorem actualSingularCompletedLocalRing : IsLocalRing D := by
  let : IsNoetherianRing (X.presheaf.stalk x) := originalTarget_isNoetherianRing f x
  let : IsNoetherianRing ((I).subscheme.presheaf.stalk z) :=
    isNoetherianRing_of_surjective (X.presheaf.stalk x) ((I).subscheme.presheaf.stalk z)
      ((I).subschemeι.stalkMap z).hom ((I).subschemeι.stalkMap_surjective z)
  infer_instance

local instance : Algebra A C := completedAlgebra f x

variable (T : Type u) [CommRing T] [IsLocalRing T]
  [Algebra T (X.completedLocalRing ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))]
  [Algebra (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T]
  [IsScalarTower (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T
    (X.completedLocalRing ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))]
  [Algebra.FormallyUnramified
    (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T]
  [Module.Free (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T]
  [Module.Finite (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T]
  [IsLocalHom
    (algebraMap (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T)]
  (Q : NodeNonsplit.Quadratic T) (h : T)
  (e : X.completedLocalRing ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z) ≃ₐ[T]
    NodeSingular.Node Q h)

local instance : Algebra T D := singularCoefficientAlgebra f z T

include e in
/-- The original singular point internally gives native local structure on the SAME actual norm quotient. -/
theorem actualNormQuotientLocalRing : IsLocalRing (A ⧸ Ideal.span {Algebra.norm A h}) :=
  normQuotientLocalRing (R := A) h (actualParameter_mem_maximalIdeal f z T Q h e)

include e in
/-- The already constructed SAME actual finite norm factor is a native local homomorphism. -/
theorem actualNormFactor_isLocalHom :
    IsLocalHom (NodeFittingRelativeNormTrace.normLocusSingularMap f z T Q h e) := by
  let := parameterQuotientLocalRing h (actualParameter_mem_maximalIdeal f z T Q h e)
  let := actualNormQuotientLocalRing f z T Q h e
  let : IsLocalHom (NodeSingular.normLocusMap (R := A) h) :=
    normLocusMap_isLocalHom h (actualParameter_mem_maximalIdeal f z T Q h e)
  let : IsLocalHom (actualSingularCompletedEquiv f z T Q h e).symm.toRingHom :=
    CompletionLocalMap.instIsLocalHomRingEquivToRingHom
      (actualSingularCompletedEquiv f z T Q h e).symm.toRingEquiv
  change IsLocalHom ((actualSingularCompletedEquiv f z T Q h e).symm.toRingHom.comp
    (NodeSingular.normLocusMap (R := A) h))
  infer_instance

include e in
/-- The WHOLE native completed-singular maximal ideal has precisely the SAME original norm-quotient comap. -/
theorem actualNormFactor_maximalIdeal_comap :
    letI := actualNormQuotientLocalRing f z T Q h e
    letI := actualSingularCompletedLocalRing f z
    (maximalIdeal D).comap (NodeFittingRelativeNormTrace.normLocusSingularMap f z T Q h e) =
      maximalIdeal (A ⧸ Ideal.span {Algebra.norm A h}) := by
  let := actualNormQuotientLocalRing f z T Q h e
  let := actualSingularCompletedLocalRing f z
  let := actualNormFactor_isLocalHom f z T Q h e
  exact maximalIdeal_comap _

end Hironaka.Algebra.NodeFittingRelativeNormLocal
