import Hironaka.Algebra.NodeFittingRelativeNormTrace

/-! # The actual original singular point forces the same smoothing parameter to vanish -/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Algebra.NodeFittingRelativeParameter

open NodeFittingRelativeClosedTrace Geometry.NodeCompletedLocalMap

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u

/-- The genuine nontrivial parameter quotient internally forces the original parameter to vanish. -/
theorem parameter_mem_maximalIdeal_of_equiv
    {T D : Type*} [CommRing T] [IsLocalRing T] [CommRing D] [Nontrivial D]
    (h : T) (e : D ≃+* T ⧸ Ideal.span {h}) : h ∈ maximalIdeal T := by
  let : Nontrivial (T ⧸ Ideal.span {h}) := e.injective.nontrivial
  exact le_maximalIdeal (Ideal.Quotient.nontrivial_iff.mp inferInstance)
    (Ideal.subset_span (Set.mem_singleton h))

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
  [IsLocallyNoetherian S]

local notation "I" => NodeFittingOmegaGluing.idealSheaf f 1
variable (z : (NodeFittingOmegaGluing.idealSheaf f 1).subscheme)
local notation "x" => (I).subschemeι z
local notation "A" => S.completedLocalRing (f x)
local notation "C" => X.completedLocalRing x
local notation "D" => (I).subscheme.completedLocalRing z

/-- Native nontriviality comes from the SAME actual singular stalk and its native completion. -/
theorem actualSingularCompleted_nontrivial : Nontrivial D := by
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
  (Q : NodeNonsplit.Quadratic T) (h : T)
  (e : X.completedLocalRing ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z) ≃ₐ[T]
    NodeSingular.Node Q h)

local instance : Algebra T D := singularCoefficientAlgebra f z T

include e in
/-- The SAME actual original singular-completion equivalence removes any parameter-vanishing premise. -/
theorem actualParameter_mem_maximalIdeal : h ∈ maximalIdeal T := by
  let : Nontrivial D := actualSingularCompleted_nontrivial f z
  exact parameter_mem_maximalIdeal_of_equiv h
    (actualSingularCompletedEquiv f z T Q h e).toRingEquiv

variable
  [Module.Free (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T]
  [Module.Finite (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T]
  [IsLocalHom
    (algebraMap (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T)]

include e in
/-- The actual norm vanishes at the SAME original completed-base point, with no supplied vanishing premise. -/
theorem actualNorm_mem_originalCompletedBase_maximalIdeal :
    Algebra.norm A h ∈ maximalIdeal A :=
  NodeFittingRelativeNormTrace.norm_mem_originalCompletedBase_maximalIdeal f z T h
    (actualParameter_mem_maximalIdeal f z T Q h e)

end Hironaka.Algebra.NodeFittingRelativeParameter
