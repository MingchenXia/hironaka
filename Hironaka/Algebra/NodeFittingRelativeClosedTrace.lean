import Hironaka.Algebra.NodeFittingClosedCompletion
import Hironaka.Algebra.NodeFittingRelativeSchemeTrace

/-! # The ACTUAL original Sing completed stalk with its WHOLE original completed-base map

The coefficient action uses only the actual forward coefficient lift and actual
completed closed inclusion. No inverse-defined original action or ideal certificate.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Algebra.NodeFittingRelativeClosedTrace

open NodeFittingIdealSheaf Geometry.NodeCompletedLocalMap

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
local notation "C" => X.completedLocalRing x
local notation "D" => (I).subscheme.completedLocalRing z
local notation "J" => stalkIdeal I x

local instance : Algebra (S.completedLocalRing (f x)) C := completedAlgebra f x

variable (T : Type u) [CommRing T]
  [Algebra T (X.completedLocalRing ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))]

/-- The SAME actual T coefficient lift followed by the ACTUAL completed closed inclusion. -/
@[instance_reducible]
def singularCoefficientAlgebra : Algebra T D :=
  ((completedMap (I).subschemeι z).comp (algebraMap T C)).toAlgebra

local instance : Algebra T D := singularCoefficientAlgebra f z T

/-- The entire original closed completed quotient retains the actual forward T coefficient action. -/
def nativeClosedQuotientEquiv :
    (C ⧸ (J).map (X.toCompletedLocalRing x)) ≃ₐ[T] D := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine
    { toRingEquiv := NodeFittingClosedCompletion.closedCompletionQuotientRingEquiv I z
      commutes' := ?_ }
  intro t
  exact NodeFittingClosedCompletion.closedCompletionQuotientAlgEquiv_mk I z (algebraMap T C t)

/-- EVERY completed original ambient representative follows the ENTIRE actual completed inclusion. -/
theorem nativeClosedQuotientEquiv_mk (c : X.completedLocalRing ((I).subschemeι z)) :
    nativeClosedQuotientEquiv f z T
      (Ideal.Quotient.mk ((J).map (X.toCompletedLocalRing x)) c) =
        completedMap (I).subschemeι z c := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact NodeFittingClosedCompletion.closedCompletionQuotientAlgEquiv_mk I z c

variable [IsLocalRing T]
  [Algebra (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T]
  [IsScalarTower (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T
    (X.completedLocalRing ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))]
  [Algebra.FormallyUnramified
    (S.completedLocalRing (f ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z))) T]

variable (Q : NodeNonsplit.Quadratic T) (h : T)
  (e : X.completedLocalRing ((NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z) ≃ₐ[T]
    NodeSingular.Node Q h)

/-- The ACTUAL native singular completed stalk is the SAME original parameter-zero T-algebra. -/
def actualSingularCompletedEquiv : D ≃ₐ[T] T ⧸ Ideal.span {h} :=
  (nativeClosedQuotientEquiv f z T).symm.trans
    (NodeFittingRelativeSchemeTrace.globalSingularQuotientEquiv f x T Q h e)

/-- EVERY actual completed ambient element follows its SAME completed inclusion, SAME e and original parameter evaluation. -/
theorem actualSingularCompletedEquiv_completed (c : X.completedLocalRing ((I).subschemeι z)) :
    actualSingularCompletedEquiv f z T Q h e (completedMap (I).subschemeι z c) =
      NodeSingular.nodeEvaluation Q h (e c) := by
  rw [← nativeClosedQuotientEquiv_mk f z T c, actualSingularCompletedEquiv,
    AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  exact NodeFittingRelativeSchemeTrace.globalSingularQuotientEquiv_mk f x T Q h e c

/-- EVERY native original ambient germ retains the original actual stalk and completion maps. -/
theorem actualSingularCompletedEquiv_original (r : X.presheaf.stalk ((I).subschemeι z)) :
    actualSingularCompletedEquiv f z T Q h e
      ((I).subscheme.toCompletedLocalRing z ((I).subschemeι.stalkMap z r)) =
        NodeSingular.nodeEvaluation Q h (e (X.toCompletedLocalRing x r)) := by
  rw [← completedMap_coefficient (I).subschemeι z r]
  exact actualSingularCompletedEquiv_completed f z T Q h e (X.toCompletedLocalRing x r)

/-- EVERY actual original T coefficient retains its native parameter-zero residue class. -/
theorem actualSingularCompletedEquiv_coefficient (t : T) :
    actualSingularCompletedEquiv f z T Q h e (algebraMap T D t) =
      Ideal.Quotient.mk (Ideal.span {h}) t :=
  (actualSingularCompletedEquiv f z T Q h e).commutes t

omit [IsLocallyNoetherian S] in
/-- The ENTIRE native original completed-base map is the SAME actual composite completed map. -/
theorem completedStructuralMap_comp (a : S.completedLocalRing (f ((I).subschemeι z))) :
    completedMap (NodeFittingOmegaGluing.fittingMorphism f 1) z a =
      completedMap (I).subschemeι z (completedMap f x a) := by
  have hMap : ((I).subschemeι ≫ f).stalkMap z =
      f.stalkMap x ≫ (I).subschemeι.stalkMap z := by
    rw [Scheme.Hom.stalkMap_comp]
  have hRing : (((I).subschemeι ≫ f).stalkMap z).hom =
      ((I).subschemeι.stalkMap z).hom.comp (f.stalkMap x).hom :=
    congrArg CommRingCat.Hom.hom hMap
  have hFull := (CompletionLocalMap.completionMap_congr hRing).trans
    (CompletionLocalMap.completionMap_comp (f.stalkMap x).hom ((I).subschemeι.stalkMap z).hom)
  exact DFunLike.congr_fun hFull a

/-- EVERY completed original base coefficient follows the ACTUAL structural map and SAME parameter-zero T map. -/
theorem actualSingularCompletedEquiv_completedBase
    (a : S.completedLocalRing (f ((I).subschemeι z))) :
    actualSingularCompletedEquiv f z T Q h e
      (completedMap (NodeFittingOmegaGluing.fittingMorphism f 1) z a) =
        Ideal.Quotient.mk (Ideal.span {h})
          (algebraMap (S.completedLocalRing (f ((I).subschemeι z))) T a) := by
  rw [completedStructuralMap_comp]
  have hcoeff : completedMap f x a =
      algebraMap T C (algebraMap (S.completedLocalRing (f x)) T a) :=
    IsScalarTower.algebraMap_apply (S.completedLocalRing (f x)) T C a
  rw [hcoeff]
  exact actualSingularCompletedEquiv_coefficient f z T Q h e _

end Hironaka.Algebra.NodeFittingRelativeClosedTrace
