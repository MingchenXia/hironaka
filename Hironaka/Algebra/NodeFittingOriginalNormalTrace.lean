import Hironaka.Geometry.NodeCompletedLocalOriginalNormalForm
import Hironaka.Algebra.NodeFittingRelativeNormTrace

/-! # Original source-produced normal forms compute the WHOLE actual singular completion and finite norm trace -/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Algebra.NodeFittingOriginalNormalTrace

open Geometry.NodeCompletedLocalMap Geometry.NodeCompletedLocalOriginalNodeJets
  Geometry.NodeCompletedLocalOriginalNormalForm NodeFittingRelativeClosedTrace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [Geometry.IsSemistableCurve f]
  [IsLocallyNoetherian S]

local notation "I" => NodeFittingOmegaGluing.idealSheaf f 1
variable (z : (NodeFittingOmegaGluing.idealSheaf f 1).subscheme)
local notation "x" => (I).subschemeι z
local notation "A" => S.presheaf.stalk (f x)
local notation "B" => X.presheaf.stalk x
local notation "Ah" => S.completedLocalRing (f x)
local notation "C" => X.completedLocalRing x
local notation "D" => (I).subscheme.completedLocalRing z

attribute [local instance] originalAlgebra
local instance originalLocalMap : IsLocalHom (algebraMap A B) :=
  inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
local instance originalNoetherian : IsNoetherianRing B := originalTarget_isNoetherianRing f x
local instance originalResidueFinite : FiniteDimensional (ResidueField A) (ResidueField B) :=
  (originalResidue_finite_separable f z).1
local instance originalResidueSeparable : Algebra.IsSeparable (ResidueField A) (ResidueField B) :=
  (originalResidue_finite_separable f z).2

local instance : Algebra Ah C := completedAlgebra f x
local instance completedLocalMap : IsLocalHom (algebraMap Ah C) := completedMap_isLocalHom f x
local instance completedResidueFinite :
    FiniteDimensional (ResidueField Ah) (ResidueField C) :=
  NodeGeometricCompletion.completedResidue_finite A B
local instance completedResidueSeparable : Algebra.IsSeparable (ResidueField Ah) (ResidueField C) :=
  NodeGeometricCompletion.completedResidue_separable A B

local notation "T" => CompletedStalkCoefficientRing f x
local instance : Algebra T C := upperCompletedStalkAlgebra f x
local instance actualScalarTower : IsScalarTower Ah T C :=
  IsScalarTower.of_algebraMap_eq' (completedStalkCoefficientMap_triangle f x).symm

/-- The native singular completed stalk receives ONLY the actual forward upper coefficient map and completed inclusion. -/
@[instance_reducible]
def originalSingularCoefficientAlgebra : Algebra T D := singularCoefficientAlgebra f z T

local instance : Algebra T D := originalSingularCoefficientAlgebra f z

/-- Original semistability INTERNALLY produces the SAME Q,h,e and WHOLE actual singular-completion trace. -/
theorem exists_original_normal_trace :
    ∃ (Q : NodeNonsplit.Quadratic T) (h : T) (e : C ≃ₐ[T] NodeSingular.Node Q h),
      h ∈ maximalIdeal T ∧
      (∀ t : T, e (completedStalkCoefficientMap f x t) =
        Ideal.Quotient.mk _ (MvPowerSeries.C t)) ∧
      (∀ a : Ah, e (completedMap f x a) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap Ah T a))) ∧
      Nonempty (D ≃ₐ[T] T ⧸ Ideal.span {h}) ∧
      (∀ c : C, actualSingularCompletedEquiv f z T Q h e
        (completedMap (I).subschemeι z c) = NodeSingular.nodeEvaluation Q h (e c)) ∧
      (∀ a : Ah, actualSingularCompletedEquiv f z T Q h e
        (completedMap (NodeFittingOmegaGluing.fittingMorphism f 1) z a) =
          Ideal.Quotient.mk (Ideal.span {h}) (algebraMap Ah T a)) := by
  let : IsScalarTower Ah T C := actualScalarTower f z
  obtain ⟨Q, h, hh, ⟨e⟩⟩ := exists_normalForm f x (singular_mem_support f z)
  refine ⟨Q, h, e, hh, ?_, ?_, ⟨actualSingularCompletedEquiv f z T Q h e⟩, ?_, ?_⟩
  · intro t
    exact e.commutes t
  · intro a
    have hc : completedMap f x a = algebraMap T C (algebraMap Ah T a) :=
      IsScalarTower.algebraMap_apply Ah T C a
    rw [hc]
    exact e.commutes _
  · exact actualSingularCompletedEquiv_completed f z T Q h e
  · exact actualSingularCompletedEquiv_completedBase f z T Q h e

/-- The SAME source-produced Q,h,e gives the actual finite norm factor and every native completed structural coefficient. -/
theorem exists_original_norm_trace :
    ∃ (Q : NodeNonsplit.Quadratic T) (h : T) (e : C ≃ₐ[T] NodeSingular.Node Q h),
      h ∈ maximalIdeal T ∧
      (∀ t : T, e (completedStalkCoefficientMap f x t) =
        Ideal.Quotient.mk _ (MvPowerSeries.C t)) ∧
      (∀ a : Ah, e (completedMap f x a) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap Ah T a))) ∧
      Nonempty (D ≃ₐ[T] T ⧸ Ideal.span {h}) ∧
      (∀ c : C, actualSingularCompletedEquiv f z T Q h e
        (completedMap (I).subschemeι z c) = NodeSingular.nodeEvaluation Q h (e c)) ∧
      (∀ a : Ah, actualSingularCompletedEquiv f z T Q h e
        (completedMap (NodeFittingOmegaGluing.fittingMorphism f 1) z a) =
          Ideal.Quotient.mk (Ideal.span {h}) (algebraMap Ah T a)) ∧
      (NodeFittingRelativeNormTrace.normLocusSingularMap f z T Q h e).Finite ∧
      (∀ a : Ah, NodeFittingRelativeNormTrace.normLocusSingularMap f z T Q h e
        (Ideal.Quotient.mk (Ideal.span {Algebra.norm Ah h}) a) =
          completedMap (NodeFittingOmegaGluing.fittingMorphism f 1) z a) ∧
      Algebra.norm Ah h ∈ maximalIdeal Ah := by
  obtain ⟨Q, h, e, hh, hT, hA, hD, hC, hbase⟩ := exists_original_normal_trace f z
  refine ⟨Q, h, e, hh, hT, hA, hD, hC, hbase, ?_, ?_, ?_⟩
  · exact NodeFittingRelativeNormTrace.normLocusSingularMap_finite f z T Q h e
  · exact NodeFittingRelativeNormTrace.normLocusSingularMap_mk f z T Q h e
  · exact NodeFittingRelativeNormTrace.norm_mem_originalCompletedBase_maximalIdeal f z T h hh

end Hironaka.Algebra.NodeFittingOriginalNormalTrace
