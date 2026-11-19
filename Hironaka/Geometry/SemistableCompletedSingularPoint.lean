import Hironaka.Algebra.NodeFittingOriginalNormalTrace
import Hironaka.Algebra.NodeFittingRelativeNormLocal

/-!
# The nonsplit completed singular point of the original semistable family

The same source-produced normal form computes the whole original Fitting
ideal, the actual singular completed stalk, and its finite local norm factor.
The split refinement of source 2.23 remains a separate assertion.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Hironaka.Geometry.SemistableCompletedSingularPoint

open NodeCompletedLocalMap Algebra.NodeFittingRelativeClosedTrace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSemistableCurve f]
  [IsLocallyNoetherian S]

local notation "I" => Algebra.NodeFittingOmegaGluing.idealSheaf f 1
variable (z : (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subscheme)
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
  (NodeCompletedLocalOriginalNodeJets.originalResidue_finite_separable f z).1
local instance originalResidueSeparable : Algebra.IsSeparable (ResidueField A) (ResidueField B) :=
  (NodeCompletedLocalOriginalNodeJets.originalResidue_finite_separable f z).2

local instance : Algebra Ah C := completedAlgebra f x
local instance completedLocalMap : IsLocalHom (algebraMap Ah C) := completedMap_isLocalHom f x
local instance completedResidueFinite : FiniteDimensional (ResidueField Ah) (ResidueField C) :=
  Algebra.NodeGeometricCompletion.completedResidue_finite A B
local instance completedResidueSeparable : Algebra.IsSeparable (ResidueField Ah) (ResidueField C) :=
  Algebra.NodeGeometricCompletion.completedResidue_separable A B

local notation "T" => CompletedStalkCoefficientRing f x
local instance : Algebra T C := upperCompletedStalkAlgebra f x
local instance actualScalarTower : IsScalarTower Ah T C :=
  IsScalarTower.of_algebraMap_eq' (completedStalkCoefficientMap_triangle f x).symm
local instance : Algebra T D :=
  Algebra.NodeFittingOriginalNormalTrace.originalSingularCoefficientAlgebra f z

/-- The SAME original singular point produces its normal form, whole original
Fitting ideal, actual singular completion and finite LOCAL norm factor. -/
theorem exists_nonsplit_completed_local_description :
    ∃ (Q : Algebra.NodeNonsplit.Quadratic T) (h : T)
      (e : C ≃ₐ[T] Algebra.NodeSingular.Node Q h),
      h ∈ maximalIdeal T ∧
      (∀ t : T, e (completedStalkCoefficientMap f x t) =
        Ideal.Quotient.mk _ (MvPowerSeries.C t)) ∧
      (∀ a : Ah, e (completedMap f x a) =
        Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap Ah T a))) ∧
      (∀ a : A, e (X.toCompletedLocalRing x (f.stalkMap x a)) =
        Ideal.Quotient.mk _ (MvPowerSeries.C
          (algebraMap Ah T (S.toCompletedLocalRing (f x) a)))) ∧
      (Algebra.NodeFittingIdealSheaf.stalkIdeal I x).map
          (e.toRingHom.comp (X.toCompletedLocalRing x)) =
        Algebra.NodeSingular.coordinateIdeal Q h ∧
      Nonempty (D ≃ₐ[T] T ⧸ Ideal.span {h}) ∧
      (∀ c : C, actualSingularCompletedEquiv f z T Q h e
        (completedMap (I).subschemeι z c) = Algebra.NodeSingular.nodeEvaluation Q h (e c)) ∧
      (∀ b : B, actualSingularCompletedEquiv f z T Q h e
        ((I).subscheme.toCompletedLocalRing z ((I).subschemeι.stalkMap z b)) =
          Algebra.NodeSingular.nodeEvaluation Q h (e (X.toCompletedLocalRing x b))) ∧
      (∀ a : Ah, actualSingularCompletedEquiv f z T Q h e
        (completedMap (Algebra.NodeFittingOmegaGluing.fittingMorphism f 1) z a) =
          Ideal.Quotient.mk (Ideal.span {h}) (algebraMap Ah T a)) ∧
      (Algebra.NodeFittingRelativeNormTrace.normLocusSingularMap f z T Q h e).Finite ∧
      IsLocalHom (Algebra.NodeFittingRelativeNormTrace.normLocusSingularMap f z T Q h e) ∧
      (∀ a : Ah, Algebra.NodeFittingRelativeNormTrace.normLocusSingularMap f z T Q h e
        (Ideal.Quotient.mk (Ideal.span {Algebra.norm Ah h}) a) =
          completedMap (Algebra.NodeFittingOmegaGluing.fittingMorphism f 1) z a) ∧
      Algebra.norm Ah h ∈ maximalIdeal Ah := by
  let : IsScalarTower Ah T C := actualScalarTower f z
  obtain ⟨Q, h, e, hh, hT, hA, hD, hC, hbase, hfinite, hnorm, hmax⟩ :=
    Algebra.NodeFittingOriginalNormalTrace.exists_original_norm_trace f z
  refine ⟨Q, h, e, hh, hT, hA, ?_, ?_, hD, hC, ?_, hbase, hfinite, ?_, hnorm, hmax⟩
  · intro a
    have ha := hA (S.toCompletedLocalRing (f x) a)
    rw [completedMap_coefficient] at ha
    exact ha
  · exact Algebra.NodeFittingRelativeSchemeTrace.globalStalkIdeal_eq_coordinateIdeal f x T Q h e
  · exact actualSingularCompletedEquiv_original f z T Q h e
  · exact Algebra.NodeFittingRelativeNormLocal.actualNormFactor_isLocalHom f z T Q h e

end Hironaka.Geometry.SemistableCompletedSingularPoint
