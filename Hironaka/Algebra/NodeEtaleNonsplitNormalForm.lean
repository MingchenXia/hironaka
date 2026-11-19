import Hironaka.Algebra.NodeEtaleCompletedCoefficientAgreement
import Hironaka.Algebra.NodeEtaleQuadraticLift
import Hironaka.Algebra.NodeGeometricCompletionCoefficientReindex
import Hironaka.Algebra.NodeSingularQuotient

/-! # The SAME original completed total space, from its actual original residue quadratic model -/

noncomputable section

namespace Hironaka.Algebra.NodeEtaleNonsplitNormalForm

open IsLocalRing MvPowerSeries CompletionRegularityBasics CompletionLocalMap NodeGeometricCompletion
  NodeGeometricCompletionOriginalFiberSection NodeGeometricCompletionCoefficientReindex
  NodeEtaleCompletedClosedFiber NodeEtaleCompletedCoefficientAgreement NodeNonsplit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

attribute [local instance] CompletionFlatMap.completedAlgebra baseResidueAlgebra

local notation "F" => FiberRing A B
local notation "C" => Completion (FiberRing A B)
local notation "T" => CompletedCoefficientRing A B
local instance originalFiber_local : IsLocalRing F :=
  CompletionIdealQuotient.quotientLocalRing _ (closedFiberIdeal_le_maximalIdeal (algebraMap A B))
local instance : Algebra T (Completion B) := upperCompletedAlgebra A B
local instance : IsLocalHom (algebraMap T (Completion B)) := completedCoefficientMap_local A B
local instance : Algebra (ResidueField T) (NodeFlatPresentation.ClosedFiber T (Completion B)) :=
  NodeFlatPresentation.closedFiberAlgebra T (Completion B)

variable (Q : Quadratic (ResidueField B))

/-- The actual original quadratic is reindexed by canonical actual native residue maps only. -/
def residueQuadratic : Quadratic (ResidueField T) :=
  Q.map (upperOriginalResidueEquiv A B).symm.toRingHom

/-- The actual three coefficients are lifted INTERNALLY into the SAME actual upper coefficient ring. -/
def liftedQuadratic : Quadratic T :=
  NodeEtaleQuadraticLift.lift T (residueQuadratic A B Q)

/-- The ENTIRE native residue reduction is the SAME actual reindexed original quadratic. -/
theorem liftedQuadratic_reduction :
    (liftedQuadratic A B Q).map (residue T) = residueQuadratic A B Q :=
  NodeEtaleQuadraticLift.lift_reduction T _

/-- The genuine native upper closed-fibre model is DERIVED from the actual original point-field model. -/
def upperClosedFiberModel (e : letI := pointFieldAlgebra A B
    QuadraticNode Q ≃ₐ[ResidueField B] C) :
    QuadraticNode (residueQuadratic A B Q) ≃ₐ[ResidueField T]
      NodeFlatPresentation.ClosedFiber T (Completion B) := by
  letI := pointFieldAlgebra A B
  letI := upperResidueAlgebra A B
  refine
    { ((quadraticReindex (upperOriginalResidueEquiv A B) Q).trans e.toRingEquiv).trans
        (upperClosedFiberEquiv A B).symm.toRingEquiv with commutes' := ?_ }
  intro a
  apply (upperClosedFiberEquiv A B).injective
  change upperClosedFiberEquiv A B ((upperClosedFiberEquiv A B).symm
    (e (quadraticReindex (upperOriginalResidueEquiv A B) Q
      (algebraMap (ResidueField T) (QuadraticNode (residueQuadratic A B Q)) a)))) = _
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
  change e (quadraticReindex (upperOriginalResidueEquiv A B) Q
    (Ideal.Quotient.mk _ (MvPowerSeries.C a))) = upperResidueMap A B a
  rw [quadraticReindex_C]
  exact (e.commutes (upperOriginalResidueEquiv A B a)).trans
    (upperResidueMap_pointFieldSection A B a).symm

/-- The actual upper fibre has precisely the native residue quadratic of the internally lifted original coefficients. -/
def liftedClosedFiberModel (e : letI := pointFieldAlgebra A B
    QuadraticNode Q ≃ₐ[ResidueField B] C) :
    QuadraticNode ((liftedQuadratic A B Q).map (residue T)) ≃ₐ[ResidueField T]
      NodeFlatPresentation.ClosedFiber T (Completion B) := by
  rw [liftedQuadratic_reduction]
  exact upperClosedFiberModel A B Q e

variable [Module.Flat A B] [Algebra.EssFiniteType A B]

local instance : Module.Flat T (Completion B) := upperCompletedAlgebra_flat A B
local instance : IsScalarTower (Completion A) T (Completion B) :=
  upperCompletedAlgebra_isScalarTower A B

/-- The parameter is constructed by the SAME-ring flat-presentation and nonsplit complete Morse producers. -/
def normalFormParameter (e : letI := pointFieldAlgebra A B
    QuadraticNode Q ≃ₐ[ResidueField B] C) : T :=
  NodeNonsplit.normalFormParameter T (Completion B) (liftedQuadratic A B Q)
    (liftedClosedFiberModel A B Q e)

/-- The actual internally produced smoothing parameter vanishes in the SAME native upper residue field. -/
theorem normalFormParameter_mem (e : letI := pointFieldAlgebra A B
    QuadraticNode Q ≃ₐ[ResidueField B] C) : normalFormParameter A B Q e ∈ maximalIdeal T :=
  NodeNonsplit.normalFormParameter_mem T (Completion B) (liftedQuadratic A B Q)
    (liftedClosedFiberModel A B Q e)

/-- The genuine normal form has the SAME original completed total-space ring as its source. -/
def normalFormEquiv (e : letI := pointFieldAlgebra A B
    QuadraticNode Q ≃ₐ[ResidueField B] C) : Completion B ≃ₐ[T]
    NodeSingular.Node (liftedQuadratic A B Q) (normalFormParameter A B Q e) :=
  NodeNonsplit.normalFormEquiv T (Completion B) (liftedQuadratic A B Q)
    (liftedClosedFiberModel A B Q e)

/-- EVERY actual upper coefficient retains the SAME actual original coefficient map. -/
theorem normalFormEquiv_coefficient (e : letI := pointFieldAlgebra A B
    QuadraticNode Q ≃ₐ[ResidueField B] C) (t : T) :
    normalFormEquiv A B Q e (completedCoefficientMap A B t) =
      Ideal.Quotient.mk _ (MvPowerSeries.C t) :=
  (normalFormEquiv A B Q e).commutes t

/-- ALL original completed-base coefficients retain the SAME completed structural map. -/
theorem normalFormEquiv_completedBase (e : letI := pointFieldAlgebra A B
    QuadraticNode Q ≃ₐ[ResidueField B] C) (a : Completion A) :
    normalFormEquiv A B Q e (completionMap (algebraMap A B) a) =
      Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap (Completion A) T a)) := by
  have h := normalFormEquiv_coefficient A B Q e (algebraMap (Completion A) T a)
  rw [AlgHom.commutes] at h
  exact h

/-- EVERY original uncompleted-base representative retains precisely its original structural image. -/
theorem normalFormEquiv_originalBase (e : letI := pointFieldAlgebra A B
    QuadraticNode Q ≃ₐ[ResidueField B] C) (a : A) :
    normalFormEquiv A B Q e (algebraMap B (Completion B) (algebraMap A B a)) =
      Ideal.Quotient.mk _ (MvPowerSeries.C
        (algebraMap (Completion A) T (algebraMap A (Completion A) a))) := by
  rw [← completionMap_algebraMap (algebraMap A B) a]
  exact normalFormEquiv_completedBase A B Q e _

end Hironaka.Algebra.NodeEtaleNonsplitNormalForm
