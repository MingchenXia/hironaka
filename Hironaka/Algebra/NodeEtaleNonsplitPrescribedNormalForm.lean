import Hironaka.Algebra.NodeEtaleNonsplitNormalForm

/-! # The SAME completed total space preserves ANY actual prescribed lift of its residue quadratic -/

noncomputable section

namespace Hironaka.Algebra.NodeEtaleNonsplitPrescribedNormalForm

open IsLocalRing MvPowerSeries NodeNonsplit CompletionRegularityBasics CompletionLocalMap
  NodeGeometricCompletion NodeGeometricCompletionOriginalFiberSection
  NodeEtaleNonsplitNormalForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u

/-- The SAME prescribed coefficients have unit discriminant INTERNALLY, from their actual residue coefficients only. -/
theorem prescribedDiscriminant_unit (T : Type*) [CommRing T] [IsLocalRing T]
    (q : Quadratic (ResidueField T)) (a0 a1 a2 : T)
    (h0 : residue T a0 = q.a0) (h1 : residue T a1 = q.a1) (h2 : residue T a2 = q.a2) :
    IsUnit (a1 ^ 2 - 4 * a0 * a2) := by
  apply unit_discriminant_of_residue
  rw [h0, h1, h2]
  exact NodeEtaleQuadraticLift.discriminant_ne_zero T q

/-- The actual quadratic retains EXACTLY the three prescribed elements; only its actual inverse is obtained internally. -/
def prescribedQuadratic (T : Type*) [CommRing T] [IsLocalRing T]
    (q : Quadratic (ResidueField T)) (a0 a1 a2 : T)
    (h0 : residue T a0 = q.a0) (h1 : residue T a1 = q.a1) (h2 : residue T a2 = q.a2) :
    Quadratic T :=
  Quadratic.ofCoefficients a0 a1 a2 (prescribedDiscriminant_unit T q a0 a1 a2 h0 h1 h2)

/-- The ENTIRE native residue quadratic is the SAME original one, including its actual inverse discriminant. -/
theorem prescribedQuadratic_reduction (T : Type*) [CommRing T] [IsLocalRing T]
    (q : Quadratic (ResidueField T)) (a0 a1 a2 : T)
    (h0 : residue T a0 = q.a0) (h1 : residue T a1 = q.a1) (h2 : residue T a2 = q.a2) :
    (prescribedQuadratic T q a0 a1 a2 h0 h1 h2).map (residue T) = q := by
  apply Quadratic.ext
  · exact h0
  · exact h1
  · exact h2
  · apply mul_right_cancel₀ (NodeEtaleQuadraticLift.discriminant_ne_zero T q)
    have h := ((prescribedQuadratic T q a0 a1 a2 h0 h1 h2).map (residue T)).inverse_discriminant
    change residue T (prescribedQuadratic T q a0 a1 a2 h0 h1 h2).invDiscriminant *
      (residue T a1 ^ 2 - 4 * residue T a0 * residue T a2) = 1 at h
    rw [h0, h1, h2] at h
    exact h.trans q.inverse_discriminant.symm

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

variable (q : Quadratic (ResidueField B))

/-- The actual upper closed fibre is DERIVED for these EXACT prescribed coefficients, with no supplied total-space model. -/
def closedFiberModel (a0 a1 a2 : T)
    (h0 : residue T a0 = (residueQuadratic A B q).a0)
    (h1 : residue T a1 = (residueQuadratic A B q).a1)
    (h2 : residue T a2 = (residueQuadratic A B q).a2)
    (e : letI := pointFieldAlgebra A B; QuadraticNode q ≃ₐ[ResidueField B] C) :
    QuadraticNode ((prescribedQuadratic T (residueQuadratic A B q) a0 a1 a2 h0 h1 h2).map
      (residue T)) ≃ₐ[ResidueField T] NodeFlatPresentation.ClosedFiber T (Completion B) := by
  rw [prescribedQuadratic_reduction]
  exact upperClosedFiberModel A B q e

variable [Module.Flat A B] [Algebra.EssFiniteType A B]

local instance : Module.Flat T (Completion B) := upperCompletedAlgebra_flat A B
local instance : IsScalarTower (Completion A) T (Completion B) :=
  upperCompletedAlgebra_isScalarTower A B

/-- The smoothing parameter is produced for the SAME prescribed quadratic. -/
def normalFormParameter (a0 a1 a2 : T)
    (h0 : residue T a0 = (residueQuadratic A B q).a0)
    (h1 : residue T a1 = (residueQuadratic A B q).a1)
    (h2 : residue T a2 = (residueQuadratic A B q).a2)
    (e : letI := pointFieldAlgebra A B; QuadraticNode q ≃ₐ[ResidueField B] C) : T :=
  NodeNonsplit.normalFormParameter T (Completion B)
    (prescribedQuadratic T (residueQuadratic A B q) a0 a1 a2 h0 h1 h2)
    (closedFiberModel A B q a0 a1 a2 h0 h1 h2 e)

/-- The actual parameter belongs to the SAME native upper maximal ideal. -/
theorem normalFormParameter_mem (a0 a1 a2 : T)
    (h0 : residue T a0 = (residueQuadratic A B q).a0)
    (h1 : residue T a1 = (residueQuadratic A B q).a1)
    (h2 : residue T a2 = (residueQuadratic A B q).a2)
    (e : letI := pointFieldAlgebra A B; QuadraticNode q ≃ₐ[ResidueField B] C) :
    normalFormParameter A B q a0 a1 a2 h0 h1 h2 e ∈ maximalIdeal T :=
  NodeNonsplit.normalFormParameter_mem T (Completion B) _
    (closedFiberModel A B q a0 a1 a2 h0 h1 h2 e)

/-- The SAME original completed total space retains EXACTLY the prescribed quadratic coefficients. -/
def normalFormEquiv (a0 a1 a2 : T)
    (h0 : residue T a0 = (residueQuadratic A B q).a0)
    (h1 : residue T a1 = (residueQuadratic A B q).a1)
    (h2 : residue T a2 = (residueQuadratic A B q).a2)
    (e : letI := pointFieldAlgebra A B; QuadraticNode q ≃ₐ[ResidueField B] C) :
    Completion B ≃ₐ[T]
      NodeSingular.Node (prescribedQuadratic T (residueQuadratic A B q) a0 a1 a2 h0 h1 h2)
        (normalFormParameter A B q a0 a1 a2 h0 h1 h2 e) :=
  NodeNonsplit.normalFormEquiv T (Completion B) _
    (closedFiberModel A B q a0 a1 a2 h0 h1 h2 e)

/-- EVERY actual upper coefficient retains its SAME original Hensel image. -/
theorem normalFormEquiv_coefficient (a0 a1 a2 : T)
    (h0 : residue T a0 = (residueQuadratic A B q).a0)
    (h1 : residue T a1 = (residueQuadratic A B q).a1)
    (h2 : residue T a2 = (residueQuadratic A B q).a2)
    (e : letI := pointFieldAlgebra A B; QuadraticNode q ≃ₐ[ResidueField B] C) (t : T) :
    normalFormEquiv A B q a0 a1 a2 h0 h1 h2 e (completedCoefficientMap A B t) =
      Ideal.Quotient.mk _ (MvPowerSeries.C t) :=
  (normalFormEquiv A B q a0 a1 a2 h0 h1 h2 e).commutes t

/-- ALL original completed-base coefficients retain the SAME completed structural map. -/
theorem normalFormEquiv_completedBase (a0 a1 a2 : T)
    (h0 : residue T a0 = (residueQuadratic A B q).a0)
    (h1 : residue T a1 = (residueQuadratic A B q).a1)
    (h2 : residue T a2 = (residueQuadratic A B q).a2)
    (e : letI := pointFieldAlgebra A B; QuadraticNode q ≃ₐ[ResidueField B] C) (a : Completion A) :
    normalFormEquiv A B q a0 a1 a2 h0 h1 h2 e (completionMap (algebraMap A B) a) =
      Ideal.Quotient.mk _ (MvPowerSeries.C (algebraMap (Completion A) T a)) := by
  have h := normalFormEquiv_coefficient A B q a0 a1 a2 h0 h1 h2 e (algebraMap (Completion A) T a)
  rw [AlgHom.commutes] at h
  exact h

/-- EVERY original uncompleted-base representative retains its actual original structural image. -/
theorem normalFormEquiv_originalBase (a0 a1 a2 : T)
    (h0 : residue T a0 = (residueQuadratic A B q).a0)
    (h1 : residue T a1 = (residueQuadratic A B q).a1)
    (h2 : residue T a2 = (residueQuadratic A B q).a2)
    (e : letI := pointFieldAlgebra A B; QuadraticNode q ≃ₐ[ResidueField B] C) (a : A) :
    normalFormEquiv A B q a0 a1 a2 h0 h1 h2 e (algebraMap B (Completion B) (algebraMap A B a)) =
      Ideal.Quotient.mk _ (MvPowerSeries.C
        (algebraMap (Completion A) T (algebraMap A (Completion A) a))) := by
  rw [← completionMap_algebraMap (algebraMap A B) a]
  exact normalFormEquiv_completedBase A B q a0 a1 a2 h0 h1 h2 e _

/-- The literal source claim holds for ANY prescribed lift; its coefficients are not replaced by chosen lifts. -/
theorem exists_prescribed_normal_form (a0 a1 a2 : T)
    (h0 : residue T a0 = (residueQuadratic A B q).a0)
    (h1 : residue T a1 = (residueQuadratic A B q).a1)
    (h2 : residue T a2 = (residueQuadratic A B q).a2)
    (e : letI := pointFieldAlgebra A B; QuadraticNode q ≃ₐ[ResidueField B] C) :
    ∃ h : T, h ∈ maximalIdeal T ∧ Nonempty (Completion B ≃ₐ[T]
      (NodeFormalMorse.Series T ⧸ Ideal.span {
        MvPowerSeries.C a0 * X 0 ^ 2 + MvPowerSeries.C a1 * X 0 * X 1 +
          MvPowerSeries.C a2 * X 1 ^ 2 - MvPowerSeries.C h})) :=
  ⟨normalFormParameter A B q a0 a1 a2 h0 h1 h2 e,
    normalFormParameter_mem A B q a0 a1 a2 h0 h1 h2 e,
    ⟨normalFormEquiv A B q a0 a1 a2 h0 h1 h2 e⟩⟩

end Hironaka.Algebra.NodeEtaleNonsplitPrescribedNormalForm
