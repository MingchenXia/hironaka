import Hironaka.Algebra.NodeGeometricCompletionResidue
import Hironaka.Algebra.CompletionLocalMapClosedFiber

/-!
# Actual etale coefficients for the literal completed map of an original local algebra

The field extension hypothesis concerns the original point residue map only.
Its completed counterpart, the coefficient ring, local coefficient map and
upper flatness are all constructed internally.
-/

noncomputable section

open IsLocalRing

namespace Hironaka.Algebra.NodeGeometricCompletion

open CompletionRegularityBasics CompletionLocalMap CompletionFlatMap

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (A B : Type u) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
  [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [FiniteDimensional (ResidueField A) (ResidueField B)]
  [Algebra.IsSeparable (ResidueField A) (ResidueField B)]

attribute [local instance] CompletionFlatMap.completedAlgebra

local instance completedBaseMap_local :
    IsLocalHom (algebraMap (Completion A) (Completion B)) :=
  isLocalHom_completionMap (algebraMap A B)

local instance completedCoefficientResidue_finite :
    FiniteDimensional (ResidueField (Completion A)) (ResidueField (Completion B)) :=
  completedResidue_finite A B

local instance completedCoefficientResidue_separable :
    Algebra.IsSeparable (ResidueField (Completion A)) (ResidueField (Completion B)) :=
  completedResidue_separable A B

/-- The actual finite-free local etale coefficient ring lifted from the ORIGINAL residue extension. -/
abbrev CompletedCoefficientRing :=
  NodeEtaleCoefficients.CoefficientRing (Completion A) (Completion B)

/-- The actual upper coefficient map into the literal completed original target. -/
def completedCoefficientMap : CompletedCoefficientRing A B →ₐ[Completion A] Completion B :=
  NodeEtaleCoefficients.coefficientMap (Completion A) (Completion B)

/-- The upper action is precisely the constructed Hensel coefficient map. -/
@[instance_reducible]
def upperCompletedAlgebra : Algebra (CompletedCoefficientRing A B) (Completion B) :=
  (completedCoefficientMap A B).toAlgebra

/-- The constructed finite etale coefficient ring has all required original structural properties. -/
theorem completedCoefficientRing_properties :
    Module.Finite (Completion A) (CompletedCoefficientRing A B) ∧
      Module.Free (Completion A) (CompletedCoefficientRing A B) ∧
      Algebra.Etale (Completion A) (CompletedCoefficientRing A B) ∧
      IsLocalRing (CompletedCoefficientRing A B) ∧
      IsNoetherianRing (CompletedCoefficientRing A B) ∧
      IsAdicComplete (maximalIdeal (CompletedCoefficientRing A B)) (CompletedCoefficientRing A B) :=
  NodeEtaleCoefficients.coefficientRing_properties (Completion A) (Completion B)

/-- The actual upper local homomorphism is constructed, not assumed. -/
theorem completedCoefficientMap_local : IsLocalHom (completedCoefficientMap A B).toRingHom :=
  inferInstanceAs (IsLocalHom
    (NodeEtaleCoefficients.coefficientMap (Completion A) (Completion B)).toRingHom)

/-- The actual complete coefficient triangle retains the ENTIRE original completed map. -/
theorem completedCoefficientMap_triangle :
    (completedCoefficientMap A B).toRingHom.comp
      (algebraMap (Completion A) (CompletedCoefficientRing A B)) =
        completionMap (algebraMap A B) :=
  NodeEtaleCoefficients.coefficientMap_triangle (Completion A) (Completion B)

/-- In particular, every original uncompleted coefficient keeps its original structural image. -/
theorem completedCoefficientMap_original (a : A) :
    completedCoefficientMap A B
      (algebraMap (Completion A) (CompletedCoefficientRing A B)
        (algebraMap A (Completion A) a)) = algebraMap B (Completion B) (algebraMap A B a) := by
  rw [AlgHom.commutes]
  exact completionMap_algebraMap (algebraMap A B) a

/-- The actual upper native residue map is an isomorphism. -/
def completedCoefficientResidueEquiv :
    ResidueField (CompletedCoefficientRing A B) ≃+* ResidueField (Completion B) :=
  NodeEtaleCoefficients.coefficientResidueEquiv (Completion A) (Completion B)

/-- The actual upper maximal ideal gives exactly the original completed closed-fibre ideal. -/
theorem completedCoefficient_maximalIdeal_image :
    (maximalIdeal (CompletedCoefficientRing A B)).map (completedCoefficientMap A B).toRingHom =
      (maximalIdeal (Completion A)).map (completionMap (algebraMap A B)) :=
  NodeEtaleFlat.coefficientTarget_maximalIdeal_image (Completion A) (Completion B)

/-- Actual upper flatness follows from ORIGINAL uncompleted flatness and essential finite type. -/
theorem upperCompletedAlgebra_flat [Module.Flat A B] [Algebra.EssFiniteType A B] :
    letI := upperCompletedAlgebra A B
    Module.Flat (CompletedCoefficientRing A B) (Completion B) := by
  let : Module.Flat (Completion A) (Completion B) := flat_completedAlgebra A B
  exact NodeEtaleFlat.coefficientTarget_flat (Completion A) (Completion B)

/-- The upper algebra is local for precisely the constructed upper map. -/
theorem upperCompletedAlgebra_isLocalHom :
    letI := upperCompletedAlgebra A B
    IsLocalHom (algebraMap (CompletedCoefficientRing A B) (Completion B)) :=
  completedCoefficientMap_local A B

/-- The scalar tower uses the entire original completed coefficient map. -/
theorem upperCompletedAlgebra_isScalarTower :
    letI := upperCompletedAlgebra A B
    IsScalarTower (Completion A) (CompletedCoefficientRing A B) (Completion B) :=
  NodeEtaleCoefficients.coefficientTargetScalarTower (Completion A) (Completion B)

/-- After the actual etale coefficient extension, the closed fibre is STILL the
literal completion of the original uncompleted closed-fibre quotient. -/
def upperClosedFiberCompletionEquiv :
    letI := CompletionIdealQuotient.quotientLocalRing
      (closedFiberIdeal (algebraMap A B)) (closedFiberIdeal_le_maximalIdeal (algebraMap A B))
    (Completion B ⧸ (maximalIdeal (CompletedCoefficientRing A B)).map
      (completedCoefficientMap A B).toRingHom) ≃+*
        Completion (B ⧸ closedFiberIdeal (algebraMap A B)) := by
  let := CompletionIdealQuotient.quotientLocalRing
    (closedFiberIdeal (algebraMap A B)) (closedFiberIdeal_le_maximalIdeal (algebraMap A B))
  exact (Ideal.quotEquivOfEq (completedCoefficient_maximalIdeal_image A B)).trans
    (closedFiberEquiv (algebraMap A B))

/-- The full original target-germ formula survives both completion and etale coefficients. -/
theorem upperClosedFiberCompletionEquiv_coefficient (b : B) :
    letI := CompletionIdealQuotient.quotientLocalRing
      (closedFiberIdeal (algebraMap A B)) (closedFiberIdeal_le_maximalIdeal (algebraMap A B))
    upperClosedFiberCompletionEquiv A B (Ideal.Quotient.mk _ (algebraMap B (Completion B) b)) =
      algebraMap (B ⧸ closedFiberIdeal (algebraMap A B))
        (Completion (B ⧸ closedFiberIdeal (algebraMap A B)))
          (Ideal.Quotient.mk (closedFiberIdeal (algebraMap A B)) b) :=
  closedFiberEquiv_coefficient (algebraMap A B) b

end Hironaka.Algebra.NodeGeometricCompletion
