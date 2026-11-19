import Hironaka.Algebra.NodeGeometricCompletionDiagonalEtale
import Hironaka.Algebra.NodeGeometricCompletionJets
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! Genuine coefficients in the SAME original completion, from its ACTUAL diagonal neighbourhood. -/

noncomputable section

open IsLocalRing

namespace Hironaka.Algebra.NodeGeometricCompletionDiagonalCoefficients

open CompletionRegularityBasics

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable (K R : Type u) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
  [IsNoetherianRing R] [FiniteDimensional K (ResidueField R)]
  [Algebra.IsSeparable K (ResidueField R)]

local notation "κ" => ResidueField R
local notation "T" => NodeGeometricCompletionDiagonalPoint.DiagonalLocal K R
local notation "C" => Completion R
local notation "C'" => AdicCompletion (maximalIdeal T) T

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  NodeGeometricCompletionDiagonalPoint.diagonalPoint_isMaximal
  NodeGeometricCompletionDiagonalPoint.pointFieldAlgebra
  NodeGeometricCompletionDiagonalPoint.originalAlgebra
  NodeGeometricCompletionDiagonalPoint.originalMap_isLocalHom
  NodeGeometricCompletionDiagonalEtale.original_essFiniteType

omit [Algebra.IsSeparable K κ] in
/-- Noetherianity of the SAME original diagonal local ring is internally derived. -/
theorem diagonal_isNoetherianRing : IsNoetherianRing T :=
  Algebra.EssFiniteType.isNoetherianRing R T

attribute [local instance] diagonal_isNoetherianRing

/-- The original completed ring receives its ACTUAL original residue coefficients through the SAME diagonal map. -/
def pointCoefficientMap : κ →+* C :=
  (NodeGeometricCompletionDiagonalEtale.completedOriginalEquiv K R).symm.toRingHom.comp
    (algebraMap κ C')

/-- The actual coefficient action on the SAME original completed ring. -/
@[instance_reducible]
def pointCoefficientAlgebra : Algebra κ C := (pointCoefficientMap K R).toAlgebra

omit [IsNoetherianRing R] in
/-- The ENTIRE original base field action is preserved by the actual diagonal coefficient section. -/
theorem pointCoefficient_base_triangle :
    (pointCoefficientMap K R).comp (algebraMap K κ) = algebraMap K C := by
  apply RingHom.ext
  intro k
  change (NodeGeometricCompletionDiagonalEtale.completedOriginalEquiv K R).symm
    (algebraMap κ C' (algebraMap K κ k)) = algebraMap K C k
  rw [← IsScalarTower.algebraMap_apply K κ C']
  rw [IsScalarTower.algebraMap_apply K R C' k]
  rw [AlgEquiv.commutes]
  rfl

omit [IsNoetherianRing R] in
/-- The actual original-base and new point-field coefficients form a genuine native scalar tower. -/
theorem pointCoefficient_scalarTower :
    letI := pointCoefficientAlgebra K R
    IsScalarTower K κ C := by
  let := pointCoefficientAlgebra K R
  exact IsScalarTower.of_algebraMap_eq' (pointCoefficient_base_triangle K R).symm

/-- The SAME original completed map is an equivalence over the WHOLE actual original point field. -/
def completedPointEquiv :
    letI := pointCoefficientAlgebra K R
    C ≃ₐ[κ] C' := by
  letI := pointCoefficientAlgebra K R
  refine AlgEquiv.ofRingEquiv
    (f := (NodeGeometricCompletionDiagonalEtale.completedOriginalEquiv K R).toRingEquiv) ?_
  intro a
  change NodeGeometricCompletionDiagonalEtale.completedOriginalEquiv K R
    ((NodeGeometricCompletionDiagonalEtale.completedOriginalEquiv K R).symm (algebraMap κ C' a)) = _
  exact (NodeGeometricCompletionDiagonalEtale.completedOriginalEquiv K R).apply_symm_apply _

omit [IsNoetherianRing R] in
/-- Its ENTIRE forward map is still the SAME actual canonical original completed local map. -/
theorem completedPointEquiv_toRingHom :
    letI := pointCoefficientAlgebra K R
    (completedPointEquiv K R).toRingHom =
      CompletionLocalMap.completionMap (algebraMap R T) :=
  NodeGeometricCompletionDiagonalEtale.completedOriginalEquiv_toRingHom K R

/-- The entire residue identity is exactly the ORIGINAL canonical completion residue isomorphism. -/
theorem residue_pointCoefficientMap (a : κ) :
    residue C (pointCoefficientMap K R a) = residueFieldEquiv R a := by
  let e := NodeGeometricCompletionDiagonalEtale.completedOriginalEquiv K R
  let : IsLocalHom e.toRingHom :=
    CompletionLocalMap.instIsLocalHomRingEquivToRingHom e.toRingEquiv
  apply (ResidueField.map e.toRingHom).injective
  rw [ResidueField.map_residue]
  change residue C' (e (e.symm (algebraMap κ C' a))) = _
  rw [AlgEquiv.apply_symm_apply]
  obtain ⟨r, rfl⟩ := residue_surjective a
  rw [residueFieldEquiv_apply, ResidueField.map_residue, ResidueField.map_residue]
  change residue C' (algebraMap κ C' (residue R r)) = residue C' (e (algebraMap R C r))
  rw [e.commutes r]
  have h := congrArg (ResidueField.map (algebraMap T C'))
    (NodeGeometricCompletionDiagonalPoint.externalCoefficient_residue K R (residue R r))
  rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue] at h
  rw [IsScalarTower.algebraMap_apply κ T C', IsScalarTower.algebraMap_apply R T C']
  exact h.symm

/-- The actual original coefficient-residue map is internally bijective, never a supplied certificate. -/
theorem pointCoefficient_residue_bijective :
    Function.Bijective ((residue C).comp (pointCoefficientMap K R)) := by
  have h : (residue C).comp (pointCoefficientMap K R) = (residueFieldEquiv R).toRingHom :=
    RingHom.ext (residue_pointCoefficientMap K R)
  rw [h]
  exact (residueFieldEquiv R).bijective

end Hironaka.Algebra.NodeGeometricCompletionDiagonalCoefficients
