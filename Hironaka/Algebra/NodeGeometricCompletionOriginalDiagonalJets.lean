import Hironaka.Algebra.NodeGeometricCompletionDiagonalCoefficients

/-! EVERY original completion jet, with its ACTUAL original point-field coefficients. -/

noncomputable section

open IsLocalRing

namespace Hironaka.Algebra.NodeGeometricCompletionOriginalDiagonalJets

open CompletionRegularityBasics NodeGeometricCompletionDiagonalCoefficients

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
  diagonal_isNoetherianRing

/-- EVERY actual completed original jet is transported by the SAME original completed local equivalence. -/
def completedJetEquiv (n : ℕ) :
    letI := pointCoefficientAlgebra K R
    (C ⧸ maximalIdeal C ^ n) ≃ₐ[κ] (C' ⧸ maximalIdeal C' ^ n) := by
  letI := pointCoefficientAlgebra K R
  exact Ideal.quotientEquivAlg (maximalIdeal C ^ n) (maximalIdeal C' ^ n) (completedPointEquiv K R) (by
    symm
    change (maximalIdeal C ^ n).map (completedPointEquiv K R).toRingEquiv.toRingHom = _
    rw [Ideal.map_pow]
    exact congrArg (fun I : Ideal C' => I ^ n)
      (map_ringEquiv_maximalIdeal (completedPointEquiv K R).toRingEquiv))

/-- EVERY original completed representative retains its SAME actual completed-map image. -/
theorem completedJetEquiv_mk (n : ℕ) (c : C) :
    letI := pointCoefficientAlgebra K R
    completedJetEquiv K R n (Ideal.Quotient.mk (maximalIdeal C ^ n) c) =
      Ideal.Quotient.mk (maximalIdeal C' ^ n) (completedPointEquiv K R c) := rfl

/-- The SAME original completion jet is the literal original diagonal local jet, over the entire κ. -/
def originalJetEquiv (n : ℕ) :
    letI := pointCoefficientAlgebra K R
    (C ⧸ maximalIdeal C ^ n) ≃ₐ[κ] (T ⧸ maximalIdeal T ^ n) := by
  letI := pointCoefficientAlgebra K R
  exact (completedJetEquiv K R n).trans ((NodeGeometricCompletionJets.jetEquiv T n).restrictScalars κ).symm

/-- Every ORIGINAL local germ retains precisely its SAME actual diagonal local image in EVERY finite jet. -/
theorem originalJetEquiv_of (n : ℕ) (r : R) :
    letI := pointCoefficientAlgebra K R
    originalJetEquiv K R n (Ideal.Quotient.mk (maximalIdeal C ^ n) (algebraMap R C r)) =
      Ideal.Quotient.mk (maximalIdeal T ^ n) (algebraMap R T r) := by
  let := pointCoefficientAlgebra K R
  apply ((NodeGeometricCompletionJets.jetEquiv T n).restrictScalars κ).injective
  change NodeGeometricCompletionJets.jetEquiv T n
    ((NodeGeometricCompletionJets.jetEquiv T n).symm
      (completedJetEquiv K R n (Ideal.Quotient.mk (maximalIdeal C ^ n) (algebraMap R C r)))) = _
  rw [AlgEquiv.apply_symm_apply, completedJetEquiv_mk]
  change Ideal.Quotient.mk (maximalIdeal C' ^ n) (completedPointEquiv K R (algebraMap R C r)) =
    NodeGeometricCompletionJets.jetEquiv T n
      (Ideal.Quotient.mk (maximalIdeal T ^ n) (algebraMap R T r))
  rw [NodeGeometricCompletionJets.jetEquiv_mk]
  change Ideal.Quotient.mk (maximalIdeal C' ^ n)
    (NodeGeometricCompletionDiagonalEtale.completedOriginalEquiv K R (algebraMap R C r)) = _
  rw [AlgEquiv.commutes]
  exact congrArg (Ideal.Quotient.mk (maximalIdeal C' ^ n)) (IsScalarTower.algebraMap_apply R T C' r)

end Hironaka.Algebra.NodeGeometricCompletionOriginalDiagonalJets
