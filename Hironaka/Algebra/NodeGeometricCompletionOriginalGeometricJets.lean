import Hironaka.Algebra.NodeGeometricCompletionOriginalDiagonalJets
import Hironaka.Algebra.NodeGeometricCompletionDiagonalCompletedJets

/-! ALL finite jets of the ORIGINAL completion at the SAME actual geometric point. -/

noncomputable section

open IsLocalRing TensorProduct

namespace Hironaka.Algebra.NodeGeometricCompletionOriginalGeometricJets

open CompletionRegularityBasics NodeGeometricCompletionDiagonalCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable (K R : Type u) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
  [Algebra.EssFiniteType K R] [FiniteDimensional K (ResidueField R)]
  [Algebra.IsSeparable K (ResidueField R)]

include K in
omit [IsLocalRing R] [FiniteDimensional K (ResidueField R)]
  [Algebra.IsSeparable K (ResidueField R)] in
theorem original_isNoetherianRing : IsNoetherianRing R :=
  Algebra.EssFiniteType.isNoetherianRing K R

local notation "κ" => ResidueField R
local notation "T" => NodeGeometricCompletionDiagonalPoint.DiagonalLocal K R
local notation "C" => Completion R

variable (L : Type u) [Field L] [Algebra (ResidueField R) L]

local notation "G" => NodeGeometricCompletionDiagonalGeometric.DiagonalGeometricStalk K R L

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  NodeGeometricCompletionDiagonalPoint.diagonalPoint_isMaximal
  NodeGeometricCompletionDiagonalPoint.pointFieldAlgebra
  NodeGeometricCompletionDiagonalPoint.originalAlgebra
  NodeGeometricCompletionTensorLocalization.localizedPoint_isMaximal
  NodeGeometricCompletionDiagonalCompletedJets.selectedStalk_isNoetherianRing

/-- Every actual original completed finite jet, scalar extended only AFTER quotienting, is the SAME geometric completed jet. -/
def jetEquiv (n : ℕ) :
    letI := original_isNoetherianRing K R
    letI := pointCoefficientAlgebra K R
    (L ⊗[κ] (C ⧸ maximalIdeal C ^ n)) ≃ₐ[L]
      (Completion G ⧸ maximalIdeal (Completion G) ^ n) := by
  letI := original_isNoetherianRing K R
  letI := pointCoefficientAlgebra K R
  exact (Algebra.TensorProduct.congr (AlgEquiv.refl : L ≃ₐ[L] L)
    (NodeGeometricCompletionOriginalDiagonalJets.originalJetEquiv K R n)).trans
      (NodeGeometricCompletionDiagonalCompletedJets.completedJetEquiv K R L n)

/-- EVERY original local representative retains the literal original diagonal/tensor/localization/completion image. -/
theorem jetEquiv_original (n : ℕ) (l : L) (r : R) :
    letI := original_isNoetherianRing K R
    letI := pointCoefficientAlgebra K R
    jetEquiv K R L n (l ⊗ₜ[κ] Ideal.Quotient.mk (maximalIdeal C ^ n) (algebraMap R C r)) =
      Ideal.Quotient.mk (maximalIdeal (Completion G) ^ n)
        (algebraMap G (Completion G)
          (algebraMap (L ⊗[κ] T) G (l ⊗ₜ[κ] algebraMap R T r))) := by
  let := original_isNoetherianRing K R
  let := pointCoefficientAlgebra K R
  change NodeGeometricCompletionDiagonalCompletedJets.completedJetEquiv K R L n
    (l ⊗ₜ[κ] NodeGeometricCompletionOriginalDiagonalJets.originalJetEquiv K R n
      (Ideal.Quotient.mk (maximalIdeal C ^ n) (algebraMap R C r))) = _
  rw [NodeGeometricCompletionOriginalDiagonalJets.originalJetEquiv_of,
    NodeGeometricCompletionDiagonalCompletedJets.completedJetEquiv_tmul]

end Hironaka.Algebra.NodeGeometricCompletionOriginalGeometricJets
