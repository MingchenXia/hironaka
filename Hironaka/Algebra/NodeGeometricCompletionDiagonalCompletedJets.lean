import Hironaka.Algebra.NodeGeometricCompletionDiagonalJets
import Hironaka.Algebra.NodeGeometricCompletionJets
import Mathlib.RingTheory.Localization.Submodule

/-! Internal Noetherianity and EVERY finite jet of the SAME actual diagonal geometric completion. -/

noncomputable section

open IsLocalRing TensorProduct

namespace Hironaka.Algebra.NodeGeometricCompletionDiagonalCompletedJets

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 3000
set_option quotPrecheck false

universe u
variable (K R : Type u) [Field K] [CommRing R] [IsLocalRing R] [Algebra K R]
  [Algebra.EssFiniteType K R]

local notation "κ" => ResidueField R
local notation "D" => NodeGeometricCompletionDiagonalPoint.TensorRing K R
local notation "T" => NodeGeometricCompletionDiagonalPoint.DiagonalLocal K R

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  NodeGeometricCompletionDiagonalPoint.diagonalPoint_isMaximal
  NodeGeometricCompletionDiagonalPoint.pointFieldAlgebra
  NodeGeometricCompletionDiagonalPoint.originalAlgebra
  NodeGeometricCompletionTensorLocalization.localizedPoint_isMaximal

/-- Essential finite type of the SAME actual diagonal local ring is derived over its native point field. -/
theorem diagonal_essFiniteType : Algebra.EssFiniteType κ T := by
  let : Algebra.EssFiniteType κ D := inferInstance
  let : Algebra.EssFiniteType D T := Algebra.EssFiniteType.of_isLocalization _
    (NodeGeometricCompletionDiagonalPoint.diagonalPoint K R).primeCompl
  exact Algebra.EssFiniteType.comp κ D T

attribute [local instance] diagonal_essFiniteType

/-- Native Noetherianity of the SAME diagonal local ring is not an input. -/
theorem diagonal_isNoetherianRing : IsNoetherianRing T :=
  Algebra.EssFiniteType.isNoetherianRing κ T

variable (L : Type u) [Field L] [Algebra (ResidueField R) L]

local notation "B" => L ⊗[κ] T
local notation "G" => NodeGeometricCompletionDiagonalGeometric.DiagonalGeometricStalk K R L

/-- Native Noetherianity of the SAME actual further scalar-extension ring is internally derived. -/
theorem tensor_isNoetherianRing : IsNoetherianRing B :=
  Algebra.EssFiniteType.isNoetherianRing L B

/-- The SAME actual selected geometric local ring is internally Noetherian. -/
theorem selectedStalk_isNoetherianRing : IsNoetherianRing G := by
  let := tensor_isNoetherianRing K R L
  infer_instance

attribute [local instance] selectedStalk_isNoetherianRing

/-- EVERY actual scalar-extended diagonal jet is the SAME selected completed-geometric jet. -/
def completedJetEquiv (n : ℕ) :
    (L ⊗[κ] (T ⧸ maximalIdeal T ^ n)) ≃ₐ[L]
      (CompletionRegularityBasics.Completion G ⧸
        maximalIdeal (CompletionRegularityBasics.Completion G) ^ n) :=
  (NodeGeometricCompletionDiagonalJets.jetEquiv K R L n).trans
    ((NodeGeometricCompletionJets.jetEquiv G n).restrictScalars L)

/-- Every actual tensor representative retains the SAME original localization/completion image. -/
theorem completedJetEquiv_tmul (n : ℕ) (l : L) (t : T) :
    completedJetEquiv K R L n (l ⊗ₜ[κ] Ideal.Quotient.mk (maximalIdeal T ^ n) t) =
      Ideal.Quotient.mk (maximalIdeal (CompletionRegularityBasics.Completion G) ^ n)
        (algebraMap G (CompletionRegularityBasics.Completion G) (algebraMap B G (l ⊗ₜ[κ] t))) := by
  change NodeGeometricCompletionJets.jetEquiv G n
    (NodeGeometricCompletionDiagonalJets.jetEquiv K R L n
      (l ⊗ₜ[κ] Ideal.Quotient.mk (maximalIdeal T ^ n) t)) = _
  rw [NodeGeometricCompletionDiagonalJets.jetEquiv_tmul,
    NodeGeometricCompletionJets.jetEquiv_mk]

end Hironaka.Algebra.NodeGeometricCompletionDiagonalCompletedJets
