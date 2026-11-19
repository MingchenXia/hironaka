import Hironaka.Geometry.NodeCompletedLocalOriginalNodeRelation
import Hironaka.Algebra.NodeFieldGeometricCubicMap

/-! Genuine original singular-point geometry internally gives a nondegenerate whole relation. -/

noncomputable section

open AlgebraicGeometry IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalOriginalNodeQuadraticRelation

open NodeCompletedLocalMap NodeCompletedLocalOriginalNodeJets NodeCompletedLocalResiduePoint
  NodeCompletedLocalOriginalNodePresentation NodeCompletedLocalSelectedFiberGeometric

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSemistableCurve f]
  (z : (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subscheme)

local notation "x" => (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z
local notation "Q" => OriginalFiberRing f x
local notation "κ" => ResidueField Q
local notation "C" => Algebra.CompletionRegularityBasics.Completion Q

attribute [local instance] originalAlgebra originalFiberResidueAlgebra originalFiber_isNoetherianRing
  originalBaseAlgebra selectedQuotientPointAlgebra selectedQuotientPoint_scalarTower

local instance originalQuotientLocalRing : IsLocalRing Q := originalFiberLocalRing f x

variable (L : Type u) [Field L] [IsAlgClosed L]
  [Algebra (X.residueField ((Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z)) L]

theorem exists_nondegenerate_relation :
    letI := originalPointAlgebra f z
    ∃ F : Algebra.NodeFormalMorse.Series κ,
      evaluation f z L F = 0 ∧ F ∈ Algebra.NodeVariableMorse.variableIdeal κ ^ 2 ∧
      F ∉ Algebra.NodeVariableMorse.variableIdeal κ ^ 3 ∧
      Algebra.NodeVariableMorse.jetDiscriminant F ≠ 0 := by
  let := originalCompletion_isNoetherianRing f z
  let := originalCompletion_isAdicComplete f z
  let := originalPointAlgebra f z
  obtain ⟨F, hF, hF2, hF3⟩ := NodeCompletedLocalOriginalNodeRelation.exists_relation f z L
  have hV : (Algebra.NodeVariableMorse.variableIdeal κ).map
      (evaluation f z L).toRingHom = maximalIdeal C := by
    simpa only [pow_one] using variableIdeal_pow_image f z L 1
  have hΔ := Algebra.NodeFieldGeometricCubicMap.relation_discriminant_ne_zero
    κ L C (evaluation f z L) hV (nodeJetEquiv f z L 3)
    (evaluation_surjective f z L) F hF hF2 hF3
  exact ⟨F, hF, hF2, hF3, hΔ⟩

end Hironaka.Geometry.NodeCompletedLocalOriginalNodeQuadraticRelation
