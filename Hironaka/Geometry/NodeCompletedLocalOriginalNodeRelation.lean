import Hironaka.Geometry.NodeCompletedLocalOriginalNodePresentation
import Hironaka.Algebra.NodeFieldCubicRelation

/-! The genuine original singular-point evaluation has an actual quadratic-order relation. -/

noncomputable section

open AlgebraicGeometry IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalOriginalNodeRelation

open NodeCompletedLocalMap NodeCompletedLocalOriginalNodeJets
  NodeCompletedLocalOriginalNodeJetDimensions NodeCompletedLocalOriginalNodePresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option quotPrecheck false

universe u
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSemistableCurve f]
  (z : (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subscheme)

local notation "x" => (Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z
local notation "Q" => OriginalFiberRing f x
local notation "κ" => ResidueField Q
local notation "C" => Algebra.CompletionRegularityBasics.Completion Q

attribute [local instance] originalAlgebra originalFiberResidueAlgebra originalFiber_isNoetherianRing

local instance originalQuotientLocalRing : IsLocalRing Q := originalFiberLocalRing f x

variable (L : Type u) [Field L] [IsAlgClosed L]
  [Algebra (X.residueField ((Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z)) L]

include L in
/-- Actual ORIGINAL semistable geometry produces an ENTIRE relation in the SAME actual evaluation kernel, of order exactly two. -/
theorem exists_relation :
    letI := originalPointAlgebra f z
    ∃ F : Algebra.NodeFormalMorse.Series κ,
      evaluation f z L F = 0 ∧ F ∈ Algebra.NodeVariableMorse.variableIdeal κ ^ 2 ∧
        F ∉ Algebra.NodeVariableMorse.variableIdeal κ ^ 3 := by
  let := originalCompletion_isNoetherianRing f z
  let := originalCompletion_isAdicComplete f z
  let := originalPointAlgebra f z
  exact Algebra.NodeFieldCubicRelation.originalEvaluation_relation κ C
    (originalPoint_residue_bijective f z) (jet_finrank_two f z L) (jet_finrank_three f z L)

end Hironaka.Geometry.NodeCompletedLocalOriginalNodeRelation
