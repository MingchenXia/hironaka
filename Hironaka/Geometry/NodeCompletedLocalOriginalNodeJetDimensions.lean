import Hironaka.Geometry.NodeCompletedLocalOriginalNodeJets
import Hironaka.Algebra.NodeFieldJetDimensionDescent

/-! Actual original singular-point jet finiteness and ranks, derived from genuine source geometry. -/

noncomputable section

open AlgebraicGeometry IsLocalRing

namespace Hironaka.Geometry.NodeCompletedLocalOriginalNodeJetDimensions

open NodeCompletedLocalMap NodeCompletedLocalResiduePoint
  NodeCompletedLocalSelectedFiberGeometric NodeCompletedLocalOriginalNodeJets

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

local instance originalQuotientLocalRing : IsLocalRing Q := originalFiberLocalRing f x

variable (L : Type u) [Field L] [IsAlgClosed L]
  [Algebra (X.residueField ((Algebra.NodeFittingOmegaGluing.idealSheaf f 1).subschemeι z)) L]

attribute [local instance] originalBaseAlgebra selectedQuotientPointAlgebra

include L in
/-- EVERY original native finite jet is finite dimensional, internally descended from its SAME actual source geometric node. -/
theorem jet_finiteDimensional (n : ℕ) :
    letI := originalPointAlgebra f z
    FiniteDimensional κ (C ⧸ maximalIdeal C ^ n) := by
  let := originalPointAlgebra f z
  exact Algebra.NodeFieldJetDimensionDescent.originalJet_finiteDimensional κ L C n
    (nodeJetEquiv f z L n).toLinearEquiv

include L in
/-- The SAME actual original native jet has its derived dimension at EVERY positive order. -/
theorem jet_finrank_succ (n : ℕ) :
    letI := originalPointAlgebra f z
    Module.finrank κ (C ⧸ maximalIdeal C ^ (n + 1)) = 2 * n + 1 := by
  let := originalPointAlgebra f z
  exact Algebra.NodeFieldJetDimensionDescent.originalJet_finrank_succ κ L C n
    (nodeJetEquiv f z L (n + 1)).toLinearEquiv

include L in
/-- The first infinitesimal neighbourhood of the SAME original completion has native dimension THREE, with no dimension input. -/
theorem jet_finrank_two :
    letI := originalPointAlgebra f z
    Module.finrank κ (C ⧸ maximalIdeal C ^ 2) = 3 := by
  let := originalPointAlgebra f z
  exact Algebra.NodeFieldJetDimensionDescent.originalJet_finrank_two κ L C
    (nodeJetEquiv f z L 2).toLinearEquiv

include L in
/-- The cubic-power quotient of the SAME original completion has native dimension FIVE, with no dimension input. -/
theorem jet_finrank_three :
    letI := originalPointAlgebra f z
    Module.finrank κ (C ⧸ maximalIdeal C ^ 3) = 5 := by
  let := originalPointAlgebra f z
  exact Algebra.NodeFieldJetDimensionDescent.originalJet_finrank_three κ L C
    (nodeJetEquiv f z L 3).toLinearEquiv

end Hironaka.Geometry.NodeCompletedLocalOriginalNodeJetDimensions
