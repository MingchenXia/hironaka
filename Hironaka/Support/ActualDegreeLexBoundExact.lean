/- Complete original prerequisites; mathematical statements and proofs are unchanged. -/
import Hironaka.Resolution.HironakaActualFormalVertexDivision

/-! Actual diagram-complement monomials give the genuine whole formal jet quotient and HS count. -/
set_option autoImplicit false
open Set Classical
namespace Hironaka.HironakaActualFormalStandardMonomialHS
noncomputable section
open HolGerm HironakaHolomorphicPointJets HironakaRelativeNormalMonomialBasis
  HironakaActualOriginalFormalTaylor HironakaActualOriginalFormalHSTransfer
  HironakaActualFormalInitialDiagram HironakaActualFormalVertexDivision

variable {n : ℕ}

/-- The genuine degree-first order is compatible with the actual total exponent degree. -/
theorem actual_degree_le_of_deglex_lt (a b : Fin n →₀ ℕ)
    (h : MonomialOrder.degLex.toSyn a < MonomialOrder.degLex.toSyn b) :
    normalExponentDegree a ≤ normalExponentDegree b := by
  have hd := Finsupp.DegLex.monotone_degree (MonomialOrder.degLex_lt_iff.mp h).le
  simpa only [ofDegLex_toDegLex,Finsupp.degree_eq_sum,normalExponentDegree] using hd


end
end Hironaka.HironakaActualFormalStandardMonomialHS
