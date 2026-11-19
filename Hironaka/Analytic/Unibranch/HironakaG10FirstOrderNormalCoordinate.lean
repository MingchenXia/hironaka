import Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJetApply
import Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalNilpotence

/-! The split linear coordinates are the literal square-zero normal coordinate germs. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJet
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJetApply
namespace Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalCoordinate
noncomputable section

/-- A single degree-one normal monomial is the actual normal coordinate. -/
theorem normalExponentMonomial_single (d a : ℕ) (i : Fin a) :
    normalExponentMonomial d a (Finsupp.single i 1) = normalCoordinate d a i := by
  classical
  simp [normalExponentMonomial, Finsupp.single_apply, Finset.prod_ite_eq]

/-- A coordinate singleton in the first-order split is literally the normal coordinate class. -/
theorem firstOrderNormalLinearEquiv_coordinate (d a : ℕ) (i : Fin a)
    (b : HolGerm (ComplexModel d)) :
    letI := tangentAlgebra d a
    firstOrderNormalLinearEquiv d a (0,Pi.single i b) =
      b • Ideal.Quotient.mk (normalIdeal d a ^ 2) (normalCoordinate d a i) := by
  have h := firstOrderNormalLinearEquiv_option_single d a (some i) b
  have he : ((firstOrderExponentEquiv a) (some i)).val = Finsupp.single i 1 := rfl
  simpa [he,normalExponentMonomial_single] using h
end
end Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalCoordinate
