import Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalCoordinate

/-! Images of whole linear normal-coordinate combinations. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJet
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalCoordinate
namespace Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalVector
noncomputable section

/-- The linear part of the actual quotient is the literal sum of coordinate classes. -/
theorem firstOrderNormalLinearEquiv_vector (d a : ℕ) (v : Fin a → HolGerm (ComplexModel d)) :
    letI := tangentAlgebra d a
    firstOrderNormalLinearEquiv d a (0,v) =
      ∑ i, (v i) • Ideal.Quotient.mk (normalIdeal d a ^ 2) (normalCoordinate d a i) := by
  classical
  let _ := tangentAlgebra d a
  have hvec : ((0 : HolGerm (ComplexModel d)),v) =
      ∑ i : Fin a, ((0 : HolGerm (ComplexModel d)), Pi.single i (v i)) := by
    apply Prod.ext
    · simp [Prod.fst_sum]
    · funext j
      simp [Prod.snd_sum, Finset.sum_apply]
  rw [hvec, map_sum]
  exact Finset.sum_congr rfl fun i _ => firstOrderNormalLinearEquiv_coordinate d a i (v i)
end
end Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalVector
