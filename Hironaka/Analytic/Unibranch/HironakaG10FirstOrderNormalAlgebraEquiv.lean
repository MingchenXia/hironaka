import Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalMultiplication
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-! The actual first normal neighborhood is the trivial square-zero algebra. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaRelativeNormalMonomialBasis
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalJet
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalConstant
  Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalMultiplication
namespace Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalAlgebraEquiv
noncomputable section

/-- The actual holomorphic normal-square quotient is the trivial square-zero
extension of the actual base germ ring by its finite free normal module. -/
def firstOrderNormalAlgEquiv (d a : ℕ) :
    letI := tangentAlgebra d a
    TrivSqZeroExt (HolGerm (ComplexModel d)) (Fin a → HolGerm (ComplexModel d)) ≃ₐ[HolGerm (ComplexModel d)]
      (HolGerm (ComplexModel (d+a)) ⧸ normalIdeal d a ^ 2) := by
  letI := tangentAlgebra d a
  let B := HolGerm (ComplexModel d)
  let M := Fin a → B
  let E : TrivSqZeroExt B M ≃ₗ[B] (HolGerm (ComplexModel (d+a)) ⧸ normalIdeal d a ^ 2) :=
    firstOrderNormalLinearEquiv d a
  apply AlgEquiv.ofLinearEquiv E
  · change firstOrderNormalLinearEquiv d a (1,0) = 1
    rw [firstOrderNormalLinearEquiv_constant]
    simp
  · intro x y
    have hp : x*y = (x.fst*y.fst, x.fst • y.snd + y.fst • x.snd) := by
      apply TrivSqZeroExt.ext
      · rfl
      · change x.fst • y.snd + (MulOpposite.op y.fst) • x.snd = _
        simp
    have hx : ((x.fst,x.snd) : TrivSqZeroExt B M) = x := Prod.eta x
    have hy : ((y.fst,y.snd) : TrivSqZeroExt B M) = y := Prod.eta y
    have hxE : E (x.fst,x.snd) = E x := congrArg E hx
    have hyE : E (y.fst,y.snd) = E y := congrArg E hy
    rw [hp, ← hxE, ← hyE]
    exact (firstOrderNormalLinearEquiv_mul d a x.fst y.fst x.snd y.snd).symm
end
end Hironaka.Analytic.Unibranch.HironakaG10FirstOrderNormalAlgebraEquiv
