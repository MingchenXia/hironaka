import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.RingTheory.Flat.Stability

set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10HigherRankBaseChange
noncomputable section

variable (R A Q : Type) [CommRing R] [CommRing A] [CommRing Q] [Algebra R A] [Algebra R Q]
variable {a b : ℕ}

/-- Actual entrywise scalar extension into the tensor algebra. -/
def baseMatrix (M : Matrix (Fin a) (Fin b) A) : Matrix (Fin a) (Fin b) (Q ⊗[R] A) :=
  fun i j => 1 ⊗ₜ[R] M i j

/-- Finite-product tensor comparison intertwines the original and the
entrywise base-changed matrix maps. -/
theorem baseMatrix_commutes (M : Matrix (Fin a) (Fin b) A) :
    (TensorProduct.piRight R Q Q (fun _ : Fin a => A)).toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor Q Q (M.mulVecLin.restrictScalars R)) =
    ((baseMatrix R A Q M).mulVecLin.restrictScalars Q).comp
      (TensorProduct.piRight R Q Q (fun _ : Fin b => A)).toLinearMap := by
  classical
  ext q v i
  simp [baseMatrix, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm, TensorProduct.tmul_ite]


/-- The whole base-changed relation submodule is the actual image of the
entrywise base-changed matrix. -/
theorem baseMatrix_range (M : Matrix (Fin a) (Fin b) A) :
    let N := LinearMap.range M.mulVecLin
    (LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor Q Q
      (N.subtype.restrictScalars R))).map
        (TensorProduct.piRight R Q Q (fun _ : Fin a => A)).toLinearMap =
      LinearMap.range ((baseMatrix R A Q M).mulVecLin.restrictScalars Q) := by
  let N := LinearMap.range M.mulVecLin
  have hrange : LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor Q Q
        (N.subtype.restrictScalars R)) =
      LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor Q Q
        (M.mulVecLin.restrictScalars R)) := by
    ext z
    change z ∈ LinearMap.range ((N.subtype.restrictScalars R).lTensor Q) ↔
      z ∈ LinearMap.range ((M.mulVecLin.restrictScalars R).lTensor Q)
    symm
    rw [LinearMap.lTensor_range]
    rfl
  change (LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor Q Q
      (N.subtype.restrictScalars R))).map
        (TensorProduct.piRight R Q Q (fun _ : Fin a => A)).toLinearMap = _
  rw [hrange, ← LinearMap.range_comp, baseMatrix_commutes, LinearMap.range_comp]
  simp

/-- Base change commutes with the literal finite matrix cokernel. -/
def baseMatrixCokernelEquiv (M : Matrix (Fin a) (Fin b) A) :
    (Q ⊗[R] ((Fin a → A) ⧸ LinearMap.range M.mulVecLin)) ≃ₗ[Q]
      ((Fin a → Q ⊗[R] A) ⧸
        LinearMap.range ((baseMatrix R A Q M).mulVecLin.restrictScalars Q)) := by
  let N := LinearMap.range M.mulVecLin
  let e := TensorProduct.AlgebraTensorModule.tensorQuotientEquiv (R := R) Q A Q N
  exact e.trans (Submodule.Quotient.equiv _ _
    (TensorProduct.piRight R Q Q (fun _ : Fin a => A)) (baseMatrix_range R A Q M))

/-- Flatness of the original whole cokernel passes to its actual
arbitrary-rank matrix base change. -/
theorem baseMatrixCokernel_flat (M : Matrix (Fin a) (Fin b) A)
    (hflat : Module.Flat R ((Fin a → A) ⧸ LinearMap.range M.mulVecLin)) :
    Module.Flat Q ((Fin a → Q ⊗[R] A) ⧸
      LinearMap.range ((baseMatrix R A Q M).mulVecLin.restrictScalars Q)) := by
  let := hflat
  exact Module.Flat.of_linearEquiv (baseMatrixCokernelEquiv R A Q M).symm

end
end Hironaka.Analytic.Unibranch.HironakaG10HigherRankBaseChange
