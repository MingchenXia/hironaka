import Hironaka.Analytic.Unibranch.HironakaG10ComplexNilpotentRelationFlat
import Hironaka.Analytic.Unibranch.HironakaG10HigherRankBaseChange

/-! Nilpotent lifted-relation flatness for literal finite matrix cokernels
on the full tensor algebra. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10NilpotentMatrixFlatness
open Hironaka.Analytic.Unibranch.HironakaG10ComplexNilpotentRelationFlat
  Hironaka.Analytic.Unibranch.HironakaG10HigherRankBaseChange
noncomputable section

/-- The actual matrix cokernel is flat if its original exact reference
complex lifts with full map-level nilpotent congruences. -/
theorem matrixCokernel_flat_of_nilpotent_lifted_relation
    {Q H : Type} [CommRing Q] [Algebra ℂ Q] [CommRing H] [Algebra ℂ H]
    {a b c : ℕ} (I : Ideal Q) (hnil : ∃ n : ℕ, I ^ n = ⊥)
    (M : Matrix (Fin a) (Fin b) H) (N : Matrix (Fin b) (Fin c) H)
    (hcomp : ∀ w, M.mulVecLin (N.mulVecLin w) = 0)
    (hex : ∀ u, M.mulVecLin u = 0 → ∃ w, N.mulVecLin w = u)
    (F : Matrix (Fin a) (Fin b) (Q ⊗[ℂ] H))
    (G : Matrix (Fin b) (Fin c) (Q ⊗[ℂ] H))
    (hFG : ∀ w, F.mulVecLin (G.mulVecLin w) = 0)
    (hmodF : ∀ v, (F.mulVecLin.restrictScalars Q) v -
      ((baseMatrix ℂ H Q M).mulVecLin.restrictScalars Q) v ∈
        I • (⊤ : Submodule Q (Fin a → Q ⊗[ℂ] H)))
    (hmodG : ∀ v, (G.mulVecLin.restrictScalars Q) v -
      ((baseMatrix ℂ H Q N).mulVecLin.restrictScalars Q) v ∈
        I • (⊤ : Submodule Q (Fin b → Q ⊗[ℂ] H))) :
    Module.Flat Q ((Fin a → Q ⊗[ℂ] H) ⧸ LinearMap.range (F.mulVecLin.restrictScalars Q)) := by
  let eA := TensorProduct.piRight ℂ Q Q (fun _ : Fin a => H)
  let eB := TensorProduct.piRight ℂ Q Q (fun _ : Fin b => H)
  let eC := TensorProduct.piRight ℂ Q Q (fun _ : Fin c => H)
  let f : (Q ⊗[ℂ] (Fin b → H)) →ₗ[Q] (Q ⊗[ℂ] (Fin a → H)) :=
    eA.symm.toLinearMap.comp ((F.mulVecLin.restrictScalars Q).comp eB.toLinearMap)
  let g : (Q ⊗[ℂ] (Fin c → H)) →ₗ[Q] (Q ⊗[ℂ] (Fin b → H)) :=
    eB.symm.toLinearMap.comp ((G.mulVecLin.restrictScalars Q).comp eC.toLinearMap)
  have hfg (w : Q ⊗[ℂ] (Fin c → H)) : f (g w) = 0 := by
    change eA.symm ((F.mulVecLin.restrictScalars Q) (eB (eB.symm
      ((G.mulVecLin.restrictScalars Q) (eC w))))) = 0
    rw [eB.apply_symm_apply]
    change eA.symm (F.mulVecLin (G.mulVecLin (eC w))) = 0
    rw [hFG, map_zero]
  have hfm (v : Q ⊗[ℂ] (Fin b → H)) :
      f v - (M.mulVecLin.restrictScalars ℂ).baseChange Q v ∈
        I • (⊤ : Submodule Q (Q ⊗[ℂ] (Fin a → H))) := by
    have hc := congrArg (fun T : (Q ⊗[ℂ] (Fin b → H)) →ₗ[Q] (Fin a → Q ⊗[ℂ] H) => T v)
      (baseMatrix_commutes ℂ H Q M)
    have hc' : eA ((M.mulVecLin.restrictScalars ℂ).baseChange Q v) =
        ((baseMatrix ℂ H Q M).mulVecLin.restrictScalars Q) (eB v) := hc
    have hm := hmodF (eB v)
    have hmap : (I • (⊤ : Submodule Q (Fin a → Q ⊗[ℂ] H))).map eA.symm.toLinearMap ≤
        I • (⊤ : Submodule Q (Q ⊗[ℂ] (Fin a → H))) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right I le_top
    have hh := hmap (Submodule.mem_map_of_mem hm)
    change eA.symm ((F.mulVecLin.restrictScalars Q) (eB v) -
      ((baseMatrix ℂ H Q M).mulVecLin.restrictScalars Q) (eB v)) ∈ _ at hh
    rw [map_sub, ← hc', eA.symm_apply_apply] at hh
    exact hh
  have hgm (v : Q ⊗[ℂ] (Fin c → H)) :
      g v - (N.mulVecLin.restrictScalars ℂ).baseChange Q v ∈
        I • (⊤ : Submodule Q (Q ⊗[ℂ] (Fin b → H))) := by
    have hc := congrArg (fun T : (Q ⊗[ℂ] (Fin c → H)) →ₗ[Q] (Fin b → Q ⊗[ℂ] H) => T v)
      (baseMatrix_commutes ℂ H Q N)
    have hc' : eB ((N.mulVecLin.restrictScalars ℂ).baseChange Q v) =
        ((baseMatrix ℂ H Q N).mulVecLin.restrictScalars Q) (eC v) := hc
    have hm := hmodG (eC v)
    have hmap : (I • (⊤ : Submodule Q (Fin b → Q ⊗[ℂ] H))).map eB.symm.toLinearMap ≤
        I • (⊤ : Submodule Q (Q ⊗[ℂ] (Fin b → H))) := by
      rw [Submodule.map_smul'', Submodule.map_top]
      exact smul_mono_right I le_top
    have hh := hmap (Submodule.mem_map_of_mem hm)
    change eB.symm ((G.mulVecLin.restrictScalars Q) (eC v) -
      ((baseMatrix ℂ H Q N).mulVecLin.restrictScalars Q) (eC v)) ∈ _ at hh
    rw [map_sub, ← hc', eB.symm_apply_apply] at hh
    exact hh
  have hf : Module.Flat Q ((Q ⊗[ℂ] (Fin a → H)) ⧸ LinearMap.range f) :=
    flat_cokernel_of_complex_nilpotent_lifted_relation I hnil
      (N.mulVecLin.restrictScalars ℂ) (M.mulVecLin.restrictScalars ℂ) hcomp hex f g hfg hfm hgm
  let : Module.Flat Q ((Q ⊗[ℂ] (Fin a → H)) ⧸ LinearMap.range f) := hf
  have hcomm : eA.toLinearMap.comp f = (F.mulVecLin.restrictScalars Q).comp eB.toLinearMap := by
    ext v
    simp [f]
  have hrange : (LinearMap.range f).map eA.toLinearMap =
      LinearMap.range (F.mulVecLin.restrictScalars Q) := by
    rw [← LinearMap.range_comp, hcomm, LinearMap.range_comp]
    simp
  let E := Submodule.Quotient.equiv _ _ eA hrange
  exact Module.Flat.of_linearEquiv E.symm
end
end Hironaka.Analytic.Unibranch.HironakaG10NilpotentMatrixFlatness
