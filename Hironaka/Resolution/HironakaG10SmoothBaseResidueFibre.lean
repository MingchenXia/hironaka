import Hironaka.Resolution.HironakaActualJointBaseFibre
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! The full, untruncated residue tensor of the native tangent germ action
is the actual normal fibre germ ring. -/

set_option autoImplicit false
open Set Filter
open scoped Topology TensorProduct Matrix

namespace Hironaka.HironakaG10SmoothBaseResidueFibre
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaActualJointBaseFibre
  HironakaRelativeNormalFibreHilbertSamuel HironakaRelativeNormalNearbyUniformRanks

attribute [local instance] tangentAlgebra baseGermResidueAlgebra

theorem baseMaximalIdeal_eq_ker_eval (d : ℕ) :
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) =
      RingHom.ker (HolGerm.eval : HolGerm (ComplexModel d) →+* ℂ) := by
  ext g
  exact HolGerm.mem_maximalIdeal_iff g

theorem eval_surjective (d : ℕ) :
    Function.Surjective (HolGerm.eval : HolGerm (ComplexModel d) →+* ℂ) :=
  fun c => ⟨HolGerm.constHom c, HolGerm.eval_constHom c⟩

def baseResidueRingEquiv (d : ℕ) :
    HolGerm (ComplexModel d) ⧸ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ≃+* ℂ :=
  (Ideal.quotEquivOfEq (baseMaximalIdeal_eq_ker_eval d)).trans
    ((HolGerm.eval : HolGerm (ComplexModel d) →+* ℂ).quotientKerEquivOfSurjective
      (eval_surjective d))

theorem baseResidueRingEquiv_mk (d : ℕ) (a : HolGerm (ComplexModel d)) :
    baseResidueRingEquiv d
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d))) a) =
        HolGerm.eval a := by
  rw [baseResidueRingEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

def baseResidueAlgEquiv (d : ℕ) :
    (HolGerm (ComplexModel d) ⧸ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)))
      ≃ₐ[HolGerm (ComplexModel d)] ℂ :=
  AlgEquiv.ofRingEquiv (f := baseResidueRingEquiv d) (baseResidueRingEquiv_mk d)

theorem baseResidueAlgEquiv_symm_const (d : ℕ) (c : ℂ) :
    (baseResidueAlgEquiv d).symm c =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)))
        (HolGerm.constHom c) := by
  apply (baseResidueAlgEquiv d).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (baseResidueRingEquiv_mk d (HolGerm.constHom c)).symm

def wholeFibreQuotientEquiv (d t : ℕ) :
    (HolGerm (ComplexModel (d + t)) ⧸ originalBaseMaximalIdeal d t) ≃ₐ[ℂ]
      HolGerm (ComplexModel t) :=
  (Ideal.quotientEquivAlgOfEq ℂ (baseMaximalIdeal_eq_ker_jointBaseZeroTrace d t)).trans
    (Ideal.quotientKerAlgEquivOfSurjective (jointBaseZeroTrace_surjective d t))

theorem wholeFibreQuotientEquiv_mk (d t : ℕ) (r : HolGerm (ComplexModel (d + t))) :
    wholeFibreQuotientEquiv d t (Ideal.Quotient.mk (originalBaseMaximalIdeal d t) r) =
      jointBaseZeroTrace d t r := rfl

/-- Built from the whole quotient and actual origin evaluation, with no normal truncation. -/
def residueTensorRingEquiv (d t : ℕ) :
    (HolGerm (ComplexModel (d + t)) ⊗[HolGerm (ComplexModel d)] ℂ) ≃+*
      HolGerm (ComplexModel t) :=
  ((Algebra.TensorProduct.congr
    (AlgEquiv.refl : HolGerm (ComplexModel (d + t)) ≃ₐ[HolGerm (ComplexModel (d + t))]
      HolGerm (ComplexModel (d + t)))
    (baseResidueAlgEquiv d)).symm.toRingEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot
        (HolGerm (ComplexModel (d + t)))
        (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)))).symm.toRingEquiv).trans
    (wholeFibreQuotientEquiv d t).toRingEquiv

theorem residueTensorRingEquiv_tmul (d t : ℕ)
    (r : HolGerm (ComplexModel (d + t))) (c : ℂ) :
    residueTensorRingEquiv d t (r ⊗ₜ[HolGerm (ComplexModel d)] c) =
      c • jointBaseZeroTrace d t r := by
  let q := Algebra.TensorProduct.quotIdealMapEquivTensorQuot
    (HolGerm (ComplexModel (d + t))) (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)))
  calc
    _ = wholeFibreQuotientEquiv d t
        (q.symm (r ⊗ₜ[HolGerm (ComplexModel d)] (baseResidueAlgEquiv d).symm c)) := rfl
    _ = wholeFibreQuotientEquiv d t
        (q.symm (r ⊗ₜ[HolGerm (ComplexModel d)]
          Ideal.Quotient.mk (IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)))
            (HolGerm.constHom c))) :=
      congrArg (fun a => wholeFibreQuotientEquiv d t
        (q.symm (r ⊗ₜ[HolGerm (ComplexModel d)] a))) (baseResidueAlgEquiv_symm_const d c)
    _ = jointBaseZeroTrace d t (tangentPullback d t (HolGerm.constHom c) * r) := rfl
    _ = _ := by
      rw [map_mul]
      change jointBaseZeroTrace d t
        (tangentPullback d t (algebraMap ℂ (HolGerm (ComplexModel d)) c)) *
          jointBaseZeroTrace d t r =
        algebraMap ℂ (HolGerm (ComplexModel t)) c * jointBaseZeroTrace d t r
      rw [(tangentPullback d t).commutes, (jointBaseZeroTrace d t).commutes]

def residueTensorAlgEquiv (d t : ℕ) :
    (HolGerm (ComplexModel (d + t)) ⊗[HolGerm (ComplexModel d)] ℂ) ≃ₐ[ℂ]
      HolGerm (ComplexModel t) :=
  AlgEquiv.ofRingEquiv (f := residueTensorRingEquiv d t) (by
    intro c
    change residueTensorRingEquiv d t
      ((algebraMap ℂ (HolGerm (ComplexModel (d + t))) c) ⊗ₜ[HolGerm (ComplexModel d)] 1) = _
    rw [residueTensorRingEquiv_tmul, one_smul, (jointBaseZeroTrace d t).commutes])

theorem residueTensorAlgEquiv_tmul (d t : ℕ)
    (r : HolGerm (ComplexModel (d + t))) (c : ℂ) :
    residueTensorAlgEquiv d t (r ⊗ₜ[HolGerm (ComplexModel d)] c) =
      c • jointBaseZeroTrace d t r := residueTensorRingEquiv_tmul d t r c

def leftResidueTensorRingEquiv (d t : ℕ) :
    (ℂ ⊗[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d + t))) ≃+*
      HolGerm (ComplexModel t) :=
  (Algebra.TensorProduct.comm (HolGerm (ComplexModel d)) ℂ
    (HolGerm (ComplexModel (d + t)))).toRingEquiv.trans (residueTensorRingEquiv d t)

theorem leftResidueTensorRingEquiv_tmul (d t : ℕ)
    (c : ℂ) (r : HolGerm (ComplexModel (d + t))) :
    leftResidueTensorRingEquiv d t (c ⊗ₜ[HolGerm (ComplexModel d)] r) =
      c • jointBaseZeroTrace d t r := by
  exact residueTensorRingEquiv_tmul d t r c

def leftResidueTensorAlgEquiv (d t : ℕ) :
    (ℂ ⊗[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d + t))) ≃ₐ[ℂ]
      HolGerm (ComplexModel t) :=
  AlgEquiv.ofRingEquiv (f := leftResidueTensorRingEquiv d t) (by
    intro c
    change leftResidueTensorRingEquiv d t
      (c ⊗ₜ[HolGerm (ComplexModel d)] (1 : HolGerm (ComplexModel (d + t)))) = _
    rw [leftResidueTensorRingEquiv_tmul, map_one]
    simp only [Algebra.smul_def, mul_one])

theorem leftResidueTensorAlgEquiv_tmul (d t : ℕ)
    (c : ℂ) (r : HolGerm (ComplexModel (d + t))) :
    leftResidueTensorAlgEquiv d t (c ⊗ₜ[HolGerm (ComplexModel d)] r) =
      c • jointBaseZeroTrace d t r := leftResidueTensorRingEquiv_tmul d t c r

/-- Actual residue tensor fibres of finite free native germ modules. -/
def fibreTensorVectorEquiv (d t n : ℕ) :
    (ℂ ⊗[HolGerm (ComplexModel d)] (Fin n → HolGerm (ComplexModel (d + t)))) ≃ₗ[ℂ]
      (Fin n → HolGerm (ComplexModel t)) :=
  (TensorProduct.piRight (HolGerm (ComplexModel d)) ℂ ℂ
    (fun _ : Fin n => HolGerm (ComplexModel (d + t)))).trans
    (LinearEquiv.piCongrRight fun _ => (leftResidueTensorAlgEquiv d t).toLinearEquiv)

theorem fibreTensorVectorEquiv_tmul (d t n : ℕ) (c : ℂ)
    (v : Fin n → HolGerm (ComplexModel (d + t))) :
    fibreTensorVectorEquiv d t n (c ⊗ₜ[HolGerm (ComplexModel d)] v) =
      c • (fun i => jointBaseZeroTrace d t (v i)) := by
  funext i
  exact leftResidueTensorAlgEquiv_tmul d t c (v i)

/-- The complete matrix action is carried to the actual zero-base trace matrix. -/
theorem fibreTensorVectorEquiv_lTensor_mulVec (d t m n : ℕ)
    (M : Matrix (Fin m) (Fin n) (HolGerm (ComplexModel (d + t))))
    (x : ℂ ⊗[HolGerm (ComplexModel d)] (Fin n → HolGerm (ComplexModel (d + t)))) :
    fibreTensorVectorEquiv d t m
        ((M.mulVecLin.restrictScalars (HolGerm (ComplexModel d))).lTensor ℂ x) =
      (M.map (jointBaseZeroTrace d t)) *ᵥ fibreTensorVectorEquiv d t n x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Matrix.mulVec_zero]
  | tmul c v =>
    change fibreTensorVectorEquiv d t m
      (c ⊗ₜ[HolGerm (ComplexModel d)] (M *ᵥ v)) = _
    rw [fibreTensorVectorEquiv_tmul, fibreTensorVectorEquiv_tmul]
    let T := (M.map (jointBaseZeroTrace d t)).mulVecLin.restrictScalars ℂ
    change c • (fun i => jointBaseZeroTrace d t ((M *ᵥ v) i)) =
      T (c • (fun i => jointBaseZeroTrace d t (v i)))
    rw [T.map_smul]
    congr 1
    ext i
    simp only [T, LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  | add x y hx hy => simp only [map_add, hx, hy, Matrix.mulVec_add]

end
end Hironaka.HironakaG10SmoothBaseResidueFibre
