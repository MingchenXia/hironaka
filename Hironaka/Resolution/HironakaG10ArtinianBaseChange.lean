import Hironaka.Resolution.HironakaG10ArtinianPolynomialIdentity
import Mathlib.RingTheory.TensorProduct.Quotient
set_option autoImplicit false
open scoped TensorProduct
namespace Hironaka.HironakaG10ArtinianBaseChange
open HolGerm HironakaRelativeNormalIdeal HironakaG10ArtinianParameterPullback
  HironakaG10ArtinianTensorSection HironakaG10ArtinianPolynomialIdentity
noncomputable section

local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

def truncatedParameterIdeal (d q : ℕ) (I : Ideal (HolGerm (ComplexModel d))) :
    Ideal (HolGerm (ComplexModel d)) := I ⊔ IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1)

/-- Actual base change of the whole joint germ ring to a canonical finite
parameter quotient is the whole complex tensor fibre. -/
def actualBaseChangeTensorRingEquiv (d t q : ℕ) (I : Ideal (HolGerm (ComplexModel d))) :
    let J := truncatedParameterIdeal d q I
    let Q := HolGerm (ComplexModel d) ⧸ J
    (Q ⊗[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t))) ≃+*
      (Q ⊗[ℂ] HolGerm (ComplexModel t)) := by
  let J := truncatedParameterIdeal d q I
  let Q := HolGerm (ComplexModel d) ⧸ J
  let φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q := Ideal.Quotient.mkₐ ℂ J
  have hker : RingHom.ker φ.toRingHom = J := Ideal.mk_ker
  have hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom := by rw [hker]; exact le_sup_right
  have hsurj : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have e : (HolGerm (ComplexModel (d+t)) ⧸
      Ideal.map (tangentPullback d t).toRingHom J) ≃+* (Q ⊗[ℂ] HolGerm (ComplexModel t)) :=
    (Ideal.quotientEquivAlgOfEq ℂ (congrArg (Ideal.map (tangentPullback d t).toRingHom) hker.symm)).toRingEquiv.trans
      (actualJointQuotientTensorEquiv d t q φ hφ hsurj).toRingEquiv
  exact ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor
    (HolGerm (ComplexModel (d+t))) J).symm.toRingEquiv).trans e
set_option backward.isDefEq.respectTransparency false in
/-- The base-change equivalence preserves each original whole joint germ. -/
theorem actualBaseChangeTensorRingEquiv_one_tmul (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) (g : HolGerm (ComplexModel (d+t))) :
    let J := truncatedParameterIdeal d q I
    let Q := HolGerm (ComplexModel d) ⧸ J
    let φ : HolGerm (ComplexModel d) →ₐ[ℂ] Q := Ideal.Quotient.mkₐ ℂ J
    let hφ : IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker φ.toRingHom := by
        change _ ≤ RingHom.ker (Ideal.Quotient.mk J)
        rw [Ideal.mk_ker]
        exact le_sup_right
    actualBaseChangeTensorRingEquiv d t q I ((1 : Q) ⊗ₜ[HolGerm (ComplexModel d)] g) =
      actualArtinianParameterPullback d t q φ hφ g := by
  let J := truncatedParameterIdeal d q I
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor (HolGerm (ComplexModel (d+t))) J
  have he : e.symm ((1 : HolGerm (ComplexModel d) ⧸ J) ⊗ₜ[HolGerm (ComplexModel d)] g) =
      Ideal.Quotient.mk _ g := by
    apply e.symm_apply_eq.mpr
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk _ _ g).symm
  simp only [actualBaseChangeTensorRingEquiv, RingEquiv.trans_apply]
  change (Algebra.TensorProduct.quotIdealMapEquivQuotTensor
    (HolGerm (ComplexModel (d+t))) J).symm.toRingEquiv
      ((1 : HolGerm (ComplexModel d) ⧸ J) ⊗ₜ[HolGerm (ComplexModel d)] g) =
    Ideal.Quotient.mk _ g at he
  rw [he]
  rfl
/-- The actual whole base-change equivalence preserves every parameter scalar. -/
def actualBaseChangeTensorParamEquiv (d t q : ℕ) (I : Ideal (HolGerm (ComplexModel d))) :
    let J := truncatedParameterIdeal d q I
    let Q := HolGerm (ComplexModel d) ⧸ J
    (Q ⊗[HolGerm (ComplexModel d)] HolGerm (ComplexModel (d+t))) ≃ₐ[Q]
      (Q ⊗[ℂ] HolGerm (ComplexModel t)) := by
  let J := truncatedParameterIdeal d q I
  let Q := HolGerm (ComplexModel d) ⧸ J
  refine { actualBaseChangeTensorRingEquiv d t q I with commutes' := ?_ }
  intro a
  obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective a
  change actualBaseChangeTensorRingEquiv d t q I
    ((algebraMap (HolGerm (ComplexModel d)) Q b) ⊗ₜ[HolGerm (ComplexModel d)] 1) =
      (Ideal.Quotient.mk J b) ⊗ₜ[ℂ] (1 : HolGerm (ComplexModel t))
  rw [Algebra.TensorProduct.tmul_one_eq_one_tmul]
  change actualBaseChangeTensorRingEquiv d t q I
    ((1 : Q) ⊗ₜ[HolGerm (ComplexModel d)] tangentPullback d t b) = _
  rw [actualBaseChangeTensorRingEquiv_one_tmul]
  exact actualArtinianParameterPullback_base d t q _ _ b
end
end Hironaka.HironakaG10ArtinianBaseChange
