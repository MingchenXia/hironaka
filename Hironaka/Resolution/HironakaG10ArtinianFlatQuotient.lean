import Hironaka.Resolution.HironakaG10ArtinianBaseChange
import Mathlib.RingTheory.Flat.Stability
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open scoped TensorProduct
namespace Hironaka.HironakaG10ArtinianFlatQuotient
open HolGerm HironakaRelativeNormalIdeal HironakaG10ArtinianParameterPullback
  HironakaG10ArtinianBaseChange
noncomputable section
local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

def parameterQuotientMap (d q : ℕ) (I : Ideal (HolGerm (ComplexModel d))) :
    HolGerm (ComplexModel d) →ₐ[ℂ]
      (HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I) :=
  Ideal.Quotient.mkₐ ℂ _

theorem parameterQuotientMap_kills (d q : ℕ) (I : Ideal (HolGerm (ComplexModel d))) :
    IsLocalRing.maximalIdeal (HolGerm (ComplexModel d)) ^ (q+1) ≤
      RingHom.ker (parameterQuotientMap d q I).toRingHom := by
  change _ ≤ RingHom.ker (Ideal.Quotient.mk (truncatedParameterIdeal d q I))
  rw [Ideal.mk_ker]
  exact le_sup_right

/-- Base change of an entire original joint-germ ideal quotient is the
entire tensor-fibre quotient by its actual substituted ideal. -/
def actualBaseChangedQuotientEquiv (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) (K : Ideal (HolGerm (ComplexModel (d+t)))) :
    let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
    (Q ⊗[HolGerm (ComplexModel d)] (HolGerm (ComplexModel (d+t)) ⧸ K)) ≃ₐ[Q]
      ((Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
        Ideal.map (actualArtinianParameterPullback d t q (parameterQuotientMap d q I)
          (parameterQuotientMap_kills d q I)).toRingHom K) := by
  let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
  let A := HolGerm (ComplexModel (d+t))
  let R := HolGerm (ComplexModel d)
  let C := Q ⊗[ℂ] HolGerm (ComplexModel t)
  let e : (Q ⊗[R] A) ≃ₐ[Q] C := actualBaseChangeTensorParamEquiv d t q I
  let ψ := actualArtinianParameterPullback d t q (parameterQuotientMap d q I)
    (parameterQuotientMap_kills d q I)
  have hmap : Ideal.map e.toRingHom (Ideal.map
      (Algebra.TensorProduct.includeRight : A →ₐ[R] (Q ⊗[R] A)).toRingHom K) =
      Ideal.map ψ.toRingHom K := by
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro g
    change actualBaseChangeTensorParamEquiv d t q I (1 ⊗ₜ[R] g) = ψ g
    exact actualBaseChangeTensorRingEquiv_one_tmul d t q I g
  let P : Ideal (Q ⊗[R] A) := Ideal.map
    (Algebra.TensorProduct.includeRight : A →ₐ[R] (Q ⊗[R] A)).toRingHom K
  let P' : Ideal C := Ideal.map ψ.toRingHom K
  letI : P.IsTwoSided := ⟨fun b ha => mul_comm b _ ▸ P.smul_mem _ ha⟩
  letI : P'.IsTwoSided := ⟨fun b ha => mul_comm b _ ▸ P'.smul_mem _ ha⟩
  let f := Algebra.TensorProduct.tensorQuotientEquiv (R := R) Q A Q K
  have he : P' = Ideal.map e.toRingHom P := hmap.symm
  exact f.trans (Ideal.quotientEquivAlg P P' e he)

/-- Native flatness remains flat after actual finite-parameter base change. -/
theorem actualBaseChangedQuotient_flat (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel d))) (K : Ideal (HolGerm (ComplexModel (d+t))))
    (hflat : Module.Flat (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t)) ⧸ K)) :
    let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
    Module.Flat Q ((Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
      Ideal.map (actualArtinianParameterPullback d t q (parameterQuotientMap d q I)
        (parameterQuotientMap_kills d q I)).toRingHom K) := by
  letI := hflat
  exact Module.Flat.of_linearEquiv (actualBaseChangedQuotientEquiv d t q I K).symm.toLinearEquiv
end
end Hironaka.HironakaG10ArtinianFlatQuotient
