import Hironaka.Analytic.Unibranch.HironakaG10HigherRankBaseChange
import Hironaka.Resolution.HironakaG10ArtinianFlatQuotient
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10HigherRankArtinianBaseChange
open Hironaka Hironaka
  HironakaRelativeNormalIdeal HironakaG10ArtinianParameterPullback
  HironakaG10ArtinianBaseChange HironakaG10ArtinianFlatQuotient
  Hironaka.Analytic.Unibranch.HironakaG10HigherRankBaseChange
noncomputable section

variable {S A B : Type} [CommRing S] [CommRing A] [CommRing B] [Algebra S A] [Algebra S B]
variable {a b : ℕ}

/-- Applying a scalar-preserving algebra equivalence entrywise commutes
with the entire finite matrix map. -/
theorem matrixEquiv_commutes (e : A ≃ₐ[S] B) (M : Matrix (Fin a) (Fin b) A) :
    (LinearEquiv.piCongrRight (fun _ : Fin a => e.toLinearEquiv)).toLinearMap.comp
      (M.mulVecLin.restrictScalars S) =
    ((Matrix.mulVecLin (fun i j => e (M i j))).restrictScalars S).comp
      (LinearEquiv.piCongrRight (fun _ : Fin b => e.toLinearEquiv)).toLinearMap := by
  classical
  apply LinearMap.ext
  intro v
  funext i
  change e (∑ j, M i j * v j) = ∑ j, e (M i j) * e (v j)
  simp

/-- Transporting the entries of a matrix through an algebra equivalence
identifies the whole cokernel as a module over the common scalar ring. -/
def matrixCokernelEquiv (e : A ≃ₐ[S] B) (M : Matrix (Fin a) (Fin b) A) :
    ((Fin a → A) ⧸ LinearMap.range (M.mulVecLin.restrictScalars S)) ≃ₗ[S]
      ((Fin a → B) ⧸ LinearMap.range
        ((Matrix.mulVecLin (fun i j => e (M i j))).restrictScalars S)) := by
  apply Submodule.Quotient.equiv _ _ (LinearEquiv.piCongrRight (fun _ : Fin a => e.toLinearEquiv))
  rw [← LinearMap.range_comp, matrixEquiv_commutes, LinearMap.range_comp]
  simp

local instance (n : ℕ) : Algebra ℂ (HolGerm (ComplexModel n)) :=
  (HolGerm.constHom : ℂ →+* HolGerm (ComplexModel n)).toAlgebra
local instance (d t : ℕ) : Algebra (HolGerm (ComplexModel d)) (HolGerm (ComplexModel (d+t))) :=
  tangentAlgebra d t

/-- The entire cokernel of an arbitrary-rank original joint-germ matrix,
after actual finite-parameter base change, is the literal cokernel of its
substituted matrix over the full tensor-fibre germ. -/
def actualJointMatrixCokernelEquiv (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel d)))
    (M : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t)))) :
    let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
    (Q ⊗[HolGerm (ComplexModel d)] ((Fin a → HolGerm (ComplexModel (d+t))) ⧸
      LinearMap.range M.mulVecLin)) ≃ₗ[Q]
    ((Fin a → Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
      LinearMap.range ((Matrix.mulVecLin (fun i j => actualArtinianParameterPullback d t q
        (parameterQuotientMap d q I) (parameterQuotientMap_kills d q I) (M i j))).restrictScalars Q)) := by
  let R := HolGerm (ComplexModel d)
  let A := HolGerm (ComplexModel (d+t))
  let Q := R ⧸ truncatedParameterIdeal d q I
  let e : (Q ⊗[R] A) ≃ₐ[Q] (Q ⊗[ℂ] HolGerm (ComplexModel t)) :=
    actualBaseChangeTensorParamEquiv d t q I
  let P : Matrix (Fin a) (Fin b) (Q ⊗[R] A) := baseMatrix R A Q M
  have hentries : (fun i j => e (P i j)) = (fun i j =>
      actualArtinianParameterPullback d t q (parameterQuotientMap d q I)
        (parameterQuotientMap_kills d q I) (M i j)) := by
    funext i j
    exact actualBaseChangeTensorRingEquiv_one_tmul d t q I (M i j)
  let E := matrixCokernelEquiv (S := Q) (A := Q ⊗[R] A)
    (B := Q ⊗[ℂ] HolGerm (ComplexModel t)) e P
  rw [hentries] at E
  exact (baseMatrixCokernelEquiv R A Q M).trans E

/-- Native flatness of the full original joint-germ matrix cokernel
survives actual finite-parameter substitution in every finite output rank. -/
theorem actualJointMatrixCokernel_flat (d t q : ℕ)
    (I : Ideal (HolGerm (ComplexModel d)))
    (M : Matrix (Fin a) (Fin b) (HolGerm (ComplexModel (d+t))))
    (hflat : Module.Flat (HolGerm (ComplexModel d))
      ((Fin a → HolGerm (ComplexModel (d+t))) ⧸ LinearMap.range M.mulVecLin)) :
    let Q := HolGerm (ComplexModel d) ⧸ truncatedParameterIdeal d q I
    Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm (ComplexModel t)) ⧸
      LinearMap.range ((Matrix.mulVecLin (fun i j => actualArtinianParameterPullback d t q
        (parameterQuotientMap d q I) (parameterQuotientMap_kills d q I) (M i j))).restrictScalars Q)) := by
  let := hflat
  exact Module.Flat.of_linearEquiv (actualJointMatrixCokernelEquiv d t q I M).symm
end
end Hironaka.Analytic.Unibranch.HironakaG10HigherRankArtinianBaseChange
