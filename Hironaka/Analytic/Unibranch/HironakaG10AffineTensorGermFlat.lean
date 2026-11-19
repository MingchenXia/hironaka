import Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
import Hironaka.Analytic.Unibranch.HironakaG10HigherRankArtinianBaseChange

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10AffineTensorGermFlat
open Hironaka HolGerm OkaRelationSheaf OkaGermBridge
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10HigherRankArtinianBaseChange
noncomputable section

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
local instance : Algebra ℂ (HolGerm X) := (HolGerm.constHom : ℂ →+* HolGerm X).toAlgebra

/-- Whole scalar-germ pullback under an actual complex-linear equivalence. -/
def germLinearAlgEquiv (L : X ≃L[ℂ] X) : HolGerm X ≃ₐ[ℂ] HolGerm X where
  toRingEquiv := HolGerm.comapEquiv L
  commutes' _ := rfl

def affineAt (L : X ≃L[ℂ] X) (z w x : X) : X := w + L (x - z)

/-- The actual recentered scalar germ is sent to the literal affine pullback. -/
theorem germAt_affine (L : X ≃L[ℂ] X) (z w : X) (f : X → ℂ)
    (hf : HolAt f w) :
    germLinearAlgEquiv L (germAt w f) = germAt z (fun x => f (affineAt L z w x)) := by
  have hφ : Continuous (affineAt L z w) :=
    continuous_const.add (L.continuous.comp (continuous_id.sub continuous_const))
  have hφd : ∀ x, DifferentiableAt ℂ (affineAt L z w) x := by
    intro x
    exact (differentiableAt_const w).add (L.differentiableAt.comp x (differentiableAt_id.sub (differentiableAt_const z)))
  have hcomp : HolAt (fun x => f (affineAt L z w x)) z := by
    have hf' : HolAt f (affineAt L z w z) := by simpa [affineAt] using hf
    exact hf'.comp hφ hφd
  rw [germAt_of_holAt hf, germAt_of_holAt hcomp]
  change HolGerm.comapEquiv L (HolGerm.mk (fun x => f (w + x)) hf.translate) = _
  rw [HolGerm.comapEquiv_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun x => by simp [affineAt]

/-- The induced tensor equivalence fixes the entire Q parameter algebra. -/
def tensorGermLinearAlgEquiv {Q : Type*} [CommRing Q] [Algebra ℂ Q]
    (L : X ≃L[ℂ] X) : (Q ⊗[ℂ] HolGerm X) ≃ₐ[Q] (Q ⊗[ℂ] HolGerm X) :=
  Algebra.TensorProduct.congr (AlgEquiv.refl : Q ≃ₐ[Q] Q) (germLinearAlgEquiv L)

/-- Every coordinate of the actual finite-parameter tensor germ follows the
same affine pullback, without truncating the source germ. -/
theorem tensorGermAt_affine
    {Q ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Q)
    (L : X ≃L[ℂ] X) (z w : X) (f : X → Q)
    (hf : ∀ᶠ x in 𝓝 w, DifferentiableAt ℂ f x) :
    tensorGermLinearAlgEquiv L (tensorGermAt b w f) =
      tensorGermAt b z (fun x => f (affineAt L z w x)) := by
  simp only [tensorGermAt, map_sum, tensorGermLinearAlgEquiv,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  apply Finset.sum_congr rfl
  intro i hi
  exact congrArg (fun q => b i ⊗ₜ[ℂ] q)
    (germAt_affine L z w (fun x => b.coord i (f x)) (holomorphic_coordinate b i hf))

/-- The actual finite matrix tensor-germ cokernels are Q-linearly equivalent
under the literal centred affine fibre coordinate change. -/
def affineMatrixGermCokernelEquiv
    {Q ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Q)
    {a k : ℕ} (L : X ≃L[ℂ] X) (z w : X) (F : Fin a → Fin k → X → Q)
    (hF : ∀ i j, ∀ᶠ x in 𝓝 w, DifferentiableAt ℂ (F i j) x) :
    ((Fin a → Q ⊗[ℂ] HolGerm X) ⧸ LinearMap.range (matrixGermMap b w F)) ≃ₗ[Q]
      ((Fin a → Q ⊗[ℂ] HolGerm X) ⧸ LinearMap.range
        (matrixGermMap b z (fun i j x => F i j (affineAt L z w x)))) := by
  let M : Matrix (Fin a) (Fin k) (Q ⊗[ℂ] HolGerm X) :=
    fun i j => tensorGermAt b w (F i j)
  have hmat : (fun i j => tensorGermLinearAlgEquiv (Q := Q) L (M i j)) =
      (fun i j => tensorGermAt b z (fun x => F i j (affineAt L z w x))) := by
    funext i j
    exact tensorGermAt_affine b L z w (F i j) (hF i j)
  have h := matrixCokernelEquiv (tensorGermLinearAlgEquiv (Q := Q) L) M
  rw [hmat] at h
  exact h

/-- Flatness is preserved by the same actual affine fibre-coordinate change. -/
theorem matrixGermMap_flat_iff_affine
    {Q ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Q)
    {a k : ℕ} (L : X ≃L[ℂ] X) (z w : X) (F : Fin a → Fin k → X → Q)
    (hF : ∀ i j, ∀ᶠ x in 𝓝 w, DifferentiableAt ℂ (F i j) x) :
    Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm X) ⧸ LinearMap.range (matrixGermMap b w F)) ↔
    Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm X) ⧸ LinearMap.range
      (matrixGermMap b z (fun i j x => F i j (affineAt L z w x)))) :=
  Module.Flat.equiv_iff (affineMatrixGermCokernelEquiv b L z w F hF)

/-- Nonzero complex scalar multiplication is an actual fibre-coordinate equivalence. -/
def scalarLinearEquiv (r : ℂ) (hr : r ≠ 0) : X ≃L[ℂ] X where
  toFun x := r • x
  invFun x := r⁻¹ • x
  map_add' x y := smul_add _ _ _
  map_smul' a x := by simp only [RingHom.id_apply, smul_smul]; rw [mul_comm]
  left_inv x := by simp [smul_smul,hr]
  right_inv x := by simp [smul_smul,hr]
  continuous_toFun := continuous_const.smul continuous_id
  continuous_invFun := continuous_const.smul continuous_id

/-- Positive real contraction preserves the actual finite-parameter tensor
matrix-germ flatness, at the corresponding contracted source point. -/
theorem matrixGermMap_flat_iff_radial
    {Q ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ Q)
    {a k : ℕ} (c : X) (r : ℝ) (hr : 0 < r) (z : X)
    (F : Fin a → Fin k → X → Q)
    (hF : ∀ i j, ∀ᶠ x in 𝓝 (c + r • (z-c)), DifferentiableAt ℂ (F i j) x) :
    Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm X) ⧸ LinearMap.range
      (matrixGermMap b (c + r • (z-c)) F)) ↔
    Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm X) ⧸ LinearMap.range
      (matrixGermMap b z (fun i j x => F i j (c + r • (x-c))))) := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hr)
  let L := scalarLinearEquiv (X := X) (r : ℂ) hr'
  have hφ : ∀ x, affineAt L z (c + r • (z-c)) x = c + r • (x-c) := by
    intro x
    change (c + r • (z-c)) + ((r : ℂ) • (x-z)) = c + r • (x-c)
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    module
  have hfun : (fun i j x => F i j (affineAt L z (c + r • (z-c)) x)) =
      (fun i j x => F i j (c + r • (x-c))) := by
    funext i j x
    rw [hφ]
  have h := matrixGermMap_flat_iff_affine b L z (c + r • (z-c)) F hF
  rw [hfun] at h
  exact h

end
end Hironaka.Analytic.Unibranch.HironakaG10AffineTensorGermFlat
