import Hironaka.Analytic.Unibranch.HironakaG10TensorGermResidueCongruence
import Hironaka.Analytic.Unibranch.HironakaG10MatrixIdealCongruence
import Hironaka.Analytic.Unibranch.HironakaG10NilpotentMatrixFlatness

/-! An actual holomorphic lift of the complete reference relation makes
the literal Artinian tensor-germ matrix cokernel flat. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Filter
open scoped Topology TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrixFlat
open Hironaka OkaRelationSheaf OkaGermBridge
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CompactArtinianRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10TensorGermResidueCongruence
  Hironaka.Analytic.Unibranch.HironakaG10MatrixIdealCongruence
  Hironaka.Analytic.Unibranch.HironakaG10NilpotentMatrixFlatness
  Hironaka.Analytic.Unibranch.HironakaG10HigherRankBaseChange
noncomputable section
local instance {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] :
    Algebra ℂ (HolGerm X) := (HolGerm.constHom : ℂ →+* HolGerm X).toAlgebra

/-- The lifted matrices and their residue are literal holomorphic functions;
the conclusion is the entire actual tensor-germ matrix cokernel. -/
theorem matrixGermMap_flat_of_holomorphic_relation_lift
    {Q X ι : Type} [NormedCommRing Q] [NormedAlgebra ℂ Q] [FiniteDimensional ℂ Q]
    [NormedAddCommGroup X] [NormedSpace ℂ X] [Fintype ι] [DecidableEq ι]
    {a b c : ℕ} (basis : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (hnil : ∃ n : ℕ, (RingHom.ker ε.toRingHom) ^ n = ⊥) {z : X}
    (F : Fin a → Fin b → X → Q) (G : Fin b → Fin c → X → Q)
    (F₀ : Fin a → Fin b → X → ℂ) (G₀ : Fin b → Fin c → X → ℂ)
    (hF : ∀ i j, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (F i j) x)
    (hG : ∀ j l, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (G j l) x)
    (hF₀ : ∀ i j, HolAt (F₀ i j) z) (hG₀ : ∀ j l, HolAt (G₀ j l) z)
    (hresF : ∀ i j, ∀ᶠ x in 𝓝 z, ε (F i j x) = F₀ i j x)
    (hresG : ∀ j l, ∀ᶠ x in 𝓝 z, ε (G j l x) = G₀ j l x)
    (hFG : ∀ᶠ x in 𝓝 z, ∀ i l, ∑ j, F i j x * G j l x = 0)
    (hcomp : ∀ w, (Matrix.mulVecLin (fun i j => germAt z (F₀ i j)))
      ((Matrix.mulVecLin (fun j l => germAt z (G₀ j l))) w) = 0)
    (hex : ∀ u, (Matrix.mulVecLin (fun i j => germAt z (F₀ i j))) u = 0 →
      ∃ w, (Matrix.mulVecLin (fun j l => germAt z (G₀ j l))) w = u) :
    Module.Flat Q ((Fin a → Q ⊗[ℂ] HolGerm X) ⧸ LinearMap.range (matrixGermMap basis z F)) := by
  let M : Matrix (Fin a) (Fin b) (HolGerm X) := fun i j => germAt z (F₀ i j)
  let N : Matrix (Fin b) (Fin c) (HolGerm X) := fun j l => germAt z (G₀ j l)
  let FM : Matrix (Fin a) (Fin b) (Q ⊗[ℂ] HolGerm X) := fun i j => tensorGermAt basis z (F i j)
  let GM : Matrix (Fin b) (Fin c) (Q ⊗[ℂ] HolGerm X) := fun j l => tensorGermAt basis z (G j l)
  have hentry : ∀ i l, ∑ j, FM i j * GM j l = 0 :=
    (matrix_tensor_relation_iff basis hF hG).mpr hFG
  have hmat : FM * GM = 0 := by
    ext i l
    exact hentry i l
  have hFG' (w : Fin c → Q ⊗[ℂ] HolGerm X) : FM.mulVecLin (GM.mulVecLin w) = 0 := by
    change FM.mulVec (GM.mulVec w) = 0
    rw [Matrix.mulVec_mulVec, hmat]
    simp
  have hmodF := matrix_map_congruent_of_entries (RingHom.ker ε.toRingHom) FM
    (baseMatrix ℂ (HolGerm X) Q M) (fun i j =>
      tensorGermAt_sub_reference_mem_residue_ideal basis ε (hF i j) (hF₀ i j) (hresF i j))
  have hmodG := matrix_map_congruent_of_entries (RingHom.ker ε.toRingHom) GM
    (baseMatrix ℂ (HolGerm X) Q N) (fun j l =>
      tensorGermAt_sub_reference_mem_residue_ideal basis ε (hG j l) (hG₀ j l) (hresG j l))
  exact matrixCokernel_flat_of_nilpotent_lifted_relation (RingHom.ker ε.toRingHom) hnil
    M N hcomp hex FM GM hFG' hmodF hmodG
end
end Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrixFlat
