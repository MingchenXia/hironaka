import Hironaka.Analytic.Unibranch.HironakaG10CoefficientHolomorphicReconstruction

/-! Actual coefficient kernel columns with prescribed residues reconstruct
holomorphic Q-valued relation columns. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10CoefficientColumnRelation
open Hironaka.HironakaG10FlatPolydiscAlgebra
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
  Hironaka.Analytic.Unibranch.HironakaG10CoefficientHolomorphicReconstruction
noncomputable section
variable {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
  [FiniteDimensional ℂ Q] [NormedAddCommGroup X] [NormedSpace ℂ X]
  [Fintype ι] [DecidableEq ι]

/-- Actual kernel coefficient columns with prescribed whole residue reconstruct holomorphic relations. -/
theorem exists_holomorphic_relation_of_coefficient_columns
    (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ) {K U : Set X} [CompactSpace K]
    (hKU : K ⊆ U) {a r c : ℕ} (F : Fin a → Fin r → X → Q)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (G₀ : Fin r → Fin c → holSubalgebra K) :
    ∀ (v : Fin c → ι → Fin r → holSubalgebra K),
      (∀ l, banachMatrixCLM b hKU F hF (v l) = 0) →
      (∀ l, coefficientResidue b ε (v l) = fun j => G₀ j l) →
      ∃ G : Fin r → Fin c → X → Q,
        (∀ j l, DifferentiableOn ℂ (G j l) (interior K)) ∧
        (∀ x ∈ interior K, ∀ i l, ∑ j, F i j x * G j l x = 0) ∧
        (∀ x (hx : x ∈ interior K), ∀ j l,
          ε (G j l x) = ((G₀ j l : holSubalgebra K) : C(K,ℂ)) ⟨x, interior_subset hx⟩) := by
  intro v hrel hres
  let G : Fin r → Fin c → X → Q := fun j l => coefficientFunction b K (v l) j
  refine ⟨G, fun j l => coefficientFunction_holomorphic b K (v l) j, ?_, ?_⟩
  · intro x hx i l
    let z : K := ⟨x, interior_subset hx⟩
    have he := banachMatrix_evaluation b hKU F hF z (v l) i
    have hz : banachMatrixCLM b hKU F hF (v l) = 0 := hrel l
    rw [hz, map_zero, Pi.zero_apply] at he
    change ∑ j, F i j (z : X) * coefficientFunction b K (v l) j (z : X) = 0
    simp_rw [coefficientFunction_on_window]
    exact he.symm
  · intro x hx j l
    let z : K := ⟨x, interior_subset hx⟩
    have hr : coefficientResidue b ε (v l) = fun j => G₀ j l := hres l
    change ε (coefficientFunction b K (v l) j (z : X)) =
      ((G₀ j l : holSubalgebra K) : C(K,ℂ)) z
    rw [coefficientFunction_residue_on_window, hr]
end
end Hironaka.Analytic.Unibranch.HironakaG10CoefficientColumnRelation
