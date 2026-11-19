import Hironaka.Analytic.Unibranch.HironakaG10CoefficientHolomorphicReconstruction

/-! A parameter-linear kernel operator with the reference residue constructs
actual Q-valued holomorphic relation columns. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Set
open scoped TensorProduct
namespace Hironaka.Analytic.Unibranch.HironakaG10CoefficientOperatorRelation
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

def unitCoefficientColumn (b : Module.Basis ι ℂ Q) (K : Set X) {c : ℕ} (l : Fin c) :
    ι → Fin c → holSubalgebra K :=
  parameterTensorEquiv b ((1 : Q) ⊗ₜ[ℂ] (Pi.single l (1 : holSubalgebra K)))

omit [FiniteDimensional ℂ Q] in
theorem unitCoefficientColumn_residue (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (K : Set X) {c : ℕ} (l : Fin c) :
    coefficientResidue b ε (unitCoefficientColumn b K l) = Pi.single l 1 := by
  simp only [coefficientResidue, unitCoefficientColumn, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, residueTensor_tmul, map_one, one_smul]

/-- The actual coefficient operator produces actual holomorphic relation
columns on int K, retaining the whole reference residue there. -/
theorem exists_holomorphic_relation_of_coefficient_lift
    (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ) {K U : Set X} [CompactSpace K]
    (hKU : K ⊆ U) {a r c : ℕ} (F : Fin a → Fin r → X → Q)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (G₀ : Fin r → Fin c → holSubalgebra K) :
    letI := parameterCoefficientModule (E := Fin c → holSubalgebra K) b
    letI := parameterCoefficientModule (E := Fin r → holSubalgebra K) b
    ∀ (T : (ι → Fin c → holSubalgebra K) →ₗ[Q] (ι → Fin r → holSubalgebra K)),
      (∀ u, banachMatrixCLM b hKU F hF (T u) = 0) →
      (∀ u, T u - coefficientMap b (matrixOperator G₀).toLinearMap u ∈
        RingHom.ker ε.toRingHom • (⊤ : Submodule Q (ι → Fin r → holSubalgebra K))) →
      ∃ G : Fin r → Fin c → X → Q,
        (∀ j l, DifferentiableOn ℂ (G j l) (interior K)) ∧
        (∀ x ∈ interior K, ∀ i l, ∑ j, F i j x * G j l x = 0) ∧
        (∀ x (hx : x ∈ interior K), ∀ j l,
          ε (G j l x) = ((G₀ j l : holSubalgebra K) : C(K,ℂ)) ⟨x, interior_subset hx⟩) := by
  let := parameterCoefficientModule (E := Fin c → holSubalgebra K) b
  let := parameterCoefficientModule (E := Fin r → holSubalgebra K) b
  intro T hrel hmod
  let v : Fin c → ι → Fin r → holSubalgebra K := fun l => T (unitCoefficientColumn b K l)
  let G : Fin r → Fin c → X → Q := fun j l => coefficientFunction b K (v l) j
  refine ⟨G, fun j l => coefficientFunction_holomorphic b K (v l) j, ?_, ?_⟩
  · intro x hx i l
    let z : K := ⟨x, interior_subset hx⟩
    have he := banachMatrix_evaluation b hKU F hF z (v l) i
    have hz : banachMatrixCLM b hKU F hF (v l) = 0 := hrel (unitCoefficientColumn b K l)
    rw [hz, map_zero, Pi.zero_apply] at he
    change ∑ j, F i j (z : X) * coefficientFunction b K (v l) j (z : X) = 0
    simp_rw [coefficientFunction_on_window]
    exact he.symm
  · intro x hx j l
    let z : K := ⟨x, interior_subset hx⟩
    have hm := hmod (unitCoefficientColumn b K l)
    have hz := (coefficientResidue_eq_zero_iff b ε _).mpr hm
    rw [map_sub, sub_eq_zero] at hz
    have hr : coefficientResidue b ε (v l) = matrixOperator G₀ (Pi.single l 1) := by
      rw [show v l = T (unitCoefficientColumn b K l) from rfl, hz,
        coefficientResidue_coefficientMap, unitCoefficientColumn_residue]
      rfl
    change ε (coefficientFunction b K (v l) j (z : X)) =
      ((G₀ j l : holSubalgebra K) : C(K,ℂ)) z
    rw [coefficientFunction_residue_on_window, hr]
    simp [matrixOperator_apply, Pi.single_apply, apply_ite]
end
end Hironaka.Analytic.Unibranch.HironakaG10CoefficientOperatorRelation
