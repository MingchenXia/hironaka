import Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
import Hironaka.Resolution.HironakaG10FlatPolydiscAlgebra

/-! # Actual parameter-valued holomorphic matrices on the finite coefficient Banach spaces

The scalar block matrix is derived from the actual holomorphic matrix.
Its bounded complex-linear action is proved linear over the actual parameter
algebra.  Point evaluation detects whole operator relations and whole residue
ideal errors; no correctness or linearity certificate is assumed.
-/

set_option autoImplicit false
open scoped TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix

open Hironaka.HironakaG10FlatPolydiscAlgebra
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianCoefficientOperators
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianRelationLift
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix

noncomputable section

variable {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
  [FiniteDimensional ℂ Q] [NormedAddCommGroup X] [NormedSpace ℂ X]
  [Fintype ι] [DecidableEq ι]

/-- Scalar evaluation with its value included into the actual parameter algebra. -/
def scalarEvaluation {K : Set X} {r : Type*} (z : K) :
    (r → holSubalgebra K) →ₗ[ℂ] (r → Q) where
  toFun v j := algebraMap ℂ Q ((v j : C(K, ℂ)) z)
  map_add' v w := by ext j; simp
  map_smul' c v := by ext j; simp [Algebra.smul_def]

/-- Actual parameter-linear evaluation, obtained by scalar extension of
ordinary scalar point evaluation. -/
def coefficientEvaluation (b : Module.Basis ι ℂ Q) {K : Set X} {r : Type*} (z : K) :
    letI := parameterCoefficientModule (E := r → holSubalgebra K) b
    (ι → r → holSubalgebra K) →ₗ[Q] (r → Q) := by
  let := parameterCoefficientModule (E := r → holSubalgebra K) b
  exact (scalarEvaluation (Q := Q) z).liftBaseChange Q ∘ₗ
    (parameterCoefficientLinearEquiv (E := r → holSubalgebra K) b).toLinearMap

omit [FiniteDimensional ℂ Q] in
private theorem parameterTensorEquiv_symm_eq_sum {E : Type*} [AddCommGroup E] [Module ℂ E]
    (b : Module.Basis ι ℂ Q) (v : ι → E) :
    (parameterTensorEquiv b).symm v = ∑ l, b l ⊗ₜ[ℂ] v l := by
  apply (parameterTensorEquiv b).injective
  ext i
  simp [parameterTensorEquiv_tmul]

omit [FiniteDimensional ℂ Q] in
/-- Point evaluation reconstructs the original parameter-valued vector. -/
theorem coefficientEvaluation_apply (b : Module.Basis ι ℂ Q) {K : Set X} {r : Type*}
    (z : K) (v : ι → r → holSubalgebra K) (j : r) :
    letI := parameterCoefficientModule (E := r → holSubalgebra K) b
    coefficientEvaluation b z v j = ∑ l, ((v l j : C(K, ℂ)) z) • b l := by
  let := parameterCoefficientModule (E := r → holSubalgebra K) b
  change (scalarEvaluation (Q := Q) (r := r) z).liftBaseChange Q
    ((parameterTensorEquiv (E := r → holSubalgebra K) b).symm v) j = _
  rw [parameterTensorEquiv_symm_eq_sum (E := r → holSubalgebra K)]
  simp only [map_sum, LinearMap.liftBaseChange_tmul, Finset.sum_apply,
    scalarEvaluation, LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

omit [FiniteDimensional ℂ Q] in
/-- The original scalar coefficient is recovered by its basis functional. -/
theorem coordinate_coefficientEvaluation (b : Module.Basis ι ℂ Q) {K : Set X} {r : Type*}
    (z : K) (v : ι → r → holSubalgebra K) (j : r) (l : ι) :
    letI := parameterCoefficientModule (E := r → holSubalgebra K) b
    b.coord l (coefficientEvaluation b z v j) = (v l j : C(K, ℂ)) z := by
  let := parameterCoefficientModule (E := r → holSubalgebra K) b
  rw [coefficientEvaluation_apply]
  simp [map_smul, Finsupp.single_apply, eq_comm]

omit [FiniteDimensional ℂ Q] in
/-- Point evaluations jointly detect equality of whole coefficient vectors. -/
theorem coefficientEvaluation_jointly_injective (b : Module.Basis ι ℂ Q)
    {K : Set X} {r : Type*} {v w : ι → r → holSubalgebra K} :
    letI := parameterCoefficientModule (E := r → holSubalgebra K) b
    (∀ z : K, coefficientEvaluation b z v = coefficientEvaluation b z w) → v = w := by
  let := parameterCoefficientModule (E := r → holSubalgebra K) b
  intro h
  funext l j
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  rw [← coordinate_coefficientEvaluation b z v j l,
    ← coordinate_coefficientEvaluation b z w j l, h z]

/-- The actual scalar block coefficients, restricted as genuine elements of B(K). -/
def banachBlockMatrix (b : Module.Basis ι ℂ Q) {K U : Set X} (hKU : K ⊆ U)
    {a r : Type*} (F : a → r → X → Q)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) :
    (a × ι) → (r × ι) → holSubalgebra K :=
  fun p q => restrict K hKU (complexBlockMatrix b F p q)
    ((b.coord p.2).toContinuousLinearMap.differentiable.comp_differentiableOn
      ((hF p.1 q.1).mul_const (b q.2)))

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem banachBlockMatrix_apply (b : Module.Basis ι ℂ Q) {K U : Set X}
    (hKU : K ⊆ U) {a r : Type*} (F : a → r → X → Q)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) (p : a × ι) (q : r × ι) (z : K) :
    (banachBlockMatrix b hKU F hF p q : C(K, ℂ)) z =
      b.coord p.2 (F p.1 q.1 z * b q.2) := rfl

/-- Bounded complex-linear matrix action on the original finite product norms. -/
def banachMatrixCLM (b : Module.Basis ι ℂ Q) {K U : Set X} [CompactSpace K]
    (hKU : K ⊆ U) {a r : Type*} [Fintype a] [Fintype r]
    (F : a → r → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) :
    (ι → r → holSubalgebra K) →L[ℂ] (ι → a → holSubalgebra K) :=
  ContinuousLinearMap.pi fun k => ContinuousLinearMap.pi fun i =>
    ∑ j, ∑ l, (ContinuousLinearMap.mul ℂ (holSubalgebra K)
      (banachBlockMatrix b hKU F hF (i, k) (j, l))).comp
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : r => holSubalgebra K) j).comp
          (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => r → holSubalgebra K) l))

omit [DecidableEq ι] in
@[simp]
theorem banachMatrixCLM_apply (b : Module.Basis ι ℂ Q) {K U : Set X} [CompactSpace K]
    (hKU : K ⊆ U) {a r : Type*} [Fintype a] [Fintype r]
    (F : a → r → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (v : ι → r → holSubalgebra K) (k : ι) (i : a) :
    banachMatrixCLM b hKU F hF v k i =
      ∑ j, ∑ l, banachBlockMatrix b hKU F hF (i, k) (j, l) * v l j := by
  simp [banachMatrixCLM]

/-- The bounded block action is precisely the actual Q-valued matrix action
at every point of the original compact set. -/
theorem banachMatrix_evaluation (b : Module.Basis ι ℂ Q) {K U : Set X} [CompactSpace K]
    (hKU : K ⊆ U) {a r : Type*} [Fintype a] [Fintype r]
    (F : a → r → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (z : K) (v : ι → r → holSubalgebra K) (i : a) :
    letI := parameterCoefficientModule (E := r → holSubalgebra K) b
    letI := parameterCoefficientModule (E := a → holSubalgebra K) b
    coefficientEvaluation b z (banachMatrixCLM b hKU F hF v) i =
      ∑ j, F i j z * coefficientEvaluation b z v j := by
  let := parameterCoefficientModule (E := r → holSubalgebra K) b
  let := parameterCoefficientModule (E := a → holSubalgebra K) b
  apply b.repr.injective
  apply Finsupp.ext
  intro k
  change b.coord k (coefficientEvaluation b z (banachMatrixCLM b hKU F hF v) i) = _
  rw [coordinate_coefficientEvaluation]
  simp [banachMatrixCLM_apply, coefficientEvaluation_apply, Finset.mul_sum,
    map_sum, map_smul, mul_comm]

theorem banachMatrixCLM_map_smul (b : Module.Basis ι ℂ Q) {K U : Set X} [CompactSpace K]
    (hKU : K ⊆ U) {a r : Type*} [Fintype a] [Fintype r]
    (F : a → r → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) :
    letI := parameterCoefficientModule (E := r → holSubalgebra K) b
    letI := parameterCoefficientModule (E := a → holSubalgebra K) b
    letI : SMul Q (ι → r → holSubalgebra K) :=
      (parameterCoefficientModule (E := r → holSubalgebra K) b).toSMul
    letI : SMul Q (ι → a → holSubalgebra K) :=
      (parameterCoefficientModule (E := a → holSubalgebra K) b).toSMul
    ∀ (q : Q) (v : ι → r → holSubalgebra K),
      banachMatrixCLM b hKU F hF (q • v : ι → r → holSubalgebra K) =
        (q • banachMatrixCLM b hKU F hF v : ι → a → holSubalgebra K) := by
  let := parameterCoefficientModule (E := r → holSubalgebra K) b
  let := parameterCoefficientModule (E := a → holSubalgebra K) b
  let : SMul Q (ι → r → holSubalgebra K) :=
    (parameterCoefficientModule (E := r → holSubalgebra K) b).toSMul
  let : SMul Q (ι → a → holSubalgebra K) :=
    (parameterCoefficientModule (E := a → holSubalgebra K) b).toSMul
  intro q v
  apply coefficientEvaluation_jointly_injective (r := a) b
  intro z
  ext i
  simp only [banachMatrix_evaluation, map_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _

/-- The same actual bounded complex-linear map is genuinely Q-linear for
the transported whole scalar-extension actions. -/
def banachMatrixLinear (b : Module.Basis ι ℂ Q) {K U : Set X} [CompactSpace K]
    (hKU : K ⊆ U) {a r : Type*} [Fintype a] [Fintype r]
    (F : a → r → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) :
    letI := parameterCoefficientModule (E := r → holSubalgebra K) b
    letI := parameterCoefficientModule (E := a → holSubalgebra K) b
    (ι → r → holSubalgebra K) →ₗ[Q] (ι → a → holSubalgebra K) := by
  let := parameterCoefficientModule (E := r → holSubalgebra K) b
  let := parameterCoefficientModule (E := a → holSubalgebra K) b
  exact
    { toFun := fun v => banachMatrixCLM b hKU F hF v
      map_add' := fun v w => (banachMatrixCLM b hKU F hF).map_add v w
      map_smul' := fun q v => banachMatrixCLM_map_smul b hKU F hF q v }

@[simp]
theorem banachMatrixLinear_apply (b : Module.Basis ι ℂ Q) {K U : Set X} [CompactSpace K]
    (hKU : K ⊆ U) {a r : Type*} [Fintype a] [Fintype r]
    (F : a → r → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (v : ι → r → holSubalgebra K) :
    letI := parameterCoefficientModule (E := r → holSubalgebra K) b
    letI := parameterCoefficientModule (E := a → holSubalgebra K) b
    banachMatrixLinear b hKU F hF v = banachMatrixCLM b hKU F hF v := rfl

/-- An actual matrix relation on K is a zero composition of the whole bounded operators. -/
theorem banachMatrix_comp_eq_zero (b : Module.Basis ι ℂ Q) {K U : Set X} [CompactSpace K]
    (hKU : K ⊆ U) {a r c : Type*} [Fintype a] [Fintype r] [Fintype c]
    (F : a → r → X → Q) (G : r → c → X → Q)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (hG : ∀ j l, DifferentiableOn ℂ (G j l) U)
    (hFG : ∀ (z : K) i l, ∑ j, F i j z * G j l z = 0) :
    (banachMatrixCLM b hKU F hF).comp (banachMatrixCLM b hKU G hG) = 0 := by
  let := parameterCoefficientModule (E := c → holSubalgebra K) b
  let := parameterCoefficientModule (E := r → holSubalgebra K) b
  let := parameterCoefficientModule (E := a → holSubalgebra K) b
  apply ContinuousLinearMap.ext
  intro v
  apply coefficientEvaluation_jointly_injective b
  intro z
  ext i
  simp only [ContinuousLinearMap.comp_apply, zero_apply,
    banachMatrix_evaluation, map_zero, Pi.zero_apply]
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hFG, zero_mul, Finset.sum_const_zero]

/-- Residue reduction of the entire coefficient module, not a pointwise
ideal membership predicate. -/
def coefficientResidue {E : Type*} [AddCommGroup E] [Module ℂ E]
    (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ) : (ι → E) →ₗ[ℂ] E :=
  (residueTensor ε).comp (parameterTensorEquiv (E := E) b).symm.toLinearMap

omit [FiniteDimensional ℂ Q] in
theorem coefficientResidue_apply {E : Type*} [AddCommGroup E] [Module ℂ E]
    (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ) (v : ι → E) :
    coefficientResidue b ε v = ∑ l, ε (b l) • v l := by
  change residueTensor ε ((parameterTensorEquiv (E := E) b).symm v) = _
  rw [parameterTensorEquiv_symm_eq_sum]
  simp

omit [FiniteDimensional ℂ Q] in
/-- The whole kernel of coefficient residue is exactly the whole residue-ideal multiple. -/
theorem coefficientResidue_eq_zero_iff {E : Type*} [AddCommGroup E] [Module ℂ E]
    (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ) (v : ι → E) :
    letI := parameterCoefficientModule (E := E) b
    coefficientResidue b ε v = 0 ↔
      v ∈ RingHom.ker ε.toRingHom • (⊤ : Submodule Q (ι → E)) := by
  let := parameterCoefficientModule (E := E) b
  let e := parameterCoefficientLinearEquiv (E := E) b
  have hmap : (RingHom.ker ε.toRingHom • (⊤ : Submodule Q (ι → E))).map e.toLinearMap =
      RingHom.ker ε.toRingHom • (⊤ : Submodule Q (Q ⊗[ℂ] E)) := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective]
  change residueTensor ε (e v) = 0 ↔ _
  rw [residueTensor_eq_zero_iff_mem_ideal_smul, ← hmap]
  constructor
  · rintro ⟨w, hw, heq⟩
    exact e.injective heq ▸ hw
  · intro hv
    exact Submodule.mem_map_of_mem hv

omit [FiniteDimensional ℂ Q] in
/-- Coefficientwise extension of a reference operator commutes with whole residue. -/
theorem coefficientResidue_coefficientMap {E N : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup N] [Module ℂ N] (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    (f : E →ₗ[ℂ] N) (v : ι → E) :
    letI := parameterCoefficientModule (E := E) b
    letI := parameterCoefficientModule (E := N) b
    coefficientResidue b ε (coefficientMap b f v) = f (coefficientResidue b ε v) := by
  let := parameterCoefficientModule (E := E) b
  let := parameterCoefficientModule (E := N) b
  simp only [coefficientResidue_apply, coefficientMap_apply, map_sum, map_smul]

omit [FiniteDimensional ℂ Q] in
/-- Evaluating whole scalar residue equals applying residue after actual
parameter evaluation. -/
theorem coefficientResidue_evaluation (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    {K : Set X} {r : Type*} (v : ι → r → holSubalgebra K) (z : K) (j : r) :
    letI := parameterCoefficientModule (E := r → holSubalgebra K) b
    (coefficientResidue b ε v j : C(K, ℂ)) z = ε (coefficientEvaluation b z v j) := by
  let := parameterCoefficientModule (E := r → holSubalgebra K) b
  simp [coefficientResidue_apply, coefficientEvaluation_apply, map_sum, map_smul, mul_comm]

/-- Actual entrywise residue agreement gives equality of the entire scalar
B(K)-valued operator outputs. -/
theorem coefficientResidue_banachMatrix (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    {K U : Set X} [CompactSpace K] (hKU : K ⊆ U)
    {a r : Type*} [Fintype a] [Fintype r]
    (F : a → r → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (F₀ : a → r → holSubalgebra K)
    (hred : ∀ (z : K) i j, ε (F i j z) = (F₀ i j : C(K, ℂ)) z)
    (v : ι → r → holSubalgebra K) :
    coefficientResidue b ε (banachMatrixCLM b hKU F hF v) =
      matrixOperator F₀ (coefficientResidue b ε v) := by
  let := parameterCoefficientModule (E := r → holSubalgebra K) b
  let := parameterCoefficientModule (E := a → holSubalgebra K) b
  funext i
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  rw [coefficientResidue_evaluation, banachMatrix_evaluation]
  simp [map_sum, map_mul, hred, matrixOperator_apply, coefficientResidue_evaluation]

/-- The actual Q-linear matrix differs from the coefficientwise reference
operator by a whole residue-ideal multiple, on every source vector. -/
theorem banachMatrix_reduction_error (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    {K U : Set X} [CompactSpace K] (hKU : K ⊆ U)
    {a r : Type*} [Fintype a] [Fintype r]
    (F : a → r → X → Q) (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    (F₀ : a → r → holSubalgebra K)
    (hred : ∀ (z : K) i j, ε (F i j z) = (F₀ i j : C(K, ℂ)) z) :
    letI := parameterCoefficientModule (E := r → holSubalgebra K) b
    letI := parameterCoefficientModule (E := a → holSubalgebra K) b
    letI : SMul Q (ι → a → holSubalgebra K) :=
      (parameterCoefficientModule (E := a → holSubalgebra K) b).toSMul
    letI : DistribMulAction Q (ι → a → holSubalgebra K) :=
      (parameterCoefficientModule (E := a → holSubalgebra K) b).toDistribMulAction
    letI : IsScalarTower Q Q (ι → a → holSubalgebra K) := ⟨mul_smul⟩
    ∀ v : ι → r → holSubalgebra K, banachMatrixLinear b hKU F hF v -
      coefficientMap (E := r → holSubalgebra K) (F := a → holSubalgebra K)
        b (matrixOperator F₀).toLinearMap v ∈
        (RingHom.ker ε.toRingHom • ⊤ : Submodule Q (ι → a → holSubalgebra K)) := by
  let := parameterCoefficientModule (E := r → holSubalgebra K) b
  let := parameterCoefficientModule (E := a → holSubalgebra K) b
  let : SMul Q (ι → a → holSubalgebra K) :=
    (parameterCoefficientModule (E := a → holSubalgebra K) b).toSMul
  let : DistribMulAction Q (ι → a → holSubalgebra K) :=
    (parameterCoefficientModule (E := a → holSubalgebra K) b).toDistribMulAction
  let : IsScalarTower Q Q (ι → a → holSubalgebra K) := ⟨mul_smul⟩
  intro v
  apply (coefficientResidue_eq_zero_iff b ε _).mp
  rw [map_sub, banachMatrixLinear_apply, coefficientResidue_banachMatrix b ε hKU F hF F₀ hred,
    coefficientResidue_coefficientMap]
  exact sub_self _

end
end Hironaka.Analytic.Unibranch.HironakaG10ArtinianBanachMatrix
