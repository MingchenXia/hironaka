import Hironaka.Manifold.HolomorphicContDiff
import Hironaka.Resolution.HironakaG10FlatFrischHolomorphicFlattener
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # The Banach algebra `B(K)` and the bounded operators of holomorphic matrices

For a compact subset `K` of a complex normed space `E` (in Frisch 1968 and Douady 1966:
a compact polydisc), `B(K)` is the algebra of continuous functions on `K` that are
holomorphic on the interior of `K`, with the supremum norm.

* `holSubalgebra K`: `B(K)` as a subalgebra of `C(K,ℂ)`; `isClosed_holSubalgebra`: it is
  closed (several-variable Weierstrass theorem
  `Hironaka.differentiableAt_of_tendstoUniformlyOn_ball`), hence a commutative Banach
  algebra (`CompleteSpace` instance; the normed algebra structure is inherited).
* `restrict`: a function holomorphic on a set `U ⊇ K` defines an element of `B(K)`, with
  `norm_restrict_le`; `restrictHom : holOn U →+* B(K)` is the restriction ring map from the
  ring of holomorphic functions on `U` used by the relative-dimension-0 flattener.
* `matrixOperator`: a matrix `A` over ANY normed `ℂ`-algebra `R` acts by a bounded operator
  `R^p → R^q`, `norm_matrixOperator_le`; `matrixOperatorCLM` makes `A ↦ matrixOperator A` a
  continuous linear map, so holomorphic families of matrices give holomorphic operator
  families (`differentiableAt_matrixOperator`).

This is the first absent parent of Frisch's Lemme 2 (FLAT03-FRISCH-CONTRACT.md, item 1); no
privilege statement is made. BP: hironaka-g10-flat-polydisc-algebra.tex. -/
set_option autoImplicit false
open Set Filter Metric
open scoped Topology
namespace Hironaka.HironakaG10FlatPolydiscAlgebra
noncomputable section
open Classical

section BK
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Extension by zero of a function on a subset. -/
def extendZero (K : Set E) (f : K → ℂ) : E → ℂ := fun z => if hz : z ∈ K then f ⟨z, hz⟩ else 0

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem extendZero_of_mem (K : Set E) (f : K → ℂ) {z : E} (hz : z ∈ K) :
    extendZero K f z = f ⟨z, hz⟩ := dif_pos hz

/-- `B(K)`: continuous functions on `K` that are holomorphic on the interior of `K`. -/
def holSubalgebra (K : Set E) : Subalgebra ℂ C(K, ℂ) where
  carrier := {f | DifferentiableOn ℂ (extendZero K f) (interior K)}
  mul_mem' {f g} hf hg := by
    refine (DifferentiableOn.mul hf hg).congr fun z hz => ?_
    have hzK := interior_subset hz
    simp only [Pi.mul_apply, extendZero_of_mem K _ hzK, ContinuousMap.mul_apply]
  add_mem' {f g} hf hg := by
    refine (DifferentiableOn.add hf hg).congr fun z hz => ?_
    have hzK := interior_subset hz
    simp only [Pi.add_apply, extendZero_of_mem K _ hzK, ContinuousMap.add_apply]
  algebraMap_mem' c := by
    refine (differentiableOn_const c).congr fun z hz => ?_
    rw [extendZero_of_mem K _ (interior_subset hz)]
    rfl

theorem mem_holSubalgebra {K : Set E} {f : C(K, ℂ)} :
    f ∈ holSubalgebra K ↔ DifferentiableOn ℂ (extendZero K f) (interior K) := Iff.rfl

/-- `B(K)` is closed in `C(K,ℂ)`: a uniform limit of functions holomorphic on the interior is
holomorphic there. -/
theorem isClosed_holSubalgebra (K : Set E) [CompactSpace K] :
    IsClosed (holSubalgebra K : Set C(K, ℂ)) := by
  refine isClosed_of_closure_subset fun f hf => ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hf
  have hu' : ∀ n, DifferentiableOn ℂ (extendZero K (u n)) (interior K) := fun n => hu n
  have hunif : TendstoUniformly (fun n (a : K) => u n a) f atTop :=
    ContinuousMap.tendsto_iff_tendstoUniformly.mp hlim
  rw [SetLike.mem_coe, mem_holSubalgebra]
  intro z hz
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  refine DifferentiableAt.differentiableWithinAt ?_
  refine Hironaka.differentiableAt_of_tendstoUniformlyOn_ball
    (g := fun n => extendZero K (u n)) hR
    (Eventually.of_forall fun n => (hu' n).mono hball) ?_
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hunif ε hε] with n hn
  intro w hw
  have hwK : w ∈ K := interior_subset (hball hw)
  rw [extendZero_of_mem K _ hwK, extendZero_of_mem K _ hwK]
  exact hn ⟨w, hwK⟩

/-- `B(K)` is a commutative Banach algebra. -/
instance completeSpace_holSubalgebra (K : Set E) [CompactSpace K] :
    CompleteSpace (holSubalgebra K) :=
  (isClosed_holSubalgebra K).completeSpace_coe

theorem norm_holSubalgebra (K : Set E) [CompactSpace K] (f : holSubalgebra K) :
    ‖f‖ = ‖(f : C(K, ℂ))‖ := rfl

/-- A function holomorphic on a set containing `K` defines an element of `B(K)`. -/
def restrict (K : Set E) {U : Set E} (hKU : K ⊆ U) (F : E → ℂ) (hF : DifferentiableOn ℂ F U) :
    holSubalgebra K :=
  ⟨⟨fun z => F z, (hF.continuousOn.mono hKU).comp_continuous continuous_subtype_val
      fun z => z.property⟩,
    (hF.mono (interior_subset.trans hKU)).congr fun z hz => by
      rw [extendZero_of_mem K _ (interior_subset hz)]
      rfl⟩

@[simp] theorem restrict_apply (K : Set E) {U : Set E} (hKU : K ⊆ U) (F : E → ℂ)
    (hF : DifferentiableOn ℂ F U) (z : K) :
    ((restrict K hKU F hF : holSubalgebra K) : C(K, ℂ)) z = F z := rfl

/-- The sup-norm of a restriction is at most any bound of the function on `K`. -/
theorem norm_restrict_le (K : Set E) [CompactSpace K] {U : Set E} (hKU : K ⊆ U) (F : E → ℂ)
    (hF : DifferentiableOn ℂ F U) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ z ∈ K, ‖F z‖ ≤ M) :
    ‖restrict K hKU F hF‖ ≤ M := by
  rw [norm_holSubalgebra, ContinuousMap.norm_le _ hM0]
  exact fun z => hM z z.property

open HironakaG10FlatFrischHolomorphicFlattener in
/-- The restriction ring map from functions holomorphic on `U ⊇ K` to `B(K)`. -/
def restrictHom (K : Set E) {U : Set E} (hKU : K ⊆ U) : holOn U →+* holSubalgebra K where
  toFun F := restrict K hKU F.1 F.2
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

end BK

/-! ## Bounded operators of matrices over a normed algebra -/

section Matrix
variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] {p q : Type*} [Fintype p] [Fintype q]

/-- Left multiplication by a matrix `A` over `R`, as a bounded operator `R^p → R^q`. -/
def matrixOperator (A : q → p → R) : (p → R) →L[ℂ] (q → R) :=
  ContinuousLinearMap.pi fun i =>
    ∑ j, (ContinuousLinearMap.mul ℂ R (A i j)).comp (ContinuousLinearMap.proj j)

omit [Fintype q] in
@[simp] theorem matrixOperator_apply (A : q → p → R) (v : p → R) (i : q) :
    matrixOperator A v i = ∑ j, A i j * v j := by
  simp [matrixOperator]

omit [Fintype q] in
theorem matrixOperator_apply_eq_mulVec (A : q → p → R) (v : p → R) :
    matrixOperator A v = Matrix.mulVec (Matrix.of A) v := by
  funext i
  simp [Matrix.mulVec, dotProduct]

/-- Operator norm bound: `‖A‖_{op} ≤ ∑_{i,j} ‖A_{ij}‖`. -/
theorem norm_matrixOperator_le (A : q → p → R) :
    ‖matrixOperator A‖ ≤ ∑ i, ∑ j, ‖A i j‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) fun v => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  rw [matrixOperator_apply]
  calc ‖∑ j, A i j * v j‖ ≤ ∑ j, ‖A i j‖ * ‖v‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ =>
          (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm v j)
            (norm_nonneg _)))
    _ = (∑ j, ‖A i j‖) * ‖v‖ := by rw [Finset.sum_mul]
    _ ≤ (∑ i, ∑ j, ‖A i j‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (Finset.single_le_sum
          (f := fun i => ∑ j, ‖A i j‖) (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _)
          (Finset.mem_univ i)) (norm_nonneg _)

/-- `A ↦ matrixOperator A` as a linear map. -/
def matrixOperatorLinear : (q → p → R) →ₗ[ℂ] ((p → R) →L[ℂ] (q → R)) where
  toFun := matrixOperator
  map_add' A B := by
    ext v i
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c A := by
    ext v i
    simp [Finset.smul_sum]

theorem norm_matrixOperatorLinear_le (A : q → p → R) :
    ‖matrixOperatorLinear (R := R) (p := p) (q := q) A‖ ≤
      ((Fintype.card q : ℝ) * Fintype.card p) * ‖A‖ := by
  change ‖matrixOperator A‖ ≤ _
  refine (norm_matrixOperator_le A).trans ?_
  calc ∑ i, ∑ j, ‖A i j‖ ≤ ∑ _i : q, ∑ _j : p, ‖A‖ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)
    _ = ((Fintype.card q : ℝ) * Fintype.card p) * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

/-- `A ↦ matrixOperator A` is a bounded linear map. -/
theorem isBoundedLinearMap_matrixOperator :
    IsBoundedLinearMap ℂ (fun A : q → p → R => matrixOperator A) :=
  (matrixOperatorLinear (R := R) (p := p) (q := q)).isLinear.with_bound
    ((Fintype.card q : ℝ) * Fintype.card p) fun A => norm_matrixOperatorLinear_le A

/-- `A ↦ matrixOperator A` as a continuous linear map. -/
def matrixOperatorCLM : (q → p → R) →L[ℂ] ((p → R) →L[ℂ] (q → R)) :=
  (isBoundedLinearMap_matrixOperator (R := R) (p := p) (q := q)).toContinuousLinearMap

theorem matrixOperatorCLM_apply (A : q → p → R) :
    matrixOperatorCLM (R := R) (p := p) (q := q) A = matrixOperator A := rfl

/-- A holomorphic family of matrices gives a holomorphic family of operators. -/
theorem differentiableAt_matrixOperator {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {A : X → q → p → R} {s : X} (hA : ∀ i j, DifferentiableAt ℂ (fun x => A x i j) s) :
    DifferentiableAt ℂ (fun x => matrixOperator (A x)) s := by
  have h : DifferentiableAt ℂ A s :=
    differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j => hA i j
  have hL := IsBoundedLinearMap.differentiableAt (𝕜 := ℂ) (E := q → p → R)
    (F := (p → R) →L[ℂ] (q → R)) (isBoundedLinearMap_matrixOperator (R := R) (p := p) (q := q))
    (x := A s)
  exact hL.comp s h

end Matrix

end
end Hironaka.HironakaG10FlatPolydiscAlgebra
