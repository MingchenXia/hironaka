import Hironaka.Algebra.PluckerQuotMatrix
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi

/-!
# Exact classification of the normalized quotient chart

The original left-coordinate map into the original quotient is the sole chart
condition. It internally determines a unique actual matrix, without a supplied
quotient basis or freeness certificate. The matrix chart is equivalent to the
corresponding intrinsic subset of the native quotient Grassmannian.
-/

noncomputable section

open scoped BigOperators

namespace Hironaka.Algebra.PluckerQuot

universe u v w

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w}
  [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
@[simp]
theorem pivotSection_single (i : ι) :
    pivotSection (κ := κ) (Pi.single i (1 : R)) = Pi.single (Sum.inl i) 1 := by
  ext k
  cases k <;> simp [Pi.single_apply]

omit [Fintype ι] in
@[simp]
theorem matrixQuotient_single_inl (a : Matrix ι κ R) (i : ι) :
    matrixQuotient a (Pi.single (Sum.inl i) 1) = Pi.single i 1 := by
  rw [← pivotSection_single, matrixQuotient_pivotSection]

/-- Every original normalized quotient map is exactly its original right-column matrix. -/
theorem eq_matrixQuotient_of_pivot (q : ((ι ⊕ κ) → R) →ₗ[R] (ι → R))
    (hq : q.comp pivotSection = LinearMap.id) :
    q = matrixQuotient (fun i j ↦ q (Pi.single (Sum.inr j) 1) i) := by
  apply (Pi.basisFun R (ι ⊕ κ)).ext
  intro k
  simp only [Pi.basisFun_apply]
  cases k with
  | inl i =>
    have hi := DFunLike.congr_fun hq (Pi.single i 1)
    change q (Pi.single (Sum.inl i) 1) = _
    rw [matrixQuotient_single_inl]
    simpa using hi
  | inr j =>
    change q (Pi.single (Sum.inr j) 1) = _
    rw [matrixQuotient_single_inr]

/-- The actual original pivot map into the actual original quotient. -/
def pivotToQuotient (N : Submodule R ((ι ⊕ κ) → R)) :
    (ι → R) →ₗ[R] (((ι ⊕ κ) → R) ⧸ N) := N.mkQ.comp pivotSection

/-- The actual original pivot map determines one and only one original normalized matrix. -/
theorem exists_unique_matrix_of_pivot (N : Submodule R ((ι ⊕ κ) → R))
    (hN : Function.Bijective (pivotToQuotient N)) :
    ∃! a : Matrix ι κ R, (matrixQuotient a).ker = N := by
  let e := LinearEquiv.ofBijective (pivotToQuotient N) hN
  let q := e.symm.toLinearMap.comp N.mkQ
  have hq : q.comp pivotSection = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply funext
    intro i
    change e.symm (e v) i = v i
    rw [e.symm_apply_apply]
  let a : Matrix ι κ R := fun i j ↦ q (Pi.single (Sum.inr j) 1) i
  have hqa : q = matrixQuotient a := eq_matrixQuotient_of_pivot q hq
  have hker : (matrixQuotient a).ker = N := by
    rw [← hqa]
    change LinearMap.ker (e.symm.toLinearMap.comp N.mkQ) = N
    ext v
    change e.symm (N.mkQ v) = 0 ↔ v ∈ N
    rw [e.symm.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero N
  refine ⟨a, hker, ?_⟩
  intro b hb
  exact matrixQuotient_ker_injective (hb.trans hker.symm)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
@[simp]
theorem matrixQuotientEquiv_mkQ (a : Matrix ι κ R) (v : (ι ⊕ κ) → R) :
    matrixQuotientEquiv a ((matrixQuotient a).ker.mkQ v) = matrixQuotient a v := by
  simp [matrixQuotientEquiv]

omit [DecidableEq ι] [DecidableEq κ] in
/-- The pivot map of the actual constructed matrix quotient is automatically an isomorphism. -/
theorem pivotToQuotient_matrixPoint_bijective (a : Matrix ι κ R) :
    Function.Bijective (pivotToQuotient (matrixPoint a).toSubmodule) := by
  have h : pivotToQuotient (matrixPoint a).toSubmodule =
      (matrixQuotientEquiv a).symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    apply (matrixQuotientEquiv a).injective
    change matrixQuotientEquiv a ((matrixQuotient a).ker.mkQ (pivotSection v)) = _
    rw [matrixQuotientEquiv_mkQ, matrixQuotient_pivotSection]
    exact ((matrixQuotientEquiv a).apply_symm_apply v).symm
  rw [h]
  exact (matrixQuotientEquiv a).symm.bijective

/-- The intrinsic pivot-open condition on a native quotient Grassmannian point. -/
def PivotChart := {N : Module.Grassmannian R ((ι ⊕ κ) → R) (Fintype.card ι) //
  Function.Bijective (pivotToQuotient N.toSubmodule)}

/-- The original matrix produces its actual native point in the intrinsic chart. -/
def matrixChartPoint (a : Matrix ι κ R) : PivotChart (R := R) (ι := ι) (κ := κ) :=
  ⟨matrixPoint a, pivotToQuotient_matrixPoint_bijective a⟩

/-- The normalized matrix chart classifies exactly the original Grassmannian quotient kernels. -/
def matrixChartEquiv : Matrix ι κ R ≃ PivotChart (R := R) (ι := ι) (κ := κ) :=
  Equiv.ofBijective matrixChartPoint ⟨fun a b h ↦
    matrixPoint_injective (congrArg Subtype.val h), by
      intro N
      obtain ⟨a, ha, _⟩ := exists_unique_matrix_of_pivot N.val.toSubmodule N.property
      refine ⟨a, Subtype.ext ?_⟩
      exact Module.Grassmannian.ext ha⟩

end Hironaka.Algebra.PluckerQuot
