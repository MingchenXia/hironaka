import Mathlib.RingTheory.Grassmannian
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The actual normalized quotient matrices in a Grassmannian chart

Each original matrix gives the literal split quotient of the original finite
free module. Its actual kernel quotient is finite free with the exact stalk
rank, hence gives a native quotient Grassmannian point over any coefficient
ring. Different original matrices have different literal kernels.
-/

noncomputable section

open scoped BigOperators

namespace Hironaka.Algebra.PluckerQuot

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w}
  [Fintype κ]

/-- The original quotient with its actual identity pivot block. -/
def matrixQuotient (a : Matrix ι κ R) : ((ι ⊕ κ) → R) →ₗ[R] (ι → R) :=
  (LinearMap.pi fun i ↦ (LinearMap.proj (Sum.inl i) : ((ι ⊕ κ) → R) →ₗ[R] R)) +
    (Matrix.mulVecLin a).comp
      (LinearMap.pi fun j ↦ (LinearMap.proj (Sum.inr j) : ((ι ⊕ κ) → R) →ₗ[R] R))

@[simp]
theorem matrixQuotient_apply (a : Matrix ι κ R) (v : (ι ⊕ κ) → R) (i : ι) :
    matrixQuotient a v i = v (Sum.inl i) + ∑ j, a i j * v (Sum.inr j) := rfl

/-- The original coordinate inclusion used to normalize this chart. -/
def pivotSection : (ι → R) →ₗ[R] ((ι ⊕ κ) → R) :=
  LinearMap.pi fun k ↦ match k with
    | Sum.inl i => LinearMap.proj i
    | Sum.inr _ => 0

omit [Fintype κ] in
@[simp]
theorem pivotSection_inl (v : ι → R) (i : ι) : pivotSection (κ := κ) v (Sum.inl i) = v i := rfl

omit [Fintype κ] in
@[simp]
theorem pivotSection_inr (v : ι → R) (j : κ) : pivotSection v (Sum.inr j) = 0 := rfl

@[simp]
theorem matrixQuotient_pivotSection (a : Matrix ι κ R) (v : ι → R) :
    matrixQuotient a (pivotSection v) = v := by
  ext i
  simp

/-- The actual normalized quotient is split surjective without any rank certificate. -/
theorem matrixQuotient_surjective (a : Matrix ι κ R) : Function.Surjective (matrixQuotient a) :=
  fun v ↦ ⟨pivotSection v, matrixQuotient_pivotSection a v⟩

/-- The actual quotient by the original kernel is the same finite free target. -/
def matrixQuotientEquiv (a : Matrix ι κ R) :
    (((ι ⊕ κ) → R) ⧸ (matrixQuotient a).ker) ≃ₗ[R] (ι → R) :=
  (matrixQuotient a).quotKerEquivOfSurjective (matrixQuotient_surjective a)

variable [DecidableEq ι] [DecidableEq κ]

@[simp]
theorem matrixQuotient_single_inr (a : Matrix ι κ R) (j : κ) :
    matrixQuotient a (Pi.single (Sum.inr j) 1) = fun i ↦ a i j := by
  ext i
  simp [Pi.single_apply]

variable [Fintype ι]

/-- The actual finite free quotient, including its exact native stalk rank. -/
def matrixPoint (a : Matrix ι κ R) :
    Module.Grassmannian R ((ι ⊕ κ) → R) (Fintype.card ι) where
  toSubmodule := (matrixQuotient a).ker
  finite_quotient := Module.Finite.equiv (matrixQuotientEquiv a).symm
  projective_quotient := Module.Projective.of_equiv (matrixQuotientEquiv a).symm
  rankAtStalk_eq p := by
    let : Nontrivial R := ⟨⟨0, 1, fun h ↦ p.isPrime.ne_top
      ((Ideal.eq_top_iff_one p.asIdeal).mpr (h ▸ p.asIdeal.zero_mem))⟩⟩
    rw [congrFun (Module.rankAtStalk_eq_of_equiv (matrixQuotientEquiv a)) p]
    simp

omit [DecidableEq ι] [DecidableEq κ] in
@[simp]
theorem matrixPoint_toSubmodule (a : Matrix ι κ R) :
    (matrixPoint a).toSubmodule = (matrixQuotient a).ker := rfl

omit [Fintype ι] in
/-- Different original normalized matrices give different actual quotient kernels. -/
theorem matrixQuotient_ker_injective :
    Function.Injective (fun a : Matrix ι κ R ↦ (matrixQuotient a).ker) := by
  intro a b hab
  change (matrixQuotient a).ker = (matrixQuotient b).ker at hab
  ext i j
  let v : (ι ⊕ κ) → R := Pi.single (Sum.inr j) 1 - pivotSection (fun i ↦ a i j)
  have hva : v ∈ (matrixQuotient a).ker := by
    change matrixQuotient a v = 0
    simp [v]
  have hvb : v ∈ (matrixQuotient b).ker := by
    rw [← hab]
    exact hva
  change matrixQuotient b v = 0 at hvb
  dsimp only [v] at hvb
  rw [map_sub, matrixQuotient_single_inr, matrixQuotient_pivotSection] at hvb
  have hba : b i j - a i j = 0 := congrFun hvb i
  exact (sub_eq_zero.mp hba).symm

/-- The normalized chart embeds into the native quotient Grassmannian. -/
theorem matrixPoint_injective : Function.Injective (matrixPoint (R := R) (ι := ι) (κ := κ)) := by
  intro a b h
  exact matrixQuotient_ker_injective (congrArg Module.Grassmannian.toSubmodule h)

end Hironaka.Algebra.PluckerQuot
