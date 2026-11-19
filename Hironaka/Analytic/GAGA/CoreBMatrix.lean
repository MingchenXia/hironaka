import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Hironaka.Manifold.HolomorphicContDiff

/-!
# Holomorphic matrix-valued functions

Infrastructure of lane SERRE-CORE2 (Serre's GAGA, towards source `lma:GAGA`), for Cartan's
matrix lemma (step M2.3 of `blueprint/src/claude-serre-core.tex`, see
`blueprint/src/claude-serre-core2.tex`).

A matrix-valued function `A : X → Matrix m m' ℂ` on a complex normed space is *holomorphic on*
`U` (`MatHolOn A U`) if all its entries are complex differentiable on `U`. Matrix products, sums,
determinants, adjugates and (where the determinant does not vanish) inverses of holomorphic
matrices are holomorphic, and a locally uniform limit of holomorphic matrices on an open set is
holomorphic (Weierstrass, entrywise, from `Hironaka`).

For estimates we use the entrywise `ℓ¹` norm `mnorm A = ∑_{a,b} ‖A_{ab}‖`, which is
subadditive and submultiplicative (`mnorm_mul_le`) and dominates every entry. A matrix with
`mnorm (A - 1) < 1` is invertible (`det_ne_zero_of_mnorm_sub_one_lt`, Gershgorin's theorem).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter Metric
open scoped Topology

namespace Hironaka.Analytic.GAGA.Core.Mat

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
variable {m m' m'' : Type} [Fintype m] [Fintype m'] [Fintype m'']

/-! ### The entrywise `ℓ¹` norm -/

/-- The entrywise `ℓ¹` norm of a complex matrix. -/
noncomputable def mnorm (A : Matrix m m' ℂ) : ℝ :=
  ∑ a, ∑ b, ‖A a b‖

theorem mnorm_nonneg (A : Matrix m m' ℂ) : 0 ≤ mnorm A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem norm_entry_le_mnorm (A : Matrix m m' ℂ) (a : m) (b : m') : ‖A a b‖ ≤ mnorm A := by
  classical
  calc ‖A a b‖ ≤ ∑ b', ‖A a b'‖ :=
        Finset.single_le_sum (f := fun b' => ‖A a b'‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ b)
    _ ≤ mnorm A :=
        Finset.single_le_sum (f := fun a' => ∑ b', ‖A a' b'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)

theorem mnorm_le_of_forall_entry_le {A : Matrix m m' ℂ} {c : ℝ} (h : ∀ a b, ‖A a b‖ ≤ c) :
    mnorm A ≤ (Fintype.card m * Fintype.card m' : ℝ) * c := by
  calc mnorm A ≤ ∑ _a : m, ∑ _b : m', c :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h a b
    _ = (Fintype.card m * Fintype.card m' : ℝ) * c := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

theorem mnorm_add_le (A B : Matrix m m' ℂ) : mnorm (A + B) ≤ mnorm A + mnorm B := by
  simp only [mnorm, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => norm_add_le _ _

theorem mnorm_neg (A : Matrix m m' ℂ) : mnorm (-A) = mnorm A := by
  simp [mnorm]

theorem mnorm_sub_le (A B : Matrix m m' ℂ) : mnorm (A - B) ≤ mnorm A + mnorm B := by
  rw [sub_eq_add_neg, ← mnorm_neg B]
  exact mnorm_add_le _ _

theorem mnorm_zero : mnorm (0 : Matrix m m' ℂ) = 0 := by
  simp [mnorm]

/-- The sum of the `ℓ¹` norms of a row is at most `mnorm`. -/
theorem sum_norm_row_le_mnorm (A : Matrix m m' ℂ) (a : m) : ∑ b, ‖A a b‖ ≤ mnorm A := by
  classical
  exact Finset.single_le_sum (f := fun a' => ∑ b, ‖A a' b‖)
    (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ a)

theorem mnorm_mul_le (A : Matrix m m' ℂ) (B : Matrix m' m'' ℂ) :
    mnorm (A * B) ≤ mnorm A * mnorm B := by
  have key : ∀ a, ∑ c, ‖(A * B) a c‖ ≤ (∑ b, ‖A a b‖) * mnorm B := by
    intro a
    calc ∑ c, ‖(A * B) a c‖ ≤ ∑ c, ∑ b, ‖A a b‖ * ‖B b c‖ :=
          Finset.sum_le_sum fun c _ => by
            rw [Matrix.mul_apply]
            exact (norm_sum_le _ _).trans
              (le_of_eq (Finset.sum_congr rfl fun b _ => norm_mul _ _))
      _ = ∑ b, ‖A a b‖ * ∑ c, ‖B b c‖ := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ b, ‖A a b‖ * mnorm B :=
          Finset.sum_le_sum fun b _ =>
            mul_le_mul_of_nonneg_left (sum_norm_row_le_mnorm B b) (norm_nonneg _)
      _ = (∑ b, ‖A a b‖) * mnorm B := (Finset.sum_mul _ _ _).symm
  calc mnorm (A * B) = ∑ a, ∑ c, ‖(A * B) a c‖ := rfl
    _ ≤ ∑ a, (∑ b, ‖A a b‖) * mnorm B := Finset.sum_le_sum fun a _ => key a
    _ = mnorm A * mnorm B := (Finset.sum_mul _ _ _).symm

theorem mnorm_one [DecidableEq m] : mnorm (1 : Matrix m m ℂ) = Fintype.card m := by
  simp [mnorm, Matrix.one_apply, apply_ite norm]

theorem continuous_mnorm : Continuous (mnorm : Matrix m m' ℂ → ℝ) :=
  continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
    continuous_norm.comp ((continuous_apply b).comp (continuous_apply a))

/-- **Gershgorin**: a matrix within `ℓ¹`-distance `< 1` of the identity is invertible. -/
theorem det_ne_zero_of_mnorm_sub_one_lt [DecidableEq m] {A : Matrix m m ℂ}
    (h : mnorm (A - 1) < 1) : A.det ≠ 0 := by
  refine det_ne_zero_of_sum_row_lt_diag fun k => ?_
  have hrow : ∑ j ∈ Finset.univ.erase k, ‖A k j‖ + ‖A k k - 1‖ ≤ mnorm (A - 1) := by
    have h1 : ∑ j ∈ Finset.univ.erase k, ‖A k j‖ + ‖A k k - 1‖ = ∑ j, ‖(A - 1) k j‖ := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
      congr 1
      · refine Finset.sum_congr rfl fun j hj => ?_
        rw [Matrix.sub_apply, Matrix.one_apply_ne (Finset.ne_of_mem_erase hj).symm, sub_zero]
      · rw [Matrix.sub_apply, Matrix.one_apply_eq]
    rw [h1]
    classical
    exact Finset.single_le_sum (f := fun a => ∑ j, ‖(A - 1) a j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ k)
  have hkk : 1 - ‖A k k - 1‖ ≤ ‖A k k‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - A k k)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
    linarith
  linarith

/-! ### Holomorphic matrices -/

/-- All entries of `A` are complex differentiable on `U`. -/
def MatHolOn (A : X → Matrix m m' ℂ) (U : Set X) : Prop :=
  ∀ a b, DifferentiableOn ℂ (fun z => A z a b) U

theorem MatHolOn.mono {A : X → Matrix m m' ℂ} {U V : Set X} (h : MatHolOn A U) (hVU : V ⊆ U) :
    MatHolOn A V := fun a b => (h a b).mono hVU

theorem MatHolOn.congr' {A B : X → Matrix m m' ℂ} {U : Set X} (h : MatHolOn A U)
    (hAB : ∀ z, A z = B z) : MatHolOn B U := by
  have : A = B := funext hAB
  exact this ▸ h

theorem MatHolOn.const (A : Matrix m m' ℂ) (U : Set X) : MatHolOn (fun _ => A) U :=
  fun _ _ => differentiableOn_const _

theorem MatHolOn.add {A B : X → Matrix m m' ℂ} {U : Set X} (hA : MatHolOn A U)
    (hB : MatHolOn B U) : MatHolOn (fun z => A z + B z) U :=
  fun a b => (hA a b).add (hB a b)

theorem MatHolOn.neg {A : X → Matrix m m' ℂ} {U : Set X} (hA : MatHolOn A U) :
    MatHolOn (fun z => -A z) U :=
  fun a b => (hA a b).neg

theorem MatHolOn.sub {A B : X → Matrix m m' ℂ} {U : Set X} (hA : MatHolOn A U)
    (hB : MatHolOn B U) : MatHolOn (fun z => A z - B z) U :=
  fun a b => (hA a b).sub (hB a b)

theorem MatHolOn.mul {A : X → Matrix m m' ℂ} {B : X → Matrix m' m'' ℂ} {U : Set X}
    (hA : MatHolOn A U) (hB : MatHolOn B U) : MatHolOn (fun z => A z * B z) U := by
  intro a c
  have h := DifferentiableOn.sum (u := Finset.univ) (A := fun b z => A z a b * B z b c)
    fun b _ => (hA a b).mul (hB b c)
  refine h.congr fun z _ => ?_
  simp [Matrix.mul_apply]

theorem MatHolOn.smul {f : X → ℂ} {A : X → Matrix m m' ℂ} {U : Set X}
    (hf : DifferentiableOn ℂ f U) (hA : MatHolOn A U) : MatHolOn (fun z => f z • A z) U :=
  fun a b => (hf.mul (hA a b)).congr fun z _ => by simp [Matrix.smul_apply]

/-- Finite products of holomorphic functions are holomorphic. -/
theorem differentiableOn_finset_prod {ι : Type*} (s : Finset ι) {f : ι → X → ℂ} {U : Set X}
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) :
    DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).mul
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem MatHolOn.det [DecidableEq m] {A : X → Matrix m m ℂ} {U : Set X} (hA : MatHolOn A U) :
    DifferentiableOn ℂ (fun z => (A z).det) U := by
  have h := DifferentiableOn.sum (u := Finset.univ)
    (A := fun σ z => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A z (σ i) i)
    fun σ _ => (differentiableOn_const _).mul
      (differentiableOn_finset_prod Finset.univ fun i _ => hA (σ i) i)
  refine h.congr fun z _ => ?_
  simp [Matrix.det_apply']

theorem MatHolOn.adjugate [DecidableEq m] {A : X → Matrix m m ℂ} {U : Set X}
    (hA : MatHolOn A U) : MatHolOn (fun z => (A z).adjugate) U := by
  intro a b
  simp only [Matrix.adjugate_apply]
  refine MatHolOn.det (A := fun z => (A z).updateRow b (Pi.single a 1)) (fun i j => ?_)
  simp only [Matrix.updateRow_apply]
  by_cases h : i = b
  · simp only [h, if_true]
    exact differentiableOn_const _
  · simp only [h, if_false]
    exact hA i j

/-- The inverse of a holomorphic matrix is holomorphic where its determinant does not vanish. -/
theorem MatHolOn.inv [DecidableEq m] {A : X → Matrix m m ℂ} {U : Set X} (hA : MatHolOn A U)
    (hdet : ∀ z ∈ U, (A z).det ≠ 0) : MatHolOn (fun z => (A z)⁻¹) U := by
  have h : MatHolOn (fun z => ((A z).det)⁻¹ • (A z).adjugate) U :=
    MatHolOn.smul (hA.det.inv hdet) hA.adjugate
  intro a b
  refine (h a b).congr fun z _ => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv']

theorem det_inv_ne_zero [DecidableEq m] {A : Matrix m m ℂ} (h : A.det ≠ 0) : A⁻¹.det ≠ 0 := by
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  exact inv_ne_zero h

/-- If `B' A B'' = 1` with `B'` invertible, then `A = B'⁻¹ B''⁻¹`. -/
theorem eq_inv_mul_inv_of_mul_mul_eq_one [DecidableEq m] {A B' B'' : Matrix m m ℂ}
    (h : B' * A * B'' = 1) (hB' : B'.det ≠ 0) : A = B'⁻¹ * B''⁻¹ := by
  have hu : IsUnit B'.det := isUnit_iff_ne_zero.2 hB'
  have h1 : A * B'' = B'⁻¹ := by
    calc A * B'' = B'⁻¹ * (B' * A * B'') := by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc B'⁻¹, Matrix.nonsing_inv_mul _ hu,
            Matrix.one_mul]
      _ = B'⁻¹ := by rw [h, Matrix.mul_one]
  have hB'' : IsUnit B''.det := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at this
    exact isUnit_iff_ne_zero.2 fun h0 => by rw [h0, mul_zero] at this; exact zero_ne_one this
  calc A = A * B'' * B''⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB'', Matrix.mul_one]
    _ = B'⁻¹ * B''⁻¹ := by rw [h1]

/-! ### Uniform limits -/

/-- **Weierstrass for matrices**: an entrywise locally uniform limit of holomorphic matrices on
an open set is holomorphic. -/
theorem MatHolOn.of_tendstoUniformlyOn {A : ℕ → X → Matrix m m' ℂ} {B : X → Matrix m m' ℂ}
    {U : Set X} (hU : IsOpen U) (hA : ∀ N, MatHolOn (A N) U)
    (hlim : ∀ a b, TendstoUniformlyOn (fun N z => A N z a b) (fun z => B z a b) atTop U) :
    MatHolOn B U := by
  intro a b x hx
  obtain ⟨R, hR, hRU⟩ := Metric.isOpen_iff.1 hU x hx
  exact (Hironaka.differentiableAt_of_tendstoUniformlyOn_ball hR
    (Eventually.of_forall fun N => (hA N a b).mono hRU) ((hlim a b).mono hRU)).differentiableWithinAt

end Hironaka.Analytic.GAGA.Core.Mat
