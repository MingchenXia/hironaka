import Hironaka.Analytic.Unibranch.HironakaG10ArtinianRelationLift
import Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
import Hironaka.Coherence.OkaGermBridge
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual holomorphic matrices with finite parameter coefficients

A finite basis constructs the whole tensor germ of an actual
parameter-algebra-valued holomorphic function.  Its coordinates are the
actual scalar holomorphic germs; ring operations, residue reduction and
finite matrix relations retain those same functions and whole tensors.
No encoding-correctness or matrix-solvability certificate is supplied.
-/

set_option autoImplicit false

open Filter Set
open scoped Topology TensorProduct

namespace Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix

open Hironaka OkaRelationSheaf OkaGermBridge
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianTensorCoefficients
  Hironaka.Analytic.Unibranch.HironakaG10ArtinianRelationLift

noncomputable section

variable {Q X ι : Type*} [NormedCommRing Q] [NormedAlgebra ℂ Q]
  [FiniteDimensional ℂ Q] [NormedAddCommGroup X] [NormedSpace ℂ X]
  [Fintype ι] [DecidableEq ι]

local instance : Algebra ℂ (HolGerm X) :=
  (HolGerm.constHom : ℂ →+* HolGerm X).toAlgebra

omit [Fintype ι] [DecidableEq ι] in
/-- The scalar coordinate functions of an actual holomorphic map are
holomorphic, because the finite-dimensional coordinate maps are continuous. -/
theorem holomorphic_coordinate (b : Module.Basis ι ℂ Q) (i : ι) {f : X → Q} {z : X}
    (hf : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x) :
    HolAt (fun x => b.coord i (f x)) z := by
  filter_upwards [hf] with x hx
  exact (b.coord i).toContinuousLinearMap.differentiableAt.comp x hx

/-- The actual finite-basis tensor germ, with every scalar germ centered at
the same original point. Ring identities require genuine holomorphic inputs. -/
def tensorGermAt (b : Module.Basis ι ℂ Q) (z : X) (f : X → Q) :
    Q ⊗[ℂ] HolGerm X :=
  ∑ i, b i ⊗ₜ[ℂ] germAt z (fun x => b.coord i (f x))

omit [FiniteDimensional ℂ Q] in
/-- Each tensor coefficient is literally the corresponding scalar
holomorphic germ of the original function. -/
theorem tensorGermAt_coordinate (b : Module.Basis ι ℂ Q) (z : X) (f : X → Q) (i : ι) :
    parameterTensorEquiv b (tensorGermAt b z f) i =
      germAt z (fun x => b.coord i (f x)) := by
  simp [tensorGermAt, parameterTensorEquiv_tmul]

/-- Vanishing of the whole tensor germ detects actual nearby vanishing of
the original parameter-valued holomorphic function. -/
theorem tensorGermAt_eq_zero_iff (b : Module.Basis ι ℂ Q) {z : X} {f : X → Q}
    (hf : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x) :
    tensorGermAt b z f = 0 ↔ ∀ᶠ x in 𝓝 z, f x = 0 := by
  constructor
  · intro hz
    have hcoords : ∀ i, ∀ᶠ x in 𝓝 z, b.coord i (f x) = 0 := by
      intro i
      apply (germAt_eq_zero_iff (holomorphic_coordinate b i hf)).mp
      rw [← tensorGermAt_coordinate b z f i, hz, map_zero]
      rfl
    filter_upwards [eventually_all.mpr hcoords] with x hx
    apply b.repr.injective
    apply Finsupp.ext
    intro i
    simpa only [Module.Basis.coord_apply, map_zero, Finsupp.zero_apply] using hx i
  · intro hz
    apply (parameterTensorEquiv b).injective
    apply funext
    intro i
    rw [tensorGermAt_coordinate, map_zero]
    apply (germAt_eq_zero_iff (holomorphic_coordinate b i hf)).mpr
    filter_upwards [hz] with x hx
    simp [hx]

theorem tensorGermAt_add (b : Module.Basis ι ℂ Q) {z : X} {f g : X → Q}
    (hf : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x)
    (hg : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ g x) :
    tensorGermAt b z (fun x => f x + g x) = tensorGermAt b z f + tensorGermAt b z g := by
  apply (parameterTensorEquiv b).injective
  apply funext
  intro i
  simp only [map_add, tensorGermAt_coordinate, Pi.add_apply]
  exact germAt_add (holomorphic_coordinate b i hf) (holomorphic_coordinate b i hg)

/-- Tensor germs commute with finite sums of actual holomorphic functions. -/
theorem tensorGermAt_finset_sum (b : Module.Basis ι ℂ Q) {κ : Type*} (s : Finset κ)
    {z : X} {f : κ → X → Q}
    (hf : ∀ k ∈ s, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (f k) x) :
    tensorGermAt b z (fun x => ∑ k ∈ s, f k x) = ∑ k ∈ s, tensorGermAt b z (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tensorGermAt, germAt_zero]
  | @insert k s hks ih =>
    have hsum : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (fun x => ∑ j ∈ s, f j x) x := by
      filter_upwards [(eventually_all_finset s).mpr fun j hj =>
        hf j (Finset.mem_insert_of_mem hj)] with x hx
      exact DifferentiableAt.fun_sum hx
    simp only [Finset.sum_insert hks]
    rw [tensorGermAt_add b (hf k (Finset.mem_insert_self k s)) hsum,
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

omit [FiniteDimensional ℂ Q] in
/-- The tensor germ of a scalar holomorphic function times a constant
parameter vector is its actual pure tensor. -/
theorem tensorGermAt_smul_const (b : Module.Basis ι ℂ Q) {z : X} {f : X → ℂ}
    (hf : HolAt f z) (a : Q) :
    tensorGermAt b z (fun x => f x • a) = a ⊗ₜ[ℂ] germAt z f := by
  apply (parameterTensorEquiv b).injective
  apply funext
  intro i
  rw [tensorGermAt_coordinate, parameterTensorEquiv_tmul]
  simp only [map_smul, smul_eq_mul]
  change germAt z (fun x => f x * b.coord i a) = b.coord i a • germAt z f
  rw [germAt_mul hf (holAt_const _ z), germAt_const, Algebra.smul_def]
  exact mul_comm _ _

/-- Multiplication of actual parameter-valued holomorphic functions is
the genuine multiplication of their whole tensor germs. -/
theorem tensorGermAt_mul (b : Module.Basis ι ℂ Q) {z : X} {f g : X → Q}
    (hf : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x)
    (hg : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ g x) :
    tensorGermAt b z (fun x => f x * g x) = tensorGermAt b z f * tensorGermAt b z g := by
  have hfg (i j : ι) : HolAt (fun x => b.coord i (f x) * b.coord j (g x)) z :=
    (holomorphic_coordinate b i hf).mul (holomorphic_coordinate b j hg)
  have hterm (i j : ι) : ∀ᶠ x in 𝓝 z,
      DifferentiableAt ℂ (fun x =>
        (b.coord i (f x) * b.coord j (g x)) • (b i * b j)) x :=
    (hfg i j).mono fun _ hx => hx.smul_const _
  have hsum (i : ι) : ∀ᶠ x in 𝓝 z,
      DifferentiableAt ℂ (fun x => ∑ j,
        (b.coord i (f x) * b.coord j (g x)) • (b i * b j)) x := by
    filter_upwards [eventually_all.mpr (hterm i)] with x hx
    exact DifferentiableAt.fun_sum fun j _ => hx j
  have hfun : (fun x => f x * g x) = fun x =>
      ∑ i, ∑ j, (b.coord i (f x) * b.coord j (g x)) • (b i * b j) := by
    funext x
    calc
      f x * g x = (∑ i, b.coord i (f x) • b i) *
          (∑ j, b.coord j (g x) • b j) := by
        rw [show (∑ i, b.coord i (f x) • b i) = f x from b.sum_repr _,
          show (∑ j, b.coord j (g x) • b j) = g x from b.sum_repr _]
      _ = _ := by
        simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm]
        exact Finset.sum_comm
  calc
    tensorGermAt b z (fun x => f x * g x) =
        ∑ i, tensorGermAt b z (fun x => ∑ j,
          (b.coord i (f x) * b.coord j (g x)) • (b i * b j)) := by
      rw [hfun]
      exact tensorGermAt_finset_sum b Finset.univ fun i _ => hsum i
    _ = ∑ i, ∑ j, (b i * b j) ⊗ₜ[ℂ]
        (germAt z (fun x => b.coord i (f x)) * germAt z (fun x => b.coord j (g x))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [tensorGermAt_finset_sum b Finset.univ fun j _ => hterm i j]
      apply Finset.sum_congr rfl
      intro j _
      rw [tensorGermAt_smul_const b (hfg i j),
        germAt_mul (holomorphic_coordinate b i hf) (holomorphic_coordinate b j hg)]
    _ = tensorGermAt b z f * tensorGermAt b z g := by
      simp only [tensorGermAt, Finset.sum_mul, Finset.mul_sum,
        Algebra.TensorProduct.tmul_mul_tmul]
      exact Finset.sum_comm

omit [DecidableEq ι] in
/-- The actual tensor reduction agrees with the scalar germ of the
original residue-valued function. -/
theorem residueTensor_tensorGermAt (b : Module.Basis ι ℂ Q) (ε : Q →ₐ[ℂ] ℂ)
    {z : X} {f : X → Q} (hf : ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ f x) :
    residueTensor ε (tensorGermAt b z f) = germAt z (fun x => ε (f x)) := by
  have hfun : (fun x => ε (f x)) = fun x => ∑ i, ε (b i) * b.coord i (f x) := by
    funext x
    have heq := congrArg ε (b.sum_repr (f x))
    simpa only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply, mul_comm]
      using heq.symm
  simp only [tensorGermAt, map_sum, residueTensor_tmul]
  rw [hfun, germAt_sum Finset.univ fun i _ =>
    (holAt_const (ε (b i)) z).mul (holomorphic_coordinate b i hf)]
  apply Finset.sum_congr rfl
  intro i _
  rw [germAt_mul (holAt_const (ε (b i)) z) (holomorphic_coordinate b i hf),
    germAt_const, Algebra.smul_def]
  rfl

/-- Taking the whole tensor germ commutes with actual matrix products. -/
theorem matrix_tensorGermAt_mul (b : Module.Basis ι ℂ Q)
    {a c k : Type*} [Fintype k] {z : X}
    {F : a → k → X → Q} {G : k → c → X → Q}
    (hF : ∀ i j, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (F i j) x)
    (hG : ∀ j l, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (G j l) x) (i : a) (l : c) :
    tensorGermAt b z (fun x => ∑ j, F i j x * G j l x) =
      ∑ j, tensorGermAt b z (F i j) * tensorGermAt b z (G j l) := by
  calc
    tensorGermAt b z (fun x => ∑ j, F i j x * G j l x) =
        ∑ j, tensorGermAt b z (fun x => F i j x * G j l x) :=
      tensorGermAt_finset_sum b Finset.univ
        (f := fun j x => F i j x * G j l x) fun j _ =>
          (hF i j).and (hG j l) |>.mono fun _ hx => hx.1.mul hx.2
    _ = _ := Finset.sum_congr rfl fun j _ => tensorGermAt_mul b (hF i j) (hG j l)

/-- The literal tensor-matrix relation is equivalent to the actual
holomorphic matrix relation on one neighborhood of the original point. -/
theorem matrix_tensor_relation_iff (b : Module.Basis ι ℂ Q)
    {a c k : Type*} [Fintype a] [Fintype c] [Fintype k] {z : X}
    {F : a → k → X → Q} {G : k → c → X → Q}
    (hF : ∀ i j, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (F i j) x)
    (hG : ∀ j l, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (G j l) x) :
    (∀ i l, ∑ j, tensorGermAt b z (F i j) * tensorGermAt b z (G j l) = 0) ↔
      ∀ᶠ x in 𝓝 z, ∀ i l, ∑ j, F i j x * G j l x = 0 := by
  have hhol (i : a) (l : c) : ∀ᶠ x in 𝓝 z,
      DifferentiableAt ℂ (fun x => ∑ j, F i j x * G j l x) x := by
    filter_upwards [eventually_all.mpr (hF i), eventually_all.mpr (fun j => hG j l)]
      with x hxF hxG
    exact DifferentiableAt.fun_sum fun j _ => (hxF j).mul (hxG j)
  constructor
  · intro h
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro l
    apply (tensorGermAt_eq_zero_iff b (hhol i l)).mp
    rw [matrix_tensorGermAt_mul b hF hG i l]
    exact h i l
  · intro h i l
    rw [← matrix_tensorGermAt_mul b hF hG i l]
    apply (tensorGermAt_eq_zero_iff b (hhol i l)).mpr
    exact h.mono fun _ hx => hx i l

/-- The actual complex matrix of multiplication by the parameter-valued
matrix: each input basis vector is multiplied before its output coordinate
is taken. -/
def complexBlockMatrix (b : Module.Basis ι ℂ Q) {a k : Type*}
    (F : a → k → X → Q) : (a × ι) → (k × ι) → X → ℂ :=
  fun p q x => b.coord p.2 (F p.1 q.1 x * b q.2)

omit [Fintype ι] [DecidableEq ι] in
/-- All entries of the actual finite complex block matrix are holomorphic. -/
theorem holomorphic_complexBlockMatrix (b : Module.Basis ι ℂ Q)
    {a k : Type*} {F : a → k → X → Q} {z : X}
    (hF : ∀ i j, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (F i j) x)
    (p : a × ι) (q : k × ι) : HolAt (complexBlockMatrix b F p q) z :=
  holomorphic_coordinate b p.2 ((hF p.1 q.1).mono fun _ hx => hx.mul_const _)

/-- The finite complex block action agrees with the whole tensor germ
action on the same original holomorphic vector. -/
theorem complexBlockMatrix_germ_action (b : Module.Basis ι ℂ Q)
    {a k : Type*} [Fintype k] {F : a → k → X → Q} {v : k → X → Q} {z : X}
    (hF : ∀ i j, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (F i j) x)
    (hv : ∀ j, ∀ᶠ x in 𝓝 z, DifferentiableAt ℂ (v j) x) (i : a) (r : ι) :
    parameterTensorEquiv b (∑ j, tensorGermAt b z (F i j) * tensorGermAt b z (v j)) r =
      ∑ j, ∑ l, germAt z (complexBlockMatrix b F (i, r) (j, l)) *
        germAt z (fun x => b.coord l (v j x)) := by
  have hblock (j : k) (l : ι) : HolAt (complexBlockMatrix b F (i, r) (j, l)) z :=
    holomorphic_complexBlockMatrix b hF (i, r) (j, l)
  have hinner (j : k) : HolAt (fun x => ∑ l,
      complexBlockMatrix b F (i, r) (j, l) x * b.coord l (v j x)) z :=
    HolAt.fintype_sum fun l => (hblock j l).mul (holomorphic_coordinate b l (hv j))
  have hfun : (fun x => b.coord r (∑ j, F i j x * v j x)) = fun x =>
      ∑ j, ∑ l, complexBlockMatrix b F (i, r) (j, l) x * b.coord l (v j x) := by
    funext x
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    have heq : F i j x * v j x = ∑ l, b.coord l (v j x) • (F i j x * b l) := by
      calc
        F i j x * v j x = F i j x * (∑ l, b.coord l (v j x) • b l) := by
          rw [show (∑ l, b.coord l (v j x) • b l) = v j x from b.sum_repr _]
        _ = _ := by simp only [Finset.mul_sum, mul_smul_comm]
    rw [heq, map_sum]
    apply Finset.sum_congr rfl
    intro l _
    simp only [map_smul, smul_eq_mul, complexBlockMatrix]
    exact mul_comm _ _
  rw [← matrix_tensorGermAt_mul b (G := fun j (_ : Unit) => v j)
    hF (fun j _ => hv j) i (), tensorGermAt_coordinate, hfun,
    germAt_sum Finset.univ fun j _ => hinner j]
  apply Finset.sum_congr rfl
  intro j _
  rw [germAt_sum Finset.univ fun l _ =>
    (hblock j l).mul (holomorphic_coordinate b l (hv j))]
  exact Finset.sum_congr rfl fun l _ =>
    germAt_mul (hblock j l) (holomorphic_coordinate b l (hv j))

end

end Hironaka.Analytic.Unibranch.HironakaG10ArtinianHolomorphicMatrix
