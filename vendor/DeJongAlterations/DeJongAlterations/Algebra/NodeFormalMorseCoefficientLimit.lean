import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.AdicCompletion.Algebra

/-!
# The coefficientwise inverse limit of actual quotient power-series rings

Only the original coefficient ring is assumed adically complete. The result
does not identify coefficientwise ideals with ideals extended to a series ring,
and does not assert that substitutions with nonnilpotent constants are native
`MvPowerSeries.HasSubst` substitutions.
-/

noncomputable section

namespace DeJongAlterations.Algebra.NodeFormalMorse.CoefficientLimit

open MvPowerSeries

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v
variable {R : Type u} [CommRing R] (I : Ideal R) (σ : Type v)

/-- The actual coefficient-reduction transition between two quotient series rings. -/
def transition {m n : ℕ} (hmn : m ≤ n) :
    MvPowerSeries σ (R ⧸ I ^ n) →+* MvPowerSeries σ (R ⧸ I ^ m) :=
  MvPowerSeries.map (Ideal.Quotient.factorPow I hmn)

/-- Compatibility under the original coefficient-reduction maps. -/
def Compatible (f : ∀ n : ℕ, MvPowerSeries σ (R ⧸ I ^ n)) : Prop :=
  ∀ {m n : ℕ} (hmn : m ≤ n), transition I σ hmn (f n) = f m

/-- The actual inverse-limit subalgebra of the product of the quotient series rings. -/
def compatibleSubalgebra : Subalgebra R (∀ n : ℕ, MvPowerSeries σ (R ⧸ I ^ n)) where
  carrier := {f | Compatible I σ f}
  zero_mem' := by
    change Compatible I σ 0
    intro m n hmn
    exact map_zero _
  one_mem' := by
    change Compatible I σ 1
    intro m n hmn
    exact map_one _
  add_mem' hf hg m n hmn := by
    change transition I σ hmn (_ + _) = _ + _
    rw [map_add, hf hmn, hg hmn]
  mul_mem' hf hg m n hmn := by
    change transition I σ hmn (_ * _) = _ * _
    rw [map_mul, hf hmn, hg hmn]
  algebraMap_mem' r m n hmn := by
    change transition I σ hmn (algebraMap R (MvPowerSeries σ (R ⧸ I ^ n)) r) =
      algebraMap R (MvPowerSeries σ (R ⧸ I ^ m)) r
    simp [transition, MvPowerSeries.algebraMap_apply, Ideal.Quotient.algebraMap_eq]

/-- Compatible families, with the literal inherited ring and coefficient structure. -/
abbrev CompatibleSeries := ↥(compatibleSubalgebra I σ)

theorem compatible (f : CompatibleSeries I σ) : Compatible I σ f.val := f.property

/-- Evaluation of a compatible family at an actual quotient coefficient level. -/
def eval (n : ℕ) : CompatibleSeries I σ →ₐ[R] MvPowerSeries σ (R ⧸ I ^ n) where
  toFun f := f.val n
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl

/-- The original coefficient quotient maps, assembled as an actual algebra homomorphism. -/
def reduce : MvPowerSeries σ R →ₐ[R] CompatibleSeries I σ where
  toFun f := ⟨fun n => MvPowerSeries.map (Ideal.Quotient.mk (I ^ n)) f, by
    change Compatible I σ _
    intro m n hmn
    ext d
    simp [transition, coeff_map]⟩
  map_zero' := by apply Subtype.ext; funext n; exact map_zero _
  map_one' := by apply Subtype.ext; funext n; exact map_one _
  map_add' _ _ := by apply Subtype.ext; funext n; exact map_add _ _ _
  map_mul' _ _ := by apply Subtype.ext; funext n; exact map_mul _ _ _
  commutes' r := by
    apply Subtype.ext
    funext n
    change MvPowerSeries.map (Ideal.Quotient.mk (I ^ n)) (algebraMap R (MvPowerSeries σ R) r) =
      algebraMap R (MvPowerSeries σ (R ⧸ I ^ n)) r
    simp [MvPowerSeries.algebraMap_apply, Ideal.Quotient.algebraMap_eq]

@[simp]
theorem eval_reduce (n : ℕ) (f : MvPowerSeries σ R) :
    eval I σ n (reduce I σ f) = MvPowerSeries.map (Ideal.Quotient.mk (I ^ n)) f := rfl

variable {σ}

/-- Separatedness detects equality using precisely the original scalar quotient maps. -/
theorem scalar_ext [IsHausdorff I R] {x y : R}
    (h : ∀ n : ℕ, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) : x = y := by
  exact congrFun (IsHausdorff.funext' I (f := fun _ : Unit => x)
    (g := fun _ : Unit => y) (fun n _ => h n)) ()

/-- Actual completeness lifts a compatible scalar family, without any finite-generation hypothesis. -/
theorem exists_scalar_lift [IsAdicComplete I R] (q : ∀ n : ℕ, R ⧸ I ^ n)
    (hq : ∀ {m n : ℕ} (hmn : m ≤ n), Ideal.Quotient.factorPow I hmn (q n) = q m) :
    ∃ x : R, ∀ n : ℕ, Ideal.Quotient.mk (I ^ n) x = q n := by
  choose a ha using fun n => Ideal.Quotient.mk_surjective (q n)
  have hc : ∀ {m n : ℕ}, m ≤ n → a m ≡ a n [SMOD (I ^ m • ⊤ : Submodule R R)] := by
    intro m n hmn
    have he : Ideal.Quotient.mk (I ^ m) (a m) = Ideal.Quotient.mk (I ^ m) (a n) := by
      rw [ha m, ← hq hmn, ← ha n]
      rfl
    simpa using! he
  obtain ⟨x, hx⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I R) hc
  refine ⟨x, fun n => ?_⟩
  have he : Ideal.Quotient.mk (I ^ n) (a n) = Ideal.Quotient.mk (I ^ n) x := by
    simpa using! hx n
  rw [← he, ha n]

/-- The unique scalar coefficient supplied by the actual complete coefficient ring. -/
def scalarLimit [IsAdicComplete I R] (q : ∀ n : ℕ, R ⧸ I ^ n)
    (hq : ∀ {m n : ℕ} (hmn : m ≤ n), Ideal.Quotient.factorPow I hmn (q n) = q m) : R :=
  (exists_scalar_lift I q hq).choose

@[simp]
theorem mk_scalarLimit [IsAdicComplete I R] (q : ∀ n : ℕ, R ⧸ I ^ n)
    (hq : ∀ {m n : ℕ} (hmn : m ≤ n), Ideal.Quotient.factorPow I hmn (q n) = q m) (n : ℕ) :
    Ideal.Quotient.mk (I ^ n) (scalarLimit I q hq) = q n :=
  (exists_scalar_lift I q hq).choose_spec n

variable (σ)

/-- Separatedness detects equality of the original series through coefficient reduction. -/
theorem series_ext [IsHausdorff I R] {f g : MvPowerSeries σ R}
    (h : ∀ n : ℕ, MvPowerSeries.map (Ideal.Quotient.mk (I ^ n)) f =
      MvPowerSeries.map (Ideal.Quotient.mk (I ^ n)) g) : f = g := by
  ext d
  apply scalar_ext I
  intro n
  simpa only [coeff_map] using congrArg (coeff d) (h n)

theorem reduce_injective [IsHausdorff I R] : Function.Injective (reduce I σ) := by
  intro f g h
  apply series_ext I σ
  intro n
  exact congrArg (eval I σ n) h

theorem coefficient_compatible (f : CompatibleSeries I σ) (d : σ →₀ ℕ)
    {m n : ℕ} (hmn : m ≤ n) :
    Ideal.Quotient.factorPow I hmn (coeff d (f.val n)) = coeff d (f.val m) := by
  have he := congrArg (coeff d) ((compatible I σ f) hmn)
  simpa only [transition, coeff_map] using he

/-- The actual compatible family supplies the coefficients of a unique original series. -/
def lift [IsAdicComplete I R] (f : CompatibleSeries I σ) : MvPowerSeries σ R :=
  fun d => scalarLimit I (fun n => coeff d (f.val n)) (coefficient_compatible I σ f d)

@[simp]
theorem reduction_lift [IsAdicComplete I R] (f : CompatibleSeries I σ) (n : ℕ) :
    MvPowerSeries.map (Ideal.Quotient.mk (I ^ n)) (lift I σ f) = f.val n := by
  ext d
  rw [coeff_map]
  simpa only [lift, coeff_apply] using
    mk_scalarLimit I (fun n => coeff d (f.val n)) (coefficient_compatible I σ f d) n

theorem reduce_surjective [IsAdicComplete I R] : Function.Surjective (reduce I σ) := by
  intro f
  refine ⟨lift I σ f, ?_⟩
  apply Subtype.ext
  funext n
  exact reduction_lift I σ f n

/-- The actual power-series ring is the coefficientwise inverse limit as an R-algebra. -/
def equivalence [IsAdicComplete I R] : MvPowerSeries σ R ≃ₐ[R] CompatibleSeries I σ :=
  AlgEquiv.ofBijective (reduce I σ) ⟨reduce_injective I σ, reduce_surjective I σ⟩

@[simp]
theorem equivalence_toAlgHom [IsAdicComplete I R] :
    (equivalence I σ).toAlgHom = reduce I σ := rfl

@[simp]
theorem equivalence_symm_reduction [IsAdicComplete I R] (f : CompatibleSeries I σ) (n : ℕ) :
    MvPowerSeries.map (Ideal.Quotient.mk (I ^ n)) ((equivalence I σ).symm f) = f.val n := by
  exact congrArg (eval I σ n) ((equivalence I σ).apply_symm_apply f)

end DeJongAlterations.Algebra.NodeFormalMorse.CoefficientLimit
