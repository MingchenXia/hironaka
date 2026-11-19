import Hironaka.Analytic.Unibranch.HironakaG10LfChartAlgebra
import Mathlib.RingTheory.Ideal.Over

/-!
# Base change of a cokernel to `R ⧸ I` as a cokernel over `B ⧸ I B` (lane G10LF, ALG-3 of G10GN's route N)

For an `R`-algebra `B`, an ideal `I ⊆ R` and a matrix `F` over `B`:
**`baseChangeCokerEquiv`** : `(R ⧸ I) ⊗[R] ((Fin a → B) ⧸ range F) ≃ₗ[R ⧸ I]
(Fin a → B ⧸ I B) ⧸ range (F mod I B)`, and **`flat_baseChange_coker_iff`**: flatness over `R ⧸ I` of the two
sides agrees. (With `R = 𝒪_d`, `B = 𝒪_{d+t}` the left side is lane G10MW's `ChartFlat`.)

No named input. BP: hironaka-g10lf-generic-freeness.tex.
-/

set_option autoImplicit false

open Function TensorProduct
open scoped Matrix

namespace Hironaka.Analytic.Unibranch.HironakaG10LfQuotientCoker

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (I : Ideal R)

/-- Coordinatewise reduction `Bᵃ → (B ⧸ I B)ᵃ`. -/
noncomputable def reduce (a : ℕ) : (Fin a → B) →ₗ[B] (Fin a → B ⧸ I.map (algebraMap R B)) :=
  LinearMap.pi fun i => (Submodule.mkQ (I.map (algebraMap R B))).comp (LinearMap.proj i)

theorem reduce_apply {a : ℕ} (v : Fin a → B) (i : Fin a) :
    reduce I a v i = Ideal.Quotient.mk (I.map (algebraMap R B)) (v i) := rfl

theorem reduce_surjective (a : ℕ) : Surjective (reduce (R := R) (B := B) I a) := by
  intro w
  choose v hv using fun i => Ideal.Quotient.mk_surjective (w i)
  exact ⟨v, funext fun i => hv i⟩

theorem reduce_mulVec {a b : ℕ} (F : Matrix (Fin a) (Fin b) B) (u : Fin b → B) :
    reduce I a (F *ᵥ u) =
      (F.map (Ideal.Quotient.mk (I.map (algebraMap R B)))) *ᵥ reduce I b u := by
  funext i
  rw [reduce_apply, RingHom.map_mulVec]
  rfl

theorem reduce_eq_zero_iff {a : ℕ} (v : Fin a → B) :
    reduce I a v = 0 ↔ ∀ i, v i ∈ I.map (algebraMap R B) := by
  constructor
  · intro h i
    have := congrFun h i
    rwa [reduce_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem] at this
  · intro h
    funext i
    rw [reduce_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]
    exact h i

variable {a b : ℕ} (F : Matrix (Fin a) (Fin b) B)

/-- **ALG-3: the base change of `coker F` to `R ⧸ I` is the cokernel of `F` modulo `I B`.** -/
noncomputable def baseChangeCokerEquiv :
    (R ⧸ I) ⊗[R] ((Fin a → B) ⧸ LinearMap.range F.mulVecLin) ≃ₗ[R ⧸ I]
      (Fin a → B ⧸ I.map (algebraMap R B)) ⧸
        LinearMap.range (F.map (Ideal.Quotient.mk (I.map (algebraMap R B)))).mulVecLin := by
  let IB := I.map (algebraMap R B)
  let Fb := F.map (Ideal.Quotient.mk IB)
  let ψ₀ : (Fin a → B) →ₗ[B] (Fin a → B ⧸ IB) ⧸ LinearMap.range Fb.mulVecLin :=
    ((LinearMap.range Fb.mulVecLin).mkQ.restrictScalars B).comp (reduce I a)
  have hψ : LinearMap.range F.mulVecLin ≤ LinearMap.ker ψ₀ := by
    rintro _ ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    change Submodule.Quotient.mk (reduce I a (F *ᵥ u)) = 0
    rw [reduce_mulVec, Submodule.Quotient.mk_eq_zero]
    exact ⟨reduce I b u, rfl⟩
  let ψ := (LinearMap.range F.mulVecLin).liftQ ψ₀ hψ
  let Φ := (ψ.restrictScalars R).liftBaseChange (R ⧸ I)
  let T := (R ⧸ I) ⊗[R] ((Fin a → B) ⧸ LinearMap.range F.mulVecLin)
  let Ψ₀ : (Fin a → B) →ₗ[R] T :=
    (TensorProduct.mk R (R ⧸ I) ((Fin a → B) ⧸ LinearMap.range F.mulVecLin) 1).comp
      ((LinearMap.range F.mulVecLin).mkQ.restrictScalars R)
  have hΨ₀ : ∀ v : Fin a → B, (∀ i, v i ∈ IB) → Ψ₀ v = 0 := by
    intro v hv
    rw [← HironakaG10LfChartAlgebra.mem_smul_top_pi_iff] at hv
    refine Submodule.smul_induction_on (p := fun v => Ψ₀ v = 0) hv ?_ ?_
    · intro α hα y _
      rw [map_smul]
      change α • ((1 : R ⧸ I) ⊗ₜ[R] _) = (0 : T)
      rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq,
        (Ideal.Quotient.eq_zero_iff_mem).2 hα, TensorProduct.zero_tmul]
    · intro y₁ y₂ h₁ h₂
      rw [map_add, h₁, h₂, add_zero]
  let πR := (reduce (R := R) (B := B) I a).restrictScalars R
  have hπR : Surjective πR := reduce_surjective I a
  have hker : LinearMap.ker πR ≤ LinearMap.ker Ψ₀ := by
    intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    exact hΨ₀ v ((reduce_eq_zero_iff I v).1 hv)
  let e := πR.quotKerEquivOfSurjective hπR
  let Ψ₁ : (Fin a → B ⧸ IB) →ₗ[R] T := (LinearMap.ker πR).liftQ Ψ₀ hker ∘ₗ e.symm.toLinearMap
  have hΨ₁ : ∀ v, Ψ₁ (reduce I a v) = Ψ₀ v := by
    intro v
    have h1 : e.symm (πR v) = Submodule.Quotient.mk v := by
      rw [LinearEquiv.symm_apply_eq]
      rfl
    change (LinearMap.ker πR).liftQ Ψ₀ hker (e.symm (πR v)) = Ψ₀ v
    rw [h1, Submodule.liftQ_apply]
  have hΨ₁F : (LinearMap.range Fb.mulVecLin).restrictScalars R ≤ LinearMap.ker Ψ₁ := by
    rintro _ ⟨u', rfl⟩
    obtain ⟨u, rfl⟩ := reduce_surjective I b u'
    rw [LinearMap.mem_ker]
    change Ψ₁ (Fb *ᵥ reduce I b u) = 0
    rw [← reduce_mulVec, hΨ₁]
    change (1 : R ⧸ I) ⊗ₜ[R] Submodule.Quotient.mk (F *ᵥ u) = 0
    have h0 : (Submodule.Quotient.mk (F *ᵥ u) : (Fin a → B) ⧸ LinearMap.range F.mulVecLin) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self F.mulVecLin u)
    rw [h0, TensorProduct.tmul_zero]
  let Ψ : (Fin a → B ⧸ IB) ⧸ LinearMap.range Fb.mulVecLin →ₗ[R] T :=
    ((LinearMap.range Fb.mulVecLin).restrictScalars R).liftQ Ψ₁ hΨ₁F ∘ₗ
      (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range Fb.mulVecLin)).symm.toLinearMap
  have hΨ : ∀ v, Ψ (Submodule.Quotient.mk (reduce I a v)) = Ψ₀ v := by
    intro v
    change ((LinearMap.range Fb.mulVecLin).restrictScalars R).liftQ Ψ₁ hΨ₁F
      (Submodule.Quotient.mk (reduce I a v)) = Ψ₀ v
    rw [Submodule.liftQ_apply, hΨ₁]
  have hΦ : ∀ (r : R) (v : Fin a → B), Φ (Ideal.Quotient.mk I r ⊗ₜ[R] Submodule.Quotient.mk v) =
      r • Submodule.Quotient.mk (reduce I a v) := by
    intro r v
    rw [LinearMap.liftBaseChange_tmul, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul]
    rfl
  refine
    { Φ with
      invFun := Ψ
      left_inv := fun t => ?_
      right_inv := fun q => ?_ }
  · change Ψ (Φ t) = t
    induction t using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul r n =>
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ n
      rw [Submodule.mkQ_apply, hΦ, map_smul, hΨ]
      change r • ((1 : R ⧸ I) ⊗ₜ[R] Submodule.Quotient.mk v) = _
      rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  · change Φ (Ψ q) = q
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨v, rfl⟩ := reduce_surjective I a w
    rw [Submodule.mkQ_apply, hΨ]
    change Φ ((1 : R ⧸ I) ⊗ₜ[R] Submodule.Quotient.mk v) = _
    rw [← map_one (Ideal.Quotient.mk I), hΦ, one_smul]

/-- **ALG-3, flatness form.** -/
theorem flat_baseChange_coker_iff :
    Module.Flat (R ⧸ I) ((R ⧸ I) ⊗[R] ((Fin a → B) ⧸ LinearMap.range F.mulVecLin)) ↔
      Module.Flat (R ⧸ I) ((Fin a → B ⧸ I.map (algebraMap R B)) ⧸
        LinearMap.range (F.map (Ideal.Quotient.mk (I.map (algebraMap R B)))).mulVecLin) := by
  constructor
  · intro h
    exact Module.Flat.of_linearEquiv (baseChangeCokerEquiv I F).symm
  · intro h
    exact Module.Flat.of_linearEquiv (baseChangeCokerEquiv I F)

end Hironaka.Analytic.Unibranch.HironakaG10LfQuotientCoker
