/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Original authors: Chris Elliott (Resolution).

The bounded unipotent inverse-function proof is adapted from
EnvelopeProperty/deps/hironaka-ep33/Hironaka/Algebra/Local/FormalAut.lean,
source SHA256 41f69d4cd418cad1b86d19f97b6b48bf6b0f49a2b3f814700d583200d2ce8c0c. Only Mathlib and accepted local modules are imported.
-/
import DeJongAlterations.Algebra.NodeFormalMorseDecomposition
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Genuine tangent-identity formal substitutions for the original variable ideal -/

noncomputable section

namespace DeJongAlterations.Algebra.NodeVariableMorse

open MvPowerSeries NodeFormalMorse

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (K : Type u) [Field K]

/-- The actual original variable ideal, rather than an extended coefficient ideal. -/
abbrev variableIdeal : Ideal (Series K) := Ideal.span (Set.range (X : Fin 2 → Series K))

variable {K}

/-- The deterministic original decomposition puts zero-constant series in the variable ideal. -/
theorem mem_variableIdeal_of_constantCoeff_eq_zero {f : Series K} (hf : constantCoeff f = 0) :
    f ∈ variableIdeal K := by
  rw [decomposition f, hf, map_zero, zero_add]
  exact Ideal.add_mem _
    (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩))
    (Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨1, rfl⟩))

section Subst

variable {a : Fin 2 → MvPowerSeries (Fin 2) K} (ha : HasSubst a)
include ha

/-- Over a field, a substitutable family has zero constant coefficients. -/
theorem constantCoeff_eq_zero_of_hasSubst (i : Fin 2) : constantCoeff (a i) = 0 :=
  (ha.const_coeff i).eq_zero

theorem mem_variableIdeal_of_hasSubst (i : Fin 2) :
    a i ∈ variableIdeal K := by
  exact mem_variableIdeal_of_constantCoeff_eq_zero (constantCoeff_eq_zero_of_hasSubst ha i)

/-- A substitution maps the maximal ideal into itself. -/
theorem map_variableIdeal_le_of_hasSubst :
    (variableIdeal K).map (substAlgHom (R := K) ha) ≤
      variableIdeal K := by
  rw [Ideal.map_le_iff_le_comap]
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  rw [SetLike.mem_coe, Ideal.mem_comap, substAlgHom_X]
  exact mem_variableIdeal_of_hasSubst ha i

/-- A substitution maps every power of the maximal ideal into itself. -/
theorem subst_mem_variableIdeal_pow {k : ℕ} {f : MvPowerSeries (Fin 2) K}
    (hf : f ∈ variableIdeal K ^ k) :
    substAlgHom (R := K) ha f ∈ variableIdeal K ^ k := by
  have h1 : (variableIdeal K ^ k).map (substAlgHom (R := K) ha) ≤
      variableIdeal K ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_variableIdeal_le_of_hasSubst ha) k
  exact h1 (Ideal.mem_map_of_mem _ hf)

/-- A substitution maps the maximal ideal into itself, elementwise. -/
theorem subst_mem_variableIdeal {f : MvPowerSeries (Fin 2) K}
    (hf : f ∈ variableIdeal K) :
    substAlgHom (R := K) ha f ∈ variableIdeal K := by
  have := subst_mem_variableIdeal_pow ha (k := 1) (by rwa [pow_one])
  rwa [pow_one] at this

/-- The defect `φ(fg) - fg` of a substitution `φ` on a product. -/
theorem substAlgHom_mul_sub (f g : MvPowerSeries (Fin 2) K) :
    substAlgHom (R := K) ha (f * g) - f * g =
      (substAlgHom (R := K) ha f - f) * substAlgHom (R := K) ha g +
        f * (substAlgHom (R := K) ha g - g) := by
  rw [map_mul]; ring

end Subst

/-! ### Unipotent substitutions are automorphisms

Let `φ = substAlgHom ha` with `a i ≡ Xᵢ (mod 𝔪²)`.  The defect `φ f - f` raises the `𝔪`-adic
order: `f ∈ 𝔪^k` implies `φ f - f ∈ 𝔪^(k+1)`.  This is proved by induction on `k` from the two
base facts `φ r - r ∈ 𝔪` (every `r`) and `φ x - x ∈ 𝔪²` (`x ∈ 𝔪`), both by induction over the
generators `Xᵢ` of `𝔪` using the product formula `substAlgHom_mul_sub`.  Injectivity then
follows because a series killed by `φ` lies in every `𝔪^k`, and `K⟦X⟧` is `𝔪`-adically
Hausdorff; surjectivity by successive approximation `u₀ = 0`, `uₖ₊₁ = uₖ + (f - φ uₖ)`, whose
residuals `f - φ uₖ` lie in `𝔪^k`, so that the sequence converges by `𝔪`-adic completeness to a
preimage of `f`. -/

section Unipotent

variable {a : Fin 2 → MvPowerSeries (Fin 2) K} (ha : HasSubst a)
include ha

theorem substAlgHom_sub_mem_of_mem (h : ∀ i, a i - X i ∈ variableIdeal K)
    {x : MvPowerSeries (Fin 2) K} (hx : x ∈ variableIdeal K) :
    substAlgHom (R := K) ha x - x ∈ variableIdeal K := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [substAlgHom_X]
    exact h i
  | zero => rw [map_zero, sub_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    convert Ideal.add_mem _ hx hy using 1
    ring
  | smul r x hx' hx =>
    rw [smul_eq_mul, substAlgHom_mul_sub]
    have hφx : substAlgHom (R := K) ha x ∈ variableIdeal K :=
      subst_mem_variableIdeal ha (by exact hx')
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hφx) (Ideal.mul_mem_left _ _ hx)

/-- If the `a i` are congruent to `Xᵢ` modulo `𝔪`, the substitution changes every series by an
element of `𝔪`. -/
theorem substAlgHom_sub_mem (h : ∀ i, a i - X i ∈ variableIdeal K)
    (r : MvPowerSeries (Fin 2) K) :
    substAlgHom (R := K) ha r - r ∈ variableIdeal K := by
  have hr : r - C (constantCoeff r) ∈ variableIdeal K := by
      exact mem_variableIdeal_of_constantCoeff_eq_zero (by simp)
  have hC : substAlgHom (R := K) ha (C (constantCoeff r)) = C (constantCoeff r) := by
    rw [c_eq_algebraMap]
    exact AlgHom.commutes _ _
  have := substAlgHom_sub_mem_of_mem ha h hr
  rwa [map_sub, hC, sub_sub_sub_cancel_right] at this

/-- If the `a i` are congruent to `Xᵢ` modulo `𝔪²`, the substitution changes every element of
`𝔪` by an element of `𝔪²`. -/
theorem substAlgHom_sub_mem_sq
    (h₂ : ∀ i, a i - X i ∈ variableIdeal K ^ 2)
    {x : MvPowerSeries (Fin 2) K} (hx : x ∈ variableIdeal K) :
    substAlgHom (R := K) ha x - x ∈ variableIdeal K ^ 2 := by
  have h₁ : ∀ i, a i - X i ∈ variableIdeal K := fun i =>
    Ideal.pow_le_self two_ne_zero (h₂ i)
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [substAlgHom_X]
    exact h₂ i
  | zero => rw [map_zero, sub_zero]; exact Ideal.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add]
    convert Ideal.add_mem _ hx hy using 1
    ring
  | smul r x hx' hx =>
    rw [smul_eq_mul, substAlgHom_mul_sub]
    have hφx : substAlgHom (R := K) ha x ∈ variableIdeal K :=
      subst_mem_variableIdeal ha (by exact hx')
    refine Ideal.add_mem _ ?_ (Ideal.mul_mem_left _ _ hx)
    rw [pow_two]
    exact Ideal.mul_mem_mul (substAlgHom_sub_mem ha h₁ r) hφx

/-- The defect of a unipotent substitution raises the `𝔪`-adic order by one. -/
theorem substAlgHom_sub_mem_pow_succ
    (h₂ : ∀ i, a i - X i ∈ variableIdeal K ^ 2) (k : ℕ)
    {f : MvPowerSeries (Fin 2) K} (hf : f ∈ variableIdeal K ^ k) :
    substAlgHom (R := K) ha f - f ∈ variableIdeal K ^ (k + 1) := by
  induction k generalizing f with
  | zero =>
    rw [zero_add, pow_one]
    exact substAlgHom_sub_mem ha (fun i => Ideal.pow_le_self two_ne_zero (h₂ i)) f
  | succ k ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun r hr s hs => ?_) (fun x y hx hy => ?_)
    · rw [substAlgHom_mul_sub]
      have hφs : substAlgHom (R := K) ha s ∈ variableIdeal K :=
        subst_mem_variableIdeal ha hs
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_succ]
        exact Ideal.mul_mem_mul (ih hr) hφs
      · rw [show k + 1 + 1 = k + 2 by ring, pow_add]
        exact Ideal.mul_mem_mul hr (substAlgHom_sub_mem_sq ha h₂ hs)
    · rw [map_add]
      convert Ideal.add_mem _ hx hy using 1
      ring

theorem substAlgHom_injective_of_sub_X_mem_sq
    (h₂ : ∀ i, a i - X i ∈ variableIdeal K ^ 2) :
    Function.Injective (substAlgHom (R := K) ha) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  have hk : ∀ k, f ∈ variableIdeal K ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := substAlgHom_sub_mem_pow_succ ha h₂ k ih
      rwa [hf, zero_sub, Ideal.neg_mem_iff] at this
  exact IsHausdorff.haus
    (inferInstance : IsHausdorff (Ideal.span (Set.range (X : Fin 2 → MvPowerSeries (Fin 2) K)))
      (MvPowerSeries (Fin 2) K)) f fun k => by
    rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
    exact hk k

theorem substAlgHom_surjective_of_sub_X_mem_sq
    (h₂ : ∀ i, a i - X i ∈ variableIdeal K ^ 2) :
    Function.Surjective (substAlgHom (R := K) ha) := by
  intro f
  set φ := substAlgHom (R := K) ha with hφ
  set I : Ideal (MvPowerSeries (Fin 2) K) := Ideal.span (Set.range X) with hI
  have hmI : variableIdeal K = I := rfl
  -- successive approximation
  let u : ℕ → MvPowerSeries (Fin 2) K := fun k => Nat.rec 0 (fun _ v => v + (f - φ v)) k
  have huS : ∀ k, u (k + 1) = u k + (f - φ (u k)) := fun k => rfl
  have hres : ∀ k, f - φ (u k) ∈ I ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := substAlgHom_sub_mem_pow_succ ha h₂ k (hmI ▸ ih)
      rw [hmI, map_sub] at this
      rw [huS, map_add, map_sub, ← Ideal.neg_mem_iff]
      convert this using 1
      ring
  have hcauchy : ∀ m k, m ≤ k → u k - u m ∈ I ^ m := by
    intro m k hmk
    induction k, hmk using Nat.le_induction with
    | base => simp
    | succ k hmk ih =>
      rw [huS, add_sub_right_comm]
      exact Ideal.add_mem _ ih (Ideal.pow_le_pow_right hmk (hres k))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec
    (inferInstance : IsPrecomplete I (MvPowerSeries (Fin 2) K)) (f := u) fun {m k} hmk => by
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, ← Ideal.neg_mem_iff, neg_sub]
      exact hcauchy m k hmk
  refine ⟨L, ?_⟩
  have hLk : ∀ k, φ L - f ∈ I ^ k := by
    intro k
    have h1 : u k - L ∈ I ^ k := by
      have := hL k
      rwa [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top] at this
    have h2 : φ (L - u k) ∈ I ^ k := by
      rw [← hmI] at h1 ⊢
      exact subst_mem_variableIdeal_pow ha (by rw [← Ideal.neg_mem_iff, neg_sub]; exact h1)
    have := Ideal.sub_mem _ h2 (hres k)
    rwa [map_sub, sub_sub_sub_cancel_right] at this
  have := IsHausdorff.haus (inferInstance : IsHausdorff I (MvPowerSeries (Fin 2) K)) (φ L - f)
    fun k => by
      rw [SModEq.sub_mem, sub_zero, Ideal.smul_eq_mul, Ideal.mul_top]
      exact hLk k
  exact sub_eq_zero.mp this

/-- A substitution `Xᵢ ↦ a i` with `a i ≡ Xᵢ (mod 𝔪²)` is an automorphism of `K⟦X⟧` (one half
of the criterion of [Kol07, Notation 93]). -/
theorem bijective_substAlgHom_of_sub_X_mem_sq
    (h₂ : ∀ i, a i - X i ∈ variableIdeal K ^ 2) :
    Function.Bijective (substAlgHom (R := K) ha) :=
  ⟨substAlgHom_injective_of_sub_X_mem_sq ha h₂, substAlgHom_surjective_of_sub_X_mem_sq ha h₂⟩

end Unipotent
/-- The actual tangent-identity native substitution automorphism is constructed internally. -/
def unipotentEquiv (a : Fin 2 → Series K) (ha : HasSubst a)
    (h₂ : ∀ i, a i - X i ∈ variableIdeal K ^ 2) : Series K ≃ₐ[K] Series K :=
  AlgEquiv.ofBijective (substAlgHom (R := K) ha)
    (bijective_substAlgHom_of_sub_X_mem_sq ha h₂)

/-- The actual inverse preserves each original variable-ideal power. -/
theorem unipotentEquiv_symm_mem_pow (a : Fin 2 → Series K) (ha : HasSubst a)
    (h₂ : ∀ i, a i - X i ∈ variableIdeal K ^ 2) (k : ℕ)
    (f : Series K) (hf : f ∈ variableIdeal K ^ k) :
    (unipotentEquiv a ha h₂).symm f ∈ variableIdeal K ^ k := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    have hg := ih f (Ideal.pow_le_pow_right (Nat.le_succ k) hf)
    have hd := substAlgHom_sub_mem_pow_succ ha h₂ k hg
    change unipotentEquiv a ha h₂ ((unipotentEquiv a ha h₂).symm f) -
      (unipotentEquiv a ha h₂).symm f ∈ variableIdeal K ^ (k + 1) at hd
    rw [AlgEquiv.apply_symm_apply] at hd
    have he : (unipotentEquiv a ha h₂).symm f =
        f - (f - (unipotentEquiv a ha h₂).symm f) := by abel
    rw [he]
    exact Ideal.sub_mem _ hf hd

/-- The original inverse coordinate family has the same original identity linear part. -/
theorem unipotentEquiv_symm_coordinate (a : Fin 2 → Series K) (ha : HasSubst a)
    (h₂ : ∀ i, a i - X i ∈ variableIdeal K ^ 2) (i : Fin 2) :
    (unipotentEquiv a ha h₂).symm (X i) - X i ∈ variableIdeal K ^ 2 := by
  have hx : (X i : Series K) ∈ variableIdeal K ^ 1 := by
    rw [pow_one]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hg := unipotentEquiv_symm_mem_pow a ha h₂ 1 (X i) hx
  have hd := substAlgHom_sub_mem_pow_succ ha h₂ 1 hg
  change unipotentEquiv a ha h₂ ((unipotentEquiv a ha h₂).symm (X i)) -
    (unipotentEquiv a ha h₂).symm (X i) ∈ variableIdeal K ^ 2 at hd
  rw [AlgEquiv.apply_symm_apply] at hd
  simpa only [neg_sub] using (variableIdeal K ^ 2).neg_mem hd

end DeJongAlterations.Algebra.NodeVariableMorse
