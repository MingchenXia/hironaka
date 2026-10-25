/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.Defect
import DeJongAlterations.StableModification.Valuation.Analytic.Hensel
import DeJongAlterations.StableModification.Valuation.Unramified
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Inertia and wild inertia of finite extensions of analytic fields

Let `K` be an analytic field (`[NontriviallyNormedField K] [IsUltrametricDist K]
[CompleteSpace K]`) and `N/K` a finite extension of normed fields. Every `K`-automorphism of `N`
is an isometry (`norm_algEquiv_apply`). This file introduces the inertia subgroup
`T = {σ | ‖σ x - x‖ < 1 for ‖x‖ ≤ 1}` and the wild inertia subgroup
`V = {σ | ‖σ x - x‖ < ‖x‖ for x ≠ 0}` of `Gal(N/K)` and proves the facts that replace Temkin's
use of the maximal moderately ramified extension `K^mr` in *Stable modification of relative
curves*, J. Algebraic Geom. 19 (2010), proof of Theorem 6.3.1 (`semi-stable.tex`,
lines 4057–4061 and 4091–4093); see plan simplification S5 (`PLAN-SM-VAL.md`).

## Main definitions

* `inertiaSubgroup K N`, `wildInertiaSubgroup K N`: the subgroups `T ⊇ V`, both normal.
* `normedAlgebraIntermediateField`: an intermediate field `E` of `N/K`, with the restricted norm,
  is a normed field over which `N` is a normed algebra.

## Main results

* `eq_of_forall_norm_pow_sub_lt` (**the trace argument**): an automorphism `σ` with
  `σ^d = 1` on an additive subgroup `S`, `‖d‖ = 1`, and `‖σ^i y - y‖ < ‖y‖` on `S ∖ 0`, is the
  identity on `S`.
* `isPGroup_wildInertiaSubgroup`: `V` is a `p`-group, `p` the exponential characteristic of the
  residue field of `K`.
* `wildInertiaSubgroup_eq_inertiaSubgroup` (`e = 1 ⇒ T = V`) and `inertiaSubgroup_eq_top`
  (`f = 1 ⇒ T = Gal(N/K)`).
* `eq_of_isRoot_of_norm_sub_lt_one` (uniqueness of Hensel lifts) and
  `mem_fixedField_inertiaSubgroup_of_isRoot`: `T` fixes Hensel lifts of simple roots.
* `exists_inertiaField_generator`, `isStdUnramified_inertiaField`, `inertiaDegree_inertiaField`,
  `isSeparable_residueField_inertiaField`, `isPurelyInseparable_residueField_inertiaField`: the
  inertia field `Z = N^T` is standard-unramified over `K`, `[Z̃ : K̃] = [Z : K]`, `Z̃/K̃` is
  separable and `Ñ/Z̃` is purely inseparable; `finrank_inertiaField`: `[Z : K] = [Ñ_s : K̃]`.

## References

Blueprint chapter `sm-val-ramification.tex`.
-/

noncomputable section

open IsLocalRing Polynomial IntermediateField
open scoped NNReal

namespace DeJongAlterations.StableModification.Valuation.Analytic

/-! ### The trace argument -/

section Trace

variable {F E : Type*} [Field F] [NormedField E] [IsUltrametricDist E] [Algebra F E]

/-- **The trace argument** (plan simplification S5(a)). Let `σ` be an automorphism of a
non-archimedean normed field `E`, `S` an additive subgroup with `σ S ⊆ S`, and `d` an integer with
`‖d‖ = 1` and `σ ^ d = 1` on `S`. If `‖σ ^ i y - y‖ < ‖y‖` for every `i` and every nonzero
`y ∈ S`, then `σ` is the identity on `S`. -/
theorem eq_of_forall_norm_pow_sub_lt (σ : E ≃ₐ[F] E) (S : AddSubgroup E)
    (hS : ∀ x ∈ S, σ x ∈ S) {d : ℕ} (hd : ‖(d : E)‖ = 1) (hσd : ∀ x ∈ S, (σ ^ d) x = x)
    (hV : ∀ i : ℕ, ∀ y ∈ S, y ≠ 0 → ‖(σ ^ i) y - y‖ < ‖y‖) {x : E} (hx : x ∈ S) :
    σ x = x := by
  have hd0 : (d : E) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd
    exact zero_ne_one hd
  have hdpos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · exact absurd (by rw [h, Nat.cast_zero]) hd0
    · exact h
  have hpowS : ∀ i : ℕ, ∀ y ∈ S, (σ ^ i) y ∈ S := by
    intro i
    induction i with
    | zero => intro y hy; simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', AlgEquiv.mul_apply]
      exact hS _ (ih y hy)
  -- the trace `Σ y = ∑_{i < d} σ ^ i y`
  set Sig : E → E := fun y => ∑ i ∈ Finset.range d, (σ ^ i) y with hSig
  have hSigS : ∀ y ∈ S, Sig y ∈ S := fun y hy => AddSubgroup.sum_mem _ fun i _ => hpowS i y hy
  have hσSig : ∀ y ∈ S, σ (Sig y) = Sig y := by
    intro y hy
    have h1 := Finset.sum_range_succ' (fun i => (σ ^ i) y) d
    have h2 := Finset.sum_range_succ (fun i => (σ ^ i) y) d
    have h3 : σ (Sig y) = ∑ i ∈ Finset.range d, (σ ^ (i + 1)) y := by
      simp only [hSig, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_succ', AlgEquiv.mul_apply]
    rw [h3]
    simp only [hσd y hy, pow_zero, AlgEquiv.one_apply] at h1 h2
    have := h1.symm.trans h2
    exact add_right_cancel this
  have hpowSig : ∀ i : ℕ, ∀ y ∈ S, (σ ^ i) (Sig y) = Sig y := by
    intro i
    induction i with
    | zero => intro y _; simp
    | succ n ih =>
      intro y hy
      rw [pow_succ', AlgEquiv.mul_apply, ih y hy, hσSig y hy]
  have hSigSig : ∀ y ∈ S, Sig (Sig y) = (d : E) * Sig y := by
    intro y hy
    simp only [hSig] at hpowSig ⊢
    rw [Finset.sum_congr rfl fun i _ => hpowSig i y hy, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hSigmul : ∀ y : E, Sig ((d : E) * y) = (d : E) * Sig y := by
    intro y
    simp only [hSig, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_natCast]
  have hSigsub : ∀ y z : E, Sig (y - z) = Sig y - Sig z := by
    intro y z
    simp only [hSig, map_sub, Finset.sum_sub_distrib]
  -- `y₀ = d x - Σ x` has trace zero
  set y₀ := (d : E) * x - Sig x with hy₀
  have hy₀S : y₀ ∈ S := by
    refine S.sub_mem ?_ (hSigS x hx)
    have : (d : E) * x = d • x := by rw [nsmul_eq_mul]
    rw [this]
    exact S.nsmul_mem hx d
  have hSigy₀ : Sig y₀ = 0 := by
    rw [hy₀, hSigsub, hSigmul, hSigSig x hx, sub_self]
  have hy₀0 : y₀ = 0 := by
    by_contra hne
    have hypos : 0 < ‖y₀‖ := norm_pos_iff.mpr hne
    have hsplit : Sig y₀ = (d : E) * y₀ + ∑ i ∈ Finset.range d, ((σ ^ i) y₀ - y₀) := by
      simp only [hSig, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul]
      ring
    have hrest : ‖∑ i ∈ Finset.range d, ((σ ^ i) y₀ - y₀)‖ < ‖y₀‖ := by
      obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
        (Finset.nonempty_range_iff.mpr hdpos.ne') (fun i => (σ ^ i) y₀ - y₀)
      exact hi.trans_lt (hV i y₀ hy₀S hne)
    have hdy : ‖(d : E) * y₀‖ = ‖y₀‖ := by rw [norm_mul, hd, one_mul]
    have : ‖Sig y₀‖ = ‖y₀‖ := by
      rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hdy]; exact hrest.ne'),
        hdy, max_eq_left hrest.le]
    rw [hSigy₀, norm_zero] at this
    exact hypos.ne this
  have hdx : (d : E) * x = Sig x := sub_eq_zero.mp hy₀0
  have : (d : E) * σ x = (d : E) * x := by
    calc (d : E) * σ x = σ ((d : E) * x) := by rw [map_mul, map_natCast]
      _ = σ (Sig x) := by rw [hdx]
      _ = Sig x := hσSig x hx
      _ = (d : E) * x := hdx.symm
  exact mul_left_cancel₀ hd0 this

end Trace

/-! ### Inertia and wild inertia -/

section Inertia

variable (K N : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedField N] [IsUltrametricDist N] [NormedAlgebra K N] [Algebra.IsAlgebraic K N]

/-- The **inertia subgroup** `T(N/K) = {σ | ‖σ x - x‖ < 1 for all x ∈ N°}`: the kernel of the
action of `Gal(N/K)` on the residue field of `N`. -/
def inertiaSubgroup : Subgroup (N ≃ₐ[K] N) where
  carrier := {σ | ∀ x : N, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1}
  mul_mem' := by
    intro σ τ hσ hτ x hx
    have hτx : ‖τ x‖ ≤ 1 := by rwa [norm_algEquiv_apply]
    calc ‖(σ * τ) x - x‖ = ‖(σ (τ x) - τ x) + (τ x - x)‖ := by
          rw [AlgEquiv.mul_apply]; ring_nf
      _ ≤ max ‖σ (τ x) - τ x‖ ‖τ x - x‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < 1 := max_lt (hσ _ hτx) (hτ x hx)
  one_mem' := by
    intro x _
    simp
  inv_mem' := by
    intro σ hσ x hx
    have := hσ x hx
    rwa [← norm_algEquiv_apply σ, map_sub, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply,
      norm_sub_rev]

/-- The **wild inertia subgroup** `V(N/K) = {σ | ‖σ x - x‖ < ‖x‖ for all x ≠ 0}`. -/
def wildInertiaSubgroup : Subgroup (N ≃ₐ[K] N) where
  carrier := {σ | ∀ x : N, x ≠ 0 → ‖σ x - x‖ < ‖x‖}
  mul_mem' := by
    intro σ τ hσ hτ x hx
    have hτx0 : τ x ≠ 0 := (_root_.map_ne_zero τ).mpr hx
    have hτx : ‖τ x‖ = ‖x‖ := norm_algEquiv_apply τ x
    calc ‖(σ * τ) x - x‖ = ‖(σ (τ x) - τ x) + (τ x - x)‖ := by
          rw [AlgEquiv.mul_apply]; ring_nf
      _ ≤ max ‖σ (τ x) - τ x‖ ‖τ x - x‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < ‖x‖ := max_lt (hτx ▸ hσ _ hτx0) (hτ x hx)
  one_mem' := by
    intro x hx
    simpa using norm_pos_iff.mpr hx
  inv_mem' := by
    intro σ hσ x hx
    have := hσ x hx
    rwa [← norm_algEquiv_apply σ, map_sub, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply,
      norm_sub_rev]

variable {K N}

theorem mem_inertiaSubgroup_iff {σ : N ≃ₐ[K] N} :
    σ ∈ inertiaSubgroup K N ↔ ∀ x : N, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := Iff.rfl

theorem mem_wildInertiaSubgroup_iff {σ : N ≃ₐ[K] N} :
    σ ∈ wildInertiaSubgroup K N ↔ ∀ x : N, x ≠ 0 → ‖σ x - x‖ < ‖x‖ := Iff.rfl

instance inertiaSubgroup_normal : (inertiaSubgroup K N).Normal where
  conj_mem σ hσ ρ := by
    intro x hx
    have hx' : ‖ρ⁻¹ x‖ ≤ 1 := by rwa [norm_algEquiv_apply]
    have := hσ _ hx'
    have h1 : ρ (ρ⁻¹ x) = x := by rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    rw [← norm_algEquiv_apply ρ, map_sub, h1] at this
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    exact this

instance wildInertiaSubgroup_normal : (wildInertiaSubgroup K N).Normal where
  conj_mem σ hσ ρ := by
    intro x hx
    have hx0 : ρ⁻¹ x ≠ 0 := (_root_.map_ne_zero _).mpr hx
    have := hσ _ hx0
    have h1 : ρ (ρ⁻¹ x) = x := by rw [AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    rw [← norm_algEquiv_apply ρ, map_sub, ← norm_algEquiv_apply ρ (ρ⁻¹ x), h1] at this
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    exact this

theorem wildInertiaSubgroup_le_inertiaSubgroup : wildInertiaSubgroup K N ≤ inertiaSubgroup K N := by
  intro σ hσ x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  · exact (hσ x hx0).trans_le hx

/-- The powers of an element of the wild inertia subgroup act like it. -/
theorem norm_pow_apply_sub_lt {σ : N ≃ₐ[K] N} (hσ : σ ∈ wildInertiaSubgroup K N) (i : ℕ)
    {y : N} (hy : y ≠ 0) : ‖(σ ^ i) y - y‖ < ‖y‖ :=
  (wildInertiaSubgroup K N).pow_mem hσ i y hy

end Inertia

/-! ### The wild inertia subgroup is a `p`-group -/

section PGroup

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

/-- An integer has absolute value one iff its image in the residue field is nonzero. -/
theorem norm_natCast_eq_one_iff (n : ℕ) :
    ‖(n : K)‖ = 1 ↔ (n : ResidueField (unitBall K)) ≠ 0 := by
  have hn : ((n : unitBall K) : K) = n := by simp
  have hle : ‖(n : K)‖ ≤ 1 := by rw [← hn]; exact norm_coe_unitBall_le_one _
  rw [← map_natCast (residue (unitBall K)), Ne, residue_eq_zero_iff,
    mem_maximalIdeal_unitBall_iff, hn, not_lt]
  exact ⟨fun h => h.ge, fun h => le_antisymm hle h⟩

variable [CompleteSpace K] {N : Type*} [NormedField N] [IsUltrametricDist N] [NormedAlgebra K N]
  [FiniteDimensional K N]

/-- An element of the wild inertia subgroup whose order `d` satisfies `‖d‖ = 1` is trivial. -/
theorem eq_one_of_mem_wildInertiaSubgroup {τ : N ≃ₐ[K] N} (hτ : τ ∈ wildInertiaSubgroup K N)
    (h : ‖(orderOf τ : K)‖ = 1) : τ = 1 := by
  have hd : ‖(orderOf τ : N)‖ = 1 := by
    rw [← map_natCast (algebraMap K N), norm_algebraMap', h]
  ext x
  refine eq_of_forall_norm_pow_sub_lt τ ⊤ (fun _ _ => trivial) hd (fun x _ => ?_)
    (fun i y _ hy => norm_pow_apply_sub_lt hτ i hy) (AddSubgroup.mem_top x)
  rw [pow_orderOf_eq_one, AlgEquiv.one_apply]

/-- **The wild inertia subgroup is a `p`-group** (plan simplification S5(a); replaces Temkin's
use of the pro-`p` group `Gal(K^s/K^mr)`, `semi-stable.tex` lines 4057–4061), where `p` is the
exponential characteristic of the residue field of `K`. -/
theorem isPGroup_wildInertiaSubgroup (p : ℕ) [hp : ExpChar (ResidueField (unitBall K)) p] :
    IsPGroup p (wildInertiaSubgroup K N) := by
  intro τ
  have hfin : IsOfFinOrder (τ : N ≃ₐ[K] N) := isOfFinOrder_of_finite _
  have hn : orderOf (τ : N ≃ₐ[K] N) ≠ 0 := (orderOf_pos_iff.mpr hfin).ne'
  cases hp with
  | zero =>
    refine ⟨0, Subtype.ext ?_⟩
    rw [pow_zero, pow_one, OneMemClass.coe_one]
    refine eq_one_of_mem_wildInertiaSubgroup τ.2 ((norm_natCast_eq_one_iff _).mpr ?_)
    exact Nat.cast_ne_zero.mpr hn
  | prime hprime =>
    obtain ⟨k, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hprime.ne_one
    refine ⟨k, Subtype.ext ?_⟩
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    have hk : p ^ k ≠ 0 := pow_ne_zero _ hprime.ne_zero
    have hord : orderOf ((τ : N ≃ₐ[K] N) ^ p ^ k) = m := by
      rw [orderOf_pow_of_dvd hk ⟨m, hnm⟩, hnm, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hk)]
    refine eq_one_of_mem_wildInertiaSubgroup ((wildInertiaSubgroup K N).pow_mem τ.2 _) ?_
    rw [hord, norm_natCast_eq_one_iff, Ne, CharP.cast_eq_zero_iff _ p]
    exact hpm

end PGroup

/-! ### Inertia without ramification or residue extension -/

section Unramified

variable {K N : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedField N] [IsUltrametricDist N] [NormedAlgebra K N] [Algebra.IsAlgebraic K N]

/-- If every element of `N` has the absolute value of an element of `K` (`|N^×| = |K^×|`), then
the inertia subgroup is contained in the wild inertia subgroup. -/
theorem inertiaSubgroup_le_wildInertiaSubgroup (h : ∀ x : N, x ≠ 0 → ∃ c : K, ‖c‖ = ‖x‖) :
    inertiaSubgroup K N ≤ wildInertiaSubgroup K N := by
  intro σ hσ x hx
  obtain ⟨c, hc⟩ := h x hx
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hc
    exact hx (norm_eq_zero.mp hc.symm)
  have hcN : ‖algebraMap K N c‖ = ‖x‖ := by rw [norm_algebraMap', hc]
  have hcN0 : algebraMap K N c ≠ 0 := (_root_.map_ne_zero _).mpr hc0
  have hu : ‖x / algebraMap K N c‖ ≤ 1 := by
    rw [norm_div, hcN, div_self (norm_ne_zero_iff.mpr hx)]
  have := hσ _ hu
  rw [map_div₀, AlgEquiv.commutes, ← sub_div, norm_div, hcN] at this
  exact (div_lt_one (norm_pos_iff.mpr hx)).mp this

/-- **Temkin S5(b)**: if `e_{N/K} = 1` then `T = V`. -/
theorem wildInertiaSubgroup_eq_inertiaSubgroup [FiniteDimensional K N]
    (h : ramificationIndex K N = 1) : wildInertiaSubgroup K N = inertiaSubgroup K N := by
  refine le_antisymm wildInertiaSubgroup_le_inertiaSubgroup
    (inertiaSubgroup_le_wildInertiaSubgroup fun x hx => ?_)
  have hle : valueGroup N ≤ valueGroup K := Subgroup.relIndex_eq_one.mp h
  have hmem : (Units.mk0 ‖x‖₊ (nnnorm_ne_zero_iff.mpr hx) : ℝ≥0ˣ) ∈ valueGroup N :=
    mem_valueGroup_iff.mpr ⟨x, rfl⟩
  obtain ⟨c, hc⟩ := mem_valueGroup_iff.mp (hle hmem)
  refine ⟨c, ?_⟩
  have : ‖c‖₊ = ‖x‖₊ := hc
  rw [← coe_nnnorm, this, coe_nnnorm]

/-- If every element of `N°` is congruent modulo `N°°` to an element of `K°`, then the inertia
subgroup is the whole automorphism group. -/
theorem inertiaSubgroup_eq_top_of_forall
    (h : ∀ x : N, ‖x‖ ≤ 1 → ∃ c : K, ‖c‖ ≤ 1 ∧ ‖x - algebraMap K N c‖ < 1) :
    inertiaSubgroup K N = ⊤ := by
  refine eq_top_iff.mpr fun σ _ x hx => ?_
  obtain ⟨c, -, hc⟩ := h x hx
  have heq : σ x - x = σ (x - algebraMap K N c) - (x - algebraMap K N c) := by
    rw [map_sub, AlgEquiv.commutes]; ring
  rw [heq]
  refine (norm_sub_le_max _ _).trans_lt (max_lt ?_ hc)
  rwa [norm_algEquiv_apply]

/-- **Temkin S5(c)**: if `f_{N/K} = 1` then `T = Gal(N/K)`. -/
theorem inertiaSubgroup_eq_top [FiniteDimensional K N] (h : inertiaDegree K N = 1) :
    inertiaSubgroup K N = ⊤ := by
  refine inertiaSubgroup_eq_top_of_forall fun x hx => ?_
  have hsurj := (finrank_eq_one_iff_of_nonzero' (1 : ResidueField (unitBall N)) one_ne_zero).mp h
    (residue (unitBall N) ⟨x, mem_unitBall.mpr hx⟩)
  obtain ⟨c, hc⟩ := hsurj
  obtain ⟨c, rfl⟩ := residue_surjective c
  refine ⟨c, norm_coe_unitBall_le_one c, ?_⟩
  rw [Algebra.smul_def, mul_one, algebraMap_residue, residue_eq_residue_iff] at hc
  rw [norm_sub_rev]
  exact hc

end Unramified

/-! ### Polynomials over unit balls -/

section UnitBallPoly

variable {K L : Type*} [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L]
  [NormedAlgebra K L]

/-- Evaluation of a polynomial over `K°` at an element of `L°`, computed in `L`. -/
theorem coe_eval_map_unitBall (g : (unitBall K)[X]) (y : unitBall L) :
    (((g.map (algebraMap (unitBall K) (unitBall L))).eval y : unitBall L) : L) =
      aeval (y : L) g := by
  rw [eval_map, aeval_def]
  have h := Polynomial.hom_eval₂ g (algebraMap (unitBall K) (unitBall L)) (unitBall L).subtype y
  have hc : (unitBall L).subtype.comp (algebraMap (unitBall K) (unitBall L)) =
      algebraMap (unitBall K) L := RingHom.ext fun _ => rfl
  rw [hc] at h
  exact h

/-- Reduction commutes with evaluation of polynomials over `K°` at elements of `L°`. -/
theorem residue_eval_map_unitBall (g : (unitBall K)[X]) (y : unitBall L) :
    residue (unitBall L) ((g.map (algebraMap (unitBall K) (unitBall L))).eval y) =
      aeval (residue (unitBall L) y) (g.map (residue (unitBall K))) := by
  rw [eval_map, Polynomial.hom_eval₂, aeval_def, eval₂_map]
  congr 1

/-- An element of `L` evaluated at a polynomial over `K°` has norm at most one if the element
does. -/
theorem norm_aeval_unitBall_le_one (g : (unitBall K)[X]) {y : L} (hy : ‖y‖ ≤ 1) :
    ‖aeval y g‖ ≤ 1 := by
  rw [← coe_eval_map_unitBall g ⟨y, mem_unitBall.mpr hy⟩]
  exact norm_coe_unitBall_le_one _

end UnitBallPoly

/-! ### Uniqueness of Hensel lifts -/

section HenselUnique

/-- **Uniqueness of Hensel lifts**: two roots `y, y'` of `g ∈ F°[X]` with `‖y - y'‖ < 1` and
`‖g'(y)‖ = 1` are equal. -/
theorem eq_of_isRoot_of_norm_sub_lt_one {F : Type*} [NormedField F] [IsUltrametricDist F]
    (g : (unitBall F)[X]) {y y' : unitBall F} (hy : g.IsRoot y) (hy' : g.IsRoot y')
    (hyy' : ‖(y : F) - y'‖ < 1) (hd : ‖((g.derivative.eval y : unitBall F) : F)‖ = 1) :
    y = y' := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion g y (y' - y)
  rw [add_sub_cancel, hy'.eq_zero, hy.eq_zero] at hk
  have hfac : (y' - y) * (g.derivative.eval y + k * (y' - y)) = 0 := by
    linear_combination -hk
  rcases mul_eq_zero.mp hfac with h0 | h0
  · exact (sub_eq_zero.mp h0).symm
  · exfalso
    have hkh : ‖((k * (y' - y) : unitBall F) : F)‖ < 1 := by
      have : ((k * (y' - y) : unitBall F) : F) = (k : F) * ((y' : F) - y) := by push_cast; ring
      rw [this, norm_mul, norm_sub_rev]
      calc ‖(k : F)‖ * ‖(y : F) - y'‖ ≤ 1 * ‖(y : F) - y'‖ :=
            mul_le_mul_of_nonneg_right (norm_coe_unitBall_le_one k) (norm_nonneg _)
        _ < 1 := by rw [one_mul]; exact hyy'
    have hsum : ‖((g.derivative.eval y + k * (y' - y) : unitBall F) : F)‖ = 1 := by
      have : ((g.derivative.eval y + k * (y' - y) : unitBall F) : F) =
          ((g.derivative.eval y : unitBall F) : F) + ((k * (y' - y) : unitBall F) : F) := by
        push_cast; ring
      rw [this, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hd]; exact hkh.ne'),
        hd, max_eq_left hkh.le]
    rw [h0] at hsum
    simp at hsum

end HenselUnique

/-! ### The inertia subgroup fixes Hensel lifts -/

section FixesLifts

variable {K N : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedField N] [IsUltrametricDist N] [NormedAlgebra K N] [Algebra.IsAlgebraic K N]

/-- **The inertia subgroup fixes Hensel lifts**: if `y ∈ N°` is a root of `g ∈ K°[X]` with
`‖g'(y)‖ = 1`, then `σ y = y` for every `σ` in the inertia subgroup. -/
theorem inertiaSubgroup_apply_eq_of_isRoot (g : (unitBall K)[X]) {y : N} (hy : ‖y‖ ≤ 1)
    (hg : aeval y g = 0) (hd : ‖aeval y (derivative g)‖ = 1) {σ : N ≃ₐ[K] N}
    (hσ : σ ∈ inertiaSubgroup K N) : σ y = y := by
  have hσy : ‖σ y‖ ≤ 1 := by rwa [norm_algEquiv_apply]
  set σ' : N →ₐ[unitBall K] N := (σ : N →ₐ[K] N).restrictScalars (unitBall K)
  have hσ'g : aeval (σ y) g = 0 := by
    have := Polynomial.aeval_algHom_apply σ' y g
    rw [hg, map_zero] at this
    exact this
  set G := g.map (algebraMap (unitBall K) (unitBall N))
  set y₁ : unitBall N := ⟨y, mem_unitBall.mpr hy⟩
  set y₂ : unitBall N := ⟨σ y, mem_unitBall.mpr hσy⟩
  have h1 : G.IsRoot y₁ := by
    apply Subtype.ext
    rw [coe_eval_map_unitBall]
    exact hg
  have h2 : G.IsRoot y₂ := by
    apply Subtype.ext
    rw [coe_eval_map_unitBall]
    exact hσ'g
  have hd' : ‖((G.derivative.eval y₁ : unitBall N) : N)‖ = 1 := by
    rw [Polynomial.derivative_map, coe_eval_map_unitBall]
    exact hd
  have := eq_of_isRoot_of_norm_sub_lt_one G h1 h2
    (by rw [norm_sub_rev]; exact hσ y hy) hd'
  exact (congrArg Subtype.val this).symm

/-- Hensel lifts of simple roots lie in the inertia field. -/
theorem mem_fixedField_inertiaSubgroup_of_isRoot [FiniteDimensional K N] (g : (unitBall K)[X])
    {y : N} (hy : ‖y‖ ≤ 1) (hg : aeval y g = 0) (hd : ‖aeval y (derivative g)‖ = 1) :
    y ∈ fixedField (inertiaSubgroup K N) :=
  (mem_fixedField_iff _ _).mpr fun _ hσ => inertiaSubgroup_apply_eq_of_isRoot g hy hg hd hσ

end FixesLifts

/-! ### Intermediate fields as normed fields -/

section IntermediateFieldNorm

variable {K N : Type*} [NormedField K] [NormedField N] [NormedAlgebra K N]

/-- An intermediate field `E` of `N/K` carries the restricted norm (`SubfieldClass.toNormedField`)
and `N` is a normed `E`-algebra. -/
instance normedAlgebraIntermediateField (E : IntermediateField K N) : NormedAlgebra E N where
  norm_smul_le c x := by
    rw [Algebra.smul_def, norm_mul]
    exact le_rfl

end IntermediateFieldNorm

/-! ### The inertia field -/

section InertiaField

variable {K N : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedField N] [IsUltrametricDist N] [NormedAlgebra K N] [FiniteDimensional K N]

local notation "K̃" => ResidueField (unitBall K)
local notation "Ñ" => ResidueField (unitBall N)

omit [CompleteSpace K] in
/-- A primitive element of the separable closure of `K̃` in `Ñ`. -/
theorem exists_primitive_separableClosure_residueField :
    ∃ θ : Ñ, IsSeparable K̃ θ ∧ separableClosure K̃ Ñ = K̃⟮θ⟯ := by
  obtain ⟨θs, hθs⟩ := Field.exists_primitive_element K̃ (separableClosure K̃ Ñ)
  refine ⟨θs, mem_separableClosure_iff.mp θs.2, le_antisymm ?_ ?_⟩
  · intro x hx
    have hmem : (⟨x, hx⟩ : separableClosure K̃ Ñ) ∈ K̃⟮θs⟯ := hθs ▸ IntermediateField.mem_top
    have halg : IsAlgebraic K̃ θs := Algebra.IsAlgebraic.isAlgebraic θs
    rw [← mem_toSubalgebra, adjoin_simple_toSubalgebra_of_isAlgebraic halg,
      Algebra.adjoin_singleton_eq_range_aeval] at hmem
    obtain ⟨r, hr⟩ := hmem
    have hx' : aeval (θs : Ñ) r = x :=
      (aeval_algHom_apply (separableClosure K̃ Ñ).val θs r).trans (congrArg Subtype.val hr)
    rw [← hx']
    exact algebra_adjoin_le_adjoin K̃ _ (Polynomial.aeval_mem_adjoin_singleton K̃ _)
  · rw [adjoin_simple_le_iff]
    exact θs.2

/-- If `σ` fixes `θ ∈ N°` and every element of `Ñ` has a `q ^ n`-th power which is a polynomial
in the residue of `θ` (`q` the exponential characteristic), then `σ` lies in the inertia
subgroup. -/
theorem mem_inertiaSubgroup_of_apply_eq {θ : unitBall N} {σ : N ≃ₐ[K] N}
    (hσ : σ (θ : N) = θ) (q : ℕ) [ExpChar Ñ q]
    (h : ∀ x : Ñ, ∃ n : ℕ, ∃ r : K̃[X], x ^ q ^ n = aeval (residue (unitBall N) θ) r) :
    σ ∈ inertiaSubgroup K N := by
  intro x hx
  set x₁ : unitBall N := ⟨x, mem_unitBall.mpr hx⟩
  have hσx : ‖σ x‖ ≤ 1 := by rwa [norm_algEquiv_apply]
  set x₂ : unitBall N := ⟨σ x, mem_unitBall.mpr hσx⟩
  obtain ⟨n, r, hr⟩ := h (residue (unitBall N) x₁)
  obtain ⟨r', rfl⟩ := Polynomial.map_surjective (residue (unitBall K)) residue_surjective r
  set w : unitBall N := (r'.map (algebraMap (unitBall K) (unitBall N))).eval θ with hw_def
  have hw : residue (unitBall N) w = residue (unitBall N) x₁ ^ q ^ n := by
    rw [hw_def, residue_eval_map_unitBall, hr]
  have hσw : σ (w : N) = w := by
    rw [hw_def, coe_eval_map_unitBall]
    set σ' : N →ₐ[unitBall K] N := (σ : N →ₐ[K] N).restrictScalars (unitBall K)
    have := Polynomial.aeval_algHom_apply σ' (θ : N) r'
    have hσ' : σ' (θ : N) = θ := hσ
    rw [hσ'] at this
    exact this.symm
  have h1 : ‖x ^ q ^ n - (w : N)‖ < 1 := by
    have : residue (unitBall N) (x₁ ^ q ^ n) = residue (unitBall N) w := by rw [map_pow, hw]
    rw [residue_eq_residue_iff] at this
    simpa [x₁] using this
  have h2 : ‖(σ x) ^ q ^ n - (w : N)‖ < 1 := by
    rw [← norm_algEquiv_apply σ, map_sub, map_pow, hσw] at h1
    exact h1
  have h3 : residue (unitBall N) x₂ ^ q ^ n = residue (unitBall N) x₁ ^ q ^ n := by
    rw [← hw, ← map_pow, residue_eq_residue_iff]
    simpa [x₂] using h2
  have h4 : residue (unitBall N) x₂ = residue (unitBall N) x₁ := by
    have := sub_pow_expChar_pow (residue (unitBall N) x₂) (residue (unitBall N) x₁) n (p := q)
    rw [h3, sub_self] at this
    exact sub_eq_zero.mp ((pow_eq_zero_iff (pow_ne_zero n (expChar_ne_zero Ñ q))).mp this)
  rw [residue_eq_residue_iff] at h4
  exact h4


omit [CompleteSpace K] in
/-- Elements of `Ñ` have a `q ^ n`-th power in the separable closure of `K̃`; if the latter is
generated by `θ̄`, they are polynomials in `θ̄`. -/
theorem exists_pow_eq_aeval_of_separableClosure_eq {θ : Ñ} (hθ : separableClosure K̃ Ñ = K̃⟮θ⟯)
    (x : Ñ) : ∃ n : ℕ, ∃ r : K̃[X], x ^ ringExpChar K̃ ^ n = aeval θ r := by
  set q := ringExpChar K̃
  have : ExpChar K̃ q := ringExpChar.expChar K̃
  have : ExpChar (separableClosure K̃ Ñ) q :=
    expChar_of_injective_algebraMap (algebraMap K̃ (separableClosure K̃ Ñ)).injective q
  obtain ⟨n, y, hy⟩ := IsPurelyInseparable.pow_mem (separableClosure K̃ Ñ) q x
  have hmem : (y : Ñ) ∈ K̃⟮θ⟯ := hθ ▸ y.2
  have halg : IsAlgebraic K̃ θ := (Algebra.IsAlgebraic.isAlgebraic θ)
  rw [← mem_toSubalgebra, adjoin_simple_toSubalgebra_of_isAlgebraic halg,
    Algebra.adjoin_singleton_eq_range_aeval] at hmem
  obtain ⟨r, hr⟩ := hmem
  exact ⟨n, r, hy.symm.trans hr.symm⟩

variable [IsGalois K N]

/-- **The inertia field is unramified** (plan simplification S5(d); the classical structure of
the inertia field, proved by Hensel lifting). There are `θ ∈ N°` and a monic `g ∈ K°[X]` such
that `g` is the minimal polynomial of `θ` over `K`, its reduction is the separable minimal
polynomial of `θ̃` over `K̃`, `‖g'(θ)‖ = 1`, the inertia field `Z = N^T` is `K(θ)`, `K̃(θ̃)` is the
separable closure of `K̃` in `Ñ`, and `[Z̃ : K̃] = [Z : K]`. -/
theorem exists_inertiaField_generator :
    ∃ (θ : unitBall N) (g : (unitBall K)[X]), g.Monic ∧
      g.map (algebraMap (unitBall K) K) = minpoly K (θ : N) ∧
      g.map (residue (unitBall K)) = minpoly K̃ (residue (unitBall N) θ) ∧
      (minpoly K̃ (residue (unitBall N) θ)).Separable ∧
      ‖aeval (θ : N) (derivative g)‖ = 1 ∧
      fixedField (inertiaSubgroup K N) = K⟮(θ : N)⟯ ∧
      separableClosure K̃ Ñ = K̃⟮residue (unitBall N) θ⟯ ∧
      inertiaDegree K (fixedField (inertiaSubgroup K N)) =
        Module.finrank K (fixedField (inertiaSubgroup K N)) ∧
      Algebra.IsSeparable K̃ (ResidueField (unitBall (fixedField (inertiaSubgroup K N)))) ∧
      IsPurelyInseparable (ResidueField (unitBall (fixedField (inertiaSubgroup K N)))) Ñ := by
  have : CompleteSpace N := FiniteDimensional.complete K N
  obtain ⟨θb, hsep, hθb⟩ := exists_primitive_separableClosure_residueField (K := K) (N := N)
  set gb := minpoly K̃ θb with hgb_def
  have hgbsep : gb.Separable := hsep
  have hθbint : IsIntegral K̃ θb := hsep.isIntegral
  have hgbmonic : gb.Monic := minpoly.monic hθbint
  -- lift the minimal polynomial of `θ̄` to a monic polynomial over `K°`
  obtain ⟨g₀, hg₀⟩ := Polynomial.map_surjective (residue (unitBall K)) residue_surjective gb
  obtain ⟨g, hgmap, hgdeg, hgmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts gb).mpr ⟨g₀, hg₀⟩) hgbmonic
  -- Hensel lifting in `N`
  set G := g.map (algebraMap (unitBall K) (unitBall N)) with hG_def
  have hGmonic : G.Monic := hgmonic.map _
  have hGres : G.map (residue (unitBall N)) = gb.map (algebraMap K̃ Ñ) := by
    rw [hG_def, Polynomial.map_map, ← hgmap, Polynomial.map_map]
    congr 1
  have hroot : aeval θb G = 0 := by
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map, hGres, eval_map, ← aeval_def,
      minpoly.aeval]
  have hroot' : aeval θb (derivative G) ≠ 0 := by
    rw [aeval_def, ResidueField.algebraMap_eq, ← eval_map, ← Polynomial.derivative_map, hGres,
      Polynomial.derivative_map, eval_map, ← aeval_def]
    exact hgbsep.aeval_derivative_ne_zero (minpoly.aeval K̃ θb)
  obtain ⟨θ, hθroot, hθres⟩ := exists_isRoot_residue_eq G hGmonic θb hroot hroot'
  have hθ1 : ‖(θ : N)‖ ≤ 1 := norm_coe_unitBall_le_one θ
  have hθN : aeval (θ : N) g = 0 := by
    rw [← coe_eval_map_unitBall, ← hG_def, hθroot.eq_zero]
    rfl
  have hθd : ‖aeval (θ : N) (derivative g)‖ = 1 := by
    rw [← coe_eval_map_unitBall, ← Polynomial.derivative_map, ← hG_def]
    apply norm_eq_one_of_residue_ne_zero
    rw [hG_def, Polynomial.derivative_map, residue_eval_map_unitBall, ← Polynomial.derivative_map,
      hgmap, hθres]
    exact hgbsep.aeval_derivative_ne_zero (minpoly.aeval K̃ θb)
  -- the stabilizer of `θ` is the inertia subgroup
  have hmemZ : (θ : N) ∈ fixedField (inertiaSubgroup K N) :=
    mem_fixedField_inertiaSubgroup_of_isRoot g hθ1 hθN hθd
  have hfix : (K⟮(θ : N)⟯).fixingSubgroup = inertiaSubgroup K N := by
    refine le_antisymm (fun σ hσ => ?_) ((le_iff_le _ _).mp (adjoin_simple_le_iff.mpr hmemZ))
    have hσθ : σ (θ : N) = θ := (mem_fixingSubgroup_iff _ σ).mp hσ _ (mem_adjoin_simple_self K _)
    have : ExpChar K̃ (ringExpChar K̃) := ringExpChar.expChar K̃
    have : ExpChar Ñ (ringExpChar K̃) :=
      expChar_of_injective_algebraMap (algebraMap K̃ Ñ).injective _
    refine mem_inertiaSubgroup_of_apply_eq hσθ (ringExpChar K̃) fun x => ?_
    rw [hθres]
    exact exists_pow_eq_aeval_of_separableClosure_eq hθb x
  have hZ : fixedField (inertiaSubgroup K N) = K⟮(θ : N)⟯ := by
    rw [← hfix, IsGalois.fixedField_fixingSubgroup]
  -- degrees
  set Z := fixedField (inertiaSubgroup K N) with hZ_def
  have hθKint : IsIntegral K (θ : N) := Algebra.IsIntegral.isIntegral _
  set gK := g.map (algebraMap (unitBall K) K) with hgK_def
  have hgKmonic : gK.Monic := hgmonic.map _
  have hgKroot : aeval (θ : N) gK = 0 := by rw [hgK_def, aeval_map_algebraMap, hθN]
  have hdvd : minpoly K (θ : N) ∣ gK := minpoly.dvd K _ hgKroot
  have hfinZ : Module.finrank K Z = (minpoly K (θ : N)).natDegree := by
    rw [hZ, adjoin.finrank hθKint]
  have hle1 : (minpoly K (θ : N)).natDegree ≤ gb.natDegree := by
    have := natDegree_le_of_dvd hdvd hgKmonic.ne_zero
    rwa [hgK_def, hgmonic.natDegree_map, hgdeg] at this
  -- the residue of `θ` in `Z̃` is a root of `ḡ`
  set θZ : Z := ⟨θ, hmemZ⟩
  have hθZ1 : θZ ∈ unitBall Z := mem_unitBall.mpr hθ1
  set θZ₁ : unitBall Z := ⟨θZ, hθZ1⟩
  have hrootZ : aeval (residue (unitBall Z) θZ₁) gb = 0 := by
    rw [← hgmap, ← residue_eval_map_unitBall]
    have : (g.map (algebraMap (unitBall K) (unitBall Z))).eval θZ₁ = 0 := by
      apply Subtype.ext
      rw [coe_eval_map_unitBall]
      apply Subtype.ext
      rw [show ((aeval (θZ₁ : Z) g : Z) : N) = aeval ((θZ₁ : Z) : N) g from
        (aeval_algHom_apply ((Z.val).restrictScalars (unitBall K)) (θZ₁ : Z) g).symm]
      exact hθN
    rw [this, map_zero]
  have hminZ : gb = minpoly K̃ (residue (unitBall Z) θZ₁) :=
    minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hθbint) hrootZ hgbmonic
  have hle2 : gb.natDegree ≤ inertiaDegree K Z := by
    rw [hminZ, inertiaDegree_def]
    exact minpoly.natDegree_le _
  have hle3 : inertiaDegree K Z ≤ Module.finrank K Z := inertiaDegree_le_finrank
  have hfeq : gK = minpoly K (θ : N) := by
    refine eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hθKint) hgKmonic hdvd ?_
    rw [hgK_def, hgmonic.natDegree_map, hgdeg]
    omega
  have hdegZ : inertiaDegree K Z = Module.finrank K Z := by omega
  -- the residue field of `Z` is generated by the residue of `θ`
  have hθZ₁int : IsIntegral K̃ (residue (unitBall Z) θZ₁) := Algebra.IsIntegral.isIntegral _
  have htop : K̃⟮residue (unitBall Z) θZ₁⟯ = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [IntermediateField.finrank_top', adjoin.finrank hθZ₁int, ← hminZ, ← inertiaDegree_def]
    omega
  have hsepZ : Algebra.IsSeparable K̃ (ResidueField (unitBall Z)) := by
    have h1 : IsSeparable K̃ (residue (unitBall Z) θZ₁) := by
      rw [IsSeparable, ← hminZ]
      exact hgbsep
    have h2 := (isSeparable_adjoin_simple_iff_isSeparable K̃ (ResidueField (unitBall Z))).mpr h1
    rw [htop] at h2
    exact AlgEquiv.Algebra.isSeparable IntermediateField.topEquiv
  -- `Ñ` is purely inseparable over `Z̃`
  have hinsep : IsPurelyInseparable (ResidueField (unitBall Z)) Ñ := by
    have : ExpChar K̃ (ringExpChar K̃) := ringExpChar.expChar K̃
    have : ExpChar (ResidueField (unitBall Z)) (ringExpChar K̃) :=
      expChar_of_injective_algebraMap (algebraMap K̃ (ResidueField (unitBall Z))).injective _
    rw [isPurelyInseparable_iff_pow_mem _ (ringExpChar K̃)]
    intro x
    obtain ⟨n, r, hr⟩ := exists_pow_eq_aeval_of_separableClosure_eq hθb x
    refine ⟨n, aeval (residue (unitBall Z) θZ₁) r, ?_⟩
    have hres : algebraMap (ResidueField (unitBall Z)) Ñ (residue (unitBall Z) θZ₁) = θb := by
      rw [algebraMap_residue, ← hθres]
      rfl
    rw [← Polynomial.aeval_algebraMap_apply, hres, hr]
  refine ⟨θ, g, hgmonic, hfeq, ?_, ?_, hθd, hZ, ?_, hdegZ, hsepZ, hinsep⟩
  · rw [hgmap, hθres]
  · rw [hθres]
    exact hgbsep
  · rw [hθres]
    exact hθb

/-- The inertia field is standard-unramified over `K` (Temkin's "unramified", plan S8). -/
theorem isStdUnramified_inertiaField :
    IsStdUnramified K (unitBall (fixedField (inertiaSubgroup K N))) := by
  obtain ⟨θ, g, hgmonic, hfeq, -, -, hθd, hZ, -, -, -, -⟩ :=
    exists_inertiaField_generator (K := K) (N := N)
  set Z := fixedField (inertiaSubgroup K N) with hZ_def
  have hmemZ : (θ : N) ∈ Z := hZ ▸ mem_adjoin_simple_self K _
  set θZ : Z := ⟨θ, hmemZ⟩
  have hθKint : IsIntegral K (θ : N) := Algebra.IsIntegral.isIntegral _
  have hmin : minpoly K θZ = minpoly K (θ : N) :=
    (minpoly.algHom_eq Z.val Subtype.val_injective θZ).symm
  have hθZint : IsIntegral K θZ := Algebra.IsIntegral.isIntegral _
  refine ⟨θZ, ?_, ?_, ?_⟩
  · apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [IntermediateField.finrank_top', adjoin.finrank hθZint, hmin, ← adjoin.finrank hθKint,
      ← hZ]
  · refine isIntegral_comap_of_coeff_mem _ hθZint fun i => ?_
    rw [hmin, ← hfeq, Polynomial.coeff_map, mem_unitBall, norm_algebraMap']
    exact norm_coe_unitBall_le_one _
  · rw [hmin, ← hfeq, Polynomial.derivative_map, aeval_map_algebraMap, ← map_one
      (unitBall Z).valuation, valuation_unitBall_eq_iff, norm_one]
    have : ((aeval θZ (derivative g) : Z) : N) = aeval (θ : N) (derivative g) :=
      (aeval_algHom_apply ((Z.val).restrictScalars (unitBall K)) θZ (derivative g)).symm
    change ‖((aeval θZ (derivative g) : Z) : N)‖ = 1
    rw [this, hθd]

/-- The inertia field has residue degree equal to its degree: `[Z̃ : K̃] = [Z : K]`. -/
theorem inertiaDegree_inertiaField :
    inertiaDegree K (fixedField (inertiaSubgroup K N)) =
      Module.finrank K (fixedField (inertiaSubgroup K N)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h, -⟩ := exists_inertiaField_generator (K := K) (N := N)
  exact h

/-- The residue field of the inertia field is separable over `K̃`. -/
theorem isSeparable_residueField_inertiaField :
    Algebra.IsSeparable K̃ (ResidueField (unitBall (fixedField (inertiaSubgroup K N)))) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := exists_inertiaField_generator (K := K) (N := N)
  exact h

/-- The residue field of `N` is purely inseparable over that of the inertia field. -/
theorem isPurelyInseparable_residueField_inertiaField :
    IsPurelyInseparable (ResidueField (unitBall (fixedField (inertiaSubgroup K N)))) Ñ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ := exists_inertiaField_generator (K := K) (N := N)
  exact h


/-- `[Z : K]` is the separable degree of the residue extension: `[Z : K] = [Ñ_s : K̃]`. -/
theorem finrank_inertiaField :
    Module.finrank K (fixedField (inertiaSubgroup K N)) =
      Module.finrank K̃ (separableClosure K̃ Ñ) := by
  obtain ⟨θ, g, hgmonic, hfeq, hgres, -, -, hZ, hsc, -⟩ :=
    exists_inertiaField_generator (K := K) (N := N)
  have hθKint : IsIntegral K (θ : N) := Algebra.IsIntegral.isIntegral _
  have hθbint : IsIntegral K̃ (residue (unitBall N) θ) := Algebra.IsIntegral.isIntegral _
  rw [hZ, hsc, adjoin.finrank hθKint, adjoin.finrank hθbint, ← hfeq, ← hgres,
    hgmonic.natDegree_map, hgmonic.natDegree_map]
end InertiaField

end DeJongAlterations.StableModification.Valuation.Analytic
