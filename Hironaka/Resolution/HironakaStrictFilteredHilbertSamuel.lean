import Hironaka.Resolution.HironakaStrictFilteredRegularElement
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite Hilbert–Samuel differences along a regular symbol

Multiplication by a degree-one regular symbol gives a short exact sequence on the
actual quotients by `I ⊔ N ^ q`. Over a coefficient field, this gives a dimension
recurrence and reconstructs every cumulative value by summation. The regular-symbol
hypothesis is explicit; this module does not produce it from geometric centre data.
-/

set_option autoImplicit false

namespace Hironaka.HironakaStrictFilteredHilbertSamuel

open HironakaStrictFilteredRegularElement

variable {R : Type*} [CommRing R]

noncomputable section

/-- Multiplication by `v` on the entire original finite adic quotients. -/
def quotientSymbolMul (I N : Ideal R) (v : R) (hv : v ∈ N) (q : ℕ) :
    (R ⧸ (I ⊔ N ^ q)) →ₗ[R] R ⧸ (I ⊔ N ^ (q + 1)) :=
  (I ⊔ N ^ q).liftQ
    ((Ideal.Quotient.mkₐ R (I ⊔ N ^ (q + 1))).toLinearMap.comp
      (LinearMap.mulLeft R v)) (by
    intro a ha
    change Ideal.Quotient.mk (I ⊔ N ^ (q + 1)) (v * a) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    obtain ⟨i, hi, b, hb, rfl⟩ := Submodule.mem_sup.mp ha
    rw [mul_add]
    apply (I ⊔ N ^ (q + 1)).add_mem
    · exact (le_sup_left : I ≤ I ⊔ N ^ (q + 1)) (I.mul_mem_left v hi)
    · apply (le_sup_right : N ^ (q + 1) ≤ I ⊔ N ^ (q + 1))
      rw [pow_succ']
      exact Ideal.mul_mem_mul hv hb)

@[simp]
theorem quotientSymbolMul_mk (I N : Ideal R) (v : R) (hv : v ∈ N)
    (q : ℕ) (a : R) :
    quotientSymbolMul I N v hv q (Ideal.Quotient.mk (I ⊔ N ^ q) a) =
      Ideal.Quotient.mk (I ⊔ N ^ (q + 1)) (v * a) := rfl

/-- The actual quotient factor imposing the original principal ideal `(v)`. -/
def quotientParameterMap (I N : Ideal R) (v : R) (q : ℕ) :
    (R ⧸ (I ⊔ N ^ (q + 1))) →ₗ[R]
      R ⧸ ((I ⊔ Ideal.span ({v} : Set R)) ⊔ N ^ (q + 1)) :=
  (Ideal.Quotient.factorₐ R
    (sup_le_sup le_sup_left le_rfl : I ⊔ N ^ (q + 1) ≤
      (I ⊔ Ideal.span ({v} : Set R)) ⊔ N ^ (q + 1))).toLinearMap

@[simp]
theorem quotientParameterMap_mk (I N : Ideal R) (v : R) (q : ℕ) (a : R) :
    quotientParameterMap I N v q (Ideal.Quotient.mk (I ⊔ N ^ (q + 1)) a) =
      Ideal.Quotient.mk ((I ⊔ Ideal.span ({v} : Set R)) ⊔ N ^ (q + 1)) a := rfl

/-- Regularity of the associated graded symbol gives injectivity on every finite quotient. -/
theorem quotientSymbolMul_injective (I N : Ideal R) (v : R) (hv : v ∈ N)
    (hreg : ∀ r : ℕ, ∀ b ∈ N ^ r, v * b ∈ I ⊔ N ^ (r + 2) →
      b ∈ I ⊔ N ^ (r + 1)) (q : ℕ) :
    Function.Injective (quotientSymbolMul I N v hv q) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hva : v * a ∈ I ⊔ N ^ (q + 1) :=
      Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hx)
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((mem_successor_iff_mem_current_of_regular_symbol I N v hv hreg q a).mp hva)
  · exact bot_le

/-- Every class after imposing `(v)` still has an original numerator. -/
theorem quotientParameterMap_surjective (I N : Ideal R) (v : R) (q : ℕ) :
    Function.Surjective (quotientParameterMap I N v q) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk (I ⊔ N ^ (q + 1)) a, rfl⟩

/-- The entire kernel of parameter elimination is the original multiplication image. -/
theorem ker_quotientParameterMap_eq_range (I N : Ideal R) (v : R)
    (hv : v ∈ N) (q : ℕ) :
    LinearMap.ker (quotientParameterMap I N v q) =
      LinearMap.range (quotientSymbolMul I N v hv q) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∈ (I ⊔ Ideal.span ({v} : Set R)) ⊔ N ^ (q + 1) :=
      Ideal.Quotient.eq_zero_iff_mem.mp (LinearMap.mem_ker.mp hx)
    obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp ha
    obtain ⟨i, hi, vb, hvb, rfl⟩ := Submodule.mem_sup.mp hj
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hvb
    refine ⟨Ideal.Quotient.mk (I ⊔ N ^ q) b, ?_⟩
    rw [quotientSymbolMul_mk]
    apply Ideal.Quotient.eq.mpr
    have he : v * b - (i + v * b + c) = -(i + c) := by abel
    rw [he]
    exact (I ⊔ N ^ (q + 1)).neg_mem
      ((I ⊔ N ^ (q + 1)).add_mem
        ((le_sup_left : I ≤ I ⊔ N ^ (q + 1)) hi)
        ((le_sup_right : N ^ (q + 1) ≤ I ⊔ N ^ (q + 1)) hc))
  · rintro x ⟨y, rfl⟩
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply LinearMap.mem_ker.mpr
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (le_trans le_sup_right le_sup_left : Ideal.span ({v} : Set R) ≤
      (I ⊔ Ideal.span ({v} : Set R)) ⊔ N ^ (q + 1))
      ((Ideal.span ({v} : Set R)).mul_mem_right b (Ideal.mem_span_singleton_self v))

variable (K : Type*) [Field K] [Algebra K R]

/-- The finite Hilbert–Samuel difference formula, requiring finiteness only of the
middle quotient and retaining the explicit regular-symbol hypothesis. -/
theorem finrank_quotient_recurrence (I N : Ideal R) (v : R) (hv : v ∈ N)
    (hreg : ∀ r : ℕ, ∀ b ∈ N ^ r, v * b ∈ I ⊔ N ^ (r + 2) →
      b ∈ I ⊔ N ^ (r + 1)) (q : ℕ)
    [Module.Finite K (R ⧸ (I ⊔ N ^ (q + 1)))] :
    Module.finrank K (R ⧸ ((I ⊔ Ideal.span ({v} : Set R)) ⊔ N ^ (q + 1))) +
      Module.finrank K (R ⧸ (I ⊔ N ^ q)) =
        Module.finrank K (R ⧸ (I ⊔ N ^ (q + 1))) := by
  let f := (quotientSymbolMul I N v hv q).restrictScalars K
  let g := (quotientParameterMap I N v q).restrictScalars K
  have hf : Function.Injective f := quotientSymbolMul_injective I N v hv hreg q
  have hg : Function.Surjective g := quotientParameterMap_surjective I N v q
  have hker : LinearMap.ker g = LinearMap.range f := by
    dsimp only [f, g]
    rw [LinearMap.ker_restrictScalars, LinearMap.range_restrictScalars,
      ker_quotientParameterMap_eq_range I N v hv q]
  have hdim := (LinearMap.ker g).finrank_quotient_add_finrank
  rw [(g.quotKerEquivOfSurjective hg).finrank_eq, hker,
    ← (LinearEquiv.ofInjective f hf).finrank_eq] at hdim
  exact hdim

/-- The numerical difference identity forces injectivity of the actual multiplication
map when its source and target are finite dimensional. No symbol regularity is assumed. -/
theorem quotientSymbolMul_injective_of_finrank (I N : Ideal R) (v : R) (hv : v ∈ N)
    (q : ℕ) [Module.Finite K (R ⧸ (I ⊔ N ^ q))]
    [Module.Finite K (R ⧸ (I ⊔ N ^ (q + 1)))]
    (hdim :
      Module.finrank K (R ⧸ ((I ⊔ Ideal.span ({v} : Set R)) ⊔ N ^ (q + 1))) +
        Module.finrank K (R ⧸ (I ⊔ N ^ q)) =
          Module.finrank K (R ⧸ (I ⊔ N ^ (q + 1)))) :
    Function.Injective (quotientSymbolMul I N v hv q) := by
  let f := (quotientSymbolMul I N v hv q).restrictScalars K
  let g := (quotientParameterMap I N v q).restrictScalars K
  have hg : Function.Surjective g := quotientParameterMap_surjective I N v q
  have hker : LinearMap.ker g = LinearMap.range f := by
    dsimp only [f, g]
    rw [LinearMap.ker_restrictScalars, LinearMap.range_restrictScalars,
      ker_quotientParameterMap_eq_range I N v hv q]
  have hgdim := (LinearMap.ker g).finrank_quotient_add_finrank
  rw [(g.quotKerEquivOfSurjective hg).finrank_eq, hker] at hgdim
  have hrange : Module.finrank K (LinearMap.range f) =
      Module.finrank K (R ⧸ (I ⊔ N ^ q)) := Nat.add_left_cancel (hgdim.trans hdim.symm)
  have hzero : Module.finrank K (LinearMap.ker f) = 0 := by
    have h := f.finrank_range_add_finrank_ker
    rw [hrange] at h
    omega
  have hf : Function.Injective f :=
    LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hzero)
  exact hf

/-- The whole regular-symbol condition is equivalent to all numerical finite-quotient
differences. The converse derives regularity rather than assuming it. -/
theorem regular_symbol_iff_finrank_quotient_recurrence (I N : Ideal R) (v : R)
    (hv : v ∈ N)
    (hfinite : ∀ q : ℕ, Module.Finite K (R ⧸ (I ⊔ N ^ (q + 1)))) :
    (∀ r : ℕ, ∀ b ∈ N ^ r, v * b ∈ I ⊔ N ^ (r + 2) →
      b ∈ I ⊔ N ^ (r + 1)) ↔
    ∀ q : ℕ,
      Module.finrank K (R ⧸ ((I ⊔ Ideal.span ({v} : Set R)) ⊔ N ^ ((q + 1) + 1))) +
        Module.finrank K (R ⧸ (I ⊔ N ^ (q + 1))) =
          Module.finrank K (R ⧸ (I ⊔ N ^ ((q + 1) + 1))) := by
  constructor
  · intro hreg q
    let := hfinite (q + 1)
    exact finrank_quotient_recurrence K I N v hv hreg (q + 1)
  · intro hdim r b _ hvb
    let := hfinite r
    let := hfinite (r + 1)
    have hf := quotientSymbolMul_injective_of_finrank K I N v hv (r + 1) (hdim r)
    have hb : quotientSymbolMul I N v hv (r + 1)
        (Ideal.Quotient.mk (I ⊔ N ^ (r + 1)) b) =
          quotientSymbolMul I N v hv (r + 1) 0 := by
      rw [quotientSymbolMul_mk, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hvb
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hf hb)

/-- All cumulative quotient dimensions are reconstructed from the actual parameter
quotient values, including degree zero. -/
theorem finrank_quotient_eq_sum (I N : Ideal R) (v : R) (hv : v ∈ N)
    (hreg : ∀ r : ℕ, ∀ b ∈ N ^ r, v * b ∈ I ⊔ N ^ (r + 2) →
      b ∈ I ⊔ N ^ (r + 1))
    (hfinite : ∀ q : ℕ, Module.Finite K (R ⧸ (I ⊔ N ^ (q + 1)))) (q : ℕ) :
    Module.finrank K (R ⧸ (I ⊔ N ^ (q + 1))) =
      ∑ i ∈ Finset.range (q + 1),
        Module.finrank K (R ⧸ ((I ⊔ Ideal.span ({v} : Set R)) ⊔ N ^ (i + 1))) := by
  induction q with
  | zero =>
    let := hfinite 0
    have h := finrank_quotient_recurrence K I N v hv hreg 0
    have hz : Module.finrank K (R ⧸ (I ⊔ N ^ 0)) = 0 := by
      rw [pow_zero, Ideal.one_eq_top, sup_top_eq]
      exact Module.finrank_zero_of_subsingleton
    simpa only [hz, Nat.add_zero, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.zero_add] using h.symm
  | succ q ih =>
    let := hfinite (q + 1)
    have h := finrank_quotient_recurrence K I N v hv hreg (q + 1)
    rw [Finset.sum_range_succ, ← ih]
    exact h.symm.trans (Nat.add_comm _ _)

end

end Hironaka.HironakaStrictFilteredHilbertSamuel
