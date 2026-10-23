import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Elements outside an integrally closed local ring (for Temkin, Proposition 4.3.3)

Let `A ⊆ L` be a local subring of a field which is integrally closed in `L`. This file proves
the two algebraic facts behind the local domination step in our proof of M. Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), Proposition 4.3.3
(`locunifprop`, `semi-stable.tex` lines 3048–3081), in the replacement of the flattening argument
of line 3065 (plan `PLAN-SM-GEOM.md`, S7):

* `mem_or_inv_mem_of_aeval_eq_zero` (**a root of a polynomial with a unit coefficient**): if
  `b ∈ L` is a root of a polynomial over `A` one of whose coefficients is a unit, then `b ∈ A` or
  `b⁻¹ ∈ A`. The proof uses the partial sums `w_j = c_n b^j + ⋯ + c_{n-j+1} b` (`highPart`),
  which are integral over `A` (`isIntegral_highPart`), hence lie in `A`.
* `exists_valuationSubring_valuation_aeval_eq_one` (**a valuation with transcendental residue**):
  if `b ∉ A` lies in a valuation ring `W` dominating `A`, there is a valuation ring `V` dominating
  `A` with `b ∈ V` such that `p(b)` is a unit of `V` for every polynomial `p` over `A` with a unit
  coefficient; in other words, the residue of `b` is transcendental over the residue field of `A`.

Blueprint: `lem:sm-lu-curve-unit-coefficient`, `lem:sm-lu-curve-transcendental-valuation`
(`sm-local-uniformization-curve.tex`).
-/

noncomputable section

open Polynomial IsLocalRing

namespace DeJongAlterations.StableModification.LocalUniformization.Curve

/-! ### The partial sums `w_j` -/

section HighPart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : R[X]) (b : S)

/-- The partial sums `w_j = c_n b^j + c_{n-1} b^{j-1} + ⋯ + c_{n-j+1} b` of a polynomial
`P = c_n Xⁿ + ⋯ + c₀`. -/
def highPart (j : ℕ) : S :=
  ∑ i ∈ Finset.range j, algebraMap R S (P.coeff (P.natDegree - i)) * b ^ (j - i)

@[simp]
theorem highPart_zero : highPart P b 0 = 0 := by
  simp [highPart]

/-- The recursion `w_{j+1} = b (w_j + c_{n-j})`. -/
theorem highPart_succ (j : ℕ) :
    highPart P b (j + 1) = b * (highPart P b j + algebraMap R S (P.coeff (P.natDegree - j))) := by
  rw [highPart, Finset.sum_range_succ, highPart, mul_add, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Finset.mem_range] at hi
    rw [show j + 1 - i = (j - i) + 1 by omega, pow_succ]
    ring
  · rw [show j + 1 - j = 1 by omega, pow_one]
    ring

/-- `w_n = P(b) - c₀`. -/
theorem highPart_natDegree :
    highPart P b P.natDegree = aeval b P - algebraMap R S (P.coeff 0) := by
  rw [aeval_eq_sum_range, Finset.sum_range_succ', pow_zero, Algebra.smul_def, mul_one,
    add_sub_cancel_right, highPart, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_range] at hi
  rw [Algebra.smul_def, show P.natDegree - (P.natDegree - 1 - i) = i + 1 by omega]

end HighPart

/-! ### Integrality of the partial sums and roots with a unit coefficient -/

section UnitCoefficient

variable {A L : Type*} [CommRing A] [Field L] [Algebra A L]

/-- **The partial sums `w_j` are integral** over `A` for `j ≤ deg P` when `P(b) = 0`: the
`A`-module spanned by `1, w_1, …, w_n` is stable under multiplication by each `w_j`, by the
identity `w_{j+1} w_m = (w_j + c_{n-j}) w_{m+1} - c_{n-m} w_{j+1}` and `w_n = -c₀`. -/
theorem isIntegral_highPart {P : A[X]} {b : L} (hP : aeval b P = 0) {j : ℕ}
    (hj : j ≤ P.natDegree) : IsIntegral A (highPart P b j) := by
  set n := P.natDegree with hn
  let N : Submodule A L :=
    Submodule.span A (insert (1 : L) (Set.range fun m : Fin (n + 1) ↦ highPart P b m))
  have h1 : (1 : L) ∈ N := Submodule.subset_span (Set.mem_insert _ _)
  have hw : ∀ m ≤ n, highPart P b m ∈ N := fun m hm ↦
    Submodule.subset_span (Set.mem_insert_of_mem _ ⟨⟨m, by omega⟩, rfl⟩)
  have hwn : highPart P b n = algebraMap A L (-P.coeff 0) := by
    rw [hn, highPart_natDegree, hP, zero_sub, map_neg]
  have key : ∀ j ≤ n, ∀ y ∈ N, highPart P b j * y ∈ N := by
    intro j
    induction j with
    | zero =>
      intro _ y _
      rw [highPart_zero, zero_mul]
      exact N.zero_mem
    | succ j ih =>
      intro hj y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        rcases hy with rfl | ⟨m, rfl⟩
        · rw [mul_one]
          exact hw _ hj
        · change highPart P b (j + 1) * highPart P b (m : ℕ) ∈ N
          by_cases hm : (m : ℕ) < n
          · have e := highPart_succ P b j
            have e' := highPart_succ P b m
            have hid : highPart P b (j + 1) * highPart P b m =
                (highPart P b j + algebraMap A L (P.coeff (n - j))) * highPart P b (m + 1) -
                  algebraMap A L (P.coeff (n - m)) * highPart P b (j + 1) := by
              rw [e, e']
              ring
            rw [hid]
            refine N.sub_mem ?_ ?_
            · rw [add_mul]
              refine N.add_mem (ih (by omega) _ (hw _ (by omega))) ?_
              rw [← Algebra.smul_def]
              exact N.smul_mem _ (hw _ (by omega))
            · rw [← Algebra.smul_def]
              exact N.smul_mem _ (hw _ hj)
          · have hmn : (m : ℕ) = n := by omega
            rw [hmn, hwn, mul_comm, ← Algebra.smul_def]
            exact N.smul_mem _ (hw _ hj)
      | zero =>
        rw [mul_zero]
        exact N.zero_mem
      | add x y _ _ hx hy =>
        rw [mul_add]
        exact N.add_mem hx hy
      | smul a x _ hx =>
        rw [mul_smul_comm]
        exact N.smul_mem a hx
  refine isIntegral_of_smul_mem_submodule N ?_ ?_ (highPart P b j) fun y hy ↦ key j hj y hy
  · intro h
    rw [h, Submodule.mem_bot] at h1
    exact one_ne_zero h1
  · exact Submodule.fg_span ((Set.finite_range _).insert _)

/-- **A root of a polynomial with a unit coefficient** (blueprint
`lem:sm-lu-curve-unit-coefficient`). Let `A` be a local ring integrally closed in the field `L`,
and `b ∈ L` a root of `P ∈ A[X]` whose coefficient `c_k` is a unit. Then `b ∈ A` or `b⁻¹ ∈ A`.

Proof: all `w_j` (`highPart`) lie in `A`. Put `u = c_k + w_{n-k}`. If `u` is a unit, then
`k ≥ 1` (for `k = 0`, `u = c₀ + w_n = 0`) and `b = w_{n-k+1} u⁻¹`. Otherwise `w_{n-k} = u - c_k`
is a unit, `n - k ≥ 1`, and `b⁻¹ = (w_{n-k-1} + c_{k+1}) w_{n-k}⁻¹`. -/
theorem mem_or_inv_mem_of_aeval_eq_zero [IsLocalRing A] [IsIntegrallyClosedIn A L] {P : A[X]}
    {b : L} (hP : aeval b P = 0) {k : ℕ} (hk : IsUnit (P.coeff k)) :
    b ∈ (algebraMap A L).range ∨ b⁻¹ ∈ (algebraMap A L).range := by
  set n := P.natDegree with hn
  have hinj : Function.Injective (algebraMap A L) := IsIntegralClosure.algebraMap_injective A A L
  have hkn : k ≤ n := by
    by_contra h
    rw [coeff_eq_zero_of_natDegree_lt (by omega)] at hk
    exact not_isUnit_zero hk
  have hw : ∀ j ≤ n, ∃ r : A, algebraMap A L r = highPart P b j := fun j hj ↦
    IsIntegrallyClosedIn.isIntegral_iff.mp (isIntegral_highPart hP hj)
  have hwn : highPart P b n = -algebraMap A L (P.coeff 0) := by
    rw [hn, highPart_natDegree, hP, zero_sub]
  obtain ⟨r₁, hr₁⟩ := hw (n - k) (Nat.sub_le n k)
  by_cases hu : IsUnit (P.coeff k + r₁)
  · left
    have hk1 : 1 ≤ k := by
      by_contra h0
      have hk0 : k = 0 := by omega
      subst hk0
      have h0' : P.coeff 0 + r₁ = 0 := hinj (by
        rw [map_add, hr₁, Nat.sub_zero, hwn, map_zero]
        ring)
      rw [h0'] at hu
      exact not_isUnit_zero hu
    obtain ⟨r₂, hr₂⟩ := hw (n - k + 1) (by omega)
    have e := highPart_succ P b (n - k)
    rw [show n - (n - k) = k by omega, ← hr₁, ← hr₂, ← map_add, add_comm r₁] at e
    refine ⟨r₂ * ↑hu.unit⁻¹, ?_⟩
    rw [map_mul, e, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]
  · right
    have hr₁u : IsUnit r₁ := by
      by_contra hr
      have hsum : P.coeff k + r₁ + -r₁ ∈ nonunits A :=
        IsLocalRing.nonunits_add (mem_nonunits_iff.mpr hu)
          (mem_nonunits_iff.mpr (by rwa [IsUnit.neg_iff]))
      rw [add_neg_cancel_right] at hsum
      exact hsum hk
    have hnk : 1 ≤ n - k := by
      by_contra h0
      have h0' : n - k = 0 := by omega
      rw [h0', highPart_zero] at hr₁
      rw [hinj (hr₁.trans (map_zero _).symm)] at hr₁u
      exact not_isUnit_zero hr₁u
    obtain ⟨r₃, hr₃⟩ := hw (n - k - 1) (by omega)
    have e := highPart_succ P b (n - k - 1)
    rw [show n - k - 1 + 1 = n - k by omega, show n - (n - k - 1) = k + 1 by omega, ← hr₁,
      ← hr₃, ← map_add] at e
    have hr₁0 : algebraMap A L r₁ ≠ 0 := fun h ↦ by
      rw [hinj (h.trans (map_zero _).symm)] at hr₁u
      exact not_isUnit_zero hr₁u
    have hy0 : algebraMap A L (r₃ + P.coeff (k + 1)) ≠ 0 := fun h ↦ hr₁0 (by rw [e, h, mul_zero])
    have hb0 : b ≠ 0 := fun h ↦ hr₁0 (by rw [e, h, zero_mul])
    refine ⟨(r₃ + P.coeff (k + 1)) * ↑hr₁u.unit⁻¹, ?_⟩
    have hinv : algebraMap A L ↑hr₁u.unit⁻¹ = (algebraMap A L r₁)⁻¹ := by
      refine eq_inv_of_mul_eq_one_right ?_
      rw [← map_mul, IsUnit.mul_val_inv, map_one]
    rw [map_mul, hinv, e]
    field_simp

end UnitCoefficient

/-! ### A valuation ring with transcendental residue -/

section Transcendental

variable {L : Type*} [Field L]

/-- **A valuation ring along which `b` has transcendental residue** (blueprint
`lem:sm-lu-curve-transcendental-valuation`). Let `A ⊆ L` be a local subring integrally closed in
`L`, `W` a valuation ring of `L` dominating `A`, and `b ∈ W ∖ A`. Then there is a valuation ring
`V` dominating `A` with `b ∈ V` such that `p(b)` is a unit of `V` for every `p ∈ A[X]` with a
coefficient outside `𝔪_A`.

Proof: if `p(b) = 0` for some `p` with a unit coefficient, then `b ∈ A` or `b⁻¹ ∈ A`
(`mem_or_inv_mem_of_aeval_eq_zero`); the second case gives `b⁻¹ ∈ A ∖ 𝔪_A` because `b ∈ W` and
`W` dominates `A`, hence again `b ∈ A`. So the kernel of `A[X] → A[b]`, `X ↦ b`, lies in the prime
`𝔪_A[X]`, whose image `I` in `A[b]` is a prime with preimage `𝔪_A[X]`. A valuation ring `V`
dominating `A[b]_I` works. -/
theorem exists_valuationSubring_valuation_aeval_eq_one (A : Subring L) [IsLocalRing A]
    [IsIntegrallyClosedIn A L] (W : ValuationSubring L) (hAW : A ≤ W.toSubring)
    (hdom : ∀ a : A, a ∈ maximalIdeal A → (a : L) ∈ W.nonunits) {b : L} (hbW : b ∈ W)
    (hbA : b ∉ A) :
    ∃ V : ValuationSubring L, A ≤ V.toSubring ∧
      (∀ a : A, a ∈ maximalIdeal A → (a : L) ∈ V.nonunits) ∧ b ∈ V ∧
      ∀ p : A[X], p ∉ (maximalIdeal A).map C → V.valuation (aeval b p) = 1 := by
  -- the kernel of `X ↦ b` lies in `𝔪_A[X]`
  have hker : ∀ P : A[X], aeval b P = 0 → P ∈ (maximalIdeal A).map (C : A →+* A[X]) := by
    intro P hP
    by_contra hPm
    rw [Ideal.mem_map_C_iff] at hPm
    push Not at hPm
    obtain ⟨k, hk⟩ := hPm
    have hku : IsUnit (P.coeff k) := by
      by_contra h
      exact hk ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h))
    rcases mem_or_inv_mem_of_aeval_eq_zero hP hku with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact hbA (ha ▸ a.2)
    · have hb0 : b ≠ 0 := fun h ↦ hbA (h ▸ A.zero_mem)
      have ha' : (a : L) = b⁻¹ := ha
      have hWu : IsUnit (⟨(a : L), hAW a.2⟩ : W) :=
        IsUnit.of_mul_eq_one (⟨b, hbW⟩ : W) (Subtype.ext (by
          change (a : L) * b = 1
          rw [ha', inv_mul_cancel₀ hb0]))
      have hWa1 : W.valuation (a : L) = 1 := (W.valuation_eq_one_iff _).mp hWu
      have haU : IsUnit a := by
        by_contra h
        have := hdom a ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr h))
        rw [ValuationSubring.mem_nonunits_iff, hWa1] at this
        exact lt_irrefl _ this
      refine hbA ?_
      have : b = ((haU.unit⁻¹ : Aˣ) : A) := by
        have h2 : (a : L) * ((haU.unit⁻¹ : Aˣ) : A) = 1 := by
          rw [← Subring.coe_mul, IsUnit.mul_val_inv, Subring.coe_one]
        rw [ha'] at h2
        field_simp at h2
        exact h2.symm
      rw [this]
      exact Subtype.mem _
  -- the image of `𝔪_A[X]` in `A[b]`
  let φ : A[X] →+* L := (aeval b : A[X] →ₐ[A] L).toRingHom
  let B : Subring L := φ.range
  let ψ : A[X] →+* B := φ.rangeRestrict
  have hψ : Function.Surjective ψ := φ.rangeRestrict_surjective
  have hψv : ∀ p, (ψ p : L) = aeval b p := fun _ ↦ rfl
  let J : Ideal A[X] := (maximalIdeal A).map (C : A →+* A[X])
  have : J.IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hkerJ : RingHom.ker ψ ≤ J := fun p hp ↦ hker p (by
    rw [RingHom.mem_ker] at hp
    rw [← hψv, hp, Subring.coe_zero])
  let I : Ideal B := J.map ψ
  have hI : I.IsPrime := Ideal.map_isPrime_of_surjective hψ hkerJ
  have hcomap : ∀ p, ψ p ∈ I → p ∈ J := by
    intro p hp
    have h := (Ideal.mem_comap.mpr hp : p ∈ I.comap ψ)
    rwa [Ideal.comap_map_of_surjective _ hψ, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hkerJ] at h
  -- a valuation ring dominating `A[b]_I`
  obtain ⟨V, hle⟩ := (LocalSubring.ofPrime B I).exists_le_valuationSubring
  obtain ⟨hle₁, hloc⟩ := hle
  have hBV : B ≤ V.toSubring := (LocalSubring.le_ofPrime B I).trans hle₁
  have hunit : ∀ y : B, y ∉ I → V.valuation (y : L) = 1 := by
    intro y hy
    have h1 : IsUnit (algebraMap B (LocalSubring.ofPrime B I).toSubring y) :=
      IsLocalization.map_units (M := I.primeCompl) _ ⟨y, hy⟩
    have h2 := h1.map (Subring.inclusion hle₁)
    exact (V.valuation_eq_one_iff ⟨y, hBV y.2⟩).mp h2
  have hnonunit : ∀ y : B, y ∈ I → (y : L) ∈ V.nonunits := by
    intro y hy
    have h1 : algebraMap B (LocalSubring.ofPrime B I).toSubring y ∈
        maximalIdeal (LocalSubring.ofPrime B I).toSubring :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ I y).mpr hy
    rw [ValuationSubring.mem_nonunits_iff]
    refine (V.valuation_lt_one_iff ⟨y, hBV y.2⟩).mp
      ((mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr fun hU ↦ ?_))
    exact h1 (isUnit_of_map_unit (Subring.inclusion hle₁) _ hU)
  have hAB : ∀ a : A, (a : L) ∈ B := fun a ↦ ⟨C a, by
    change aeval b (C a) = (a : L)
    rw [aeval_C]
    rfl⟩
  refine ⟨V, fun a ha ↦ hBV (hAB ⟨a, ha⟩), fun a ha ↦ ?_, hBV ⟨X, by simp [φ]⟩, fun p hp ↦ ?_⟩
  · have hmem : ψ (C a) ∈ I := Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
    have := hnonunit _ hmem
    rwa [hψv, aeval_C] at this
  · rw [← hψv]
    exact hunit _ fun h ↦ hp (hcomap p h)

end Transcendental

end DeJongAlterations.StableModification.LocalUniformization.Curve
