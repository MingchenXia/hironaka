/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# Differentials of a finite cover of the affine line and the trace dual

Let `k` be a field, `A` a domain which is a finite `k[t]`-algebra with fraction field `K`, and
suppose `K` is separable over `L = k(t)`. A derivation `D : K → K` over `k` with `D t = 1`
identifies the module of Kähler differentials of `A` with an `A`-submodule of `K`
(`ω ↦ ω / dt`). This file proves *Dedekind's theorem* for such `A`:
the differentials of `A` are exactly the trace dual of `A` times `dt`,
`Ω¹_{A/k} ≅ A^∨ = {y ∈ K | Tr_{K/L}(y A) ⊆ k[t]}`,
when `k` is algebraically closed, `A` is integrally closed and `Ω¹_{A/k}` is torsion free (`A`
smooth over `k`). Geometrically: for a finite separable morphism `f : X → 𝔸¹_k` from a smooth
curve, `f_* Ω¹_X ≅ Hom_{𝒪}(f_* 𝒪_X, Ω¹_{𝔸¹})` via the trace (the duality for a finite flat
morphism), which is the input for `deg Ω¹_X = 2g - 2` (Temkin, *Stable modification of relative
curves*, J. Algebraic Geom. 19 (2010), Thm 1.1, `references/temkin10-stable-modification/source/
semi-stable.tex`, lines 1717–1741). Blueprint: `sm-omega-degree.tex`,
`lem:sm-dedekind-different`.

The proof is local over `k[t]`: at a maximal ideal `q` of `k[t]`, `A` agrees after inverting some
`σ ∉ q` with a monogenic algebra `k[t][x] ≅ k[t][Y]/(f)`; there the trace dual is
`f'(x)⁻¹ k[t][x]` (Euler's lemma, Mathlib's `traceForm_dualSubmodule_adjoin`) and
`D x = -f^D(x)/f'(x)` (`f^D` the coefficientwise derivative), which gives
`D(A) ⊆ A^∨`; torsion freeness of `Ω¹_{A/k}` shows that `f'(x)` and `f^D(x)` generate the unit
ideal after inverting `σ`, which gives `A^∨ ⊆ A · D(A)`.

## Main definitions

* `Different.ddt`: the derivation `d/dt` of `K`.
* `Different.dCoeff`: the coefficientwise derivative of a polynomial over `k[t]`.
* `Different.kaehlerToField`: the map `Ω¹_{A/k} → K`, `a db ↦ a D(b)`.

## Main results

* `Different.ddt_X`: `d/dt (t) = 1`.
* `Different.derivation_aeval`: the chain rule
  `δ (g(y)) = g'(y) δ y + g^D(y) δ t`.
* `Different.kaehlerToField_injective`: `ω ↦ ω / dt` is injective if `Ω¹_{A/k}` is torsion free.
* `Different.exists_adjoin_of_isMaximal`: local monogenicity of `A` over `k[t]` (`k = k̄`).
* `Different.range_kaehlerToField_eq_traceDual`, `Different.kaehlerEquivTraceDual`:
  Dedekind's theorem `Ω¹_{A/k} ≅ A^∨`.
-/

universe u v w

open Polynomial
open scoped Pointwise

set_option linter.unusedSectionVars false

namespace DeJongAlterations.StableModification.CurvesField.Different

noncomputable section

/-! ### The derivation `d/dt` of a separable extension of `k(t)` -/

section Ddt

lemma formallyEtale_polynomial (k : Type u) [Field k] (L : Type v) (K : Type w) [Field L] [Field K]
    [Algebra k[X] L] [IsFractionRing k[X] L] [Algebra L K] [Algebra k[X] K]
    [IsScalarTower k[X] L K] [Algebra.IsSeparable L K] : Algebra.FormallyEtale k[X] K :=
  have : Algebra.FormallyEtale k[X] L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors k[X])
  have : Algebra.FormallyEtale L K := Algebra.FormallyEtale.of_isSeparable L K
  Algebra.FormallyEtale.comp k[X] L K

variable (k : Type u) [Field k] (L : Type v) (K : Type w) [Field L] [Field K] [Algebra k[X] L]
  [IsFractionRing k[X] L] [Algebra L K] [Algebra k[X] K] [IsScalarTower k[X] L K]
  [Algebra.IsSeparable L K] [Algebra k K] [IsScalarTower k k[X] K]

/-- `Ω¹_{K/k} ≅ K`, `dt ↦ 1`, for `K` finite separable over `k(t)`. -/
def kaehlerEquiv : Ω[K⁄k] ≃ₗ[K] K :=
  have := formallyEtale_polynomial k L K
  (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k k[X] K).symm ≪≫ₗ
    LinearEquiv.baseChange k[X] K _ _ (KaehlerDifferential.polynomialEquiv k) ≪≫ₗ
    TensorProduct.AlgebraTensorModule.rid k[X] K K

/-- The derivation `d/dt` of `K`. -/
def ddt : Derivation k K K :=
  (kaehlerEquiv k L K : Ω[K⁄k] →ₗ[K] K).compDer (KaehlerDifferential.D k K)

/-- `d/dt (t) = 1`. -/
theorem ddt_X : ddt k L K (algebraMap k[X] K X) = 1 := by
  have := formallyEtale_polynomial k L K
  change kaehlerEquiv k L K (KaehlerDifferential.D k K (algebraMap k[X] K X)) = 1
  simp only [kaehlerEquiv, LinearEquiv.trans_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearEquiv.baseChange_tmul, KaehlerDifferential.polynomialEquiv_D, derivative_X,
    TensorProduct.AlgebraTensorModule.rid_tmul, one_smul]

end Ddt

/-! ### The chain rule for polynomials over `k[t]` -/

section ChainRule

variable {k : Type u} [Field k]

/-- The coefficientwise derivative `g^D = ∑ (d gᵢ/dt) Yⁱ` of `g ∈ k[t][Y]`. -/
def dCoeff (g : k[X][X]) : k[X][X] := g.sum fun i c => monomial i (derivative c)

lemma dCoeff_add (g h : k[X][X]) : dCoeff (g + h) = dCoeff g + dCoeff h := by
  unfold dCoeff
  rw [Polynomial.sum_add_index]
  · intro i; simp
  · intro i c c'; simp [derivative_add]

lemma dCoeff_monomial (i : ℕ) (c : k[X]) : dCoeff (monomial i c) = monomial i (derivative c) := by
  unfold dCoeff
  rw [Polynomial.sum_monomial_index]
  simp

variable {B M : Type*} [CommRing B] [Algebra k B] [Algebra k[X] B] [IsScalarTower k k[X] B]
  [AddCommGroup M] [Module B M] [Module k M]

/-- For a `k`-derivation `δ` and `c ∈ k[t]`: `δ(c(t)) = c'(t) δ(t)`. -/
lemma derivation_algebraMap (δ : Derivation k B M) (c : k[X]) :
    δ (algebraMap k[X] B c) = algebraMap k[X] B (derivative c) • δ (algebraMap k[X] B X) := by
  have h : ∀ p : k[X], algebraMap k[X] B p = aeval (algebraMap k[X] B X) p := by
    intro p
    rw [show algebraMap k[X] B X = IsScalarTower.toAlgHom k k[X] B X from rfl,
      aeval_algHom_apply, aeval_X_left_apply]
    rfl
  rw [h c, Derivation.map_aeval, ← h]

/-- **Chain rule**: `δ (g(y)) = g'(y) δ y + g^D(y) δ t` for `g ∈ k[t][Y]`. -/
theorem derivation_aeval (δ : Derivation k B M) (y : B) (g : k[X][X]) :
    δ (aeval y g) = aeval y (derivative g) • δ y +
      aeval y (dCoeff g) • δ (algebraMap k[X] B X) := by
  induction g using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add, hp, hq, derivative_add, dCoeff_add, map_add, map_add, add_smul, add_smul]
    abel
  | monomial i c =>
    rw [aeval_monomial, Derivation.leibniz, Derivation.leibniz_pow, derivation_algebraMap,
      derivative_monomial, dCoeff_monomial, aeval_monomial, aeval_monomial,
      ← Nat.cast_smul_eq_nsmul B, smul_smul, smul_smul, smul_smul, map_mul, map_natCast]
    congr 1
    congr 1
    ring

end ChainRule

/-! ### Local-global principles and the map `Ω¹ → K` -/

section General

variable {k : Type u} [Field k]

section
variable {L : Type w} [Field L] [Algebra k[X] L]

/-- An element `z` of `L` lies in `k[t]` if for every maximal ideal `q` some `τ ∉ q` has
`τ z ∈ k[t]`. -/
lemma mem_range_of_forall_isMaximal (z : L)
    (h : ∀ q : Ideal k[X], q.IsMaximal → ∃ τ ∉ q, algebraMap k[X] L τ * z ∈
      (algebraMap k[X] L).range) : z ∈ (algebraMap k[X] L).range := by
  let I : Ideal k[X] :=
    { carrier := {τ | algebraMap k[X] L τ * z ∈ (algebraMap k[X] L).range}
      add_mem' := by
        rintro a b ⟨c, hc⟩ ⟨d, hd⟩
        exact ⟨c + d, by simp only [map_add, add_mul, hc, hd]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨d, hd⟩
        exact ⟨c * d, by simp only [smul_eq_mul, map_mul, mul_assoc, hd]⟩ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨τ, hτ, hτz⟩ := h q hq
    exact hτ (hIq hτz)
  have h1 : (1 : k[X]) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

end

section
variable {A : Type v} [CommRing A] [Algebra k[X] A] {K : Type w} [Field K] [Algebra A K]
  [Algebra k[X] K] [IsScalarTower k[X] A K]

/-- A local-global principle for `A`-submodules of `K`. -/
lemma mem_of_forall_isMaximal (N : Submodule A K) (y : K)
    (h : ∀ q : Ideal k[X], q.IsMaximal → ∃ τ ∉ q, algebraMap k[X] K τ * y ∈ N) : y ∈ N := by
  let I : Ideal k[X] :=
    { carrier := {τ | algebraMap k[X] K τ * y ∈ N}
      add_mem' := by
        intro a b ha hb
        change algebraMap k[X] K (a + b) * y ∈ N
        rw [map_add, add_mul]
        exact N.add_mem ha hb
      zero_mem' := by
        change algebraMap k[X] K 0 * y ∈ N
        simp
      smul_mem' := by
        intro c a ha
        change algebraMap k[X] K (c * a) * y ∈ N
        have := N.smul_mem (algebraMap k[X] A c) ha
        rwa [Algebra.smul_def, ← IsScalarTower.algebraMap_apply, ← mul_assoc, ← map_mul] at this }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal I hne
    obtain ⟨τ, hτ, hτy⟩ := h q hq
    exact hτ (hIq hτy)
  have h1 : (1 : k[X]) ∈ I := hI ▸ Submodule.mem_top
  simpa [I] using h1

lemma algebraMap_smul_eq (σ : k[X]) (a : A) :
    algebraMap A K (σ • a) = algebraMap k[X] K σ * algebraMap A K a := by
  rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply]

end

section
variable {A : Type v} [CommRing A] [Algebra k A] {K : Type w} [Field K] [Algebra A K] [Algebra k K]
  [IsScalarTower k A K] (D : Derivation k K K)

/-- The `A`-linear map `Ω¹_{A/k} → K`, `a db ↦ a D(b)`, i.e. `ω ↦ ω / dt`. -/
def kaehlerToField : Ω[A⁄k] →ₗ[A] K := (D.compAlgebraMap A).liftKaehlerDifferential

lemma kaehlerToField_D (a : A) :
    kaehlerToField D (KaehlerDifferential.D k A a) = D (algebraMap A K a) :=
  Derivation.liftKaehlerDifferential_comp_D _ a

end

end General

/-! ### The setting -/

section Setting

variable {k : Type u} [Field k] {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
  [Algebra k[X] A] [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.IsTorsionFree k[X] A]
  {L : Type w} {K : Type w} [Field L] [Field K] [Algebra k[X] L] [IsFractionRing k[X] L]
  [Algebra A K] [IsFractionRing A K] [Algebra L K] [Algebra k[X] K] [IsScalarTower k[X] L K]
  [IsScalarTower k[X] A K] [Algebra k K] [IsScalarTower k A K] [IsScalarTower k k[X] K]
  [FiniteDimensional L K] [Algebra.IsSeparable L K]

/-! #### Minimal polynomials -/

variable (k K) in
lemma isIntegral_algebraMap (a : A) : IsIntegral k[X] (algebraMap A K a) :=
  (Algebra.IsIntegral.isIntegral (R := k[X]) a).map (IsScalarTower.toAlgHom k[X] A K)

lemma minpoly_algebraMap (a : A) : minpoly k[X] (algebraMap A K a) = minpoly k[X] a :=
  minpoly.algHom_eq (IsScalarTower.toAlgHom k[X] A K) (IsFractionRing.injective A K) a

include L in
/-- `f'(x) ≠ 0` for the minimal polynomial `f` of `x ∈ A` over `k[t]` (separability). -/
lemma aeval_derivative_minpoly_ne_zero (a : A) :
    aeval (algebraMap A K a) (derivative (minpoly k[X] a)) ≠ 0 := by
  have hi := isIntegral_algebraMap k K a
  have h := minpoly.isIntegrallyClosed_eq_field_fractions' L hi
  rw [minpoly_algebraMap] at h
  have hsep := Algebra.IsSeparable.isSeparable L (algebraMap A K a)
  have := hsep.aeval_derivative_ne_zero (minpoly.aeval L (algebraMap A K a))
  rwa [h, derivative_map, aeval_map_algebraMap] at this

lemma aeval_algebraMap_minpoly (a : A) : aeval (algebraMap A K a) (minpoly k[X] a) = 0 := by
  rw [aeval_algebraMap_apply, minpoly.aeval, map_zero]

variable (D : Derivation k K K) (hD : D (algebraMap k[X] K X) = 1)

include hD in
/-- `f'(x) D(x) = -f^D(x)` for the minimal polynomial `f` of `x`. -/
lemma derivative_mul_D (x : A) :
    aeval (algebraMap A K x) (derivative (minpoly k[X] x)) * D (algebraMap A K x) =
      -aeval (algebraMap A K x) (dCoeff (minpoly k[X] x)) := by
  have h := derivation_aeval D (algebraMap A K x) (minpoly k[X] x)
  rw [aeval_algebraMap_minpoly, map_zero, hD, smul_eq_mul, smul_eq_mul, mul_one] at h
  rw [eq_neg_iff_add_eq_zero, ← h]

/-- Traces of elements of `A` lie in `k[t]`. -/
lemma trace_algebraMap_mem (c : A) :
    Algebra.trace L K (algebraMap A K c) ∈ (algebraMap k[X] L).range := by
  have hi := Algebra.isIntegral_trace (L := L) (isIntegral_algebraMap k K c)
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := L)).mp hi
  exact ⟨y, hy⟩

variable (L K) in
include k L K in
/-- An integrally closed finite `k[t]`-algebra with separable fraction field is a Dedekind
domain. -/
lemma isDedekindDomain [IsIntegrallyClosed A] : IsDedekindDomain A :=
  have : Algebra.IsIntegral k[X] A := Algebra.IsIntegral.of_finite k[X] A
  have : IsIntegralClosure A k[X] K := IsIntegralClosure.of_isIntegrallyClosed A k[X] K
  IsIntegralClosure.isDedekindDomain k[X] L K A

/-! #### The map `Ω¹_{A/k} → K` -/

include hD in
lemma kaehlerToField_dt :
    kaehlerToField D (KaehlerDifferential.D k A (algebraMap k[X] A X)) = 1 := by
  rw [kaehlerToField_D, ← IsScalarTower.algebraMap_apply k[X] A K, hD]

include L K in
/-- Every differential of `A` has a nonzero multiple in `A · dt`. -/
lemma exists_smul_eq_smul_dt (ω : Ω[A⁄k]) : ∃ c : A, c ≠ 0 ∧ ∃ e : A,
    c • ω = e • KaehlerDifferential.D k A (algebraMap k[X] A X) := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D k A)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨a, rfl⟩ := h
    set f := minpoly k[X] a
    have h := derivation_aeval (KaehlerDifferential.D k A) a f
    rw [minpoly.aeval, map_zero] at h
    refine ⟨aeval a (derivative f), ?_, -aeval a (dCoeff f), ?_⟩
    · intro h0
      apply aeval_derivative_minpoly_ne_zero (k := k) (L := L) (K := K) a
      rw [aeval_algebraMap_apply, h0, map_zero]
    · rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left h.symm
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | add ω₁ ω₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, hc₁, e₁, he₁⟩ := h₁
    obtain ⟨c₂, hc₂, e₂, he₂⟩ := h₂
    refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, c₂ * e₁ + c₁ * e₂, ?_⟩
    rw [smul_add, mul_comm c₁ c₂, mul_smul, he₁, mul_comm c₂ c₁, mul_smul, he₂, smul_smul,
      smul_smul, ← add_smul]
  | smul b ω _ h =>
    obtain ⟨c, hc, e, he⟩ := h
    exact ⟨c, hc, b * e, by rw [smul_comm, he, smul_smul]⟩

include L hD in
/-- If `Ω¹_{A/k}` is torsion free, `ω ↦ ω / dt` is injective. -/
theorem kaehlerToField_injective [Module.IsTorsionFree A Ω[A⁄k]] :
    Function.Injective (kaehlerToField (A := A) D) := by
  rw [injective_iff_map_eq_zero]
  intro ω hω
  obtain ⟨c, hc, e, he⟩ := exists_smul_eq_smul_dt (L := L) (K := K) ω
  have h := congrArg (kaehlerToField D) he
  rw [map_smul, map_smul, hω, smul_zero, kaehlerToField_dt D hD, Algebra.smul_def, mul_one,
    eq_comm, map_eq_zero_iff _ (IsFractionRing.injective A K)] at h
  rw [h, zero_smul] at he
  rcases smul_eq_zero.mp he with h' | h'
  · exact absurd h' hc
  · exact h'

/-! #### A local monogenic presentation -/

section Monogenic

variable (x : A) (σ : k[X]) (hσ0 : σ ≠ 0) (hσ : ∀ a : A, σ • a ∈ Algebra.adjoin k[X] {x})

include hσ in
lemma exists_aeval_eq_smul (a : A) : ∃ g : k[X][X], aeval x g = σ • a := by
  have := hσ a
  rw [Algebra.adjoin_singleton_eq_range_aeval] at this
  obtain ⟨g, hg⟩ := this
  exact ⟨g, hg⟩

include hσ in
lemma smul_mem_adjoin (a : A) :
    algebraMap k[X] K σ * algebraMap A K a ∈ Algebra.adjoin k[X] {algebraMap A K x} := by
  obtain ⟨g, hg⟩ := exists_aeval_eq_smul x σ hσ a
  rw [← algebraMap_smul_eq, ← hg, ← aeval_algebraMap_apply]
  exact aeval_mem_adjoin_singleton k[X] _

include L hσ0 in
lemma algebraMap_ne_zero_of_ne_zero : algebraMap k[X] K σ ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply k[X] L K]
  exact (_root_.map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective k[X] L)).mpr hσ0)

include hσ0 hσ in
/-- `K = L(x)`. -/
lemma adjoin_eq_top : Algebra.adjoin L {algebraMap A K x} = ⊤ := by
  rw [eq_top_iff]
  intro z _
  set S := Algebra.adjoin L {algebraMap A K x}
  have key : ∀ c : A, algebraMap A K c ∈ S := by
    intro c
    obtain ⟨g, hg⟩ := exists_aeval_eq_smul x σ hσ c
    have h1 : algebraMap k[X] K σ * algebraMap A K c ∈ S := by
      rw [← algebraMap_smul_eq, ← hg, ← aeval_algebraMap_apply,
        ← aeval_map_algebraMap L]
      exact aeval_mem_adjoin_singleton L _
    have hσK := algebraMap_ne_zero_of_ne_zero (L := L) (K := K) σ hσ0
    have h2 : (algebraMap k[X] K σ)⁻¹ ∈ S := by
      rw [IsScalarTower.algebraMap_apply k[X] L K, ← map_inv₀]
      exact S.algebraMap_mem _
    have := S.mul_mem h2 h1
    rwa [← mul_assoc, inv_mul_cancel₀ hσK, one_mul] at this
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A z
  rw [div_eq_mul_inv]
  refine S.mul_mem (key a) ?_
  exact S.inv_mem_of_algebraic (x := ⟨_, key b⟩) (Algebra.IsAlgebraic.isAlgebraic _)

include hσ0 hσ in
/-- **Euler's lemma** for the local monogenic presentation: the trace dual of `k[t][x]` is
`f'(x)⁻¹ k[t][x]`. -/
lemma dualSubmodule_adjoin :
    (Algebra.traceForm L K).dualSubmodule
        (Subalgebra.toSubmodule (Algebra.adjoin k[X] {algebraMap A K x})) =
      (aeval (algebraMap A K x) (derivative (minpoly k[X] x)))⁻¹ •
        Subalgebra.toSubmodule (Algebra.adjoin k[X] {algebraMap A K x}) := by
  have hi := isIntegral_algebraMap k K x
  rw [traceForm_dualSubmodule_adjoin k[X] L (adjoin_eq_top x σ hσ0 hσ) hi,
    minpoly.isIntegrallyClosed_eq_field_fractions' L hi, minpoly_algebraMap, derivative_map,
    aeval_map_algebraMap]

include L hD hσ in
/-- `σ D(b) ∈ f'(x)⁻¹ k[t][x] + A`. -/
lemma exists_smul_D_eq (b : A) : ∃ w ∈ Algebra.adjoin k[X] {algebraMap A K x}, ∃ e : A,
    algebraMap k[X] K σ * D (algebraMap A K b) =
      (aeval (algebraMap A K x) (derivative (minpoly k[X] x)))⁻¹ * w + algebraMap A K e := by
  obtain ⟨g, hg⟩ := exists_aeval_eq_smul x σ hσ b
  set f := minpoly k[X] x
  set y := algebraMap A K x
  have hf' : aeval y (derivative f) ≠ 0 := aeval_derivative_minpoly_ne_zero (L := L) x
  have hDx : D y = (aeval y (derivative f))⁻¹ * -aeval y (dCoeff f) := by
    rw [← derivative_mul_D D hD x, ← mul_assoc, inv_mul_cancel₀ hf', one_mul]
  have h1 : algebraMap k[X] K σ * algebraMap A K b = aeval y g := by
    rw [← algebraMap_smul_eq, ← hg, aeval_algebraMap_apply]
  have h2 := congrArg D h1
  rw [Derivation.leibniz, derivation_algebraMap, derivation_aeval, hD, smul_eq_mul, smul_eq_mul,
    smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_one, mul_one, hDx] at h2
  refine ⟨aeval y (derivative g * -dCoeff f), aeval_mem_adjoin_singleton k[X] _,
    aeval x (dCoeff g) - b * algebraMap k[X] A (derivative σ), ?_⟩
  rw [map_sub, map_mul (algebraMap A K), ← aeval_algebraMap_apply,
    ← IsScalarTower.algebraMap_apply k[X] A K, map_mul (aeval y), map_neg]
  linear_combination h2

include hD hσ0 hσ in
/-- The local inclusion `D(A) ⊆ A^∨`: `σ² Tr(a D(b)) ∈ k[t]`. -/
lemma trace_mul_D_mem (a b : A) :
    algebraMap k[X] L (σ ^ 2) * Algebra.trace L K (algebraMap A K a * D (algebraMap A K b)) ∈
      (algebraMap k[X] L).range := by
  obtain ⟨w, hw, e, he⟩ := exists_smul_D_eq (L := L) D hD x σ hσ b
  set y := algebraMap A K x
  set u := (aeval y (derivative (minpoly k[X] x)))⁻¹ * w
  have hσK : algebraMap k[X] K σ = algebraMap L K (algebraMap k[X] L σ) :=
    IsScalarTower.algebraMap_apply k[X] L K σ
  have hu : u ∈ (Algebra.traceForm L K).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin k[X] {y})) := by
    rw [dualSubmodule_adjoin x σ hσ0 hσ, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨w, hw, rfl⟩
  have hmem := (LinearMap.BilinForm.mem_dualSubmodule _).mp hu
    (algebraMap k[X] K σ * algebraMap A K a) (smul_mem_adjoin x σ hσ a)
  rw [Algebra.traceForm_apply, Submodule.mem_one] at hmem
  obtain ⟨c₁, hc₁⟩ := hmem
  obtain ⟨c₂, hc₂⟩ := trace_algebraMap_mem (k := k) (L := L) (K := K) (a * e)
  refine ⟨c₁ + algebraMap k[X] k[X] σ * c₂, ?_⟩
  have hTr : ∀ (c : L) (z : K), Algebra.trace L K (algebraMap L K c * z) =
      c * Algebra.trace L K z := by
    intro c z
    rw [← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
  have expand : algebraMap k[X] L (σ ^ 2) *
      Algebra.trace L K (algebraMap A K a * D (algebraMap A K b)) =
      Algebra.trace L K (u * (algebraMap k[X] K σ * algebraMap A K a)) +
        algebraMap k[X] L σ * Algebra.trace L K (algebraMap A K (a * e)) := by
    calc algebraMap k[X] L (σ ^ 2) * Algebra.trace L K (algebraMap A K a * D (algebraMap A K b))
        = algebraMap k[X] L σ * Algebra.trace L K
            (algebraMap A K a * (algebraMap k[X] K σ * D (algebraMap A K b))) := by
          rw [show algebraMap A K a * (algebraMap k[X] K σ * D (algebraMap A K b)) =
            algebraMap L K (algebraMap k[X] L σ) * (algebraMap A K a * D (algebraMap A K b)) by
              rw [hσK]; ring, hTr, map_pow]
          ring
      _ = algebraMap k[X] L σ * Algebra.trace L K (algebraMap A K a * u) +
            algebraMap k[X] L σ * Algebra.trace L K (algebraMap A K (a * e)) := by
          rw [he, mul_add, map_add, mul_add, map_mul (algebraMap A K) a e]
      _ = _ := by
          rw [show u * (algebraMap k[X] K σ * algebraMap A K a) =
            algebraMap L K (algebraMap k[X] L σ) * (algebraMap A K a * u) by rw [hσK]; ring, hTr]
  rw [expand, ← hc₁, ← hc₂, map_add, map_mul, Algebra.algebraMap_self, RingHom.id_apply]

/-! #### The derivative along `x` -/

include A hσ0 in
lemma algebraMap_ne_zero' : algebraMap k[X] K σ ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply k[X] A K]
  refine (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ?_
  intro h
  have : σ • (1 : A) = 0 := by rw [Algebra.smul_def, h, zero_mul]
  rcases smul_eq_zero.mp this with h' | h'
  · exact hσ0 h'
  · exact one_ne_zero h'

/-- The `A`-submodule `f'(x) · A[σ⁻¹]` of `K`, `f` the minimal polynomial of `x`. -/
def relSubmodule : Submodule A K where
  carrier := {z | ∃ (j : ℕ) (c : A), algebraMap k[X] K σ ^ j * z =
    algebraMap A K (aeval x (derivative (minpoly k[X] x)) * c)}
  add_mem' := by
    rintro z₁ z₂ ⟨j₁, c₁, h₁⟩ ⟨j₂, c₂, h₂⟩
    refine ⟨j₁ + j₂, algebraMap k[X] A σ ^ j₂ * c₁ + algebraMap k[X] A σ ^ j₁ * c₂, ?_⟩
    simp only [map_mul, map_add, map_pow, ← IsScalarTower.algebraMap_apply] at h₁ h₂ ⊢
    linear_combination (algebraMap k[X] K σ ^ j₂) * h₁ + (algebraMap k[X] K σ ^ j₁) * h₂
  zero_mem' := ⟨0, 0, by simp⟩
  smul_mem' := by
    rintro c z ⟨j, d, h⟩
    refine ⟨j, c * d, ?_⟩
    simp only [Algebra.smul_def, map_mul] at h ⊢
    linear_combination (algebraMap A K c) * h

include hσ in
lemma exists_rep (a : A) : ∃ p : ℕ × k[X][X], aeval x p.2 = σ ^ p.1 • a := by
  obtain ⟨g, hg⟩ := exists_aeval_eq_smul x σ hσ a
  exact ⟨(1, g), by rw [pow_one]; exact hg⟩

/-- A chosen presentation `σʲ a = g(x)`. -/
def rep (a : A) : ℕ × k[X][X] := Classical.choose (exists_rep x σ hσ a)

lemma rep_spec (a : A) : aeval x (rep x σ hσ a).2 = σ ^ (rep x σ hσ a).1 • a :=
  Classical.choose_spec (exists_rep x σ hσ a)

/-- The value `σ⁻ʲ g'(x)` of the derivative along `x` in `K ⧸ f'(x) A[σ⁻¹]`. -/
def deltaFun (a : A) : K ⧸ relSubmodule (K := K) x σ :=
  Submodule.Quotient.mk ((algebraMap k[X] K σ ^ (rep x σ hσ a).1)⁻¹ *
    aeval (algebraMap A K x) (derivative (rep x σ hσ a).2))

include hσ0 in
/-- The value of `deltaFun` does not depend on the presentation. -/
lemma deltaFun_eq {a : A} {j : ℕ} {g : k[X][X]} (hg : aeval x g = σ ^ j • a) :
    deltaFun (K := K) x σ hσ a = Submodule.Quotient.mk ((algebraMap k[X] K σ ^ j)⁻¹ *
      aeval (algebraMap A K x) (derivative g)) := by
  set j₀ := (rep x σ hσ a).1
  set g₀ := (rep x σ hσ a).2
  have h₀ : aeval x g₀ = σ ^ j₀ • a := rep_spec x σ hσ a
  set f := minpoly k[X] x
  have hfx : IsIntegral k[X] x := Algebra.IsIntegral.isIntegral x
  have hdvd : f ∣ C (σ ^ j₀) * g - C (σ ^ j) * g₀ := by
    apply minpoly.isIntegrallyClosed_dvd hfx
    rw [map_sub, map_mul, map_mul, aeval_C, aeval_C, hg, h₀, ← Algebra.smul_def,
      ← Algebra.smul_def, smul_smul, smul_smul, mul_comm, sub_self]
  obtain ⟨h, hh⟩ := hdvd
  have hder := congrArg derivative hh
  rw [derivative_sub, derivative_mul, derivative_mul, derivative_C, derivative_C, zero_mul,
    zero_add, zero_mul, zero_add, derivative_mul] at hder
  have hev := congrArg (aeval (algebraMap A K x)) hder
  rw [map_sub, map_mul, map_mul, aeval_C, aeval_C, map_add, map_mul, map_mul,
    aeval_algebraMap_minpoly, zero_mul, add_zero] at hev
  have hσK : algebraMap k[X] K σ ≠ 0 := algebraMap_ne_zero' (A := A) (K := K) σ hσ0
  change Submodule.Quotient.mk _ = _
  rw [Submodule.Quotient.eq]
  refine ⟨j + j₀, -aeval x h, ?_⟩
  rw [map_mul, map_neg, ← aeval_algebraMap_apply, ← aeval_algebraMap_apply]
  rw [map_pow, map_pow] at hev
  have e : algebraMap k[X] K σ ^ (j + j₀) *
      ((algebraMap k[X] K σ ^ j₀)⁻¹ * aeval (algebraMap A K x) (derivative g₀) -
        (algebraMap k[X] K σ ^ j)⁻¹ * aeval (algebraMap A K x) (derivative g)) =
      algebraMap k[X] K σ ^ j * aeval (algebraMap A K x) (derivative g₀) -
        algebraMap k[X] K σ ^ j₀ * aeval (algebraMap A K x) (derivative g) := by
    rw [pow_add]
    field_simp
  rw [e]
  linear_combination -hev

include hσ0 in
lemma deltaFun_add (a b : A) : deltaFun (K := K) x σ hσ (a + b) =
    deltaFun (K := K) x σ hσ a + deltaFun (K := K) x σ hσ b := by
  set p := rep x σ hσ a
  set q := rep x σ hσ b
  have hp : aeval x p.2 = σ ^ p.1 • a := rep_spec x σ hσ a
  have hq : aeval x q.2 = σ ^ q.1 • b := rep_spec x σ hσ b
  have hpq : aeval x (C (σ ^ q.1) * p.2 + C (σ ^ p.1) * q.2) = σ ^ (p.1 + q.1) • (a + b) := by
    rw [map_add, map_mul, map_mul, aeval_C, aeval_C, hp, hq, ← Algebra.smul_def,
      ← Algebra.smul_def, smul_smul, smul_smul, smul_add, pow_add, mul_comm]
  rw [deltaFun_eq (K := K) x σ hσ0 hσ hpq, deltaFun_eq (K := K) x σ hσ0 hσ hp,
    deltaFun_eq (K := K) x σ hσ0 hσ hq,
    ← Submodule.Quotient.mk_add]
  congr 1
  have hσK : algebraMap k[X] K σ ≠ 0 := algebraMap_ne_zero' (A := A) (K := K) σ hσ0
  rw [derivative_add, derivative_mul, derivative_mul, derivative_C, derivative_C, zero_mul,
    zero_mul, zero_add, zero_add, map_add, map_mul, map_mul, aeval_C, aeval_C, map_pow, map_pow]
  field_simp
  ring

include hσ0 in
lemma deltaFun_smul (c : k) (a : A) : deltaFun (K := K) x σ hσ (c • a) =
    c • deltaFun (K := K) x σ hσ a := by
  set p := rep x σ hσ a
  have hp : aeval x p.2 = σ ^ p.1 • a := rep_spec x σ hσ a
  have hc : aeval x (C (algebraMap k k[X] c) * p.2) = σ ^ p.1 • (c • a) := by
    rw [map_mul, aeval_C, hp, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def,
      smul_comm]
  rw [deltaFun_eq (K := K) x σ hσ0 hσ hc, deltaFun_eq (K := K) x σ hσ0 hσ hp,
    ← Submodule.Quotient.mk_smul]
  congr 1
  rw [derivative_mul, derivative_C, zero_mul, zero_add, map_mul, aeval_C, Algebra.smul_def,
    ← IsScalarTower.algebraMap_apply]
  ring

include hσ0 in
lemma deltaFun_mul (a b : A) : deltaFun (K := K) x σ hσ (a * b) =
    a • deltaFun (K := K) x σ hσ b + b • deltaFun (K := K) x σ hσ a := by
  set p := rep x σ hσ a
  set q := rep x σ hσ b
  have hp : aeval x p.2 = σ ^ p.1 • a := rep_spec x σ hσ a
  have hq : aeval x q.2 = σ ^ q.1 • b := rep_spec x σ hσ b
  have hpq : aeval x (p.2 * q.2) = σ ^ (p.1 + q.1) • (a * b) := by
    rw [map_mul, hp, hq, smul_mul_smul_comm, pow_add]
  rw [deltaFun_eq (K := K) x σ hσ0 hσ hpq, deltaFun_eq (K := K) x σ hσ0 hσ hp,
    deltaFun_eq (K := K) x σ hσ0 hσ hq,
    ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  have hσK : algebraMap k[X] K σ ≠ 0 := algebraMap_ne_zero' (A := A) (K := K) σ hσ0
  have hp' : aeval (algebraMap A K x) p.2 = algebraMap k[X] K σ ^ p.1 * algebraMap A K a := by
    rw [aeval_algebraMap_apply, hp, algebraMap_smul_eq, map_pow]
  have hq' : aeval (algebraMap A K x) q.2 = algebraMap k[X] K σ ^ q.1 * algebraMap A K b := by
    rw [aeval_algebraMap_apply, hq, algebraMap_smul_eq, map_pow]
  rw [derivative_mul, map_add, map_mul, map_mul, hp', hq', Algebra.smul_def, Algebra.smul_def]
  field_simp
  ring

/-- The derivative along `x`: the `k[t]`-derivation of `A` into `K ⧸ f'(x) A[σ⁻¹]` with
`x ↦ 1` (it kills `t`). -/
def delta : Derivation k A (K ⧸ relSubmodule (K := K) x σ) :=
  Derivation.mk'
    { toFun := deltaFun (K := K) x σ hσ
      map_add' := deltaFun_add x σ hσ0 hσ
      map_smul' := deltaFun_smul x σ hσ0 hσ }
    (deltaFun_mul x σ hσ0 hσ)

lemma delta_apply (a : A) : delta (K := K) x σ hσ0 hσ a = deltaFun (K := K) x σ hσ a := rfl

lemma delta_t : delta (K := K) x σ hσ0 hσ (algebraMap k[X] A X) = 0 := by
  rw [delta_apply, deltaFun_eq (K := K) x σ hσ0 hσ (j := 0) (g := C X)
    (by rw [aeval_C, pow_zero, one_smul])]
  simp

lemma delta_x : delta (K := K) x σ hσ0 hσ x = Submodule.Quotient.mk 1 := by
  rw [delta_apply, deltaFun_eq (K := K) x σ hσ0 hσ (j := 0) (g := X)
    (by rw [aeval_X, pow_zero, one_smul])]
  simp

/-! #### The unit ideal `(f'(x), f^D(x))` -/

include L hD hσ0 hσ in
/-- **Torsion freeness gives the Jacobian condition**: if `Ω¹_{A/k}` is torsion free, some power
of `σ` lies in the ideal `(f'(x), f^D(x))` of `A`. -/
theorem exists_pow_mem_span [IsIntegrallyClosed A] [Module.IsTorsionFree A Ω[A⁄k]] :
    ∃ j : ℕ, algebraMap k[X] A (σ ^ j) ∈ Ideal.span
      {aeval x (derivative (minpoly k[X] x)), aeval x (dCoeff (minpoly k[X] x))} := by
  have := isDedekindDomain (k := k) (A := A) L K
  set f := minpoly k[X] x
  set F' := aeval x (derivative f)
  set U := aeval x (dCoeff f)
  set J := Ideal.span {F', U}
  have hF'K : algebraMap A K F' ≠ 0 := by
    rw [← aeval_algebraMap_apply]; exact aeval_derivative_minpoly_ne_zero (L := L) x
  have hF' : F' ≠ 0 := fun h => hF'K (by rw [h, map_zero])
  have hJ : J ≠ ⊥ := by
    intro h
    apply hF'
    have : F' ∈ J := Ideal.subset_span (by simp)
    rwa [h, Ideal.mem_bot] at this
  let I : FractionalIdeal (nonZeroDivisors A) K := ↑J
  have hI : I ≠ 0 := by
    change (↑J : FractionalIdeal (nonZeroDivisors A) K) ≠ 0
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  have key : ∀ g ∈ I⁻¹, ∃ (j : ℕ) (c : A), algebraMap k[X] K σ ^ j * g = algebraMap A K c := by
    intro g hg
    rw [FractionalIdeal.mem_inv_iff hI] at hg
    obtain ⟨b₁, hb₁⟩ := (FractionalIdeal.mem_one_iff _).mp (hg (algebraMap A K F')
      ((FractionalIdeal.mem_coeIdeal _).mpr ⟨F', Ideal.subset_span (by simp), rfl⟩))
    obtain ⟨b₂, hb₂⟩ := (FractionalIdeal.mem_one_iff _).mp (hg (algebraMap A K U)
      ((FractionalIdeal.mem_coeIdeal _).mpr ⟨U, Ideal.subset_span (by simp), rfl⟩))
    set ω : Ω[A⁄k] := b₂ • KaehlerDifferential.D k A (algebraMap k[X] A X) +
      b₁ • KaehlerDifferential.D k A x
    have hψ : kaehlerToField D ω = 0 := by
      have hDx := derivative_mul_D D hD x
      rw [aeval_algebraMap_apply, aeval_algebraMap_apply] at hDx
      simp only [ω, map_add, map_smul, kaehlerToField_dt D hD, kaehlerToField_D, Algebra.smul_def,
        mul_one, hb₁, hb₂]
      linear_combination g * hDx
    have hω : ω = 0 := kaehlerToField_injective (L := L) D hD (by rw [hψ, map_zero])
    have hΔ := congrArg (delta (K := K) x σ hσ0 hσ).liftKaehlerDifferential hω
    simp only [ω, map_add, map_smul, Derivation.liftKaehlerDifferential_comp_D, delta_t, delta_x,
      smul_zero, zero_add, map_zero] at hΔ
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def,
      mul_one] at hΔ
    obtain ⟨j, c, hc⟩ := hΔ
    refine ⟨j, c, ?_⟩
    rw [hb₁, map_mul] at hc
    apply mul_right_cancel₀ hF'K
    linear_combination hc
  let T : Submodule A K :=
    { carrier := {z | ∃ (j : ℕ), ∃ c ∈ J, algebraMap k[X] K σ ^ j * z = algebraMap A K c}
      add_mem' := by
        rintro z₁ z₂ ⟨j₁, c₁, hc₁, h₁⟩ ⟨j₂, c₂, hc₂, h₂⟩
        refine ⟨j₁ + j₂, algebraMap k[X] A σ ^ j₂ * c₁ + algebraMap k[X] A σ ^ j₁ * c₂,
          J.add_mem (J.mul_mem_left _ hc₁) (J.mul_mem_left _ hc₂), ?_⟩
        simp only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at h₁ h₂ ⊢
        linear_combination (algebraMap k[X] K σ ^ j₂) * h₁ + (algebraMap k[X] K σ ^ j₁) * h₂
      zero_mem' := ⟨0, 0, J.zero_mem, by simp⟩
      smul_mem' := by
        rintro b z ⟨j, c, hc, h⟩
        refine ⟨j, b * c, J.mul_mem_left _ hc, ?_⟩
        simp only [Algebra.smul_def, map_mul] at h ⊢
        linear_combination (algebraMap A K b) * h }
  have hle : ((I * I⁻¹ : FractionalIdeal (nonZeroDivisors A) K) : Submodule A K) ≤ T := by
    rw [FractionalIdeal.coe_mul, Submodule.mul_le]
    intro y hy g hg
    obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    obtain ⟨j, c, hc⟩ := key g hg
    refine ⟨j, y' * c, J.mul_mem_right _ hy', ?_⟩
    rw [map_mul, ← hc]
    ring
  have h1 : (1 : K) ∈ ((I * I⁻¹ : FractionalIdeal (nonZeroDivisors A) K) : Submodule A K) := by
    rw [mul_inv_cancel₀ hI]
    exact FractionalIdeal.one_mem_one _
  obtain ⟨j, c, hc, hjc⟩ := hle h1
  refine ⟨j, ?_⟩
  have : algebraMap k[X] A (σ ^ j) = c := by
    apply IsFractionRing.injective A K
    rw [← IsScalarTower.algebraMap_apply, map_pow, ← hjc, mul_one]
  rw [this]
  exact hc

include hD hσ0 hσ in
/-- **The local inclusion `A^∨ ⊆ Ω¹_{A/k}`**. -/
lemma pow_mul_mem_range {j : ℕ} (hj : algebraMap k[X] A (σ ^ j) ∈ Ideal.span
      {aeval x (derivative (minpoly k[X] x)), aeval x (dCoeff (minpoly k[X] x))})
    {y : K} (hy : y ∈ Submodule.traceDual k[X] L (1 : Submodule A K)) :
    algebraMap k[X] K (σ ^ j) * y ∈ LinearMap.range (kaehlerToField (A := A) D) := by
  set f := minpoly k[X] x
  have hyC : y ∈ (Algebra.traceForm L K).dualSubmodule
      (Subalgebra.toSubmodule (Algebra.adjoin k[X] {algebraMap A K x})) := by
    rw [LinearMap.BilinForm.mem_dualSubmodule]
    intro z hz
    rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨g, rfl⟩ := hz
    have := (Submodule.mem_traceDual.mp hy) (algebraMap A K (aeval x g))
      (Submodule.mem_one.mpr ⟨_, rfl⟩)
    change (Algebra.traceForm L K y) (aeval (algebraMap A K x) g) ∈ 1
    rw [aeval_algebraMap_apply]
    obtain ⟨c, hc⟩ := this
    exact Submodule.mem_one.mpr ⟨c, hc⟩
  rw [dualSubmodule_adjoin x σ hσ0 hσ, Submodule.mem_smul_pointwise_iff_exists] at hyC
  obtain ⟨w, hw, rfl⟩ := hyC
  rw [Subalgebra.mem_toSubmodule, Algebra.adjoin_singleton_eq_range_aeval] at hw
  obtain ⟨g₀, rfl⟩ := hw
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp hj
  set c₀ := aeval x g₀
  have hF'K : aeval (algebraMap A K x) (derivative f) ≠ 0 :=
    aeval_derivative_minpoly_ne_zero (L := L) x
  have hDx : D (algebraMap A K x) =
      (aeval (algebraMap A K x) (derivative f))⁻¹ * -aeval (algebraMap A K x) (dCoeff f) := by
    rw [← derivative_mul_D D hD x, ← mul_assoc, inv_mul_cancel₀ hF'K, one_mul]
  have hαβK := congrArg (algebraMap A K) hαβ
  rw [map_add, map_mul, map_mul, ← aeval_algebraMap_apply, ← aeval_algebraMap_apply,
    ← IsScalarTower.algebraMap_apply] at hαβK
  have hc₀ : algebraMap A K c₀ = aeval (algebraMap A K x) g₀ := by
    rw [aeval_algebraMap_apply]
  refine ⟨(α * c₀) • KaehlerDifferential.D k A (algebraMap k[X] A X) -
    (β * c₀) • KaehlerDifferential.D k A x, ?_⟩
  have target : kaehlerToField D ((α * c₀) • KaehlerDifferential.D k A (algebraMap k[X] A X) -
      (β * c₀) • KaehlerDifferential.D k A x) = algebraMap k[X] K (σ ^ j) *
        ((aeval (algebraMap A K x) (derivative f))⁻¹ * aeval (algebraMap A K x) g₀) := by
    simp only [map_sub, map_smul, kaehlerToField_dt D hD, kaehlerToField_D, Algebra.smul_def,
      mul_one, map_mul, hDx]
    rw [hc₀, ← hαβK]
    field_simp
    ring
  rw [target]
  rfl

end Monogenic

/-! ### Local monogenicity over an algebraically closed field -/

omit [Field k] in
lemma prime_span_X_sub_C {F : Type*} [Field F] (a : F) : Prime (Ideal.span {X - C a}) :=
  (Ideal.prime_iff_isPrime (by rw [Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero a)).mpr
    ((Ideal.span_singleton_prime (X_sub_C_ne_zero a)).mpr (prime_X_sub_C a))

omit [Field k] in
lemma span_X_sub_C_injective {F : Type*} [Field F] {a b : F}
    (h : Ideal.span {X - C a} = Ideal.span {X - C b}) : a = b := by
  have := eq_of_monic_of_associated (monic_X_sub_C a) (monic_X_sub_C b)
    (Ideal.span_singleton_eq_span_singleton.mp h)
  exact C_injective (sub_right_injective this)

section LocalMonogenic

variable [IsAlgClosed k]

/-- The residue fields of `A` at maximal ideals are `k`. -/
lemma exists_sub_mem_of_isMaximal (P : Ideal A) [P.IsMaximal] (a : A) :
    ∃ c : k, a - algebraMap k A c ∈ P := by
  let : Field (A ⧸ P) := Ideal.Quotient.field P
  have : Algebra.FiniteType k[X] A := inferInstance
  have : Algebra.FiniteType k A := Algebra.FiniteType.trans (S := k[X]) inferInstance inferInstance
  have : Algebra.FiniteType k (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P) (Ideal.Quotient.mkₐ_surjective k P)
  have : Module.Finite k (A ⧸ P) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ P)
  have : Algebra.IsIntegral k (A ⧸ P) := Algebra.IsIntegral.of_finite k _
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := A ⧸ P)).2
    (Ideal.Quotient.mk P a)
  refine ⟨c, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, Ideal.Quotient.mk_algebraMap, hc, sub_self]

variable (L K) in
include k L K in
/-- `Pⁿ = (yⁿ) + Pⁿ⁺¹` for a uniformizer `y` at a maximal ideal `P` of the Dedekind domain `A`. -/
lemma pow_le_span_sup [IsIntegrallyClosed A] (P : Ideal A) [hP : P.IsMaximal] {y : A}
    (hy : y ∈ P) (hy2 : y ∉ P ^ 2) (n : ℕ) : P ^ n ≤ Ideal.span {y ^ n} ⊔ P ^ (n + 1) := by
  have := isDedekindDomain (k := k) (A := A) L K
  have hdvd : P ∣ Ideal.span {y} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hy)
  obtain ⟨J, hJ⟩ := hdvd
  have hJP : ¬ J ≤ P := by
    intro h
    apply hy2
    have : y ∈ Ideal.span {y} := Ideal.mem_span_singleton_self y
    rw [hJ] at this
    rw [pow_two]
    exact Ideal.mul_mono_right h this
  have hJn : ¬ J ^ n ≤ P := fun h => hJP (hP.isPrime.le_of_pow_le h)
  have hsup : J ^ n ⊔ P = ⊤ := by
    by_contra hne
    exact hJn ((hP.eq_of_le hne le_sup_right).symm ▸ le_sup_left)
  calc P ^ n = P ^ n * (J ^ n ⊔ P) := by rw [hsup, Ideal.mul_top]
    _ = Ideal.span {y ^ n} ⊔ P ^ (n + 1) := by
      rw [Ideal.mul_sup, ← mul_pow, ← hJ, Ideal.span_singleton_pow, pow_succ]
    _ ≤ _ := le_rfl

variable (L K) in
include k L K in
/-- **Local generation**: modulo `Pⁿ`, every element of `A` is a polynomial in a uniformizer `y`
with coefficients in `k`. -/
lemma exists_aeval_sub_mem_pow [IsIntegrallyClosed A] (P : Ideal A) [P.IsMaximal] {y : A}
    (hy : y ∈ P) (hy2 : y ∉ P ^ 2) (n : ℕ) (a : A) : ∃ h : k[X], a - aeval y h ∈ P ^ n := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨h, hh⟩ := ih
    obtain ⟨u, hu, v, hv, huv⟩ :=
      Submodule.mem_sup.mp (pow_le_span_sup (k := k) L K P hy hy2 n hh)
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hu
    obtain ⟨c, hc⟩ := exists_sub_mem_of_isMaximal (k := k) P r
    refine ⟨h + C c * X ^ n, ?_⟩
    have e : a - aeval y (h + C c * X ^ n) = y ^ n * (r - algebraMap k A c) + v := by
      rw [map_add, map_mul, aeval_C, map_pow, aeval_X]
      linear_combination (-1 : A) * huv
    rw [e]
    refine Ideal.add_mem _ ?_ hv
    rw [pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hy n) hc

variable (L K) in
include L K in
/-- **Local monogenicity**: for every maximal ideal `q` of `k[t]` there are `x ∈ A` and `σ ∉ q`
with `σ A ⊆ k[t][x]`. -/
theorem exists_adjoin_of_isMaximal [IsIntegrallyClosed A] (q : Ideal k[X]) [hq : q.IsMaximal] :
    ∃ (x : A) (σ : k[X]), σ ∉ q ∧ ∀ a : A, σ • a ∈ Algebra.adjoin k[X] {x} := by
  classical
  have := isDedekindDomain (k := k) (A := A) L K
  set 𝔞 := q.map (algebraMap k[X] A)
  have hq0 : q ≠ ⊥ := (Ideal.bot_lt_of_maximal q (Polynomial.not_isField k)).ne'
  have h𝔞 : 𝔞 ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective]
    · exact hq0
    · intro c d h
      have : (c - d) • (1 : A) = 0 := by rw [sub_smul, Algebra.smul_def, Algebra.smul_def, h,
        sub_self]
      rcases smul_eq_zero.mp this with h' | h'
      · exact sub_eq_zero.mp h'
      · exact absurd h' one_ne_zero
  set F := (UniqueFactorizationMonoid.normalizedFactors 𝔞).toFinset
  set e : Ideal A → ℕ := fun P => (UniqueFactorizationMonoid.normalizedFactors 𝔞).count P
  have hprime : ∀ P ∈ F, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  have hne : ∀ P ∈ F, P ≠ ⊥ := fun P hP => (hprime P hP).ne_zero
  have hmax : ∀ P ∈ F, P.IsMaximal := fun P hP =>
    (Ideal.isPrime_of_prime (hprime P hP)).isMaximal (hne P hP)
  have hfact : 𝔞 = F.inf (fun P => P ^ e P) := by
    have h := IsDedekindDomain.inf_pow_eq_prod_of_prime F id e (fun P hP => hprime P hP)
      (fun P _ Q _ h => h)
    simp only [id_eq] at h
    rw [h]
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self h𝔞]
    rw [Finset.prod_multiset_count]
  -- distinct residues `a P ∈ k`
  set aF : F → k := fun P => Infinite.natEmbedding k (F.equivFin P)
  have haF : Function.Injective aF := fun P Q h =>
    F.equivFin.injective (Fin.ext ((Infinite.natEmbedding k).injective h))
  -- uniformizers
  have hπ : ∀ P : F, ∃ π ∈ (P : Ideal A) ^ 1, π ∉ (P : Ideal A) ^ (1 + 1) := fun P =>
    Ideal.exists_mem_pow_notMem_pow_succ _ (hne P P.2) (hmax P P.2).ne_top 1
  choose π hπ1 hπ2 using hπ
  obtain ⟨x, hx⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := F) id (fun _ => 2)
    (fun P hP => hprime P hP) (fun P _ Q _ h => h) (fun P => algebraMap k A (aF P) + π P)
  set y : F → A := fun P => x - algebraMap k A (aF P)
  have hyP : ∀ P : F, y P ∈ (P : Ideal A) := by
    intro P
    have h1 := hx P P.2
    have h2 := hπ1 P
    rw [pow_one] at h2
    have : y P = (x - (algebraMap k A (aF P) + π P)) + π P := by simp only [y]; ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero h1) h2
  have hyP2 : ∀ P : F, y P ∉ (P : Ideal A) ^ 2 := by
    intro P h
    apply hπ2 P
    have h1 := hx P P.2
    have : π P = y P - (x - (algebraMap k A (aF P) + π P)) := by simp only [y]; ring
    rw [this]
    exact Ideal.sub_mem _ h h1
  -- every element of `A` is a polynomial in `x` modulo `𝔞`
  have hS : ∀ a : A, ∃ h : k[X], a - aeval x h ∈ 𝔞 := by
    intro a
    have hloc : ∀ P : F, ∃ h : k[X], a - aeval (y P) h ∈ (P : Ideal A) ^ e P := fun P =>
      haveI := hmax P P.2
      exists_aeval_sub_mem_pow L K (P : Ideal A) (hyP P) (hyP2 P) (e P) a
    choose hP hhP using hloc
    obtain ⟨h, hh⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (R := k[X]) (s := F)
      (fun P => if hP : P ∈ F then Ideal.span {X - C (aF ⟨P, hP⟩)} else ⊥) e
      (fun P hP => by
        rw [dif_pos hP]
        exact prime_span_X_sub_C _)
      (fun P hP Q hQ hPQ => by
        rw [dif_pos hP, dif_pos hQ]
        intro h
        exact hPQ (congrArg Subtype.val (haF (span_X_sub_C_injective h))))
      (fun P => (hP P).comp (X - C (aF P)))
    refine ⟨h, ?_⟩
    rw [hfact]
    apply (Ideal.span_singleton_le_iff_mem _).mp
    refine Finset.le_inf fun P hPF => (Ideal.span_singleton_le_iff_mem _).mpr ?_
    have h1 := hhP ⟨P, hPF⟩
    have h2 := hh P hPF
    rw [dif_pos hPF, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
    obtain ⟨g, hg⟩ := h2
    have h3 : aeval x h - aeval (y ⟨P, hPF⟩) (hP ⟨P, hPF⟩) = y ⟨P, hPF⟩ ^ e P * aeval x g := by
      have := congrArg (aeval x) hg
      rw [map_sub, aeval_comp, map_mul, map_pow, map_sub, aeval_X, aeval_C] at this
      exact this
    have : a - aeval x h = (a - aeval (y ⟨P, hPF⟩) (hP ⟨P, hPF⟩)) -
        (aeval x h - aeval (y ⟨P, hPF⟩) (hP ⟨P, hPF⟩)) := by ring
    rw [this, h3]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (hyP ⟨P, hPF⟩) (e P)))
  -- Nakayama
  set C' : Submodule k[X] A := Subalgebra.toSubmodule (Algebra.adjoin k[X] {x})
  have hle : (⊤ : Submodule k[X] (A ⧸ C')) ≤ q • ⊤ := by
    rintro m -
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' m
    obtain ⟨h, hh⟩ := hS a
    have hmem : a - aeval x h ∈ q • (⊤ : Submodule k[X] A) := by
      rw [Ideal.smul_top_eq_map]; exact hh
    have hC : aeval x h ∈ C' := by
      rw [← aeval_map_algebraMap k[X]]
      exact aeval_mem_adjoin_singleton k[X] x
    have : Submodule.Quotient.mk (p := C') a = C'.mkQ (a - aeval x h) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_sub,
        (Submodule.Quotient.mk_eq_zero C').mpr hC, sub_zero]
    have hmap : C'.mkQ (a - aeval x h) ∈ q • (⊤ : Submodule k[X] (A ⧸ C')) := by
      have := Submodule.mem_map_of_mem (f := C'.mkQ) hmem
      rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
    rw [this]
    exact hmap
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul q ⊤
    Module.Finite.fg_top hle
  refine ⟨x, r, fun hrq => hq.ne_top ?_, fun a => ?_⟩
  · rw [Ideal.eq_top_iff_one]
    have := q.sub_mem hrq hr1
    rwa [sub_sub_cancel] at this
  · have := hr (Submodule.Quotient.mk a) Submodule.mem_top
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at this
    exact this

end LocalMonogenic

/-! ### Dedekind's theorem -/

include hD in
/-- **`D(A) ⊆ A^∨`**, given local monogenic presentations at all maximal ideals of `k[t]`. -/
theorem D_mem_traceDual
    (hloc : ∀ q : Ideal k[X], q.IsMaximal → ∃ (x : A) (σ : k[X]), σ ∉ q ∧
      ∀ a : A, σ • a ∈ Algebra.adjoin k[X] {x}) (b : A) :
    D (algebraMap A K b) ∈ Submodule.traceDual k[X] L (1 : Submodule A K) := by
  rw [Submodule.mem_traceDual]
  intro z hz
  obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hz
  rw [Algebra.traceForm_apply, mul_comm]
  apply mem_range_of_forall_isMaximal
  intro q hq
  obtain ⟨x, σ, hσq, hσ⟩ := hloc q hq
  have hσ0 : σ ≠ 0 := fun h => hσq (h ▸ q.zero_mem)
  exact ⟨σ ^ 2, fun h => hσq (hq.isPrime.mem_of_pow_mem 2 h),
    trace_mul_D_mem D hD x σ hσ0 hσ a b⟩

include hD in
/-- **Dedekind's theorem** (duality for the finite map `Spec A → 𝔸¹`): if `A` is a Dedekind
domain with torsion free differentials and with local monogenic presentations over `k[t]`, then
`ω ↦ ω / dt` identifies `Ω¹_{A/k}` with the trace dual `A^∨` of `A`. -/
theorem range_kaehlerToField [IsIntegrallyClosed A] [Module.IsTorsionFree A Ω[A⁄k]]
    (hloc : ∀ q : Ideal k[X], q.IsMaximal → ∃ (x : A) (σ : k[X]), σ ∉ q ∧
      ∀ a : A, σ • a ∈ Algebra.adjoin k[X] {x}) :
    LinearMap.range (kaehlerToField (A := A) D) =
      Submodule.traceDual k[X] L (1 : Submodule A K) := by
  apply le_antisymm
  · rw [LinearMap.range_eq_map, ← KaehlerDifferential.span_range_derivation, Submodule.map_span,
      Submodule.span_le]
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    rw [kaehlerToField_D]
    exact D_mem_traceDual D hD hloc a
  · intro y hy
    apply mem_of_forall_isMaximal (k := k)
    intro q hq
    obtain ⟨x, σ, hσq, hσ⟩ := hloc q hq
    have hσ0 : σ ≠ 0 := fun h => hσq (h ▸ q.zero_mem)
    obtain ⟨j, hj⟩ := exists_pow_mem_span (L := L) D hD x σ hσ0 hσ
    exact ⟨σ ^ j, fun h => hσq (hq.isPrime.mem_of_pow_mem j h),
      pow_mul_mem_range D hD x σ hσ0 hσ hj hy⟩

include hD in
/-- **Dedekind's theorem** over an algebraically closed field: for `A` integrally closed, finite
over `k[t]` with separable fraction field `K ⊇ k(t)`, and with torsion free differentials (e.g.
`A` smooth over `k`), `ω ↦ ω / dt` identifies `Ω¹_{A/k}` with the trace dual `A^∨`. -/
theorem range_kaehlerToField_eq_traceDual [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] :
    LinearMap.range (kaehlerToField (A := A) D) =
      Submodule.traceDual k[X] L (1 : Submodule A K) :=
  range_kaehlerToField D hD fun q _ => exists_adjoin_of_isMaximal L K q

include hD in
/-- `Ω¹_{A/k} ≅ A^∨` as `A`-modules (Dedekind's theorem). -/
def kaehlerEquivTraceDual [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] :
    Ω[A⁄k] ≃ₗ[A] Submodule.traceDual k[X] L (1 : Submodule A K) :=
  (LinearEquiv.ofInjective _ (kaehlerToField_injective (L := L) D hD)).trans
    (LinearEquiv.ofEq _ _ (range_kaehlerToField_eq_traceDual D hD))

lemma kaehlerEquivTraceDual_apply [IsAlgClosed k] [IsIntegrallyClosed A]
    [Module.IsTorsionFree A Ω[A⁄k]] (ω : Ω[A⁄k]) :
    (kaehlerEquivTraceDual (L := L) D hD ω : K) = kaehlerToField D ω := rfl

end Setting

end

end DeJongAlterations.StableModification.CurvesField.Different

