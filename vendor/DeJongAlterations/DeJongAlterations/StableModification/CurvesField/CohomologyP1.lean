/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.RiemannRoch
import Mathlib.Algebra.Polynomial.Laurent

/-!
# Cohomology of `𝒪(n)` on the projective line

The projective line `ℙ¹_k` is covered by two affine lines `U = Spec k[t]` and `V = Spec k[s]`
glued along `U ∩ V = Spec k[t, t⁻¹]`, `s = t⁻¹`. The point `∞ = V(s) ⊆ V` is an effective Cartier
divisor of degree one and `𝒪(n) = 𝒪(n · ∞)` is the twist of `𝒪` by `sⁿ` along `(U, V)`
(`CohomologyTwist`, `RiemannRoch`). With the two-term Čech complex
`k[t] × k[s] → k[t, t⁻¹]`, `(a, b) ↦ b - t⁻ⁿ a`:

* `h⁰(𝒪(n)) = n + 1` and `h¹(𝒪(n)) = 0` for `n ≥ 0`;
* `h⁰(𝒪(n)) = 0` for `n < 0`, `h¹(𝒪(-1)) = 0` and `h¹(𝒪(n)) = -n - 1` for `n ≤ -1`.

In particular `h⁰(𝒪) = 1`, `h¹(𝒪) = 0` (arithmetic genus zero) and `h¹(𝒪(-2)) = 1`, the
cohomology group behind literature issue T10 of Temkin's Prop. 4.4.6 (M. Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), lines 3212–3214 of
`references/temkin10-stable-modification/source/semi-stable.tex`; `ERRATA.md`, T10).
Blueprint: `sm-curves-fields-cohomology.tex`, `lem:sm-p1-cohomology`.

The computation is done first for the algebraic model (`P1Model`: Laurent polynomials, with
`ρU = toLaurent` and `ρV = invert ∘ toLaurent`), then transported to any scheme with
`P1Charts`: two affine opens whose rings of sections are identified with `k[t]`, `k[s]` and
`k[t, t⁻¹]` compatibly with restriction (`P1Charts.finrank_H0`, `P1Charts.finrank_H1`).

## Main results

* `P1Model.finrank_H0`, `P1Model.finrank_H1`: the dimensions in the model.
* `P1Charts.finrank_H0`, `P1Charts.finrank_H1`: `dim Ȟ⁰((U, V), 𝒪(n))` and
  `dim Ȟ¹((U, V), 𝒪(n))` for a scheme with `ℙ¹`-charts.
* `P1Charts.finrank_cohomology_zero_twist`, `P1Charts.finrank_cohomology_one_twist`,
  `P1Charts.finrank_cohomology_zero`, `P1Charts.isZero_cohomology_one`: the same for the
  cover-free cohomology `cohomology F c p`.

The `ℙ¹`-charts of `ℙ¹_k = Proj k[X₀, X₁]` are constructed in `CohomologyP1Proj`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.StableModification.Cohomology
open Polynomial LaurentPolynomial

namespace DeJongAlterations.StableModification.CurvesField

noncomputable section

namespace P1Model

variable (k : Type u) [Field k]

/-- Restriction from `U = Spec k[t]` to `U ∩ V`: `p ↦ p(t)`. -/
abbrev ρ₀ : k[X] →ₗ[k] k[T;T⁻¹] := (toLaurentAlg (R := k)).toLinearMap

/-- Restriction from `V = Spec k[s]` to `U ∩ V`: `p ↦ p(t⁻¹)`. -/
abbrev ρInf : k[X] →ₗ[k] k[T;T⁻¹] :=
  (invert (R := k)).toLinearMap ∘ₗ (toLaurentAlg (R := k)).toLinearMap

/-- Multiplication by `T n`. -/
def tMul (n : ℤ) : k[T;T⁻¹] →ₗ[k] k[T;T⁻¹] := LinearMap.mulLeft k (T n)

/-- Multiplication by `s = T⁻¹`, a linear automorphism. -/
def sEquiv : k[T;T⁻¹] ≃ₗ[k] k[T;T⁻¹] where
  __ := tMul k (-1)
  invFun := tMul k 1
  left_inv p := by
    change T 1 * (T (-1) * p) = p
    rw [← mul_assoc, ← T_add, show (1 : ℤ) + -1 = 0 by norm_num, T_zero, one_mul]
  right_inv p := by
    change T (-1) * (T 1 * p) = p
    rw [← mul_assoc, ← T_add, show (-1 : ℤ) + 1 = 0 by norm_num, T_zero, one_mul]

/-- Multiplication by the coordinate `s` on `k[s]`. -/
def xMul : k[X] →ₗ[k] k[X] := LinearMap.mulLeft k X

/-- The twisting maps of `𝒪(n)`: multiplication by `sⁿ = T⁻ⁿ`. -/
abbrev γ (n : ℤ) : k[T;T⁻¹] →ₗ[k] k[T;T⁻¹] := tMul k (-n)

lemma ρInf_apply (p : k[X]) : ρInf k p = invert (toLaurent p) := rfl

lemma ρ₀_apply (p : k[X]) : ρ₀ k p = toLaurent p := rfl

lemma tMul_apply (n : ℤ) (q : k[T;T⁻¹]) : tMul k n q = T n * q := rfl

lemma sEquiv_apply (q : k[T;T⁻¹]) : sEquiv k q = T (-1) * q := rfl

lemma xMul_apply (p : k[X]) : xMul k p = X * p := rfl

lemma ρInf_xMul : ρInf k ∘ₗ xMul k = (sEquiv k).toLinearMap ∘ₗ ρInf k := by
  apply LinearMap.ext
  intro p
  have h1 : (ρInf k ∘ₗ xMul k) p = invert (toLaurent (X * p)) := rfl
  have h2 : ((sEquiv k).toLinearMap ∘ₗ ρInf k) p = T (-1) * invert (toLaurent p) := rfl
  rw [h1, h2, map_mul, map_mul, Polynomial.toLaurent_X, invert_T]

lemma γ_succ (n : ℤ) : γ k (n + 1) = (sEquiv k).toLinearMap ∘ₗ γ k n := by
  apply LinearMap.ext
  intro p
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, sEquiv_apply, tMul_apply, tMul_apply,
    ← mul_assoc, ← T_add]
  congr 2
  ring

lemma xMul_injective : Function.Injective (xMul k) := by
  intro p q h
  exact mul_left_cancel₀ X_ne_zero h

/-- `k[s] ⧸ (s) ≅ k`: the divisor `∞` has degree one. -/
lemma finrank_quot_xMul : Module.finrank k (k[X] ⧸ LinearMap.range (xMul k)) = 1 := by
  let e : k[X] →ₗ[k] k := Polynomial.lcoeff k 0
  have hsurj : Function.Surjective e := fun a => ⟨C a, by simp [e]⟩
  have hker : LinearMap.ker e = LinearMap.range (xMul k) := by
    ext p
    simp only [LinearMap.mem_ker, LinearMap.mem_range, e, Polynomial.lcoeff_apply]
    constructor
    · intro hp
      obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr hp
      exact ⟨q, hq.symm⟩
    · rintro ⟨q, rfl⟩
      exact Polynomial.X_dvd_iff.mp ⟨q, rfl⟩
  rw [← hker, (LinearMap.quotKerEquivOfSurjective e hsurj).finrank_eq, Module.finrank_self]

instance : FiniteDimensional k (k[X] ⧸ LinearMap.range (xMul k)) :=
  Module.finite_of_finrank_eq_succ (finrank_quot_xMul k)

lemma coeff_toLaurent_natCast (p : k[X]) (n : ℕ) : (toLaurent p).coeff (n : ℤ) = p.coeff n := by
  rw [coeff_toLaurent]
  have := Finsupp.mapDomain_apply (Nat.castEmbedding (R := ℤ)).injective p.toFinsupp.coeff n
  rw [show (n : ℤ) = Nat.castEmbedding n from rfl, this]
  rfl

lemma coeff_toLaurent_of_neg (p : k[X]) {i : ℤ} (hi : i < 0) : (toLaurent p).coeff i = 0 := by
  rw [coeff_toLaurent]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨m, rfl⟩
  exact absurd hi (by simp)

lemma coeff_T_mul (n i : ℤ) (q : k[T;T⁻¹]) : (T n * q).coeff i = q.coeff (i - n) := by
  rw [T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul]
  congr 1
  ring

lemma ρInf_C_mul_X_pow (a : k) (m : ℕ) :
    ρInf k (Polynomial.C a * X ^ m) = LaurentPolynomial.C a * T (-m) := by
  change invert (toLaurent (Polynomial.C a * X ^ m)) = _
  rw [Polynomial.toLaurent_C_mul_X_pow, map_mul, invert_C, invert_T]

/-- For `n ≥ -1` the twisted differential of `𝒪(n)` is surjective: `h¹(𝒪(n)) = 0`. -/
theorem twistDiff_surjective {n : ℤ} (hn : -1 ≤ n) :
    Function.Surjective (twistDiff (ρ₀ k) (ρInf k) (γ k n)) := by
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    exact ⟨x + y, map_add _ _ _⟩
  | C_mul_T j a =>
    rcases le_or_gt j 0 with hj | hj
    · refine ⟨(0, Polynomial.C a * X ^ (-j).toNat), ?_⟩
      rw [twistDiff_apply, map_zero, map_zero, sub_zero, ρInf_C_mul_X_pow, Int.toNat_of_nonneg
        (by omega), neg_neg]
    · refine ⟨(-(Polynomial.C a * X ^ (j + n).toNat), 0), ?_⟩
      rw [twistDiff_apply, map_zero, zero_sub, map_neg, map_neg, neg_neg]
      change T (-n) * toLaurent (Polynomial.C a * X ^ (j + n).toNat) = _
      rw [Polynomial.toLaurent_C_mul_X_pow, Int.toNat_of_nonneg (by omega), ← mul_assoc,
        T_mul, mul_assoc, ← T_add]
      congr 2
      ring

/-- For `n ≤ -1`, `𝒪(n)` has no nonzero global sections. -/
theorem H0_eq_bot {n : ℤ} (hn : n ≤ -1) : H0 (ρ₀ k) (ρInf k) (γ k n) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ hab
  rw [LinearMap.mem_ker, twistDiff_apply, sub_eq_zero] at hab
  change invert (toLaurent b) = T (-n) * toLaurent a at hab
  rw [Submodule.mem_bot, Prod.mk_eq_zero]
  constructor
  · ext m
    have := congrArg (fun q => q.coeff ((m : ℤ) - n)) hab
    simp only [invert_apply, coeff_T_mul] at this
    rw [coeff_toLaurent_of_neg k b (by omega), show (m : ℤ) - n - -n = m by ring,
      coeff_toLaurent_natCast] at this
    simpa using this.symm
  · ext m
    have := congrArg (fun q => q.coeff (-(m : ℤ))) hab
    simp only [invert_apply, coeff_T_mul, neg_neg] at this
    rw [coeff_toLaurent_natCast, coeff_toLaurent_of_neg k a (by omega)] at this
    simpa using this

/-- `H⁰(𝒪) = k`: the constants. -/
def H0zeroEquiv : H0 (ρ₀ k) (ρInf k) (γ k 0) ≃ₗ[k] k where
  toFun p := (p : k[X] × k[X]).1.coeff 0
  invFun c := ⟨(Polynomial.C c, Polynomial.C c), by
    rw [LinearMap.mem_ker, twistDiff_apply, sub_eq_zero]
    change invert (toLaurent (Polynomial.C c)) = T (-0) * toLaurent (Polynomial.C c)
    simp [Polynomial.toLaurent_C]⟩
  left_inv p := by
    obtain ⟨⟨a, b⟩, hab⟩ := p
    have hab' := hab
    rw [LinearMap.mem_ker, twistDiff_apply, sub_eq_zero] at hab'
    change invert (toLaurent b) = T (-0) * toLaurent a at hab'
    rw [neg_zero, T_zero, one_mul] at hab'
    have ha : ∀ m : ℕ, m ≠ 0 → a.coeff m = 0 := by
      intro m hm
      have := congrArg (fun q => q.coeff (m : ℤ)) hab'
      simp only [invert_apply] at this
      rw [coeff_toLaurent_natCast, coeff_toLaurent_of_neg k b (by omega)] at this
      exact this.symm
    have hb : ∀ m : ℕ, m ≠ 0 → b.coeff m = 0 := by
      intro m hm
      have := congrArg (fun q => q.coeff (-(m : ℤ))) hab'
      simp only [invert_apply, neg_neg] at this
      rw [coeff_toLaurent_natCast, coeff_toLaurent_of_neg k a (by omega)] at this
      exact this
    have h0 : b.coeff 0 = a.coeff 0 := by
      have := congrArg (fun q => q.coeff 0) hab'
      simp only [invert_apply, neg_zero] at this
      have e := coeff_toLaurent_natCast k b 0
      have e' := coeff_toLaurent_natCast k a 0
      simp only [Nat.cast_zero] at e e'
      rw [e, e'] at this
      exact this
    apply Subtype.ext
    apply Prod.ext
    · ext m
      rcases eq_or_ne m 0 with rfl | hm
      · simp
      · simp [Polynomial.coeff_C, hm, ha m hm]
    · ext m
      rcases eq_or_ne m 0 with rfl | hm
      · simp [h0]
      · simp [Polynomial.coeff_C, hm, hb m hm]
  right_inv c := by simp
  map_add' p q := by simp
  map_smul' r p := by simp

lemma finrank_H0_zero : Module.finrank k (H0 (ρ₀ k) (ρInf k) (γ k 0)) = 1 := by
  rw [(H0zeroEquiv k).finrank_eq, Module.finrank_self]

instance : FiniteDimensional k (H0 (ρ₀ k) (ρInf k) (γ k 0)) :=
  Module.finite_of_finrank_eq_succ (finrank_H0_zero k)

instance subsingleton_H1 {n : ℤ} [Fact (-1 ≤ n)] : Subsingleton (H1 (ρ₀ k) (ρInf k) (γ k n)) := by
  rw [Submodule.Quotient.subsingleton_iff, LinearMap.range_eq_top]
  exact twistDiff_surjective k (Fact.out)

instance : FiniteDimensional k (H1 (ρ₀ k) (ρInf k) (γ k 0)) := by
  have : Fact ((-1 : ℤ) ≤ 0) := ⟨by norm_num⟩
  infer_instance

/-- `χ(𝒪(n)) = n + 1` on the model of `ℙ¹`. -/
theorem euler_eq (n : ℤ) : euler (ρ₀ k) (ρInf k) (γ k n) = n + 1 := by
  have := euler_family (ρ₀ k) (ρInf k) (sEquiv k) (xMul k) (ρInf_xMul k) (xMul_injective k) (γ k)
    (γ_succ k) n
  rw [this, finrank_quot_xMul]
  unfold euler
  have : Fact ((-1 : ℤ) ≤ 0) := ⟨by norm_num⟩
  rw [finrank_H0_zero, Module.finrank_zero_of_subsingleton]
  push_cast
  ring

lemma finiteDimensional (n : ℤ) :
    FiniteDimensional k (H0 (ρ₀ k) (ρInf k) (γ k n)) ∧
      FiniteDimensional k (H1 (ρ₀ k) (ρInf k) (γ k n)) :=
  finiteDimensional_family (ρ₀ k) (ρInf k) (sEquiv k) (xMul k) (ρInf_xMul k) (xMul_injective k)
    (γ k) (γ_succ k) n

/-- **`h⁰(𝒪(n))` on the model of `ℙ¹`**: `n + 1` for `n ≥ 0` and `0` for `n < 0`. -/
theorem finrank_H0 (n : ℤ) :
    (Module.finrank k (H0 (ρ₀ k) (ρInf k) (γ k n)) : ℤ) = max (n + 1) 0 := by
  obtain ⟨h0, h1⟩ := finiteDimensional k n
  rcases le_or_gt n (-1) with hn | hn
  · rw [H0_eq_bot k hn, finrank_bot]
    push_cast
    omega
  · have : Fact (-1 ≤ n) := ⟨by omega⟩
    have := euler_eq k n
    unfold euler at this
    rw [Module.finrank_zero_of_subsingleton (M := H1 (ρ₀ k) (ρInf k) (γ k n))] at this
    push_cast at this
    omega

/-- **`h¹(𝒪(n))` on the model of `ℙ¹`**: `0` for `n ≥ -1` and `-n - 1` for `n ≤ -1`. -/
theorem finrank_H1 (n : ℤ) :
    (Module.finrank k (H1 (ρ₀ k) (ρInf k) (γ k n)) : ℤ) = max (-n - 1) 0 := by
  obtain ⟨h0, h1⟩ := finiteDimensional k n
  rcases le_or_gt n (-1) with hn | hn
  · have := euler_eq k n
    unfold euler at this
    rw [H0_eq_bot k hn, finrank_bot] at this
    push_cast at this
    omega
  · have : Fact (-1 ≤ n) := ⟨by omega⟩
    rw [Module.finrank_zero_of_subsingleton]
    push_cast
    omega

end P1Model

/-! ### Schemes with `ℙ¹`-charts -/

/-- The structure sheaf `𝒪_Y` as a module. -/
abbrev structureModule (Y : Scheme.{u}) : Y.Modules := SheafOfModules.unit Y.ringCatSheaf

set_option synthInstance.maxHeartbeats 400000 in
instance (Y : Scheme.{u}) : (structureModule Y).IsQuasicoherent := by
  have h : (SheafOfModules.free (R := Y.ringCatSheaf) PUnit.{u + 1}).IsQuasicoherent :=
    inferInstance
  obtain ⟨⟨q⟩⟩ := h
  let e : SheafOfModules.free (R := Y.ringCatSheaf) PUnit.{u + 1} ≅ structureModule Y :=
    Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit Y.ringCatSheaf)
  exact (SheafOfModules.QuasicoherentData.ofIsIso.{u, u, u, u} e.hom q).isQuasicoherent

/-- **`ℙ¹`-charts** on a scheme `Y` over a field `k` (through `c : k →+* Γ(Y, ⊤)`): two affine
opens `U`, `V` covering `Y`, with affine intersection, and identifications
`Γ(U, 𝒪) ≅ k[t]`, `Γ(V, 𝒪) ≅ k[s]`, `Γ(U ∩ V, 𝒪) ≅ k[t, t⁻¹]` compatible with restriction
(`s ↦ t⁻¹`), such that the coordinate `s` at `∞ = V(s)` acts as `t⁻¹` on `U ∩ V`. -/
structure P1Charts (Y : Scheme.{u}) (k : Type u) [Field k] (c : k →+* Γ(Y, ⊤)) where
  /-- The chart `Spec k[t]`. -/
  U : Y.Opens
  /-- The chart `Spec k[s]` at infinity. -/
  V : Y.Opens
  sup_eq : U ⊔ V = ⊤
  isAffineOpen_U : IsAffineOpen U
  isAffineOpen_V : IsAffineOpen V
  isAffineOpen_inf : IsAffineOpen (U ⊓ V)
  /-- The coordinate `s` on `V`. -/
  s : Γ(Y, V)
  isUnit_s : IsUnit (Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op s)
  /-- `Γ(U, 𝒪) ≅ k[t]`. -/
  eU : k[X] ≃ₗ[k] sectionsModuleCat (structureModule Y) c U le_top
  /-- `Γ(V, 𝒪) ≅ k[s]`. -/
  eV : k[X] ≃ₗ[k] sectionsModuleCat (structureModule Y) c V le_top
  /-- `Γ(U ∩ V, 𝒪) ≅ k[t, t⁻¹]`. -/
  eUV : k[T;T⁻¹] ≃ₗ[k] sectionsModuleCat (structureModule Y) c (U ⊓ V) le_top
  hU : ∀ p, eUV (toLaurent p) = resUV (structureModule Y) U V c (eU p)
  hV : ∀ p, eUV (invert (toLaurent p)) = resVU (structureModule Y) U V c (eV p)
  hS : ∀ q, eUV (T (-1) * q) = fEquiv (structureModule Y) U V c isUnit_s (eUV q)

namespace P1Charts

variable {Y : Scheme.{u}} {k : Type u} [Field k] {c : k →+* Γ(Y, ⊤)} (P : P1Charts Y k c)

/-- `𝒪(n) = 𝒪(n · ∞)` on a scheme with `ℙ¹`-charts. -/
abbrev twistingSheaf (n : ℤ) : Y.Modules :=
  divisorTwist (structureModule Y) P.U P.V P.isUnit_s n

lemma hS_inv (q : k[T;T⁻¹]) :
    P.eUV (T 1 * q) = (fEquiv (structureModule Y) P.U P.V c P.isUnit_s).symm (P.eUV q) := by
  rw [LinearEquiv.eq_symm_apply, ← P.hS, ← mul_assoc, ← T_add,
    show (-1 : ℤ) + 1 = 0 by norm_num, T_zero, one_mul]

lemma eUV_twist (n : ℤ) (q : k[T;T⁻¹]) :
    P.eUV (P1Model.γ k n q) = twistFamily (structureModule Y) P.U P.V c P.isUnit_s n (P.eUV q) := by
  induction n using Int.induction_on generalizing q with
  | zero =>
    rw [twistFamily_zero, smulLin_one]
    change P.eUV (T (-0) * q) = P.eUV q
    rw [neg_zero, T_zero, one_mul]
  | succ n ih =>
    rw [P1Model.γ_succ, twistFamily_succ, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, ← ih, P1Model.sEquiv_apply, P.hS]
  | pred n ih =>
    have e₁ := P1Model.γ_succ k (-(n : ℤ) - 1)
    have e₂ := twistFamily_succ (structureModule Y) P.U P.V c P.isUnit_s (-(n : ℤ) - 1)
    rw [sub_add_cancel] at e₁ e₂
    have h₁ : P1Model.γ k (-(n : ℤ) - 1) q = T 1 * P1Model.γ k (-(n : ℤ)) q := by
      rw [e₁, LinearMap.comp_apply, LinearEquiv.coe_coe, P1Model.sEquiv_apply, ← mul_assoc,
        ← T_add, show (1 : ℤ) + -1 = 0 by norm_num, T_zero, one_mul]
    have h₂ : twistFamily (structureModule Y) P.U P.V c P.isUnit_s (-(n : ℤ) - 1) (P.eUV q) =
        (fEquiv (structureModule Y) P.U P.V c P.isUnit_s).symm
          (twistFamily (structureModule Y) P.U P.V c P.isUnit_s (-(n : ℤ)) (P.eUV q)) := by
      rw [LinearEquiv.eq_symm_apply, e₂, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h₁, h₂, P.hS_inv, ih]

/-- `Ȟ⁰((U, V), 𝒪(n))` is the model `H⁰`. -/
def H0Equiv (n : ℤ) :
    H0 (P1Model.ρ₀ k) (P1Model.ρInf k) (P1Model.γ k n) ≃ₗ[k]
      cechCohomology (P.twistingSheaf n) (pairCover P.U P.V) c 0 :=
  (H0Congr P.eU P.eV P.eUV P.hU P.hV (P.eUV_twist n)).trans
    (cechDivisorTwistZeroEquiv (structureModule Y) P.U P.V c P.isUnit_s n).symm

/-- `Ȟ¹((U, V), 𝒪(n))` is the model `H¹`. -/
def H1Equiv (n : ℤ) :
    H1 (P1Model.ρ₀ k) (P1Model.ρInf k) (P1Model.γ k n) ≃ₗ[k]
      cechCohomology (P.twistingSheaf n) (pairCover P.U P.V) c 1 :=
  (H1Congr P.eU P.eV P.eUV P.hU P.hV (P.eUV_twist n)).trans
    (cechDivisorTwistOneEquiv (structureModule Y) P.U P.V c P.isUnit_s n).symm

/-- **`H⁰` of `𝒪(n)` on `ℙ¹`** (blueprint `lem:sm-p1-cohomology`): `h⁰(𝒪(n)) = max(n + 1, 0)`. -/
theorem finrank_H0 (n : ℤ) :
    (Module.finrank k (cechCohomology (P.twistingSheaf n) (pairCover P.U P.V) c 0) : ℤ) =
      max (n + 1) 0 := by
  rw [← (P.H0Equiv n).finrank_eq, P1Model.finrank_H0]

/-- **`H¹` of `𝒪(n)` on `ℙ¹`** (blueprint `lem:sm-p1-cohomology`): `h¹(𝒪(n)) = max(-n - 1, 0)`.
In particular `h¹(𝒪(n)) = 0` for `n ≥ -1` and `h¹(𝒪(-2)) = 1`. -/
theorem finrank_H1 (n : ℤ) :
    (Module.finrank k (cechCohomology (P.twistingSheaf n) (pairCover P.U P.V) c 1) : ℤ) =
      max (-n - 1) 0 := by
  rw [← (P.H1Equiv n).finrank_eq, P1Model.finrank_H1]

lemma finiteDimensional_H0 (n : ℤ) :
    FiniteDimensional k (cechCohomology (P.twistingSheaf n) (pairCover P.U P.V) c 0) :=
  have := (P1Model.finiteDimensional k n).1
  Module.Finite.equiv (P.H0Equiv n)

lemma finiteDimensional_H1 (n : ℤ) :
    FiniteDimensional k (cechCohomology (P.twistingSheaf n) (pairCover P.U P.V) c 1) :=
  have := (P1Model.finiteDimensional k n).2
  Module.Finite.equiv (P.H1Equiv n)

/-- `𝒪(0)` is `𝒪`: the Čech cohomology of `𝒪` itself. -/
def H0EquivStructure :
    H0 (P1Model.ρ₀ k) (P1Model.ρInf k) (P1Model.γ k 0) ≃ₗ[k]
      cechCohomology (structureModule Y) (pairCover P.U P.V) c 0 :=
  (H0Congr P.eU P.eV P.eUV P.hU P.hV (P.eUV_twist 0)).trans
    (cechZeroEquivTwistZero (structureModule Y) P.U P.V c P.isUnit_s).symm

/-- `Ȟ¹((U, V), 𝒪)` in the model. -/
def H1EquivStructure :
    H1 (P1Model.ρ₀ k) (P1Model.ρInf k) (P1Model.γ k 0) ≃ₗ[k]
      cechCohomology (structureModule Y) (pairCover P.U P.V) c 1 :=
  (H1Congr P.eU P.eV P.eUV P.hU P.hV (P.eUV_twist 0)).trans
    (cechOneEquivTwistZero (structureModule Y) P.U P.V c P.isUnit_s).symm

variable [CompactSpace Y] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))]

/-- **`h⁰(ℙ¹, 𝒪) = 1`** (cover-free cohomology). -/
theorem finrank_cohomology_zero (P : P1Charts Y k c) :
    Module.finrank k (cohomology (structureModule Y) c 0) = 1 := by
  have e := (cohomologyPairZeroEquiv (structureModule Y) c P.sup_eq P.isAffineOpen_U
    P.isAffineOpen_V P.isAffineOpen_inf).trans
      (cechPairZeroEquiv P.U P.V (structureModule Y) c).symm
  rw [e.finrank_eq, ← P.H0EquivStructure.finrank_eq, P1Model.finrank_H0_zero]

/-- **`h¹(ℙ¹, 𝒪) = 0`**: the arithmetic genus of `ℙ¹` is zero (cover-free cohomology). -/
theorem isZero_cohomology_one (P : P1Charts Y k c) :
    Limits.IsZero (cohomology (structureModule Y) c 1) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  have : Fact ((-1 : ℤ) ≤ 0) := ⟨by norm_num⟩
  have e := (cohomologyPairOneEquiv (structureModule Y) c P.sup_eq P.isAffineOpen_U
    P.isAffineOpen_V P.isAffineOpen_inf).trans (cechPairOneEquiv P.U P.V (structureModule Y) c).symm
  exact (e.trans P.H1EquivStructure.symm).injective.subsingleton

/-- **`h⁰(ℙ¹, 𝒪(n)) = max(n + 1, 0)`** (cover-free cohomology; blueprint
`lem:sm-p1-cohomology`). -/
theorem finrank_cohomology_zero_twist (P : P1Charts Y k c) (n : ℤ) :
    (Module.finrank k (cohomology (P.twistingSheaf n) c 0) : ℤ) = max (n + 1) 0 := by
  rw [(cohomologyDivisorTwistZeroEquiv (structureModule Y) P.U P.V c P.isUnit_s P.sup_eq
    P.isAffineOpen_U P.isAffineOpen_V P.isAffineOpen_inf n).finrank_eq,
    ← (H0Congr (ρU := P1Model.ρ₀ k) (ρV := P1Model.ρInf k) P.eU P.eV P.eUV P.hU P.hV
      (P.eUV_twist n)).finrank_eq, P1Model.finrank_H0]

/-- **`h¹(ℙ¹, 𝒪(n)) = max(-n - 1, 0)`** (cover-free cohomology; blueprint
`lem:sm-p1-cohomology`). -/
theorem finrank_cohomology_one_twist (P : P1Charts Y k c) (n : ℤ) :
    (Module.finrank k (cohomology (P.twistingSheaf n) c 1) : ℤ) = max (-n - 1) 0 := by
  rw [(cohomologyDivisorTwistOneEquiv (structureModule Y) P.U P.V c P.isUnit_s P.sup_eq
    P.isAffineOpen_U P.isAffineOpen_V P.isAffineOpen_inf n).finrank_eq,
    ← (H1Congr (ρU := P1Model.ρ₀ k) (ρV := P1Model.ρInf k) P.eU P.eV P.eUV P.hU P.hV
      (P.eUV_twist n)).finrank_eq, P1Model.finrank_H1]

/-- The cohomology of `𝒪(n)` on `ℙ¹` is finite-dimensional. -/
theorem finiteDimensional_cohomology_twist (P : P1Charts Y k c) (n : ℤ) :
    FiniteDimensional k (cohomology (P.twistingSheaf n) c 0) ∧
      FiniteDimensional k (cohomology (P.twistingSheaf n) c 1) := by
  obtain ⟨h0, h1⟩ := P1Model.finiteDimensional k n
  exact ⟨Module.Finite.equiv ((H0Congr (ρU := P1Model.ρ₀ k) (ρV := P1Model.ρInf k)
      P.eU P.eV P.eUV P.hU P.hV (P.eUV_twist n)).trans
      (cohomologyDivisorTwistZeroEquiv (structureModule Y) P.U P.V c P.isUnit_s P.sup_eq
        P.isAffineOpen_U P.isAffineOpen_V P.isAffineOpen_inf n).symm),
    Module.Finite.equiv ((H1Congr (ρU := P1Model.ρ₀ k) (ρV := P1Model.ρInf k)
      P.eU P.eV P.eUV P.hU P.hV (P.eUV_twist n)).trans
      (cohomologyDivisorTwistOneEquiv (structureModule Y) P.U P.V c P.isUnit_s P.sup_eq
        P.isAffineOpen_U P.isAffineOpen_V P.isAffineOpen_inf n).symm)⟩

end P1Charts

end

end DeJongAlterations.StableModification.CurvesField
