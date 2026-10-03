/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Coherence.OkaGermBridge
import Hironaka.Analytic.HolomorphicGermNoetherian
import Hironaka.Analytic.HolomorphicGermRing
import Hironaka.Coherence.OkaGermRelations
import Hironaka.Coherence.OkaRelationSheaf
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Oka's theorem for a Weierstrass system: the induction step on the dimension

Source: Oka's coherence theorem (Grauert--Remmert, *Coherent analytic sheaves*, Ch. 2 §5;
Demailly, *Complex analytic and differential geometry*, II.3.19--3.20).

Let `g_j(z, t) = ∑_{l ≤ D} γ_{jl}(z) t^l` (`j : ι`) be polynomials in `t ∈ ℂ` with coefficients
holomorphic near `0 ∈ E`, `g_{j₀}` monic of degree `d ≤ D`.  If `E` has Oka's property, the
relation sheaf of `(g_j)` is finitely generated near `0 ∈ E × ℂ`
(`relationsFGAt_polySystem`).

## Proof

Put `N = 2D`.  A polynomial relation `∑_j P_j g_j = 0` with `P_j = ∑_{k ≤ N} α_{jk}(z) t^k` is
the same as a relation `∑_{(j,k)} α_{jk} F_{s,(j,k)} = 0`, `s ≤ N + D`, of the coefficient
system `F_{s,(j,k)} = γ_{j, s-k}` (`sum_mul_sum_eq_sum_coeffFn`, an identity in any commutative
ring, used both for numbers and for polynomials over germs).  Oka's property of `E` gives
finitely many generators `σ_m` of the coefficient relations near `0 ∈ E`; the polynomial
vectors `ŝ_m = (∑_k σ_{m,(j,k)} t^k)_j` are relations of `g` on `U × ℂ`.  At a point
`y = (z₀, t₀)` of `U × ℂ`, a relation `a` is, by Oka's key lemma at `(z₀, t₀)`
(`OkaGermRelations.exists_eq_sum_shiftEval_polynomialRelations`), a combination of polynomial
relations of degree `≤ N` with coefficients holomorphic near `z₀`; their coefficient vectors are
relations of `F` at `z₀`, hence combinations of the `σ_m`; so `a` is a combination of the `ŝ_m`.
-/

open Filter Topology Polynomial Set

namespace Hironaka.OkaPolynomialCase

open HolGerm OkaRelationSheaf OkaGermRelations OkaGermBridge

noncomputable section

/-! ### The coefficient identity -/

section Identity

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

/-- The coefficient of `t^s` contributed by the unknown `(j, k)`: `γ_{j, s-k}` if
`k ≤ s ≤ k + D`, else `0`. -/
def coeffFn {N : ℕ} (c : ι → ℕ → R) (D : ℕ) (s : ℕ) (jk : ι × Fin (N + 1)) : R :=
  if (jk.2 : ℕ) ≤ s ∧ s - jk.2 ≤ D then c jk.1 (s - jk.2) else 0

theorem sum_range_ite_shift (f : ℕ → R) (t : R) {k D M : ℕ} (hM : k + D + 1 ≤ M) :
    ∑ s ∈ Finset.range M, (if k ≤ s ∧ s - k ≤ D then f (s - k) * t ^ s else 0) =
      ∑ l ∈ Finset.range (D + 1), f l * t ^ (k + l) := by
  rw [← Finset.sum_filter]
  have hfilt : (Finset.range M).filter (fun s => k ≤ s ∧ s - k ≤ D) = Finset.Ico k (k + (D + 1)) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hfilt, Finset.sum_Ico_eq_sum_range]
  simp only [add_tsub_cancel_left]

/-- **The coefficient identity**: `∑_j (∑_{k ≤ N} a_{jk} t^k)(∑_{l ≤ D} c_{jl} t^l)` is
`∑_{s ≤ N + D} (∑_{(j,k)} a_{jk} F_{s,(j,k)}) t^s`. -/
theorem sum_mul_sum_eq_sum_coeffFn {N D : ℕ} (a : ι × Fin (N + 1) → R) (c : ι → ℕ → R) (t : R) :
    ∑ j, (∑ k : Fin (N + 1), a (j, k) * t ^ (k : ℕ)) *
        (∑ l ∈ Finset.range (D + 1), c j l * t ^ l) =
      ∑ s : Fin (N + D + 1), (∑ jk, a jk * coeffFn c D s jk) * t ^ (s : ℕ) := by
  have hinner : ∀ jk : ι × Fin (N + 1),
      ∑ s : Fin (N + D + 1), a jk * coeffFn c D s jk * t ^ (s : ℕ) =
        a jk * t ^ (jk.2 : ℕ) * ∑ l ∈ Finset.range (D + 1), c jk.1 l * t ^ l := by
    intro jk
    have h1 : ∀ s : ℕ, a jk * coeffFn c D s jk * t ^ s =
        a jk * (if (jk.2 : ℕ) ≤ s ∧ s - jk.2 ≤ D then c jk.1 (s - jk.2) * t ^ s else 0) := by
      intro s
      simp only [coeffFn]
      split_ifs <;> ring
    rw [Fin.sum_univ_eq_sum_range (fun s => a jk * coeffFn c D s jk * t ^ s), Finset.sum_congr rfl
      fun s _ => h1 s, ← Finset.mul_sum, sum_range_ite_shift _ t (by omega), Finset.mul_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  calc ∑ j, (∑ k : Fin (N + 1), a (j, k) * t ^ (k : ℕ)) *
        (∑ l ∈ Finset.range (D + 1), c j l * t ^ l)
      = ∑ jk : ι × Fin (N + 1), a jk * t ^ (jk.2 : ℕ) *
          ∑ l ∈ Finset.range (D + 1), c jk.1 l * t ^ l := by
        rw [Fintype.sum_prod_type]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
    _ = ∑ jk : ι × Fin (N + 1), ∑ s : Fin (N + D + 1), a jk * coeffFn c D s jk * t ^ (s : ℕ) :=
        Finset.sum_congr rfl fun jk _ => (hinner jk).symm
    _ = ∑ s : Fin (N + D + 1), (∑ jk, a jk * coeffFn c D s jk) * t ^ (s : ℕ) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun s _ => by rw [Finset.sum_mul]

end Identity

/-! ### Polynomials over germs -/

section Germs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem coeff_sum_C_mul_X_pow {R : Type*} [CommRing R] (b : ℕ → R) (M n : ℕ) :
    (∑ l ∈ Finset.range M, C (b l) * X ^ l).coeff n = if n < M then b n else 0 := by
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]

theorem eq_zero_of_sum_C_mul_X_pow_eq_zero {R : Type*} [CommRing R] {M : ℕ} (b : Fin M → R)
    (h : ∑ s : Fin M, C (b s) * X ^ (s : ℕ) = 0) (s : Fin M) : b s = 0 := by
  have h1 := congrArg (fun p : R[X] => p.coeff s) h
  simp only [finsetSum_coeff, coeff_C_mul_X_pow, coeff_zero] at h1
  rw [Finset.sum_eq_single s (fun s' _ hs' => if_neg fun h => hs' (Fin.ext h).symm)
    (fun hs => absurd (Finset.mem_univ s) hs), if_pos rfl] at h1
  exact h1

/-- `shiftEval` of a polynomial with `germAt` coefficients and arbitrary exponents. -/
theorem shiftEval_sum_C_germAt' {κ : Type*} (s : Finset κ) (e : κ → ℕ) {z₀ : E} (t₀ : ℂ)
    {α : κ → E → ℂ} (hα : ∀ k ∈ s, HolAt (α k) z₀) :
    shiftEval t₀ (∑ k ∈ s, C (germAt z₀ (α k)) * X ^ (e k)) =
      germAt ((z₀, t₀) : E × ℂ) (fun x => ∑ k ∈ s, α k x.1 * x.2 ^ (e k)) := by
  have hpow : ∀ k : κ, HolAt (fun x : E × ℂ => x.2 ^ (e k)) (z₀, t₀) := fun k =>
    (holAt_snd _).eventually.mono fun x hx => hx.differentiableAt.pow (e k)
  have hterm : ∀ k ∈ s, HolAt (fun x : E × ℂ => α k x.1 * x.2 ^ (e k)) (z₀, t₀) :=
    fun k hk => ((hα k hk).comp_fst t₀).mul (hpow k)
  rw [germAt_sum _ hterm, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := hα k hk
  rw [germAt_mul (hk'.comp_fst t₀) (hpow k), germAt_pow (holAt_snd _) (e k),
    ← ofFst_germAt hk' t₀, ← lastCoord_add_ofFst_constHom z₀ t₀]
  simp only [shiftEval, coe_eval₂RingHom, eval₂_mul, eval₂_C, eval₂_X_pow]

end Germs

/-! ### The polynomial system and its coefficient system -/

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type} [Fintype ι]
  [DecidableEq ι]

/-- The system `g_j(z, t) = ∑_{l ≤ D} γ_{jl}(z) t^l`. -/
def polySystem (γ : ι → ℕ → E → ℂ) (D : ℕ) (j : ι) (x : E × ℂ) : ℂ :=
  ∑ l ∈ Finset.range (D + 1), γ j l x.1 * x.2 ^ l

/-- The coefficient system on `E`: `F_{s,(j,k)} = γ_{j, s-k}` for `k ≤ s ≤ k + D`. -/
def coeffSystem (γ : ι → ℕ → E → ℂ) (D N : ℕ) (s : Fin (N + D + 1)) (jk : ι × Fin (N + 1))
    (z : E) : ℂ :=
  coeffFn (fun j l => γ j l z) D s jk

/-- The polynomial vector `(∑_{k ≤ N} α_{jk}(z) t^k)_j` of a coefficient vector. -/
def coeffPoly {N : ℕ} (α : ι × Fin (N + 1) → E → ℂ) (j : ι) (x : E × ℂ) : ℂ :=
  ∑ k : Fin (N + 1), α (j, k) x.1 * x.2 ^ (k : ℕ)

theorem holAt_coeffSystem {γ : ι → ℕ → E → ℂ} {D N : ℕ} {z : E}
    (hγ : ∀ j, ∀ l < D + 1, HolAt (γ j l) z) (s : Fin (N + D + 1)) (jk : ι × Fin (N + 1)) :
    HolAt (coeffSystem γ D N s jk) z := by
  by_cases h : (jk.2 : ℕ) ≤ s ∧ (s : ℕ) - jk.2 ≤ D
  · have : coeffSystem γ D N s jk = γ jk.1 (s - jk.2) := by
      funext w
      simp only [coeffSystem, coeffFn, if_pos h]
    rw [this]
    exact hγ _ _ (by omega)
  · have : coeffSystem γ D N s jk = fun _ => 0 := by
      funext w
      simp only [coeffSystem, coeffFn, if_neg h]
    rw [this]
    exact holAt_const 0 z

theorem germAt_coeffSystem {γ : ι → ℕ → E → ℂ} {D N : ℕ} (z : E) (s : Fin (N + D + 1))
    (jk : ι × Fin (N + 1)) :
    germAt z (coeffSystem γ D N s jk) = coeffFn (fun j l => germAt z (γ j l)) D s jk := by
  by_cases h : (jk.2 : ℕ) ≤ s ∧ (s : ℕ) - jk.2 ≤ D
  · have : coeffSystem γ D N s jk = γ jk.1 (s - jk.2) := by
      funext w
      simp only [coeffSystem, coeffFn, if_pos h]
    rw [this]
    simp only [coeffFn, if_pos h]
  · have : coeffSystem γ D N s jk = fun _ => 0 := by
      funext w
      simp only [coeffSystem, coeffFn, if_neg h]
    rw [this, germAt_zero]
    simp only [coeffFn, if_neg h]

/-- The pointwise coefficient identity for the system. -/
theorem sum_coeffPoly_mul_polySystem {γ : ι → ℕ → E → ℂ} {D N : ℕ} (α : ι × Fin (N + 1) → E → ℂ)
    (x : E × ℂ) :
    ∑ j, coeffPoly α j x * polySystem γ D j x =
      ∑ s : Fin (N + D + 1), (∑ jk, α jk x.1 * coeffSystem γ D N s jk x.1) * x.2 ^ (s : ℕ) :=
  sum_mul_sum_eq_sum_coeffFn (fun jk => α jk x.1) (fun j l => γ j l x.1) x.2

/-- **Oka's theorem for a Weierstrass system.**  If `E` has Oka's property and
`g_j(z, t) = ∑_{l ≤ D} γ_{jl}(z) t^l`, with `γ` holomorphic near `0` and `g_{j₀}` monic of
degree `d ≤ D`, the relations of `(g_j)` are finitely generated near `0 ∈ E × ℂ`. -/
theorem relationsFGAt_polySystem (hE : OkaProperty E) (γ : ι → ℕ → E → ℂ) {D d : ℕ}
    (hdD : d ≤ D) (j₀ : ι) (hγ : ∀ j l, HolAt (γ j l) 0) (hmon : ∀ z, γ j₀ d z = 1)
    (hdeg : ∀ l, d < l → ∀ z, γ j₀ l z = 0) :
    RelationsFGAt (fun (_ : Unit) => polySystem γ D) (0 : E × ℂ) := by
  set N := 2 * D with hN
  have hγev : ∀ᶠ z in 𝓝 (0 : E), ∀ j, ∀ l : Fin (D + 1), HolAt (γ j l) z :=
    eventually_all.2 fun j => eventually_all.2 fun l => (hγ j l).eventually
  obtain ⟨V, hVγ, hV, h0V⟩ := eventually_nhds_iff.1 hγev
  have hγV : ∀ z ∈ V, ∀ j, ∀ l < D + 1, HolAt (γ j l) z := fun z hz j l hl =>
    hVγ z hz j ⟨l, hl⟩
  obtain ⟨UE, hUE, h0UE, μ, _, σ, hσd, hσrel, hσgen⟩ :=
    hE _ _ (coeffSystem γ D N) 0 (holAt_coeffSystem (hγV 0 h0V))
  refine ⟨(UE ∩ V) ×ˢ univ, (hUE.inter hV).prod isOpen_univ, ⟨⟨h0UE, h0V⟩, mem_univ _⟩, μ,
    inferInstance, fun m => coeffPoly (σ m), ?_, ?_, ?_⟩
  · intro m j
    refine DifferentiableOn.fun_sum fun k _ => DifferentiableOn.mul ?_ ?_
    · exact (hσd m (j, k)).comp differentiableOn_fst fun x hx => hx.1.1
    · exact (differentiableOn_snd).pow _
  · intro m _ x hx
    rw [sum_coeffPoly_mul_polySystem]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [hσrel m s x.1 hx.1.1, zero_mul]
  · rintro ⟨z₀, t₀⟩ ⟨⟨hyUE, hyV⟩, -⟩ a ha
    have hγz := hγV z₀ hyV
    -- the polynomials over germs at `z₀`
    set γg : ι → ℕ → HolGerm E := fun j l => germAt z₀ (γ j l) with hγg
    set g : ι → (HolGerm E)[X] := fun j => ∑ l ∈ Finset.range (D + 1), C (γg j l) * X ^ l
      with hgdef
    have hg_eval : ∀ j, shiftEval t₀ (g j) = germAt ((z₀, t₀) : E × ℂ) (polySystem γ D j) :=
      fun j => shiftEval_sum_C_germAt t₀ (hγz j)
    have hgD : ∀ j, (g j).natDegree ≤ D := fun j =>
      natDegree_sum_le_of_forall_le _ _ fun l hl =>
        (natDegree_C_mul_X_pow_le _ _).trans (by have := Finset.mem_range.1 hl; omega)
    have hW : (g j₀).Monic := by
      have hcoeff : ∀ n, (g j₀).coeff n = if n < D + 1 then γg j₀ n else 0 := fun n =>
        coeff_sum_C_mul_X_pow _ _ n
      refine monic_of_natDegree_le_of_coeff_eq_one d ?_ ?_
      · refine natDegree_le_iff_coeff_eq_zero.2 fun n hn => ?_
        rw [hcoeff]
        split_ifs
        · have : γ j₀ n = fun _ => 0 := funext (hdeg n (by exact_mod_cast hn))
          simp only [hγg, this, germAt_zero]
        · rfl
      · rw [hcoeff, if_pos (by omega)]
        have : γ j₀ d = fun _ => 1 := funext hmon
        simp only [hγg, this, germAt_const, map_one]
    -- the relation `a` as germs
    have hGhol : ∀ j, HolAt (polySystem γ D j) ((z₀, t₀) : E × ℂ) := fun j =>
      HolAt.sum _ fun l hl => ((hγz j l (Finset.mem_range.1 hl)).comp_fst t₀).mul
        ((holAt_snd _).eventually.mono fun x hx => hx.differentiableAt.pow l)
    have hagG : ∀ j, HolAt (fun x => a j x * polySystem γ D j x) ((z₀, t₀) : E × ℂ) :=
      fun j => (ha.1 j).mul (hGhol j)
    have ha' : ∑ j, germAt ((z₀, t₀) : E × ℂ) (a j) * shiftEval t₀ (g j) = 0 := by
      simp only [hg_eval]
      rw [Finset.sum_congr rfl fun j _ => (germAt_mul (ha.1 j) (hGhol j)).symm,
        ← germAt_sum _ fun j _ => hagG j, germAt_eq_zero_iff (HolAt.fintype_sum hagG)]
      exact ha.2 ()
    obtain ⟨c', P, hPdeg, hPrel, hPeq⟩ :=
      exists_eq_sum_shiftEval_polynomialRelations t₀ hW g j₀ rfl hgD _ ha'
    -- choose representatives
    choose α hα hαg using fun (l : Option ι) (jk : ι × Fin (N + 1)) =>
      exists_germAt_eq ((P l jk.1).coeff jk.2) z₀
    choose c hc hcg using fun l => exists_germAt_eq (c' l) ((z₀, t₀) : E × ℂ)
    have hPsum : ∀ l j, P l j = ∑ k : Fin (N + 1), C (germAt z₀ (α l (j, k))) * X ^ (k : ℕ) := by
      intro l j
      simp only [hαg]
      rw [Fin.sum_univ_eq_sum_range (fun k => C ((P l j).coeff k) * X ^ k) (N + 1)]
      conv_lhs => rw [as_sum_range' (P l j) (N + 1) (by have := hPdeg l j; omega)]
      simp only [← C_mul_X_pow_eq_monomial]
    have hPeval : ∀ l j, shiftEval t₀ (P l j) = germAt ((z₀, t₀) : E × ℂ) (coeffPoly (α l) j) :=
      fun l j => by
        rw [hPsum l j]
        exact shiftEval_sum_C_germAt' Finset.univ (fun k : Fin (N + 1) => (k : ℕ)) t₀
          fun k _ => hα l (j, k)
    -- the coefficient vectors are relations of the coefficient system at `z₀`
    have hαrel : ∀ l, IsRelationAt (coeffSystem γ D N) z₀ (α l) := by
      intro l
      refine ⟨hα l, fun s => ?_⟩
      have hterm : ∀ jk, HolAt (fun z => α l jk z * coeffSystem γ D N s jk z) z₀ := fun jk =>
        (hα l jk).mul (holAt_coeffSystem hγz s jk)
      refine (germAt_eq_zero_iff (HolAt.fintype_sum hterm)).1 ?_
      rw [germAt_sum _ fun jk _ => hterm jk]
      simp only [fun jk => germAt_mul (hα l jk) (holAt_coeffSystem hγz s jk), germAt_coeffSystem]
      have hid := sum_mul_sum_eq_sum_coeffFn (N := N) (D := D)
        (fun jk => C (germAt z₀ (α l jk))) (fun j l => C (γg j l)) (X : (HolGerm E)[X])
      have hlhs : ∑ j, (∑ k : Fin (N + 1), C (germAt z₀ (α l (j, k))) * X ^ (k : ℕ)) *
          (∑ m ∈ Finset.range (D + 1), C (γg j m) * X ^ m) = 0 := by
        rw [← hPrel l]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hPsum l j]
      rw [hlhs] at hid
      have hC : ∀ s' : Fin (N + D + 1), ∑ jk, C (germAt z₀ (α l jk)) *
          coeffFn (fun j m => C (γg j m)) D s' jk =
            C (∑ jk, germAt z₀ (α l jk) * coeffFn γg D s' jk) := by
        intro s'
        rw [map_sum]
        refine Finset.sum_congr rfl fun jk _ => ?_
        rw [map_mul]
        congr 1
        simp only [coeffFn]
        split_ifs <;> simp
      simp only [hC] at hid
      exact eq_zero_of_sum_C_mul_X_pow_eq_zero _ hid.symm s
    choose b hb hbσ using fun l => hσgen z₀ hyUE (α l) (hαrel l)
    refine ⟨fun m x => ∑ l, c l x * b l m x.1, fun m => HolAt.fintype_sum fun l =>
      (hc l).mul ((hb l m).comp_fst t₀), fun j => ?_⟩
    -- `a_j = ∑_l c_l · coeffPoly (α l) j` near `(z₀, t₀)`
    have hQhol : ∀ l, HolAt (coeffPoly (α l) j) ((z₀, t₀) : E × ℂ) := fun l =>
      HolAt.fintype_sum fun k => ((hα l (j, k)).comp_fst t₀).mul
        ((holAt_snd _).eventually.mono fun x hx => hx.differentiableAt.pow _)
    have h1 : a j =ᶠ[𝓝 ((z₀, t₀) : E × ℂ)] fun x => ∑ l, c l x * coeffPoly (α l) j x := by
      have hsumhol : HolAt (fun x => ∑ l, c l x * coeffPoly (α l) j x) ((z₀, t₀) : E × ℂ) :=
        HolAt.fintype_sum fun l => (hc l).mul (hQhol l)
      rw [← germAt_eq_germAt_iff (ha.1 j) hsumhol, hPeq j,
        germAt_sum _ fun l _ => (hc l).mul (hQhol l)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [germAt_mul (hc l) (hQhol l), hcg l, hPeval l j]
    -- `α l = ∑_m b_{lm} σ_m` near `z₀`, pulled back along the projection
    have hfst : Tendsto Prod.fst (𝓝 ((z₀, t₀) : E × ℂ)) (𝓝 z₀) := continuous_fst.tendsto _
    have h2 : ∀ᶠ x in 𝓝 ((z₀, t₀) : E × ℂ), ∀ l, ∀ k : Fin (N + 1),
        α l (j, k) x.1 = ∑ m, b l m x.1 * σ m (j, k) x.1 :=
      eventually_all.2 fun l => eventually_all.2 fun k => hfst.eventually (hbσ l (j, k))
    filter_upwards [h1, h2] with x hx1 hx2
    rw [hx1]
    simp only [coeffPoly, hx2, Finset.sum_mul, Finset.mul_sum]
    rw [sum_comm₃]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun l _ => by ring

end Main

end

end Hironaka.OkaPolynomialCase
