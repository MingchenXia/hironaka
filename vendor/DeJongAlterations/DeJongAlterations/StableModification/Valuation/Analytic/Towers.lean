/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Relrank
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Sylow

/-!
# Towers of degree-`p` extensions

This file proves the field-theoretic towers used in place of Temkin's towers of
`p`-extensions over the maximal moderately ramified extension `K^mr` (M. Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010), proof of Theorem 6.3.1,
`semi-stable.tex` lines 4057–4064 and 4091–4093; plan simplification S5(f) of `PLAN-SM-VAL.md`):

* every intermediate field of a finite Galois extension whose Galois group is a `p`-group is
  reached from the base by a chain of Galois extensions of degree `p`;
* every intermediate field of a finite purely inseparable extension in characteristic `p` is
  reached by a chain of steps `E ⊆ E(γ)` with `γ ^ p ∈ E`, each of degree `p`.

Both are stated as induction principles on intermediate fields.

## Main results

* `IsPGroup.exists_normal_le_relIndex_eq`: in a finite `p`-group, a proper subgroup `H` is a
  normal subgroup of index `p` of a larger subgroup.
* `isGalois_extendScalars_of_normal`: if `Gal(N/L)` is normal in `Gal(N/E)` then `L/E` is
  Galois.
* `IsPGroup.induction_intermediateField`: the induction principle for `p`-group Galois
  extensions.
* `finrank_adjoin_of_pow_char_mem`: `[E(γ) : E] = p` if `γ ∉ E` and `γ ^ p ∈ E`.
* `induction_intermediateField_of_isPurelyInseparable`: the induction principle for purely
  inseparable extensions.

## References

Blueprint chapter `sm-val-ramification.tex`: `lem:sm-an-p-towers`, `lem:sm-an-insep-towers`.
-/

open IntermediateField Polynomial

namespace DeJongAlterations.StableModification.Valuation.Analytic

/-! ### Groups -/

/-- In a finite `p`-group every proper subgroup `H` is a normal subgroup of index `p` of a larger
subgroup `H'`. -/
theorem IsPGroup.exists_normal_le_relIndex_eq {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (hG : IsPGroup p G) {H : Subgroup G} (hH : H ≠ ⊤) :
    ∃ H' : Subgroup G, H ≤ H' ∧ H.relIndex H' = p ∧ (H.subgroupOf H').Normal := by
  obtain ⟨N, hN⟩ := IsPGroup.iff_card.mp hG
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hG.to_subgroup H)
  have hlt : n < N := by
    by_contra hle
    rw [not_lt] at hle
    apply hH
    refine Subgroup.eq_top_of_card_eq H (le_antisymm (Subgroup.card_le_card_group H) ?_)
    rw [hN, hn]
    exact Nat.pow_le_pow_right hp.out.pos hle
  have hdvd : p ^ (n + 1) ∣ Nat.card G := by
    rw [hN]
    exact Nat.pow_dvd_pow p hlt
  obtain ⟨H', hH'card, hle⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hn
  have hrel : H.relIndex H' = p := by
    have h1 := Subgroup.relIndex_mul_index (H := H) (K := H') hle
    have h2 := H.card_mul_index
    have h3 := H'.card_mul_index
    have hpos : 0 < H'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have : H.relIndex H' * H'.index * Nat.card H = p * H'.index * Nat.card H := by
      rw [h1, mul_comm, h2, ← h3, hH'card, hn, pow_succ]
      ring
    have hcH : 0 < Nat.card H := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (Nat.eq_of_mul_eq_mul_right hcH this)
  refine ⟨H', hle, hrel, Subgroup.normal_of_index_eq_minFac_card ?_⟩
  rw [← Subgroup.relIndex, hrel, hH'card, Nat.Prime.pow_minFac hp.out (Nat.succ_ne_zero n)]

/-! ### Galois towers -/

section Galois

variable {M N : Type*} [Field M] [Field N] [Algebra M N]

/-- If `E ≤ L` are intermediate fields of a Galois extension `N/M` and `Gal(N/L)` is normal in
`Gal(N/E)`, then `L/E` is Galois. -/
theorem isGalois_extendScalars_of_normal [IsGalois M N] {E L : IntermediateField M N}
    (h : E ≤ L) (hn : (L.fixingSubgroup.subgroupOf E.fixingSubgroup).Normal) :
    IsGalois E (extendScalars h) := by
  rw [← InfiniteGalois.normal_iff_isGalois]
  refine ⟨fun τ' hτ' σ' => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hτ' ⊢
  intro x hx
  set σ : N ≃ₐ[M] N := σ'.restrictScalars M
  set τ : N ≃ₐ[M] N := τ'.restrictScalars M
  have hσ : σ ∈ E.fixingSubgroup :=
    (mem_fixingSubgroup_iff _ _).mpr fun e he => σ'.commutes ⟨e, he⟩
  have hτ : τ ∈ L.fixingSubgroup := (mem_fixingSubgroup_iff _ _).mpr fun y hy => hτ' y hy
  have hτE : τ ∈ E.fixingSubgroup := fixingSubgroup_le h hτ
  have hconj := hn.conj_mem ⟨τ, hτE⟩ (by rw [Subgroup.mem_subgroupOf]; exact hτ) ⟨σ, hσ⟩
  rw [Subgroup.mem_subgroupOf] at hconj
  have h2 := (mem_fixingSubgroup_iff _ _).mp hconj x hx
  simpa [σ, τ, AlgEquiv.aut_inv] using h2

variable [FiniteDimensional M N] [IsGalois M N]

/-- **Towers of Galois extensions of degree `p`** (plan S5(f)). If `Gal(N/M)` is a `p`-group and
a property of intermediate fields holds for `M` and passes from `E` to `F ⊇ E` whenever `F/E` is
Galois of degree `p`, then it holds for every intermediate field. -/
theorem IsPGroup.induction_intermediateField {p : ℕ} [Fact p.Prime]
    (hG : IsPGroup p (N ≃ₐ[M] N)) {P : IntermediateField M N → Prop} (hbot : P ⊥)
    (hstep : ∀ (E F : IntermediateField M N) (h : E ≤ F), IsGalois E (extendScalars h) →
      Module.finrank E (extendScalars h) = p → P E → P F)
    (L : IntermediateField M N) : P L := by
  induction hL : Module.finrank M L using Nat.strong_induction_on generalizing L with
  | _ n ih =>
    by_cases hbotL : L = ⊥
    · rw [hbotL]; exact hbot
    have hH : L.fixingSubgroup ≠ ⊤ := by
      intro htop
      apply hbotL
      rw [← IsGalois.fixedField_fixingSubgroup L, htop, IsGalois.fixedField_top]
    obtain ⟨H', hle, hrel, hnorm⟩ := IsPGroup.exists_normal_le_relIndex_eq hG hH
    set E := fixedField H' with hE_def
    have hEfix : E.fixingSubgroup = H' := fixingSubgroup_fixedField H'
    have hEL : E ≤ L := by
      rw [← IsGalois.fixedField_fixingSubgroup L]
      exact fixedField_le hle
    have hidxL : Module.finrank M L = L.fixingSubgroup.index := by
      rw [finrank_eq_fixingSubgroup_index]
    have hidxE : Module.finrank M E = H'.index := by
      rw [finrank_eq_fixingSubgroup_index, hEfix]
    have hmul : L.fixingSubgroup.index = p * H'.index := by
      rw [← hrel, Subgroup.relIndex_mul_index hle]
    have hpos : 0 < H'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have hlt : Module.finrank M E < n := by
      rw [← hL, hidxL, hmul, hidxE]
      have := (Fact.out : p.Prime).one_lt
      nlinarith
    have hPE := ih _ hlt E rfl
    have hdeg : Module.finrank E (extendScalars hEL) = p := by
      rw [← relfinrank_eq_finrank_of_le hEL]
      have := finrank_bot_mul_relfinrank hEL
      rw [hidxE, hidxL, hmul, mul_comm p] at this
      exact Nat.eq_of_mul_eq_mul_left hpos this
    refine hstep E L hEL (isGalois_extendScalars_of_normal hEL ?_) hdeg hPE
    rw [hEfix]
    exact hnorm


omit [IsGalois M N] in
/-- **Linear disjointness of a Galois extension** (plan node G3): if `Z/M` is Galois, then
`[L Z : M] · [L ∩ Z : M] = [L : M] · [Z : M]` for every intermediate field `L`. -/
theorem finrank_sup_mul_finrank_inf (L Z : IntermediateField M N) [IsGalois M Z] :
    Module.finrank M ↥(L ⊔ Z) * Module.finrank M ↥(L ⊓ Z) =
      Module.finrank M L * Module.finrank M Z := by
  set E := L ⊓ Z with hE_def
  have hL : E ≤ L := inf_le_left
  have hZ : E ≤ Z := inf_le_right
  have : IsGalois M (extendScalars hZ) := ‹IsGalois M Z›
  have : IsGalois E (extendScalars hZ) := IsGalois.tower_top_of_isGalois M E (extendScalars hZ)
  have hbot : extendScalars hZ ⊓ extendScalars hL = ⊥ := by
    rw [extendScalars_inf]
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxE : x ∈ E := by
      rw [mem_extendScalars] at hx
      exact ⟨hx.2, hx.1⟩
    exact (IntermediateField.mem_bot).mpr ⟨⟨x, hxE⟩, rfl⟩
  have hld := LinearDisjoint.of_inf_eq_bot hbot
  have h1 := hld.finrank_sup
  rw [extendScalars_sup, ← relfinrank_eq_finrank_of_le, ← relfinrank_eq_finrank_of_le,
    ← relfinrank_eq_finrank_of_le] at h1
  have e1 := finrank_bot_mul_relfinrank (hZ.trans le_sup_left : E ≤ Z ⊔ L)
  have e2 := finrank_bot_mul_relfinrank hZ
  have e3 := finrank_bot_mul_relfinrank hL
  rw [sup_comm, ← e1, h1, ← e2, ← e3]
  ring
end Galois

/-! ### Purely inseparable towers -/

section Inseparable

/-- If `γ ∉ E` and `γ ^ p ∈ E` in characteristic `p`, then `[E(γ) : E] = p`. -/
theorem finrank_adjoin_of_pow_char_mem {E L : Type*} [Field E] [Field L] [Algebra E L]
    (p : ℕ) [hp : Fact p.Prime] [CharP L p] {γ : L} (hγ : γ ∉ (algebraMap E L).range)
    {c : E} (hc : algebraMap E L c = γ ^ p) : Module.finrank E E⟮γ⟯ = p := by
  have hirr : Irreducible (X ^ p - C c) := by
    refine X_pow_sub_C_irreducible_of_prime hp.out fun b hb => hγ ⟨b, ?_⟩
    have : (algebraMap E L b - γ) ^ p = 0 := by
      rw [sub_pow_char, ← map_pow, hb, hc, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff hp.out.ne_zero |>.mp this)
  have hmonic : (X ^ p - C c).Monic := monic_X_pow_sub_C c hp.out.ne_zero
  have hroot : aeval γ (X ^ p - C c) = 0 := by simp [hc]
  have hmin := minpoly.eq_of_irreducible_of_monic hirr hroot hmonic
  have hint : IsIntegral E γ := ⟨_, hmonic, by rwa [← aeval_def]⟩
  rw [adjoin.finrank hint, ← hmin, natDegree_X_pow_sub_C]

variable {M L : Type*} [Field M] [Field L] [Algebra M L]

/-- **Towers of purely inseparable extensions** (plan S5(f)). Let `L/M` be finite and purely
inseparable in characteristic `p`. If a property of intermediate fields holds for `M` and passes
from `E` to `E(γ)` whenever `γ ∉ E` and `γ ^ p ∈ E`, then it holds for every intermediate
field. -/
theorem induction_intermediateField_of_isPurelyInseparable [FiniteDimensional M L] (p : ℕ)
    [Fact p.Prime] [CharP M p] [IsPurelyInseparable M L] {P : IntermediateField M L → Prop}
    (hbot : P ⊥)
    (hstep : ∀ (E : IntermediateField M L) (γ : L), γ ∉ E → γ ^ p ∈ E → P E →
      P (restrictScalars M (adjoin E {γ})))
    (F : IntermediateField M L) : P F := by
  classical
  have : ExpChar M p := ExpChar.prime (Fact.out : p.Prime)
  -- show `P E → P F` for all `E ≤ F`, by induction on `[L : E]`
  suffices key : ∀ n : ℕ, ∀ E : IntermediateField M L, Module.finrank E L = n → E ≤ F → P E →
      P F from key _ ⊥ rfl bot_le hbot
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro E hn hEF hPE
    by_cases hEq : E = F
    · rwa [← hEq]
    obtain ⟨x, hxF, hxE⟩ : ∃ x ∈ F, x ∉ E := by
      by_contra hcon
      push Not at hcon
      exact hEq (le_antisymm hEF hcon)
    have hex : ∃ k : ℕ, x ^ p ^ k ∈ E := by
      obtain ⟨k, hk⟩ := IsPurelyInseparable.pow_mem M p x
      obtain ⟨c, hc⟩ := hk
      exact ⟨k, hc ▸ E.algebraMap_mem c⟩
    set k₀ := Nat.find hex with hk₀
    have hk₀mem : x ^ p ^ k₀ ∈ E := Nat.find_spec hex
    have hk₀pos : k₀ ≠ 0 := by
      intro h0
      rw [h0, pow_zero, pow_one] at hk₀mem
      exact hxE hk₀mem
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hk₀pos
    set γ := x ^ p ^ k with hγ_def
    have hγE : γ ∉ E := Nat.find_min hex (by omega)
    have hγp : γ ^ p ∈ E := by
      have : p ^ k * p = p ^ k₀ := by rw [hk, pow_succ]
      rw [hγ_def, ← pow_mul, this]
      exact hk₀mem
    have hγF : γ ∈ F := pow_mem hxF _
    set E' := restrictScalars M (adjoin E {γ}) with hE'_def
    have hPE' := hstep E γ hγE hγp hPE
    have hEE' : E < E' := by
      refine lt_of_le_of_ne ?_ fun h => hγE ?_
      · intro y hy
        exact (adjoin E {γ}).algebraMap_mem ⟨y, hy⟩
      · rw [h]
        exact mem_adjoin_simple_self E γ
    have hE'F : E' ≤ F := by
      rw [hE'_def, restrictScalars_adjoin_eq_sup]
      exact sup_le hEF (adjoin_simple_le_iff.mpr hγF)
    exact ih _ (hn ▸ finrank_lt_of_gt hEE') E' rfl hE'F hPE'

end Inseparable

end DeJongAlterations.StableModification.Valuation.Analytic
