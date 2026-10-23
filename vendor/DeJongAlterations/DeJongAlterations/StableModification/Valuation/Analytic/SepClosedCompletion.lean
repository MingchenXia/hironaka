/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DeJongAlterations.StableModification.Valuation.Analytic.Krasner
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.FieldTheory.Perfect

/-!
# The completion of a separably closed field is algebraically closed

Temkin, *Stable modification of relative curves*, proof of Theorem 2.1.8 (`semi-stable.tex`,
lines 2208–2209): "Since `k₁` is separably closed, its completion `k̂₁` is algebraically closed".
This upgrades Mathlib's `IsAlgClosed.of_denseRange` (characteristic zero, algebraically closed
dense subfield) to separably closed dense subfields in every characteristic, which is the TODO of
Mathlib's `Mathlib/Analysis/Normed/Field/Dense.lean`.

## Main results

* `IsSepClosed.of_denseRange'`: a complete nontrivially normed non-archimedean field with a dense
  separably closed subfield is separably closed (separable approximation and Krasner's lemma).
* `perfectField_of_isSepClosed`: a complete nontrivially normed non-archimedean separably closed
  field is perfect: in characteristic `p`, a `p`-th root of `a` is the limit of roots of the
  separable polynomials `Xᵖ - πᵏ X - a`, `0 < ‖π‖ < 1`.
* `isAlgClosed_of_denseRange_of_isSepClosed`: hence such a field with a dense separably closed
  subfield is algebraically closed.
* `isAlgClosed_completion`: the completion of a nontrivially normed non-archimedean separably
  closed field is algebraically closed; `isAlgClosed_valuation_completion` is the same statement
  for the completion of a separably closed field with respect to a rank-one valuation.
-/

noncomputable section

open Polynomial IntermediateField Filter Topology

namespace DeJongAlterations.StableModification.Valuation.Analytic

/-- A complete nontrivially normed non-archimedean field with a dense separably closed subfield is
separably closed. -/
theorem IsSepClosed.of_denseRange' {K L : Type*} [Field K] [NontriviallyNormedField L]
    [CompleteSpace L] [IsUltrametricDist L] [Algebra K L] (hd : DenseRange (algebraMap K L))
    [IsSepClosed K] : IsSepClosed L := by
  classical
  refine IsSepClosed.of_exists_root L fun f hfm hfirr hfs ↦ ?_
  have hn : f.natDegree ≠ 0 := (Irreducible.natDegree_pos hfirr).ne'
  let C := AlgebraicClosure L
  let : NontriviallyNormedField C := spectralNorm.nontriviallyNormedField L C
  let : NormedAlgebra L C := spectralNorm.normedAlgebra L C
  have : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra L
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_aeval_eq_zero C f (degree_ne_of_natDegree_ne hn)
  obtain ⟨δ, hδ, hsep⟩ := exists_pos_le_norm_sub_of_mem_roots (f.map (algebraMap L C))
  obtain ⟨g, hgm, hgdeg, hgs, hgc⟩ := exists_separable_monic_approx hd hfm hfs
    (show 0 < (δ / max ‖a‖ 1) ^ f.natDegree / (f.natDegree + 1) by
      have : 0 < max ‖a‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
      positivity)
  set G := g.map (algebraMap K L) with hG
  have hGm : G.Monic := hgm.map _
  have hGdeg : G.natDegree = f.natDegree := by rw [hG, natDegree_map, hgdeg]
  obtain ⟨b, hb, hab⟩ :=
    exists_aroots_norm_sub_lt hfm hGm hGdeg hn ha hδ hgc (IsAlgClosed.splits _)
  -- `g` splits over the separably closed field `K`, so `b` comes from `K ⊆ L`
  have hgsplit : g.Splits := IsSepClosed.splits_of_separable g hgs
  have hbG : G.aeval b = 0 := (mem_aroots.mp hb).2
  have hbint : IsIntegral L b := ⟨G, hGm, by rwa [← aeval_def]⟩
  have hbbot : b ∈ (⊥ : IntermediateField L C) := by
    rw [aroots, hG, Polynomial.map_map, hgsplit.roots_map, Multiset.mem_map] at hb
    obtain ⟨c, -, rfl⟩ := hb
    exact IntermediateField.mem_bot.mpr ⟨algebraMap K L c, rfl⟩
  -- Krasner's lemma: `a ∈ L⟮b⟯ = L`
  have hmina : minpoly L a = f := (minpoly.eq_of_irreducible_of_monic hfirr ha hfm).symm
  have haLb : a ∈ L⟮b⟯ := by
    refine IsKrasner.krasner (hmina ▸ hfs) (IsAlgClosed.splits _) hbint fun x' hx' hne ↦ ?_
    have hx'f : f.aeval x' = 0 := hmina ▸ hx'.aeval_eq_zero
    refine hab.trans_le (hsep a ?_ x' ?_ hne)
    · exact mem_aroots.mpr ⟨hfm.ne_zero, ha⟩
    · exact mem_aroots.mpr ⟨hfm.ne_zero, hx'f⟩
  rw [IntermediateField.adjoin_simple_eq_bot_iff.mpr hbbot] at haLb
  obtain ⟨a₀, rfl⟩ := IntermediateField.mem_bot.mp haLb
  refine ⟨a₀, (algebraMap L C).injective ?_⟩
  rw [map_zero, ← ha, aeval_algebraMap_apply_eq_algebraMap_eval]

/-- In a complete nontrivially normed non-archimedean separably closed field of characteristic
`p`, every element is a `p`-th power: `b` is the limit of roots `bₖ` of the separable polynomials
`Xᵖ - πᵏ X - a`. -/
theorem exists_pow_char_eq {L : Type*} [NontriviallyNormedField L] [CompleteSpace L]
    [IsUltrametricDist L] [IsSepClosed L] (p : ℕ) [hp : Fact p.Prime] [CharP L p] (a : L) :
    ∃ c : L, c ^ p = a := by
  obtain ⟨π, hπ0, hπ1⟩ := NormedField.exists_norm_lt_one L
  have hπne : π ≠ 0 := norm_pos_iff.mp hπ0
  have hp2 : 2 ≤ p := hp.out.two_le
  -- roots `b k` of `Xᵖ - πᵏ X - a`
  have hroot : ∀ k : ℕ, ∃ x : L, x ^ p = π ^ k * x + a := fun k ↦ by
    obtain ⟨x, hx⟩ := IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C' p p 1 (-(π ^ k)) (-a)
      (dvd_refl p) hp2 (neg_ne_zero.mpr (pow_ne_zero _ hπne))
    exact ⟨x, by linear_combination hx⟩
  choose b hb using hroot
  set R := max 1 ‖a‖ with hR
  have hR1 : 1 ≤ R := le_max_left _ _
  -- the roots are bounded by `R`
  have hbound : ∀ k, ‖b k‖ ≤ R := by
    intro k
    by_contra hlt
    rw [not_le] at hlt
    have hb1 : 1 < ‖b k‖ := lt_of_le_of_lt hR1 hlt
    have hpow : ‖b k‖ < ‖b k‖ ^ p := by
      calc ‖b k‖ = ‖b k‖ ^ 1 := (pow_one _).symm
        _ < ‖b k‖ ^ p := pow_lt_pow_right₀ hb1 (by omega)
    have h1 : ‖b k‖ ^ p ≤ max (‖π‖ ^ k * ‖b k‖) ‖a‖ := by
      rw [← norm_pow, hb k, ← norm_pow, ← norm_mul]
      exact IsUltrametricDist.norm_add_le_max _ _
    have h2 : ‖π‖ ^ k * ‖b k‖ ≤ ‖b k‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hπ1.le)
    have h3 : ‖a‖ < ‖b k‖ := lt_of_le_of_lt (le_max_right _ _) hlt
    have : max (‖π‖ ^ k * ‖b k‖) ‖a‖ < ‖b k‖ ^ p :=
      max_lt (lt_of_le_of_lt h2 hpow) (h3.trans hpow)
    linarith
  -- successive differences
  have hdiff : ∀ k, ‖b (k + 1) - b k‖ ^ p ≤ ‖π‖ ^ k * R := by
    intro k
    rw [← norm_pow, sub_pow_char, hb, hb]
    have : π ^ (k + 1) * b (k + 1) + a - (π ^ k * b k + a) =
        π ^ (k + 1) * b (k + 1) - π ^ k * b k := by ring
    rw [this]
    refine (norm_sub_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_pow, pow_succ]
      calc ‖π‖ ^ k * ‖π‖ * ‖b (k + 1)‖ ≤ ‖π‖ ^ k * 1 * R := by
            gcongr
            · exact hbound _
        _ = ‖π‖ ^ k * R := by ring
    · rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hbound k) (by positivity)
  set r := ‖π‖ ^ ((p : ℝ)⁻¹)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hr1 : r < 1 := Real.rpow_lt_one (norm_nonneg _) hπ1 (inv_pos.mpr hp0)
  have hgeom : ∀ k, dist (b k) (b (k + 1)) ≤ R ^ ((p : ℝ)⁻¹) * r ^ k := by
    intro k
    rw [dist_comm, dist_eq_norm]
    have h := hdiff k
    rw [← Real.rpow_natCast] at h
    rw [← Real.le_rpow_inv_iff_of_pos (norm_nonneg _) (by positivity) hp0] at h
    refine h.trans_eq ?_
    rw [Real.mul_rpow (by positivity) (by positivity), mul_comm, ← Real.rpow_natCast,
      ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_natCast r, ← Real.rpow_mul (norm_nonneg _),
      mul_comm (k : ℝ)]
  have hcauchy : CauchySeq b := cauchySeq_of_le_geometric r _ hr1 hgeom
  obtain ⟨c, hc⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨c, tendsto_nhds_unique (hc.pow p) ?_⟩
  -- `b k ^ p = πᵏ b k + a → a`
  have h0 : Tendsto (fun k ↦ π ^ k * b k) atTop (𝓝 0) := by
    have hlim : Tendsto (fun k : ℕ ↦ ‖π‖ ^ k * R) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg π) hπ1).mul_const R
    refine squeeze_zero_norm (fun k ↦ ?_) hlim
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left (hbound k) (by positivity)
  have := h0.add_const a
  rw [zero_add] at this
  exact this.congr fun k ↦ (hb k).symm

/-- A complete nontrivially normed non-archimedean separably closed field is perfect. -/
theorem perfectField_of_isSepClosed (L : Type*) [NontriviallyNormedField L] [CompleteSpace L]
    [IsUltrametricDist L] [IsSepClosed L] : PerfectField L := by
  obtain ⟨p, hchar⟩ := CharP.exists L
  rcases CharP.char_is_prime_or_zero L p with hprime | rfl
  · have : Fact p.Prime := ⟨hprime⟩
    have : ExpChar L p := ExpChar.prime hprime
    have : PerfectRing L p := PerfectRing.ofSurjective L p fun a ↦ by
      obtain ⟨c, hc⟩ := exists_pow_char_eq p a
      exact ⟨c, by rw [frobenius_def, hc]⟩
    exact PerfectRing.toPerfectField L p
  · have : CharZero L := CharP.charP_to_charZero L
    infer_instance

/-- A complete nontrivially normed non-archimedean field with a dense separably closed subfield is
algebraically closed. -/
theorem isAlgClosed_of_denseRange_of_isSepClosed {K L : Type*} [Field K] [NontriviallyNormedField L]
    [CompleteSpace L] [IsUltrametricDist L] [Algebra K L] (hd : DenseRange (algebraMap K L))
    [IsSepClosed K] : IsAlgClosed L := by
  have : IsSepClosed L := IsSepClosed.of_denseRange' hd
  have : PerfectField L := perfectField_of_isSepClosed L
  exact IsSepClosed.isAlgClosed_of_perfectField L

/-- **The completion of a separably closed field is algebraically closed** (Temkin, l. 2208–2209):
for a nontrivially normed non-archimedean separably closed field `K`. -/
instance isAlgClosed_completion (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    [IsSepClosed K] : IsAlgClosed (UniformSpace.Completion K) :=
  isAlgClosed_of_denseRange_of_isSepClosed (denseRange_algebraMap_completion K)

/-- The completion of a separably closed field with respect to a rank-one valuation is
algebraically closed. -/
theorem isAlgClosed_valuation_completion {F : Type*} [Field F] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) [v.RankOne] [IsSepClosed F] :
    IsAlgClosed v.Completion := by
  let : Algebra F v.Completion := (toCompletion v).toAlgebra
  exact isAlgClosed_of_denseRange_of_isSepClosed (K := F) (denseRange_toCompletion v)

end DeJongAlterations.StableModification.Valuation.Analytic
