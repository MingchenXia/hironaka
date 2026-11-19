/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.Valuation.ValuationRing
import Hironaka.Algebra.Local.PowerSeries
import Hironaka.Algebra.Local.Taylor
import Mathlib.RingTheory.MvPowerSeries.Equiv

/-!
# `K`-algebra endomorphisms of `K⟦X₁, …, Xₙ⟧` preserving the maximal ideal

Kollár, in the proof of the formal equivalence theorem: "(91.4) is also clear" [Kol07, 95], that is,
[Kol07, Definition 91, (4)]: for the automorphism `φ^*` of `Ô_{p,X} ≅ K⟦x⟧` of the form `1 + B`,
`h − φ^*(h) ∈ B` for every `h`.
The underlying fact for `R = K⟦x⟧`: if `σ` is a `K`-algebra endomorphism of `R` and `B ⊆ 𝔪` an
ideal with `σ(Xᵢ) − Xᵢ ∈ B` for all `i`, then `σ(h) − h ∈ B` for all `h ∈ R`
(`sub_map_mem_of_forall_sub_X_mem`).

**Why it holds.** A `K`-algebra endomorphism `σ` with `σ(Xᵢ) ∈ 𝔪` maps `𝔪 = (X₁, …, Xₙ)` into `𝔪`
(the generators go into `𝔪`), hence `𝔪^N` into `𝔪^N` for every `N`
(`mem_maximalIdeal_pow_map_of_forall_X_mem`). For a polynomial `P`, `σ(P) − P ∈ B` by induction on
`P`: constants are fixed (`K`-linearity), sums add, and
`σ(P·Xᵢ) − P·Xᵢ = (σP − P)·σ(Xᵢ) + P·(σ(Xᵢ) − Xᵢ)`. For a power series `h` and each `N`, write
`h = P + G` with `P = truncTotal (N+1) h` a polynomial and `G ∈ 𝔪^{N+1}` (`sub_truncTotal_mem` of
`Hironaka/Algebra/Local/Taylor.lean`); then `σ(h) − h = (σP − P) + (σG − G) ∈ B + 𝔪^N`, and Krull's
intersection theorem (`mem_of_forall_mem_sup_pow`: `B = ⋂_N (B + 𝔪^N)` in the Noetherian local
ring `K⟦X⟧`) gives `σ(h) − h ∈ B`. No continuity of `σ` is assumed: preservation of the powers of
`𝔪` is automatic from `σ(Xᵢ) ∈ 𝔪`.

The same approximation shows that such a `σ` **is a substitution**
(`eq_substAlgHom_of_forall_X_mem`): `σ` and `substAlgHom (σ ∘ X)` are `K`-algebra maps agreeing on
the `Xᵢ`, hence on polynomials, and both map `𝔪^{N+1}` into `𝔪^{N+1}`, so they agree modulo every
`𝔪^N`, hence everywhere. This is the form in which the transported automorphism `Φ'⁻¹ ∘ Φ` of
two Cohen isomorphisms is fed to `IsOnePlus` of `Hironaka/Algebra/Local/FormalAut.lean` (whose first
clause asks for a substitution) — Kollár's description of the automorphisms of `K⟦x⟧` as the
substitutions `xᵢ ↦ gᵢ` [Kol07, Notation 93].
-/

public section

namespace IsLocalRing

open MvPowerSeries IsLocalRing

variable {K : Type*} [Field K] {n : ℕ}

/-- A power series lies in the maximal ideal of `K⟦X⟧` iff its constant coefficient vanishes. -/
theorem mem_maximalIdeal_mvPowerSeries_iff {f : MvPowerSeries (Fin n) K} :
    f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ↔ constantCoeff f = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, isUnit_iff_ne_zero,
    not_not]

/-- `Xᵢ ∈ 𝔪`. -/
theorem X_mem_maximalIdeal_mvPowerSeries (i : Fin n) :
    (X i : MvPowerSeries (Fin n) K) ∈ maximalIdeal (MvPowerSeries (Fin n) K) := by
  rw [maximalIdeal_eq_span_range_X (Fin n) K]
  exact Ideal.subset_span ⟨i, rfl⟩

section Endomorphism

variable (σ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)

/-- A `K`-algebra endomorphism sending every `Xᵢ` into `𝔪` maps `𝔪` into `𝔪`. -/
theorem map_maximalIdeal_le_of_forall_X_mem
    (hσ : ∀ i, σ (X i) ∈ maximalIdeal (MvPowerSeries (Fin n) K)) :
    (maximalIdeal (MvPowerSeries (Fin n) K)).map σ ≤ maximalIdeal (MvPowerSeries (Fin n) K) := by
  have hX := hσ
  rw [maximalIdeal_eq_span_range_X (Fin n) K, Ideal.map_span]
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  have := hX i
  rwa [maximalIdeal_eq_span_range_X (Fin n) K] at this

/-- Such a `σ` maps `𝔪^N` into `𝔪^N`. -/
theorem mem_maximalIdeal_pow_map_of_forall_X_mem
    (hσ : ∀ i, σ (X i) ∈ maximalIdeal (MvPowerSeries (Fin n) K)) {N : ℕ}
    {f : MvPowerSeries (Fin n) K} (hf : f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ N) :
    σ f ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ N := by
  have h1 : (maximalIdeal (MvPowerSeries (Fin n) K) ^ N).map σ ≤
      maximalIdeal (MvPowerSeries (Fin n) K) ^ N := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_maximalIdeal_le_of_forall_X_mem σ hσ) N
  exact h1 (Ideal.mem_map_of_mem _ hf)

/-- Two `K`-algebra endomorphisms of `K⟦X⟧` agreeing on the variables agree on polynomials. -/
theorem algHom_coe_eq_of_forall_X (τ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)
    (h : ∀ i, σ (X i) = τ (X i)) (P : MvPolynomial (Fin n) K) :
    σ (P : MvPowerSeries (Fin n) K) = τ (P : MvPowerSeries (Fin n) K) := by
  refine MvPolynomial.induction_on
    (motive := fun P : MvPolynomial (Fin n) K =>
      σ (P : MvPowerSeries (Fin n) K) = τ (P : MvPowerSeries (Fin n) K))
    P (fun a => ?_) (fun p q hp hq => ?_) (fun p i hp => ?_)
  · have hc : ((MvPolynomial.C a : MvPolynomial (Fin n) K) : MvPowerSeries (Fin n) K) =
        algebraMap K (MvPowerSeries (Fin n) K) a := by
      rw [MvPolynomial.coe_C, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply]
    rw [hc, σ.commutes, τ.commutes]
  · rw [MvPolynomial.coe_add, map_add, map_add, hp, hq]
  · rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, map_mul, hp, h]

/-- For an ideal `B ⊆ 𝔪` of `K⟦X₁, …, Xₙ⟧` and a `K`-algebra endomorphism `σ` with `σ(Xᵢ) − Xᵢ ∈ B`
for every `i`, `σ(h) − h ∈ B` for every power series `h` (Kollár's "(91.4) is also clear",
[Kol07, 95], for [Kol07, Definition 91, (4)]): on polynomials by induction, on power series by
approximation modulo `𝔪^N` and
Krull's intersection theorem. -/
theorem sub_map_mem_of_forall_sub_X_mem (B : Ideal (MvPowerSeries (Fin n) K))
    (hB : B ≤ maximalIdeal (MvPowerSeries (Fin n) K))
    (hσ : ∀ i, σ (X i) - X i ∈ B) (h : MvPowerSeries (Fin n) K) : σ h - h ∈ B := by
  have hX : ∀ i, σ (X i) ∈ maximalIdeal (MvPowerSeries (Fin n) K) := fun i => by
    have := Ideal.add_mem _ (hB (hσ i)) (X_mem_maximalIdeal_mvPowerSeries (K := K) i)
    rwa [sub_add_cancel] at this
  have hpoly : ∀ P : MvPolynomial (Fin n) K,
      σ (P : MvPowerSeries (Fin n) K) - P ∈ B := by
    intro P
    refine MvPolynomial.induction_on
      (motive := fun P : MvPolynomial (Fin n) K => σ (P : MvPowerSeries (Fin n) K) - P ∈ B)
      P (fun a => ?_) (fun p q hp hq => ?_) (fun p i hp => ?_)
    · have hc : ((MvPolynomial.C a : MvPolynomial (Fin n) K) : MvPowerSeries (Fin n) K) =
          algebraMap K (MvPowerSeries (Fin n) K) a := by
        rw [MvPolynomial.coe_C, MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self,
          RingHom.id_apply]
      rw [hc, σ.commutes, sub_self]
      exact zero_mem _
    · rw [MvPolynomial.coe_add, map_add]
      have := B.add_mem hp hq
      convert this using 1
      ring
    · rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul]
      have : σ (p : MvPowerSeries (Fin n) K) * σ (X i) - (p : MvPowerSeries (Fin n) K) * X i =
          (σ (p : MvPowerSeries (Fin n) K) - (p : MvPowerSeries (Fin n) K)) * σ (X i) +
            (p : MvPowerSeries (Fin n) K) * (σ (X i) - X i) := by ring
      rw [this]
      exact B.add_mem (B.mul_mem_right _ hp) (B.mul_mem_left _ (hσ i))
  refine mem_of_forall_mem_sup_pow fun s => ?_
  have hr := sub_truncTotal_mem h s
  set P : MvPolynomial (Fin n) K := truncTotal (s + 1) h with hP
  have hs : maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1) ≤
      maximalIdeal (MvPowerSeries (Fin n) K) ^ s := Ideal.pow_le_pow_right (Nat.le_succ s)
  have h1 : σ (h - P) - (h - P) ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ s :=
    hs (Ideal.sub_mem _ (mem_maximalIdeal_pow_map_of_forall_X_mem σ hX hr) hr)
  have h2 : σ h - h = (σ (P : MvPowerSeries (Fin n) K) - P) + (σ (h - P) - (h - P)) := by
    rw [map_sub]; ring
  rw [h2]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (hpoly P)) (Ideal.mem_sup_right h1)

/-- The substitution family `Xᵢ ↦ σ(Xᵢ)` of a `K`-algebra endomorphism sending the variables into
`𝔪` (the `xᵢ ↦ gᵢ` of [Kol07, Notation 93]). -/
theorem hasSubst_of_forall_X_mem (hσ : ∀ i, σ (X i) ∈ maximalIdeal (MvPowerSeries (Fin n) K)) :
    HasSubst fun i => σ (X i) :=
  hasSubst_of_constantCoeff_zero fun i => mem_maximalIdeal_mvPowerSeries_iff.mp (hσ i)

/-- A `K`-algebra endomorphism `σ` of `K⟦X⟧` sending every `Xᵢ` into `𝔪` is the substitution
`Xᵢ ↦ σ(Xᵢ)` [Kol07, Notation 93] — both agree on polynomials and both map `𝔪^{N+1}` into
itself, so they agree modulo every `𝔪^N`.  (Compare `continuous_iff_exists_substAlgHom` of
`Hironaka/Algebra/Local/FormalAut.lean`, which needs continuity instead.) -/
theorem eq_substAlgHom_of_forall_X_mem
    (hσ : ∀ i, σ (X i) ∈ maximalIdeal (MvPowerSeries (Fin n) K)) (f : MvPowerSeries (Fin n) K) :
    σ f = substAlgHom (R := K) (hasSubst_of_forall_X_mem σ hσ) f := by
  set τ := substAlgHom (R := K) (hasSubst_of_forall_X_mem σ hσ) with hτ
  have hX : ∀ i, σ (X i) = τ (X i) := fun i => by
    rw [hτ, coe_substAlgHom, subst_X (hasSubst_of_forall_X_mem σ hσ)]
  have hmem : ∀ s : ℕ, σ f - τ f ∈ (⊥ : Ideal (MvPowerSeries (Fin n) K)) ⊔
      maximalIdeal (MvPowerSeries (Fin n) K) ^ s := by
    intro s
    have hr := sub_truncTotal_mem f s
    set P : MvPolynomial (Fin n) K := truncTotal (s + 1) f with hP
    have hs : maximalIdeal (MvPowerSeries (Fin n) K) ^ (s + 1) ≤
        maximalIdeal (MvPowerSeries (Fin n) K) ^ s := Ideal.pow_le_pow_right (Nat.le_succ s)
    have h1 : σ (f - P) - τ (f - P) ∈ maximalIdeal (MvPowerSeries (Fin n) K) ^ s :=
      hs (Ideal.sub_mem _ (mem_maximalIdeal_pow_map_of_forall_X_mem σ hσ hr)
        (substAlgHom_mem_maximalIdeal_pow _ hr))
    have h2 : σ f - τ f = (σ (P : MvPowerSeries (Fin n) K) - τ P) + (σ (f - P) - τ (f - P)) := by
      rw [map_sub, map_sub]; ring
    rw [h2, algHom_coe_eq_of_forall_X σ τ hX P, sub_self, zero_add]
    exact Ideal.mem_sup_right h1
  have := mem_of_forall_mem_sup_pow hmem
  rwa [Ideal.mem_bot, sub_eq_zero] at this

/-- Two `K`-algebra endomorphisms of `K⟦X⟧` sending the variables into `𝔪` and agreeing on the
variables are equal (both are the substitution by their common values). -/
theorem algHom_ext_of_forall_X_mem (τ : MvPowerSeries (Fin n) K →ₐ[K] MvPowerSeries (Fin n) K)
    (hσ : ∀ i, σ (X i) ∈ maximalIdeal (MvPowerSeries (Fin n) K)) (h : ∀ i, σ (X i) = τ (X i)) :
    σ = τ := by
  have hτ : ∀ i, τ (X i) ∈ maximalIdeal (MvPowerSeries (Fin n) K) := fun i => (h i) ▸ hσ i
  refine AlgHom.ext fun f => ?_
  rw [eq_substAlgHom_of_forall_X_mem σ hσ f, eq_substAlgHom_of_forall_X_mem τ hτ f,
    coe_substAlgHom, coe_substAlgHom]
  exact congrArg (fun a => subst a f) (funext h)

end Endomorphism

end IsLocalRing
