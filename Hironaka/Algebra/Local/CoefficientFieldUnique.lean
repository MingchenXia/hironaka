/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.Unramified.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Uniqueness of algebra maps into a separated local ring with equal residues

Kollár constructs a field of representatives `k' ⊂ Ô_{p,X}` of the residue field `κ(p)` of a
closed point by Hensel's lemma [Kol07, Definition 55]: the existence of a coefficient field over
`k`. The study of formal equivalence of points also needs the complementary uniqueness: two
`k`-algebra homomorphisms `κ(p) → Ô_{p,X}` with the same residue composite coincide. This module
proves the ring-level statement behind it; it is not in the sources.

## The argument

Let `A` be a formally unramified `k`-algebra (for a field extension `κ(p)/k` this is separability,
Mathlib's `Algebra.FormallyUnramified.of_isSeparable`), `B` a local `k`-algebra separated for the
`𝔪`-adic topology (`IsHausdorff (maximalIdeal B) B`, i.e. `⋂ₙ 𝔪ⁿ = 0`; Krull's intersection
theorem for Noetherian local rings, an instance for adic completions) and `σ₁, σ₂ : A →ₐ[k] B`
with `σ₁ ≡ σ₂` modulo the maximal ideal `𝔪` (equal residues). Then
`σ₁ ≡ σ₂` modulo every `𝔪ⁿ`: if the two maps agree modulo `𝔪ⁿ`, they agree modulo `𝔪ⁿ⁺¹`, because
the ideal `𝔪ⁿ/𝔪ⁿ⁺¹` of `B/𝔪ⁿ⁺¹` has square zero and formal unramifiedness says that two maps into
`B/𝔪ⁿ⁺¹` agreeing modulo a square-zero ideal are equal
(`Algebra.FormallyUnramified.comp_injective`). Separatedness (`IsHausdorff.haus`) then gives
`σ₁ a − σ₂ a ∈ ⋂ₙ 𝔪ⁿ = 0`.

The lemma is stated for any `𝔪`-adically separated local ring `B`. It is applied to
`B = Ô_{p,X}`, the completion of the Noetherian stalk at a closed point (`𝔪̂`-adically complete by
Mathlib's instance), and `A = κ(p)`, algebraic over `k` of characteristic zero and hence
formally unramified: a residue-trivial `k`-automorphism of `Ô_{p,X} ≅ κ(p)⟦x₁, …, xₙ⟧` is then
determined by its values on the coordinates, which is how the completion of the graph of a
formal isomorphism between two points is identified.
-/

public section

namespace IsLocalRing

open IsLocalRing

/-- Two `k`-algebra homomorphisms from a formally unramified `k`-algebra `A` into an `𝔪`-adically
separated local `k`-algebra `B` with the same residue composite are equal: the uniqueness
complementing the Hensel-lemma construction of a field of representatives
[Kol07, Definition 55]; not in the sources. Induction along the powers of the maximal ideal with
`Algebra.FormallyUnramified.comp_injective` for the square-zero ideals `𝔪ⁿ/𝔪ⁿ⁺¹`, then
separatedness (Krull's intersection theorem). -/
theorem algHom_ext_of_residue_eq {k A B : Type*} [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra.FormallyUnramified k A] [IsLocalRing B]
    [IsHausdorff (maximalIdeal B) B] (σ₁ σ₂ : A →ₐ[k] B)
    (h : ∀ a, residue B (σ₁ a) = residue B (σ₂ a)) : σ₁ = σ₂ := by
  have key : ∀ n : ℕ, ∀ a, σ₁ a - σ₂ a ∈ maximalIdeal B ^ n := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · rw [zero_add, pow_one]
        exact Ideal.Quotient.eq.mp (h a)
      · set J : Ideal B := maximalIdeal B ^ (n + 1) with hJ
        set I : Ideal (B ⧸ J) := (maximalIdeal B ^ n).map (Ideal.Quotient.mk J) with hI
        have hI2 : I ^ 2 = ⊥ := by
          rw [hI, ← Ideal.map_pow, ← pow_mul]
          exact Ideal.map_mk_eq_bot_of_le (Ideal.pow_le_pow_right (by omega))
        have hinj := Algebra.FormallyUnramified.comp_injective (R := k) (A := A) I hI2
        have e : (Ideal.Quotient.mkₐ k I).comp ((Ideal.Quotient.mkₐ k J).comp σ₁) =
            (Ideal.Quotient.mkₐ k I).comp ((Ideal.Quotient.mkₐ k J).comp σ₂) := by
          refine AlgHom.ext fun b => ?_
          simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
          rw [Ideal.Quotient.eq, ← map_sub]
          exact Ideal.mem_map_of_mem _ (ih b)
        have e' := AlgHom.congr_fun (hinj e) a
        simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at e'
        exact Ideal.Quotient.eq.mp e'
  refine AlgHom.ext fun a => ?_
  rw [← sub_eq_zero]
  refine IsHausdorff.haus ‹IsHausdorff (maximalIdeal B) B› _ fun m => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  exact key m a

end IsLocalRing
