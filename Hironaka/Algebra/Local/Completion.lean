/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations extend to the adic completion

A derivation `D` of a commutative ring `R` lowers the powers of any ideal by one:
`D(Iᵃ⁺¹) ⊆ Iᵃ` (Leibniz on a product of `a + 1` elements of `I`).  Hence `D` induces, for every
`n`, a map `R/Iⁿ⁺¹ → R/Iⁿ`, and these maps are compatible with the transition maps of the
inverse system defining the `I`-adic completion `R̂ = AdicCompletion I R`; assembling them gives
a derivation `D̂` of `R̂` with `D̂ ∘ ι = ι ∘ D` for the canonical map `ι : R → R̂`
(`Derivation.adicCompletion`, `Derivation.adicCompletion_of`).  This is the completion of a
derivation behind Kollár's identity `D(Î) = D(I)^` [Kol07, Lemma 74(5)], needed for the
coordinate derivations `∂ᵢ` of a regular local ring; it needs no hypothesis on `D`, `I`
or `R`, so it is stated for an arbitrary derivation over an arbitrary base ring `k`.

## Conventions

`AdicCompletion I R` is Mathlib's: compatible families `x.val n ∈ R ⧸ (Iⁿ • ⊤)`.  The
level-`n` component of `D̂ x` is computed from the level-`n + 1` component of `x`: lift
`x.val (n + 1)` to `f ∈ R`, apply `D`, and reduce modulo `Iⁿ`; well defined by
`Derivation.mem_pow_of_mem_pow_succ`.  The properties of the completed coordinate derivations
of a regular local ring (`∂̂ᵢ xⱼ = δᵢⱼ`, commutation, linearity over the coefficient field, the
`RegularCoords` structure on `R̂`) are proved in `Hironaka/Algebra/Local/CompletionCoords.lean`.
-/

@[expose] public section

namespace Derivation

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] (I : Ideal R)
  (D : Derivation k R R)

/-- A derivation lowers the powers of an ideal by one: `D(Iᵃ⁺¹) ⊆ Iᵃ`. -/
theorem mem_pow_of_mem_pow_succ (a : ℕ) {f : R} (hf : f ∈ I ^ (a + 1)) : D f ∈ I ^ a := by
  induction a generalizing f with
  | zero => simp
  | succ a ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro g hg h hh
      rw [Derivation.leibniz, smul_eq_mul g (D h), smul_eq_mul h (D g)]
      have h1 : h * D g ∈ I ^ (a + 1) := by
        rw [pow_succ']
        exact Ideal.mul_mem_mul hh (ih hg)
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hg) h1
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy

/-- The level-`n` component of the extended derivation: `R/Iⁿ⁺¹ → R/Iⁿ`,
`f mod Iⁿ⁺¹ ↦ D f mod Iⁿ`. -/
noncomputable def adicLevel (n : ℕ) (y : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) :
    R ⧸ (I ^ n • ⊤ : Ideal R) :=
  Quotient.liftOn' y (fun f => Submodule.Quotient.mk (D f)) fun f g h => by
    refine (Submodule.Quotient.eq _).mpr ?_
    rw [← map_sub]
    have hfg : f - g ∈ I ^ (n + 1) := by
      have := (Submodule.quotientRel_def _).mp h
      rwa [Ideal.smul_eq_mul, Ideal.mul_top] at this
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact D.mem_pow_of_mem_pow_succ I n hfg

@[simp]
theorem adicLevel_mk (n : ℕ) (f : R) :
    D.adicLevel I n (Submodule.Quotient.mk f) = Submodule.Quotient.mk (D f) :=
  rfl

theorem transitionMap_adicLevel {m n : ℕ} (h : m ≤ n) (y : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) :
    AdicCompletion.transitionMap I R h (D.adicLevel I n y) =
      D.adicLevel I m (AdicCompletion.transitionMap I R (Nat.succ_le_succ h) y) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [show D.adicLevel I n (Submodule.Quotient.mk f) =
      Ideal.Quotient.mk (I ^ n • ⊤ : Ideal R) (D f) from rfl,
    AdicCompletion.transitionMap_ideal_mk,
    show (Submodule.Quotient.mk f : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) =
      Ideal.Quotient.mk (I ^ (n + 1) • ⊤ : Ideal R) f from rfl,
    AdicCompletion.transitionMap_ideal_mk]
  rfl

/-- The underlying function of the extended derivation. -/
noncomputable def adicCompletionFun (x : AdicCompletion I R) : AdicCompletion I R :=
  ⟨fun n => D.adicLevel I n (x.val (n + 1)), fun {m n} h => by
    rw [transitionMap_adicLevel, x.property (Nat.succ_le_succ h)]⟩

@[simp]
theorem adicCompletionFun_val (x : AdicCompletion I R) (n : ℕ) :
    (D.adicCompletionFun I x).val n = D.adicLevel I n (x.val (n + 1)) :=
  rfl

/-- The extension of a derivation `D` of `R` to the `I`-adic completion `R̂`, computed level by
level from `D(Iⁿ⁺¹) ⊆ Iⁿ`: the completed derivation of [Kol07, Lemma 74(5)]. -/
noncomputable def adicCompletion : Derivation k (AdicCompletion I R) (AdicCompletion I R) where
  toFun := D.adicCompletionFun I
  map_add' x y := by
    apply AdicCompletion.ext
    intro n
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + 1))
    obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (y.val (n + 1))
    rw [AdicCompletion.val_add_apply, adicCompletionFun_val, adicCompletionFun_val,
      adicCompletionFun_val, AdicCompletion.val_add_apply, ← hf, ← hg, ← Submodule.Quotient.mk_add,
      adicLevel_mk, adicLevel_mk, adicLevel_mk, map_add, Submodule.Quotient.mk_add]
  map_smul' r x := by
    apply AdicCompletion.ext
    intro n
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + 1))
    rw [RingHom.id_apply, AdicCompletion.val_smul_apply, adicCompletionFun_val,
      adicCompletionFun_val, AdicCompletion.val_smul_apply, ← hf, ← Submodule.Quotient.mk_smul,
      adicLevel_mk, adicLevel_mk, Derivation.map_smul, Submodule.Quotient.mk_smul]
  map_one_eq_zero' := by
    apply AdicCompletion.ext
    intro n
    change D.adicLevel I n ((1 : AdicCompletion I R).val (n + 1)) = (0 : AdicCompletion I R).val n
    rw [AdicCompletion.val_one, AdicCompletion.val_zero_apply,
      show (1 : R ⧸ (I ^ (n + 1) • ⊤ : Ideal R)) = Submodule.Quotient.mk 1 from
        (map_one (Ideal.Quotient.mk _)).symm,
      adicLevel_mk, map_one_eq_zero, Submodule.Quotient.mk_zero]
  leibniz' x y := by
    apply AdicCompletion.ext
    intro n
    obtain ⟨f, hf⟩ := Submodule.Quotient.mk_surjective _ (x.val (n + 1))
    obtain ⟨g, hg⟩ := Submodule.Quotient.mk_surjective _ (y.val (n + 1))
    have hxn : x.val n = Submodule.Quotient.mk f := by
      rw [← x.property (Nat.le_succ n), ← hf]
      exact AdicCompletion.transitionMap_ideal_mk I (Nat.le_succ n) f
    have hyn : y.val n = Submodule.Quotient.mk g := by
      rw [← y.property (Nat.le_succ n), ← hg]
      exact AdicCompletion.transitionMap_ideal_mk I (Nat.le_succ n) g
    have hDx : (D.adicCompletionFun I x).val n = Submodule.Quotient.mk (D f) := by
      rw [adicCompletionFun_val, ← hf, adicLevel_mk]
    have hDy : (D.adicCompletionFun I y).val n = Submodule.Quotient.mk (D g) := by
      rw [adicCompletionFun_val, ← hg, adicLevel_mk]
    have hxy : (x * y).val (n + 1) = Submodule.Quotient.mk (f * g) := by
      rw [AdicCompletion.val_mul, ← hf, ← hg]
      exact (map_mul (Ideal.Quotient.mk _) f g).symm
    change D.adicLevel I n ((x * y).val (n + 1)) =
      (x • D.adicCompletionFun I y + y • D.adicCompletionFun I x).val n
    rw [hxy, adicLevel_mk, AdicCompletion.val_add_apply, smul_eq_mul x (D.adicCompletionFun I y),
      smul_eq_mul y (D.adicCompletionFun I x), AdicCompletion.val_mul, AdicCompletion.val_mul,
      hxn, hyn, hDx, hDy, Derivation.leibniz, smul_eq_mul f (D g), smul_eq_mul g (D f)]
    exact (map_add (Ideal.Quotient.mk _) _ _).trans (by rw [map_mul, map_mul]; rfl)

@[simp]
theorem adicCompletion_val (x : AdicCompletion I R) (n : ℕ) :
    (D.adicCompletion I x).val n = D.adicLevel I n (x.val (n + 1)) :=
  rfl

/-- The extended derivation restricts to `D` along the canonical map `R → R̂`. -/
theorem adicCompletion_of (f : R) :
    D.adicCompletion I (AdicCompletion.of I R f) = AdicCompletion.of I R (D f) := by
  apply AdicCompletion.ext
  intro n
  rw [adicCompletion_val, AdicCompletion.of_apply, AdicCompletion.of_apply, Submodule.mkQ_apply,
    Submodule.mkQ_apply, adicLevel_mk]

/-- `D̂ ∘ ι = ι ∘ D` for the algebra map `ι : R → R̂`. -/
theorem adicCompletion_algebraMap (f : R) :
    D.adicCompletion I (algebraMap R (AdicCompletion I R) f) =
      algebraMap R (AdicCompletion I R) (D f) := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]
  exact adicCompletion_of I D f

end Derivation
