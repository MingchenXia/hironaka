/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Algebra.Local.CompletionMap
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Combinatorics.Matroid.Init

/-!
# Completions along flat local homomorphisms with trivial residue extension

The ring-theoretic content of "an étale map induces an isomorphism of completed local rings":
Włodarczyk's "since `φ` is étale … `Ô_{x',X'} ≃ Ô_{x,X}`" (the proof of [Wlo05, Lemma 2.6.5]) and
Kollár's "`ψ` is invertible after completion" (the discussion of [Kol07, Definition 91]).  A flat
local homomorphism `φ : R →+* S` with `𝔪_R S = 𝔪_S` and trivial residue field extension induces
a bijection `R̂ → Ŝ` of maximal-adic completions.  The level maps `R/𝔪_R^n → S/𝔪_S^n` are

* injective: `𝔪_S^n = 𝔪_R^n S` and `φ` is faithfully flat
  (`Module.FaithfullyFlat.of_flat_of_isLocalHom`), so `𝔪_R^n S ∩ R = 𝔪_R^n`
  (`Ideal.comap_map_eq_self_of_faithfullyFlat`; `comap_maximalIdeal_pow_of_flat`);
* surjective: `S = φ(R) + 𝔪_S` (trivial residue extension) and `𝔪_S^n = 𝔪_R^n S` give
  `S = φ(R) + 𝔪_S^n` for every `n` by induction (`exists_sub_mem_maximalIdeal_pow`, the graded
  step `exists_mem_sub_mem_maximalIdeal_pow_succ`);

and the completions are the limits: injectivity by `AdicCompletion.ext_evalₐ`, surjectivity by the
right inverse `completionInv` assembled from the inverse level maps with
`AdicCompletion.liftRingHom`.  No Noetherian hypothesis is needed.  In addition, `completionMap φ`
carries `I R̂` to `φ(I) Ŝ` (`map_completionMap_map`).  These are the tools for passing from the
formal to the étale case of the equivalence of hypersurfaces of maximal contact, where the key
point, in Kollár's words, is "to realize the automorphism `φ` on some étale neighborhood"
[Kol07, 95]; used in `Hironaka/Scheme/Smooth/GraphCompletion.lean`.
-/

@[expose] public section

namespace IsLocalRing

open IsLocalRing AdicCompletion

section Level

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  (φ : R →+* S) [IsLocalHom φ]

omit [IsLocalHom φ] in
/-- `𝔪_S^n = 𝔪_R^n S` when `𝔪_S = 𝔪_R S`. -/
theorem map_maximalIdeal_pow_of_map_maximalIdeal
    (hm : (maximalIdeal R).map φ = maximalIdeal S) (n : ℕ) :
    (maximalIdeal R ^ n).map φ = maximalIdeal S ^ n := by
  rw [Ideal.map_pow, hm]

/-- For a flat local `φ` with `𝔪_R S = 𝔪_S`, `𝔪_S^n ∩ R = 𝔪_R^n` (faithful flatness). -/
theorem comap_maximalIdeal_pow_of_flat (hflat : φ.Flat)
    (hm : (maximalIdeal R).map φ = maximalIdeal S) (n : ℕ) :
    (maximalIdeal S ^ n).comap φ = maximalIdeal R ^ n := by
  algebraize [φ]
  have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom φ)
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← map_maximalIdeal_pow_of_map_maximalIdeal φ hm n]
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) (maximalIdeal R ^ n)
  rwa [RingHom.algebraMap_toAlgebra] at h

/-- The level map `R/𝔪_R^n → S/𝔪_S^n` is injective. -/
theorem quotientMap_injective_of_flat (hflat : φ.Flat)
    (hm : (maximalIdeal R).map φ = maximalIdeal S) (n : ℕ) :
    Function.Injective
      (Ideal.quotientMap (maximalIdeal S ^ n) φ (maximalIdeal_pow_le_comap φ n)) :=
  Ideal.quotientMap_injective' (comap_maximalIdeal_pow_of_flat φ hflat hm n).le

/-- Trivial residue field extension: every element of `S` is congruent to an element of `φ(R)`
modulo `𝔪_S`. -/
theorem exists_sub_mem_maximalIdeal_of_surjective
    (hres : Function.Surjective (ResidueField.map φ)) (s : S) :
    ∃ r, s - φ r ∈ maximalIdeal S := by
  obtain ⟨x, hx⟩ := hres (residue S s)
  obtain ⟨r, rfl⟩ := residue_surjective x
  rw [ResidueField.map_residue] at hx
  exact ⟨r, Ideal.Quotient.eq.mp hx.symm⟩

/-- The graded step of the surjectivity of the level maps: an element of `𝔪_S^n = 𝔪_R^n S` is
congruent modulo `𝔪_S^(n+1)` to the image of an element of `𝔪_R^n`. -/
theorem exists_mem_sub_mem_maximalIdeal_pow_succ
    (hm : (maximalIdeal R).map φ = maximalIdeal S)
    (hres : Function.Surjective (ResidueField.map φ)) (n : ℕ) {m : S}
    (hmem : m ∈ maximalIdeal S ^ n) :
    ∃ r ∈ maximalIdeal R ^ n, m - φ r ∈ maximalIdeal S ^ (n + 1) := by
  rw [← map_maximalIdeal_pow_of_map_maximalIdeal φ hm n] at hmem
  refine Submodule.span_induction (p := fun m _ => ∃ r ∈ maximalIdeal R ^ n,
    m - φ r ∈ maximalIdeal S ^ (n + 1)) ?_ ?_ ?_ ?_ hmem
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, by simp⟩
  · exact ⟨0, Ideal.zero_mem _, by simp⟩
  · rintro x y _ _ ⟨r, hr, hx⟩ ⟨r', hr', hy⟩
    refine ⟨r + r', Ideal.add_mem _ hr hr', ?_⟩
    rw [map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hx hy
  · rintro s x hxs ⟨r, hr, hx⟩
    have hxm : x ∈ maximalIdeal S ^ n := by
      rw [← map_maximalIdeal_pow_of_map_maximalIdeal φ hm n]
      exact hxs
    obtain ⟨t, ht⟩ := exists_sub_mem_maximalIdeal_of_surjective φ hres s
    refine ⟨t * r, Ideal.mul_mem_left _ t hr, ?_⟩
    have h1 : (s - φ t) * x ∈ maximalIdeal S ^ (n + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul ht hxm
    have h2 : φ t * (x - φ r) ∈ maximalIdeal S ^ (n + 1) := Ideal.mul_mem_left _ _ hx
    have : s • x - φ (t * r) = (s - φ t) * x + φ t * (x - φ r) := by
      rw [smul_eq_mul, map_mul]; ring
    rw [this]
    exact Ideal.add_mem _ h1 h2

/-- `S = φ(R) + 𝔪_S^n` for every `n`. -/
theorem exists_sub_mem_maximalIdeal_pow (hm : (maximalIdeal R).map φ = maximalIdeal S)
    (hres : Function.Surjective (ResidueField.map φ)) (n : ℕ) (s : S) :
    ∃ r, s - φ r ∈ maximalIdeal S ^ n := by
  induction n generalizing s with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih s
    obtain ⟨r', -, hr'⟩ := exists_mem_sub_mem_maximalIdeal_pow_succ φ hm hres n hr
    exact ⟨r + r', by rwa [map_add, ← sub_sub]⟩

/-- The level map `R/𝔪_R^n → S/𝔪_S^n` is surjective. -/
theorem quotientMap_surjective_of_surjective (hm : (maximalIdeal R).map φ = maximalIdeal S)
    (hres : Function.Surjective (ResidueField.map φ)) (n : ℕ) :
    Function.Surjective
      (Ideal.quotientMap (maximalIdeal S ^ n) φ (maximalIdeal_pow_le_comap φ n)) := by
  intro y
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, hr⟩ := exists_sub_mem_maximalIdeal_pow φ hm hres n s
  exact ⟨Ideal.Quotient.mk _ r, by rw [Ideal.quotientMap_mk]; exact (Ideal.Quotient.eq.mpr hr).symm⟩

/-- The level maps commute with the transition maps of the two completions. -/
theorem factorPow_comp_quotientMap {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal S) hle).comp
        (Ideal.quotientMap (maximalIdeal S ^ n) φ (maximalIdeal_pow_le_comap φ n)) =
      (Ideal.quotientMap (maximalIdeal S ^ m) φ (maximalIdeal_pow_le_comap φ m)).comp
        (Ideal.Quotient.factorPow (maximalIdeal R) hle) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x => ?_)
  simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
  have h1 : Ideal.Quotient.factorPow (maximalIdeal S) hle (Ideal.Quotient.mk _ (φ x)) =
      Ideal.Quotient.mk _ (φ x) := Ideal.Quotient.factor_mk _ _
  have h2 : Ideal.Quotient.factorPow (maximalIdeal R) hle (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ x := Ideal.Quotient.factor_mk _ _
  rw [h1, h2, Ideal.quotientMap_mk]

end Level

section Completion

variable {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
  (φ : R →+* S) [IsLocalHom φ]

/-- `R̂ → Ŝ` is injective (injective level maps, `ext_evalₐ`). -/
theorem completionMap_injective_of_flat (hflat : φ.Flat)
    (hm : (maximalIdeal R).map φ = maximalIdeal S) :
    Function.Injective (completionMap φ) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine ext_evalₐ fun n => ?_
  rw [_root_.map_zero]
  apply quotientMap_injective_of_flat φ hflat hm n
  rw [_root_.map_zero, ← evalₐ_completionMap, hx, _root_.map_zero]

variable (hflat : φ.Flat) (hm : (maximalIdeal R).map φ = maximalIdeal S)
  (hres : Function.Surjective (ResidueField.map φ))

/-- The level-`n` inverse `Ŝ → S/𝔪_S^n → R/𝔪_R^n` of the bijective level map. -/
noncomputable def completionInvLevel (n : ℕ) :
    AdicCompletion (maximalIdeal S) S →+* R ⧸ maximalIdeal R ^ n :=
  ((RingEquiv.ofBijective _ ⟨quotientMap_injective_of_flat φ hflat hm n,
      quotientMap_surjective_of_surjective φ hm hres n⟩).symm :
        S ⧸ maximalIdeal S ^ n →+* R ⧸ maximalIdeal R ^ n).comp
    (evalₐ (maximalIdeal S) n : AdicCompletion (maximalIdeal S) S →+* S ⧸ maximalIdeal S ^ n)

theorem quotientMap_completionInvLevel (n : ℕ) (y : AdicCompletion (maximalIdeal S) S) :
    Ideal.quotientMap (maximalIdeal S ^ n) φ (maximalIdeal_pow_le_comap φ n)
        (completionInvLevel φ hflat hm hres n y) = evalₐ (maximalIdeal S) n y := by
  change (RingEquiv.ofBijective _ ⟨quotientMap_injective_of_flat φ hflat hm n,
      quotientMap_surjective_of_surjective φ hm hres n⟩)
    ((RingEquiv.ofBijective _ ⟨quotientMap_injective_of_flat φ hflat hm n,
      quotientMap_surjective_of_surjective φ hm hres n⟩).symm (evalₐ (maximalIdeal S) n y)) = _
  exact RingEquiv.apply_symm_apply _ _

theorem completionInvLevel_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal R) hle).comp (completionInvLevel φ hflat hm hres n) =
      completionInvLevel φ hflat hm hres m := by
  ext y
  apply quotientMap_injective_of_flat φ hflat hm m
  have h := congrArg (fun g => g (completionInvLevel φ hflat hm hres n y))
    (factorPow_comp_quotientMap φ hle)
  simp only [RingHom.comp_apply] at h
  rw [RingHom.comp_apply, ← h, quotientMap_completionInvLevel, quotientMap_completionInvLevel,
    factorPow_evalₐ]

/-- The inverse `Ŝ → R̂`, assembled from the inverse level maps. -/
noncomputable def completionInv :
    AdicCompletion (maximalIdeal S) S →+* AdicCompletion (maximalIdeal R) R :=
  AdicCompletion.liftRingHom (maximalIdeal R) (completionInvLevel φ hflat hm hres)
    fun hle => completionInvLevel_compat φ hflat hm hres hle

theorem completionMap_completionInv (y : AdicCompletion (maximalIdeal S) S) :
    completionMap φ (completionInv φ hflat hm hres y) = y := by
  refine ext_evalₐ fun n => ?_
  rw [evalₐ_completionMap, completionInv, evalₐ_liftRingHom, quotientMap_completionInvLevel]

/-- A flat local homomorphism `φ : R →+* S` of local rings with `𝔪_R S = 𝔪_S` and trivial residue
field extension induces a bijection `R̂ → Ŝ` of maximal-adic completions (the ring form of
"étale maps are invertible after completion", [Kol07, Definition 91]; the proof of
[Wlo05, Lemma 2.6.5]). -/
theorem bijective_completionMap_of_flat_of_map_maximalIdeal (hflat : φ.Flat)
    (hm : (maximalIdeal R).map φ = maximalIdeal S)
    (hres : Function.Bijective (ResidueField.map φ)) :
    Function.Bijective (completionMap φ) :=
  ⟨completionMap_injective_of_flat φ hflat hm, fun y =>
    ⟨completionInv φ hflat hm hres.2 y, completionMap_completionInv φ hflat hm hres.2 y⟩⟩

/-- The induced map on completions carries the extension `I R̂` of an ideal to the extension
`φ(I) Ŝ` of its image. -/
theorem map_completionMap_map (I : Ideal R) :
    (I.map (algebraMap R (AdicCompletion (maximalIdeal R) R))).map (completionMap φ) =
      (I.map φ).map (algebraMap S (AdicCompletion (maximalIdeal S) S)) := by
  rw [Ideal.map_map, Ideal.map_map]
  exact congrArg (fun g : R →+* AdicCompletion (maximalIdeal S) S => I.map g)
    (RingHom.ext fun a => completionMap_algebraMap φ a)

end Completion

end IsLocalRing
