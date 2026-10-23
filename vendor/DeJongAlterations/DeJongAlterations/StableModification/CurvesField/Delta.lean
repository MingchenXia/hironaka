import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Spectrum.Maximal.Basic

/-!
# The δ-invariant and ordinary points of curves

This file formalizes the local algebra of Appendix B of M. Temkin, *Stable modification of
relative curves*, J. Algebraic Geom. 19 (2010) (`references/temkin10-stable-modification`,
`semi-stable.tex`, lines 4373–4400): the number `g(x) = dim_k 𝒪_{C̃,x̃}/𝒪_{C,x}` attached to a
closed point `x` of a reduced curve `C` over a field `k` with normalization `π : C̃ → C`,
`x̃ = π⁻¹(x)`, and the characterization of ordinary points through it.

## Setting

The algebra is stated for a commutative `k`-algebra `B` (the semilocal ring `𝒪_{C̃,x̃}`, with
maximal ideals the points of `x̃`) and a `k`-subalgebra `A ⊆ B` (the local ring `𝒪_{C,x}`).
The hypotheses used are: `A` is local with residue field `k` (`x` is a `k`-point), `B` is
integral over `A` (the normalization is integral), `B` has finitely many maximal ideals, and
`B ⧸ A` is finite-dimensional over `k`.

## Main definitions

* `delta k A`: the δ-invariant `dim_k (B ⧸ A)` (Temkin's `g(x)` for closed `x`).
* `residueMap k B : B →ₗ[k] ∏_{m} B ⧸ m`: the values of elements of `B` at the points of `x̃`.
* `gluing k B`: the subalgebra of elements whose values at all points of `x̃` are equal to one
  element of `k`; when the points of `x̃` are `k`-points this is
  `{f ∈ 𝒪_{C̃,x̃} | f(x̃₁) = ⋯ = f(x̃ₙ)}`, the local ring of the curve obtained from `C̃` by gluing
  the points of `x̃` to one point (Temkin l. 4383–4387).

## Main results

* `le_gluing`: `A ⊆ gluing k B` (an element of `A` is congruent to a constant modulo the maximal
  ideal of `A`, which lies in every maximal ideal of `B`).
* `delta_add_one_eq`: `δ(A) + 1 = ∑_{m} [B/m : k] + dim_k (gluing / A)`.
* `card_le_delta_add_one`: **Temkin's inequality** `g(x) ≥ |x̃| - 1` (l. 4388–4391).
* `delta_add_one_eq_card_iff`: equality `g(x) = |x̃| - 1` holds exactly when all points of `x̃`
  are `k`-points and `A` is the gluing subalgebra (l. 4391–4397); `delta_add_one_eq_card_iff'`
  states the second condition as "every function vanishing on `x̃` lies in `A`".
* `delta_gluing`: the gluing subalgebra has `δ + 1 = ∑_{m} [B/m : k]`, so `δ = |x̃| - 1` when all
  points of `x̃` are `k`-points (the computation for ordinary points, l. 4391–4392).

Ordinary `n`-fold points are defined by Temkin through completed local rings,
`𝒪̂_{C,x} ≅ k[[T₁,…,Tₙ]]/(TᵢTⱼ)_{i≠j}`; the comparison of this completed-local form with the
gluing form used here (the first two sentences of l. 4383–4387) is not part of this file.
-/

namespace DeJongAlterations.StableModification.CurvesField

open Module

universe u v

variable (k : Type u) [Field k] (B : Type v) [CommRing B] [Algebra k B]

/-- The δ-invariant `dim_k (B ⧸ A)` of a `k`-subalgebra `A ⊆ B` (Temkin, App. B l. 4377–4378:
`g(x) = dim_k 𝒪_{C̃,x̃}/𝒪_{C,x}` for a closed point `x`). It is `0` when `B ⧸ A` is
infinite-dimensional; the results below assume finite dimension. -/
noncomputable def delta {B : Type v} [CommRing B] [Algebra k B] (A : Subalgebra k B) : ℕ :=
  finrank k (B ⧸ Subalgebra.toSubmodule A)

/-- The values `b ↦ (b mod m)_m` of elements of `B` at all maximal ideals of `B`. -/
def residueMap : B →ₗ[k] ((m : MaximalSpectrum B) → B ⧸ m.asIdeal) :=
  LinearMap.pi fun m ↦ (Ideal.Quotient.mkₐ k m.asIdeal).toLinearMap

@[simp] theorem residueMap_apply (b : B) (m : MaximalSpectrum B) :
    residueMap k B b m = Ideal.Quotient.mk m.asIdeal b :=
  rfl

/-- The *gluing subalgebra*: elements of `B` congruent to one constant `c ∈ k` modulo every
maximal ideal of `B`. For `B = 𝒪_{C̃,x̃}` with `k`-rational points `x̃ = {x̃₁, …, x̃ₙ}` it is
`{f | f(x̃₁) = ⋯ = f(x̃ₙ)}` (Temkin, App. B l. 4385–4387). -/
def gluing : Subalgebra k B where
  carrier := {b | ∃ c : k, ∀ m : MaximalSpectrum B, b - algebraMap k B c ∈ m.asIdeal}
  mul_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c * d, fun m ↦ ?_⟩
    have : a * b - algebraMap k B (c * d) =
        a * (b - algebraMap k B d) + algebraMap k B d * (a - algebraMap k B c) := by
      rw [map_mul]
      ring
    rw [this]
    exact add_mem (Ideal.mul_mem_left _ _ (hd m)) (Ideal.mul_mem_left _ _ (hc m))
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨d, hd⟩
    refine ⟨c + d, fun m ↦ ?_⟩
    have : a + b - algebraMap k B (c + d) =
        (a - algebraMap k B c) + (b - algebraMap k B d) := by
      rw [map_add]
      ring
    rw [this]
    exact add_mem (hc m) (hd m)
  algebraMap_mem' c := ⟨c, fun m ↦ by simp⟩

variable {k B}

theorem mem_gluing {b : B} :
    b ∈ gluing k B ↔ ∃ c : k, ∀ m : MaximalSpectrum B, b - algebraMap k B c ∈ m.asIdeal :=
  Iff.rfl

/-- `c • 1 = c` in a quotient of `B`. -/
theorem smul_mk_one (c : k) (I : Ideal B) :
    c • Ideal.Quotient.mk I 1 = Ideal.Quotient.mk I (algebraMap k B c) := by
  rw [Algebra.smul_def, map_one, mul_one]
  rfl

variable (k B) in
/-- The gluing subalgebra is the preimage under `residueMap` of the diagonal line
`k · (1, …, 1)`. -/
theorem toSubmodule_gluing :
    Subalgebra.toSubmodule (gluing k B) = (k ∙ residueMap k B 1).comap (residueMap k B) := by
  ext b
  simp only [Subalgebra.mem_toSubmodule, mem_gluing, Submodule.mem_comap,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, funext fun m ↦ ?_⟩
    simp only [Pi.smul_apply, residueMap_apply, smul_mk_one]
    refine Ideal.Quotient.eq.2 ?_
    rw [← neg_sub]
    exact neg_mem (hc m)
  · rintro ⟨c, hc⟩
    refine ⟨c, fun m ↦ ?_⟩
    have := congrFun hc m
    simp only [Pi.smul_apply, residueMap_apply, smul_mk_one] at this
    rw [← neg_sub]
    exact neg_mem (Ideal.Quotient.eq.1 this)

variable (k B) in
/-- **Chinese remainder theorem**: with finitely many maximal ideals, `residueMap` is onto. -/
theorem residueMap_surjective [Finite (MaximalSpectrum B)] :
    Function.Surjective (residueMap k B) := by
  intro x
  obtain ⟨b, hb⟩ := Ideal.pi_quotient_surjective
    (I := fun m : MaximalSpectrum B ↦ m.asIdeal)
    (fun m m' h ↦ MaximalSpectrum.isCoprime_of_ne h) x
  exact ⟨b, funext hb⟩

/-- **The local ring lies in the gluing subalgebra.** If `A` is local with residue field `k`
and `B` is integral over `A`, every element of `A` is congruent to a constant modulo every
maximal ideal of `B` (each maximal ideal of `B` lies over the maximal ideal of `A`). -/
theorem le_gluing (A : Subalgebra k B) [IsLocalRing A] [Algebra.IsIntegral A B]
    (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A) :
    A ≤ gluing k B := by
  intro b hb
  obtain ⟨c, hc⟩ := hres ⟨b, hb⟩
  refine ⟨c, fun m ↦ ?_⟩
  have hmax : (m.asIdeal.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) m.asIdeal
  have h' : ⟨b, hb⟩ - algebraMap k A c ∈ m.asIdeal.comap (algebraMap A B) := by
    rw [IsLocalRing.eq_maximalIdeal hmax]
    exact hc
  rw [Ideal.mem_comap, map_sub, ← IsScalarTower.algebraMap_apply] at h'
  exact h'

section Residue

theorem residueMap_one_ne_zero [Nonempty (MaximalSpectrum B)] : residueMap k B 1 ≠ 0 := by
  obtain ⟨m⟩ := ‹Nonempty (MaximalSpectrum B)›
  intro h
  have h₁ := congrFun h m
  rw [residueMap_apply, map_one, Pi.zero_apply] at h₁
  have : Nontrivial (B ⧸ m.asIdeal) := Ideal.Quotient.nontrivial_iff.2 m.isMaximal.ne_top
  exact one_ne_zero h₁

/-- A residue field `B ⧸ m` is `k` itself (the point is a `k`-point) exactly when it has
dimension one over `k`. -/
theorem finrank_residue_eq_one_iff (m : MaximalSpectrum B) :
    finrank k (B ⧸ m.asIdeal) = 1 ↔ Function.Surjective (algebraMap k (B ⧸ m.asIdeal)) := by
  have : Nontrivial (B ⧸ m.asIdeal) := Ideal.Quotient.nontrivial_iff.2 m.isMaximal.ne_top
  rw [finrank_eq_one_iff_of_nonzero' (1 : B ⧸ m.asIdeal) one_ne_zero]
  simp only [Algebra.smul_def, mul_one]
  rfl

variable (k B) in
/-- The gluing subalgebra contains every element vanishing at all maximal ideals. -/
theorem mem_gluing_of_forall_mem {b : B} (hb : ∀ m : MaximalSpectrum B, b ∈ m.asIdeal) :
    b ∈ gluing k B :=
  ⟨0, fun m ↦ by simpa using hb m⟩

/-- `A` contains the gluing subalgebra exactly when it contains every element of `B` vanishing at
all maximal ideals (the conductor-type condition `𝔪_{x̃} ⊆ 𝒪_{C,x}`). -/
theorem gluing_le_iff (A : Subalgebra k B) :
    gluing k B ≤ A ↔ ∀ b : B, (∀ m : MaximalSpectrum B, b ∈ m.asIdeal) → b ∈ A := by
  refine ⟨fun h b hb ↦ h (mem_gluing_of_forall_mem k B hb), fun h b hb ↦ ?_⟩
  obtain ⟨c, hc⟩ := hb
  have := h _ hc
  have hsum : b = (b - algebraMap k B c) + algebraMap k B c := by ring
  rw [hsum]
  exact add_mem this (A.algebraMap_mem c)

end Residue

section Count

variable [Fintype (MaximalSpectrum B)]


/-- **The δ-invariant decomposes** as the number of points of `x̃` counted with residue degree,
minus one, plus the codimension of `A` in the gluing subalgebra:
`δ(A) + 1 = ∑_{m} [B/m : k] + dim_k (gluing / A)`. -/
theorem delta_add_one_eq [Nonempty (MaximalSpectrum B)] (A : Subalgebra k B)
    (hA : A ≤ gluing k B) [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] :
    delta k A + 1 = (∑ m : MaximalSpectrum B, finrank k (B ⧸ m.asIdeal)) +
      finrank k ((Subalgebra.toSubmodule (gluing k B)).map
        (Subalgebra.toSubmodule A).mkQ) := by
  set L : Submodule k ((m : MaximalSpectrum B) → B ⧸ m.asIdeal) := k ∙ residueMap k B 1
    with hLdef
  set ψ := L.mkQ ∘ₗ residueMap k B with hψdef
  have hψ : Function.Surjective ψ :=
    (Submodule.mkQ_surjective L).comp (residueMap_surjective k B)
  have hker : LinearMap.ker ψ = Subalgebra.toSubmodule (gluing k B) := by
    rw [toSubmodule_gluing, hψdef, LinearMap.ker_comp, Submodule.ker_mkQ]
  let e₁ : (B ⧸ Subalgebra.toSubmodule (gluing k B)) ≃ₗ[k]
      ((m : MaximalSpectrum B) → B ⧸ m.asIdeal) ⧸ L :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hψ)
  set N := (Subalgebra.toSubmodule (gluing k B)).map (Subalgebra.toSubmodule A).mkQ with hN
  let e₂ : ((B ⧸ Subalgebra.toSubmodule A) ⧸ N) ≃ₗ[k] B ⧸ Subalgebra.toSubmodule (gluing k B) :=
    Submodule.quotientQuotientEquivQuotient _ _ hA
  have h₁ : finrank k ((B ⧸ Subalgebra.toSubmodule A) ⧸ N) + finrank k N =
      finrank k (B ⧸ Subalgebra.toSubmodule A) := N.finrank_quotient_add_finrank
  have : FiniteDimensional k (((m : MaximalSpectrum B) → B ⧸ m.asIdeal) ⧸ L) :=
    Module.Finite.equiv (e₂.trans e₁)
  have : FiniteDimensional k ((m : MaximalSpectrum B) → B ⧸ m.asIdeal) :=
    Module.Finite.of_submodule_quotient L
  have : ∀ m : MaximalSpectrum B, FiniteDimensional k (B ⧸ m.asIdeal) := fun m ↦ by
    classical
    exact Module.Finite.of_surjective (LinearMap.proj (R := k) (φ := fun m ↦ B ⧸ m.asIdeal) m)
      (fun y ↦ ⟨Pi.single m y, by simp⟩)
  have h₂ : finrank k (((m : MaximalSpectrum B) → B ⧸ m.asIdeal) ⧸ L) + finrank k L =
      finrank k ((m : MaximalSpectrum B) → B ⧸ m.asIdeal) := L.finrank_quotient_add_finrank
  have hL : finrank k L = 1 := finrank_span_singleton residueMap_one_ne_zero
  have hW : finrank k ((m : MaximalSpectrum B) → B ⧸ m.asIdeal) =
      ∑ m : MaximalSpectrum B, finrank k (B ⧸ m.asIdeal) := Module.finrank_pi_fintype k
  have he : finrank k ((B ⧸ Subalgebra.toSubmodule A) ⧸ N) =
      finrank k (((m : MaximalSpectrum B) → B ⧸ m.asIdeal) ⧸ L) := (e₂.trans e₁).finrank_eq
  unfold delta
  omega

/-- The residue fields of `B` are finite over `k` when `B ⧸ A` is. -/
theorem finiteDimensional_residue (A : Subalgebra k B) (hA : A ≤ gluing k B)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] (m : MaximalSpectrum B) :
    FiniteDimensional k (B ⧸ m.asIdeal) := by
  have : Nonempty (MaximalSpectrum B) := ⟨m⟩
  set L : Submodule k ((m : MaximalSpectrum B) → B ⧸ m.asIdeal) := k ∙ residueMap k B 1
  set ψ := L.mkQ ∘ₗ residueMap k B with hψdef
  have hψ : Function.Surjective ψ :=
    (Submodule.mkQ_surjective L).comp (residueMap_surjective k B)
  have hle : Subalgebra.toSubmodule A ≤ LinearMap.ker ψ := by
    rw [hψdef, LinearMap.ker_comp, Submodule.ker_mkQ, ← toSubmodule_gluing]
    exact hA
  have : FiniteDimensional k (((m : MaximalSpectrum B) → B ⧸ m.asIdeal) ⧸ L) :=
    Module.Finite.of_surjective ((Subalgebra.toSubmodule A).liftQ ψ hle)
      (fun y ↦ by
        obtain ⟨b, rfl⟩ := hψ y
        exact ⟨Submodule.Quotient.mk b, rfl⟩)
  have : FiniteDimensional k ((m : MaximalSpectrum B) → B ⧸ m.asIdeal) :=
    Module.Finite.of_submodule_quotient L
  classical
  exact Module.Finite.of_surjective (LinearMap.proj (R := k) (φ := fun m ↦ B ⧸ m.asIdeal) m)
    (fun y ↦ ⟨Pi.single m y, by simp⟩)

theorem one_le_finrank_residue (A : Subalgebra k B) (hA : A ≤ gluing k B)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] (m : MaximalSpectrum B) :
    1 ≤ finrank k (B ⧸ m.asIdeal) := by
  have := finiteDimensional_residue A hA m
  have : Nontrivial (B ⧸ m.asIdeal) := Ideal.Quotient.nontrivial_iff.2 m.isMaximal.ne_top
  exact Module.finrank_pos

variable [Nonempty (MaximalSpectrum B)]

/-- **Temkin's inequality** `g(x) ≥ |x̃| - 1` (App. B l. 4388–4391): for `A` local with residue
field `k`, `B` integral over `A` with finitely many maximal ideals and `B ⧸ A` finite over `k`,
the number of maximal ideals of `B` is at most `δ(A) + 1`. -/
theorem card_le_delta_add_one (A : Subalgebra k B) (hA : A ≤ gluing k B)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] :
    Fintype.card (MaximalSpectrum B) ≤ delta k A + 1 := by
  rw [delta_add_one_eq A hA]
  have : Fintype.card (MaximalSpectrum B) ≤ ∑ m : MaximalSpectrum B, finrank k (B ⧸ m.asIdeal) := by
    rw [Fintype.card_eq_sum_ones]
    exact Finset.sum_le_sum fun m _ ↦ one_le_finrank_residue A hA m
  omega

/-- **Equality in Temkin's inequality** (App. B l. 4391–4397): `g(x) = |x̃| - 1` exactly when all
points of `x̃` are `k`-points and `A` is the gluing subalgebra, i.e. `𝒪_{C,x}` consists of the
functions on `C̃` near `x̃` taking the same value at all points of `x̃`. -/
theorem delta_add_one_eq_card_iff (A : Subalgebra k B) (hA : A ≤ gluing k B)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] :
    delta k A + 1 = Fintype.card (MaximalSpectrum B) ↔
      (∀ m : MaximalSpectrum B, Function.Surjective (algebraMap k (B ⧸ m.asIdeal))) ∧
        A = gluing k B := by
  rw [delta_add_one_eq A hA, Fintype.card_eq_sum_ones]
  have hge := fun m : MaximalSpectrum B ↦ one_le_finrank_residue A hA m
  constructor
  · intro h
    have hsum : ∑ m : MaximalSpectrum B, finrank k (B ⧸ m.asIdeal) =
        ∑ m : MaximalSpectrum B, 1 := by
      have := Finset.sum_le_sum (s := Finset.univ) fun m _ ↦ hge m
      omega
    have hN : finrank k ((Subalgebra.toSubmodule (gluing k B)).map
        (Subalgebra.toSubmodule A).mkQ) = 0 := by omega
    have hall : ∀ m : MaximalSpectrum B, finrank k (B ⧸ m.asIdeal) = 1 := by
      intro m
      have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) fun m _ ↦ hge m).1 hsum.symm m
        (Finset.mem_univ m)
      omega
    refine ⟨fun m ↦ (finrank_residue_eq_one_iff m).1 (hall m), le_antisymm hA fun b hb ↦ ?_⟩
    rw [Submodule.finrank_eq_zero] at hN
    have : (Subalgebra.toSubmodule A).mkQ b = 0 := by
      have := Submodule.mem_map_of_mem (f := (Subalgebra.toSubmodule A).mkQ)
        (show b ∈ Subalgebra.toSubmodule (gluing k B) from hb)
      rw [hN] at this
      exact (Submodule.mem_bot k).1 this
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  · rintro ⟨hres, rfl⟩
    have hall : ∀ m : MaximalSpectrum B, finrank k (B ⧸ m.asIdeal) = 1 := fun m ↦
      (finrank_residue_eq_one_iff m).2 (hres m)
    rw [Finset.sum_congr rfl fun m _ ↦ hall m, Submodule.mkQ_map_self, finrank_bot, add_zero]

/-- **Equality in Temkin's inequality**, conductor form: `g(x) = |x̃| - 1` exactly when all
points of `x̃` are `k`-points and every function on `C̃` vanishing at all points of `x̃` lies
in `𝒪_{C,x}`. -/
theorem delta_add_one_eq_card_iff' (A : Subalgebra k B) (hA : A ≤ gluing k B)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] :
    delta k A + 1 = Fintype.card (MaximalSpectrum B) ↔
      (∀ m : MaximalSpectrum B, Function.Surjective (algebraMap k (B ⧸ m.asIdeal))) ∧
        ∀ b : B, (∀ m : MaximalSpectrum B, b ∈ m.asIdeal) → b ∈ A := by
  rw [delta_add_one_eq_card_iff A hA, ← gluing_le_iff]
  exact and_congr_right fun _ ↦ ⟨fun h ↦ h ▸ le_rfl, fun h ↦ le_antisymm hA h⟩

/-- **The gluing subalgebra realizes equality**: if all residue fields of `B` are finite over
`k`, then `δ(gluing) + 1 = ∑_{m} [B/m : k]`; in particular `δ = |x̃| - 1` when all points of `x̃`
are `k`-points (Temkin l. 4391–4392: "if `x` is ordinary then `φ` is bijective"). -/
theorem delta_gluing [∀ m : MaximalSpectrum B, FiniteDimensional k (B ⧸ m.asIdeal)] :
    ∃ _ : FiniteDimensional k (B ⧸ Subalgebra.toSubmodule (gluing k B)),
      delta k (gluing k B) + 1 = ∑ m : MaximalSpectrum B, finrank k (B ⧸ m.asIdeal) := by
  set L : Submodule k ((m : MaximalSpectrum B) → B ⧸ m.asIdeal) := k ∙ residueMap k B 1
  set ψ := L.mkQ ∘ₗ residueMap k B with hψdef
  have hψ : Function.Surjective ψ :=
    (Submodule.mkQ_surjective L).comp (residueMap_surjective k B)
  have hker : LinearMap.ker ψ = Subalgebra.toSubmodule (gluing k B) := by
    rw [toSubmodule_gluing, hψdef, LinearMap.ker_comp, Submodule.ker_mkQ]
  let e₁ : (B ⧸ Subalgebra.toSubmodule (gluing k B)) ≃ₗ[k]
      ((m : MaximalSpectrum B) → B ⧸ m.asIdeal) ⧸ L :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (ψ.quotKerEquivOfSurjective hψ)
  have : FiniteDimensional k (B ⧸ Subalgebra.toSubmodule (gluing k B)) :=
    Module.Finite.equiv e₁.symm
  refine ⟨inferInstance, ?_⟩
  rw [delta_add_one_eq (gluing k B) le_rfl, Submodule.mkQ_map_self, finrank_bot, add_zero]

end Count

section Local

/-- A nontrivial subalgebra forces `B` to have a maximal ideal. -/
theorem nonempty_maximalSpectrum (A : Subalgebra k B) [Nontrivial A] :
    Nonempty (MaximalSpectrum B) := by
  have : Nontrivial B := ⟨⟨0, 1, fun h ↦ zero_ne_one (Subtype.ext h : (0 : A) = 1)⟩⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  exact ⟨⟨m, hm⟩⟩

variable [Fintype (MaximalSpectrum B)]

/-- **Temkin's inequality `g(x) ≥ |x̃| - 1`** (App. B l. 4388–4391) under Temkin's hypotheses:
`A = 𝒪_{C,x}` is local with residue field `k` (`x` is a `k`-point), `B = 𝒪_{C̃,x̃}` is integral
over `A` with finitely many maximal ideals (the points of `x̃`), and `B ⧸ A` is finite over `k`. -/
theorem card_le_delta_add_one_of_isLocalRing (A : Subalgebra k B) [IsLocalRing A]
    [Algebra.IsIntegral A B]
    (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] :
    Fintype.card (MaximalSpectrum B) ≤ delta k A + 1 :=
  have := nonempty_maximalSpectrum A
  card_le_delta_add_one A (le_gluing A hres)

/-- **Ordinary points through the δ-invariant** (App. B l. 4388–4397), under Temkin's
hypotheses: `g(x) = |x̃| - 1` if and only if all points of `x̃` are `k`-points and `𝒪_{C,x}` is the
ring of functions on `C̃` near `x̃` taking the same value at all points of `x̃`. -/
theorem delta_add_one_eq_card_iff_of_isLocalRing (A : Subalgebra k B) [IsLocalRing A]
    [Algebra.IsIntegral A B]
    (hres : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ IsLocalRing.maximalIdeal A)
    [FiniteDimensional k (B ⧸ Subalgebra.toSubmodule A)] :
    delta k A + 1 = Fintype.card (MaximalSpectrum B) ↔
      (∀ m : MaximalSpectrum B, Function.Surjective (algebraMap k (B ⧸ m.asIdeal))) ∧
        A = gluing k B :=
  have := nonempty_maximalSpectrum A
  delta_add_one_eq_card_iff A (le_gluing A hres)

end Local

end DeJongAlterations.StableModification.CurvesField
