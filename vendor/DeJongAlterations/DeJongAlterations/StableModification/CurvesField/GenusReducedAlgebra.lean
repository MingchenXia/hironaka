/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.GenusNormalization
import DeJongAlterations.Algebra.IntegralClosureFiniteType

/-!
# The normalization of a reduced one-dimensional algebra

Let `A` be a commutative algebra of finite type over a field `k` with `dim A ≤ 1`, and let
`(𝔭ᵢ)_{i ∈ I}` be a finite family of pairwise incomparable primes of `A` containing all minimal
primes, with fields `Kᵢ` which are fraction fields of `A ⧸ 𝔭ᵢ` (`IsGenericFamily`; the fraction
field condition alone is `IsFractionFamily`). For a reduced curve `C` and an affine open
`V = Spec A` these are the generic points of `C` in `V` with their residue fields `κ(η)`, and
`∏ᵢ Kᵢ` is the total ring of fractions of `A`.

For an `A`-algebra `B` integral over `A` with an injective `A`-algebra map `B → ∏ᵢ Kᵢ` (for
instance the integral closure of `A` in `∏ᵢ Kᵢ`, the coordinate ring of the normalization over `V`):

* `IsFractionFamily.finite_of_injective`, `IsGenericFamily.finite_of_injective`: `B` is a finite
  `A`-module (the integral closure of each `A ⧸ 𝔭ᵢ` in `Kᵢ` is finite, Codex's
  `IntegralClosureFiniteType.finite_integralClosure`; `IsFractionFamily.finite_integralClosure`);
* `IsGenericFamily.exists_smul_mem_range`: `B` and `A` agree at the generic points: for every
  `b ∈ B` and every `i` some `t ∉ 𝔭ᵢ` has `t • b ∈ A`;
* `IsGenericFamily.finiteDimensional_coker`: `B ⧸ A` is finite-dimensional over `k` (its
  annihilator lies in no minimal prime, so `A` modulo the annihilator is Artinian of finite type);
* `IsGenericFamily.injective_algebraMap`: if `A` is reduced, `A → ∏ᵢ Kᵢ` is injective.

These are the hypotheses of the δ-formula (`GenusFormula.eulerChar_eq_add_finsum_delta`) for the
normalization of a reduced curve, verified on affine charts in `GenusReduced`. This generalizes the
integral case `GenusNormalization.finiteDimensional_coker_of_isFractionRing` (one prime `𝔭 = 0`).
This is the algebra behind Temkin's Lemma B.1 for reducible curves (M. Temkin, *Stable
modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, l. 4413–4433: "the sheaf
`π_*𝒪_{C̃}/𝒪_C` is a skyscraper because `π` is an isomorphism over non-closed points").

Blueprint: `sm-curves-fields-genus-reduced.tex`, `lem:sm-reduced-normalization-algebra`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open Module

set_option autoImplicit false

universe u

section Family

variable {A : Type u} [CommRing A] {ι : Type u} (p : ι → Ideal A) (K : ι → Type u)
  [∀ i, Field (K i)] [∀ i, Algebra A (K i)]

/-- A *fraction family* of a ring `A`: fields `Kᵢ` over `A` such that `A → Kᵢ` has kernel `𝔭ᵢ`
and every element of `Kᵢ` is a fraction `a / t` with `t ∉ 𝔭ᵢ` (so `Kᵢ = Frac(A ⧸ 𝔭ᵢ)`). For an
affine open `Spec A` of a scheme: any set of points of `Spec A` with their residue fields. -/
structure IsFractionFamily : Prop where
  ker_eq : ∀ i, RingHom.ker (algebraMap A (K i)) = p i
  exists_mul_eq : ∀ i (z : K i), ∃ a t : A, t ∉ p i ∧
    algebraMap A (K i) t * z = algebraMap A (K i) a

/-- A *generic family* of a ring `A`: a fraction family whose primes `𝔭ᵢ` are pairwise
incomparable and contain every minimal prime. For an affine open `Spec A` of a scheme with finitely
many irreducible components: the generic points in `Spec A` and their residue fields. -/
structure IsGenericFamily : Prop extends IsFractionFamily p K where
  incomparable : ∀ i j, i ≠ j → ¬ p i ≤ p j
  covers : ∀ q ∈ minimalPrimes A, ∃ i, p i = q

variable {p K}

namespace IsFractionFamily

variable (h : IsFractionFamily p K)
include h

theorem isPrime (i : ι) : (p i).IsPrime := by
  rw [← h.ker_eq i]
  exact RingHom.ker_isPrime _

theorem algebraMap_eq_zero_iff (i : ι) (a : A) : algebraMap A (K i) a = 0 ↔ a ∈ p i := by
  rw [← h.ker_eq i, RingHom.mem_ker]

end IsFractionFamily

namespace IsGenericFamily

variable (h : IsGenericFamily p K)
include h

theorem isPrime (i : ι) : (p i).IsPrime := h.toIsFractionFamily.isPrime i

theorem algebraMap_eq_zero_iff (i : ι) (a : A) : algebraMap A (K i) a = 0 ↔ a ∈ p i :=
  h.toIsFractionFamily.algebraMap_eq_zero_iff i a

/-- An element outside `𝔭ᵢ` lying in all the other primes of the family. -/
theorem exists_mem_of_ne [Finite ι] (i : ι) : ∃ s : A, s ∉ p i ∧ ∀ j, j ≠ i → s ∈ p j := by
  classical
  have := Fintype.ofFinite ι
  have hsel : ∀ j, j ≠ i → ∃ s, s ∈ p j ∧ s ∉ p i := fun j hj =>
    Set.not_subset.mp (h.incomparable j i hj)
  choose s hs using hsel
  let t : ι → A := fun j => if hj : j = i then 1 else s j hj
  have hpi := h.isPrime i
  refine ⟨∏ j ∈ Finset.univ.erase i, t j, ?_, fun j hj => ?_⟩
  · rw [hpi.prod_mem_iff]
    rintro ⟨j, hj, hjmem⟩
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp only [t, dif_neg hji] at hjmem
    exact (hs j hji).2 hjmem
  · rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)]
    refine Ideal.mul_mem_right _ _ ?_
    simp only [t, dif_neg hj]
    exact (hs j hj).1

variable {B : Type u} [CommRing B] [Algebra A B] (Φ : B →ₐ[A] (∀ i, K i))

/-- **`B` and `A` agree at the generic points**: for an injective `A`-algebra map
`Φ : B → ∏ᵢ Kᵢ`, every `b ∈ B` and every `i`, some `t ∉ 𝔭ᵢ` has `t • b ∈ A`. -/
theorem exists_smul_mem_range [Finite ι] (hΦ : Function.Injective Φ) (i : ι) (b : B) :
    ∃ t : A, t ∉ p i ∧ t • b ∈ LinearMap.range (Algebra.linearMap A B) := by
  obtain ⟨s, hs, hsj⟩ := h.exists_mem_of_ne i
  obtain ⟨a, t, ht, hta⟩ := h.exists_mul_eq i (Φ b i)
  have hpi := h.isPrime i
  refine ⟨s * t, fun hst => (hpi.mem_or_mem hst).elim hs ht, s * a, hΦ ?_⟩
  funext j
  simp only [Algebra.linearMap_apply, AlgHom.commutes, Algebra.smul_def, map_mul, Pi.mul_apply,
    Pi.algebraMap_apply]
  by_cases hji : j = i
  · subst hji
    rw [mul_assoc, hta]
  · rw [(h.algebraMap_eq_zero_iff j s).2 (hsj j hji), zero_mul, zero_mul, zero_mul]

end IsGenericFamily

end Family

section Finite

variable (k : Type u) [Field k] {A : Type u} [CommRing A] [Algebra k A] {ι : Type u}
  {p : ι → Ideal A} {K : ι → Type u} [∀ i, Field (K i)] [∀ i, Algebra A (K i)]

namespace IsFractionFamily

variable (h : IsFractionFamily p K)
include h

/-- `A ⧸ 𝔭ᵢ → Kᵢ`. -/
noncomputable abbrev quotientAlgebra (i : ι) : Algebra (A ⧸ p i) (K i) :=
  (Ideal.Quotient.lift (p i) (algebraMap A (K i)) fun a ha =>
    (h.algebraMap_eq_zero_iff i a).2 ha).toAlgebra

theorem quotient_isScalarTower (i : ι) :
    letI := h.quotientAlgebra i
    IsScalarTower A (A ⧸ p i) (K i) :=
  letI := h.quotientAlgebra i
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- `Kᵢ` is a fraction field of `A ⧸ 𝔭ᵢ`. -/
theorem isFractionRing (i : ι) :
    letI := h.quotientAlgebra i
    IsFractionRing (A ⧸ p i) (K i) := by
  let := h.quotientAlgebra i
  have hpi := h.isPrime i
  have hinj : Function.Injective (algebraMap (A ⧸ p i) (K i)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change algebraMap A (K i) a = 0 at hx
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((h.algebraMap_eq_zero_iff i a).1 hx)
  refine ⟨fun y => ?_, fun z => ?_, fun {x y} hxy => ?_⟩
  · exact IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero y.2))
  · obtain ⟨a, t, ht, hta⟩ := h.exists_mul_eq i z
    refine ⟨⟨Ideal.Quotient.mk _ a, ⟨Ideal.Quotient.mk _ t, mem_nonZeroDivisors_of_ne_zero
      (fun h0 => ht (Ideal.Quotient.eq_zero_iff_mem.1 h0))⟩⟩, ?_⟩
    change z * algebraMap A (K i) t = algebraMap A (K i) a
    rw [mul_comm, hta]
  · exact ⟨1, by rw [hinj hxy]⟩

/-- The integral closure of `A` in `Kᵢ` is a finite `A`-module (it is the integral closure of the
finite type domain `A ⧸ 𝔭ᵢ` in its fraction field). -/
theorem finite_integralClosure [Algebra.FiniteType k A] (i : ι) :
    Module.Finite A (integralClosure A (K i)) := by
  let := h.quotientAlgebra i
  have hpi := h.isPrime i
  have := h.isFractionRing i
  have : Algebra.FiniteType k (A ⧸ p i) :=
    Algebra.FiniteType.trans (S := A) inferInstance inferInstance
  have := h.quotient_isScalarTower i
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : Module.Finite (A ⧸ p i) (integralClosure (A ⧸ p i) (K i)) :=
    DeJongAlterations.Algebra.IntegralClosureFiniteType.finite_integralClosure k (A ⧸ p i) (K i)
  have : Module.Finite A (integralClosure (A ⧸ p i) (K i)) := Module.Finite.trans (A ⧸ p i) _
  let ψ : integralClosure A (K i) →ₗ[A] integralClosure (A ⧸ p i) (K i) :=
    { toFun := fun z => ⟨z.1, z.2.tower_top⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective ψ fun z w hzw =>
    Subtype.ext (congrArg Subtype.val hzw : (ψ z).1 = (ψ w).1)

variable {B : Type u} [CommRing B] [Algebra A B] (Φ : B →ₐ[A] (∀ i, K i))

/-- **The normalization is finite.** An `A`-algebra `B` integral over `A` with an injective map
to `∏ᵢ Kᵢ` is a finite `A`-module. -/
theorem finite_of_injective [Algebra.FiniteType k A] [Finite ι] [Algebra.IsIntegral A B]
    (hΦ : Function.Injective Φ) : Module.Finite A B := by
  classical
  have := Fintype.ofFinite ι
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have := fun i => h.finite_integralClosure k i
  let ψ : B →ₗ[A] ∀ i, integralClosure A (K i) :=
    { toFun := fun b i => ⟨Φ b i,
        (Algebra.IsIntegral.isIntegral b).map ((Pi.evalAlgHom A K i).comp Φ)⟩
      map_add' := fun b c => by
        funext i
        apply Subtype.ext
        simp
      map_smul' := fun a b => by
        funext i
        apply Subtype.ext
        simp }
  refine Module.Finite.of_injective ψ fun b c hbc => hΦ ?_
  funext i
  exact congrArg Subtype.val (congrFun hbc i)

end IsFractionFamily

namespace IsGenericFamily

variable (h : IsGenericFamily p K)
include h

variable {B : Type u} [CommRing B] [Algebra A B] (Φ : B →ₐ[A] (∀ i, K i))

theorem finite_of_injective [Algebra.FiniteType k A] [Finite ι] [Algebra.IsIntegral A B]
    (hΦ : Function.Injective Φ) : Module.Finite A B :=
  h.toIsFractionFamily.finite_of_injective k Φ hΦ

/-- **`B ⧸ A` is finite-dimensional.** For `A` of finite type over `k` with `dim A ≤ 1` and an
integral `A`-algebra `B` with an injective map to `∏ᵢ Kᵢ`, the cokernel `B ⧸ A` is
finite-dimensional over `k`: its annihilator `J` lies in no minimal prime (`B` and `A` agree at the
generic points), so every prime containing `J` is maximal, `A ⧸ J` is Artinian of finite type,
hence finite over `k`, and `B ⧸ A` is a finitely generated `A ⧸ J`-module. -/
theorem finiteDimensional_coker [Algebra.FiniteType k A] [Ring.KrullDimLE 1 A] [Finite ι]
    [Algebra.IsIntegral A B] [Algebra k B] [IsScalarTower k A B] (hΦ : Function.Injective Φ) :
    FiniteDimensional k (Coker A B) := by
  classical
  have hfin : Module.Finite A B := h.finite_of_injective k Φ hΦ
  let J : Ideal A := Module.annihilator A (Coker A B)
  -- elements killing `B ⧸ A` outside each `𝔭ᵢ`
  have hJ : ∀ i, ¬ J ≤ p i := by
    intro i hle
    obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := B)
    have hsel : ∀ b : B, ∃ t : A, t ∉ p i ∧ t • b ∈ LinearMap.range (Algebra.linearMap A B) :=
      fun b => h.exists_smul_mem_range Φ hΦ i b
    choose t ht htb using hsel
    have hpi := h.isPrime i
    refine (show ∏ b ∈ S, t b ∉ p i from fun hmem => ?_) (hle ?_)
    · obtain ⟨b, -, hb⟩ := hpi.prod_mem_iff.1 hmem
      exact ht b hb
    · rw [Module.mem_annihilator]
      intro z
      induction z using Submodule.Quotient.induction_on with
      | H y =>
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      have hy : y ∈ Submodule.span A (S : Set B) := hS ▸ Submodule.mem_top
      induction hy using Submodule.span_induction with
      | mem x hx =>
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_coe.1 hx), mul_smul]
        exact Submodule.smul_mem _ _ (htb x)
      | zero => rw [smul_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  -- `A ⧸ J` is zero-dimensional, hence finite over `k`
  have hdim0 : Ring.KrullDimLE 0 (A ⧸ J) := by
    rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
    intro P hP
    have hprime : P.IsPrime := hP.1.1
    rcases (Ring.krullDimLE_one_iff.1 inferInstance) P hprime with hmin | hmax
    · obtain ⟨i, rfl⟩ := h.covers P hmin
      exact absurd hP.1.2 (hJ i)
    · exact hmax
  have : Algebra.FiniteType k (A ⧸ J) := Algebra.FiniteType.trans (S := A) inferInstance
    inferInstance
  have : Module.Finite k (A ⧸ J) := (Module.finite_iff_krullDimLE_zero k (A ⧸ J)).2 hdim0
  -- `B ⧸ A` is a quotient of `(A ⧸ J)^S`
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := A) (M := B)
  let q : S → Coker A B := fun b => Submodule.Quotient.mk (b : B)
  have hker : ∀ b : S, J ≤ LinearMap.ker (LinearMap.toSpanSingleton A _ (q b)) := by
    intro b a ha
    simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
    exact (Module.mem_annihilator.1 ha) (q b)
  let Ψ : (S → A ⧸ J) →ₗ[A] Coker A B :=
    ∑ b : S, (J.liftQ (LinearMap.toSpanSingleton A _ (q b)) (hker b)) ∘ₗ LinearMap.proj b
  have hΨ : Function.Surjective Ψ := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H y =>
    have hy : y ∈ Submodule.span A (S : Set B) := hS ▸ Submodule.mem_top
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hy
    refine ⟨fun b => Ideal.Quotient.mk _ (c b), ?_⟩
    rw [← hc]
    simp only [Ψ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [show (Submodule.Quotient.mk (∑ a ∈ S, c a • a) : Coker A B) =
      ∑ a ∈ S, Submodule.Quotient.mk (c a • a) from map_sum (Submodule.mkQ _) _ _,
      ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun b _ => ?_
    change J.liftQ _ _ (Submodule.Quotient.mk (c b)) = _
    rw [Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, Submodule.Quotient.mk_smul]
  exact Module.Finite.of_surjective (Ψ.restrictScalars k) hΨ

end IsGenericFamily

end Finite

section Injective

variable {A : Type u} [CommRing A] {ι : Type u} {p : ι → Ideal A} {K : ι → Type u}
  [∀ i, Field (K i)] [∀ i, Algebra A (K i)]

/-- **A reduced ring embeds into the product of its generic residue fields.** -/
theorem IsGenericFamily.injective_algebraMap (h : IsGenericFamily p K) [IsReduced A] :
    Function.Injective (algebraMap A (∀ i, K i)) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hall : ∀ i, a ∈ p i := fun i =>
    (h.algebraMap_eq_zero_iff i a).1 (by simpa using congrFun ha i)
  have hnil : a ∈ nilradical A := by
    rw [nilradical, ← Ideal.sInf_minimalPrimes]
    refine Submodule.mem_sInf.2 fun q hq => ?_
    obtain ⟨i, rfl⟩ := h.covers q hq
    exact hall i
  exact (IsNilpotent.eq_zero hnil)

end Injective

end DeJongAlterations.StableModification.CurvesField.Genus
