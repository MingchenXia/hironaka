/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Ideal.Height

/-!
# Localizing the normalization data at a prime

The local theorems of `CurvesField.OrdinaryCompletion` are stated for a local ring `A`, a finite
`A`-algebra `B ⊇ A` with a conductor element `s` (`s B ⊆ A`), and an `A`-algebra `L ⊇ B` in which
`s` is invertible and in which `B` is integrally closed. For the normalization of a reduced curve
these data are available on an affine chart `V = Spec R` (with `B = ` the integral closure of `R`
in the product `T` of the residue fields at the generic points), and this file transports them to
the localizations `R_P`, `S_P`, `T_P` at a prime `P` of `R` (the local ring at the point of `P`):

* `localizedAlgHom ι P : S_P →ₐ[R_P] T_P` and its injectivity `localizedAlgHom_injective`;
* `algebraMap_localization_injective`: `R → S` injective gives `R_P → S_P` injective;
* `exists_smul_eq_algebraMap_localization`: the conductor property passes to `S_P`;
* `mem_range_localizedAlgHom_of_isIntegral`: **if `S` is integrally closed in `T` over `R`, then
  `S_P` is integrally closed in `T_P` over `R_P`**.

This is commutative algebra in support of M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010) (`references/temkin10-stable-modification/source/semi-stable.tex`,
App. B, l. 4371–4397), where all computations at a point `x` of a curve are made in the local ring
`𝒪_{C,x}` and the semilocal ring `𝒪_{C̃,x̃}`.

Blueprint: `sm-curves-fields-stabdown.tex`, `lem:sm-stabdown-localize`.
-/

namespace DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion

open IsLocalization IsLocalRing
open DeJongAlterations.Algebra.NodeGeometricCompletionFormalUV
open DeJongAlterations.Algebra.CompletionRegularityBasics

set_option autoImplicit false

noncomputable section

section LocalizationTransfer

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  (ι : S →ₐ[R] T) (P : Ideal R) [P.IsPrime]

lemma algebraMapSubmonoid_le_comap :
    Algebra.algebraMapSubmonoid S P.primeCompl ≤
      (Algebra.algebraMapSubmonoid T P.primeCompl).comap ι.toRingHom := by
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m, hm, (ι.commutes m).symm⟩

/-- The map `S_P → T_P` of localizations at `P` induced by an `R`-algebra map `ι : S → T`. -/
def localizedAlgHom :
    Localization (Algebra.algebraMapSubmonoid S P.primeCompl) →ₐ[Localization.AtPrime P]
      Localization (Algebra.algebraMapSubmonoid T P.primeCompl) where
  toRingHom := IsLocalization.map _ ι.toRingHom (algebraMapSubmonoid_le_comap ι P)
  commutes' x := by
    have h : (IsLocalization.map (Localization (Algebra.algebraMapSubmonoid T P.primeCompl))
        ι.toRingHom (algebraMapSubmonoid_le_comap ι P)).comp
          (algebraMap (Localization.AtPrime P)
            (Localization (Algebra.algebraMapSubmonoid S P.primeCompl))) =
        algebraMap (Localization.AtPrime P)
          (Localization (Algebra.algebraMapSubmonoid T P.primeCompl)) := by
      refine IsLocalization.ringHom_ext P.primeCompl ?_
      ext r
      simp only [RingHom.coe_comp, Function.comp_apply]
      have e1 : algebraMap (Localization.AtPrime P)
          (Localization (Algebra.algebraMapSubmonoid S P.primeCompl))
            (algebraMap R (Localization.AtPrime P) r) =
          algebraMap S (Localization (Algebra.algebraMapSubmonoid S P.primeCompl))
            (algebraMap R S r) := by
        rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime P),
          IsScalarTower.algebraMap_apply R S]
      have e2 : algebraMap (Localization.AtPrime P)
          (Localization (Algebra.algebraMapSubmonoid T P.primeCompl))
            (algebraMap R (Localization.AtPrime P) r) =
          algebraMap T (Localization (Algebra.algebraMapSubmonoid T P.primeCompl))
            (algebraMap R T r) := by
        rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime P),
          IsScalarTower.algebraMap_apply R T]
      rw [e1, e2, IsLocalization.map_eq]
      congr 1
      exact ι.commutes r
    exact congrArg (fun f => f x) h

lemma localizedAlgHom_algebraMap (b : S) :
    localizedAlgHom ι P (algebraMap S (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) b) =
      algebraMap T (Localization (Algebra.algebraMapSubmonoid T P.primeCompl)) (ι b) :=
  IsLocalization.map_eq (M := Algebra.algebraMapSubmonoid S P.primeCompl)
    (S := Localization (Algebra.algebraMapSubmonoid S P.primeCompl))
    (Q := Localization (Algebra.algebraMapSubmonoid T P.primeCompl))
    (algebraMapSubmonoid_le_comap ι P) b

lemma map_algebraMapSubmonoid :
    (Algebra.algebraMapSubmonoid S P.primeCompl).map ι.toRingHom =
      Algebra.algebraMapSubmonoid T P.primeCompl := by
  ext x
  simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m, hm, (ι.commutes m).symm⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨algebraMap R S m, ⟨m, hm, rfl⟩, ι.commutes m⟩

/-- The localization of an injective algebra map is injective. -/
lemma localizedAlgHom_injective (hι : Function.Injective ι) :
    Function.Injective (localizedAlgHom ι P) := by
  have : IsLocalization ((Algebra.algebraMapSubmonoid S P.primeCompl).map ι.toRingHom)
      (Localization (Algebra.algebraMapSubmonoid T P.primeCompl)) := by
    rw [map_algebraMapSubmonoid]
    infer_instance
  show Function.Injective (IsLocalization.map (M := Algebra.algebraMapSubmonoid S P.primeCompl)
    (S := Localization (Algebra.algebraMapSubmonoid S P.primeCompl))
    (Localization (Algebra.algebraMapSubmonoid T P.primeCompl)) ι.toRingHom
    (algebraMapSubmonoid_le_comap ι P))
  exact IsLocalization.map_injective_of_injective (Algebra.algebraMapSubmonoid S P.primeCompl)
    (Localization (Algebra.algebraMapSubmonoid S P.primeCompl))
    (Localization (Algebra.algebraMapSubmonoid T P.primeCompl)) hι

/-- The localization of an injective algebra map `R → S` at a prime of `R` is injective. -/
lemma algebraMap_localization_injective (hRS : Function.Injective (algebraMap R S)) :
    Function.Injective (algebraMap (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid S P.primeCompl))) := by
  exact localizationAlgebra_injective (M := P.primeCompl) (Localization.AtPrime P)
    (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) hRS

/-- **The conductor property localizes**: if `s S ⊆ R`, then `s S_P ⊆ R_P`. -/
lemma exists_smul_eq_algebraMap_localization {s : R}
    (hsS : ∀ b : S, ∃ a : R, s • b = algebraMap R S a)
    (b : Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) :
    ∃ a : Localization.AtPrime P, algebraMap R (Localization.AtPrime P) s • b =
      algebraMap (Localization.AtPrime P) _ a := by
  obtain ⟨⟨b', ⟨_, ⟨m, hm, rfl⟩⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid S P.primeCompl) b
  obtain ⟨a, ha⟩ := hsS b'
  refine ⟨IsLocalization.mk' (Localization.AtPrime P) a (⟨m, hm⟩ : P.primeCompl), ?_⟩
  have hu := IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid S P.primeCompl))
    (⟨algebraMap R S m, ⟨m, hm, rfl⟩⟩ : Algebra.algebraMapSubmonoid S P.primeCompl)
  have hsc : ∀ r : R, algebraMap (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) (algebraMap R _ r) =
      algebraMap S (Localization (Algebra.algebraMapSubmonoid S P.primeCompl)) (algebraMap R S r) :=
    fun r => by
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime P),
        IsScalarTower.algebraMap_apply R S]
  refine hu.mul_right_cancel ?_
  simp only
  rw [smul_mul_assoc, IsLocalization.mk'_spec, Algebra.smul_def, hsc, ← map_mul,
    ← Algebra.smul_def, ha, ← hsc m, ← map_mul, IsLocalization.mk'_spec, hsc]

/-- The image of a unit is a unit. -/
lemma isUnit_algebraMap_localization {s : R} (hsT : IsUnit (algebraMap R T s)) :
    IsUnit (algebraMap (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid T P.primeCompl))
        (algebraMap R (Localization.AtPrime P) s)) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R T]
  exact hsT.map _

/-- **Integral closedness localizes**: if every element of `T` integral over `R` lies in `ι(S)`,
then every element of `T_P` integral over `R_P` lies in the image of `S_P`. -/
lemma mem_range_localizedAlgHom_of_isIntegral (hint : ∀ y : T, IsIntegral R y → y ∈ ι.range)
    (y : Localization (Algebra.algebraMapSubmonoid T P.primeCompl))
    (hy : IsIntegral (Localization.AtPrime P) y) : y ∈ (localizedAlgHom ι P).range := by
  obtain ⟨⟨m, hm⟩, hmy⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization P.primeCompl (Rₘ := Localization.AtPrime P)
      y hy
  obtain ⟨⟨t, ⟨_, ⟨u, hu, rfl⟩⟩⟩, ht⟩ :=
    IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid T P.primeCompl)
      ((⟨m, hm⟩ : P.primeCompl) • y)
  have hut : algebraMap T (Localization (Algebra.algebraMapSubmonoid T P.primeCompl)) t =
      algebraMap R (Localization (Algebra.algebraMapSubmonoid T P.primeCompl)) u *
        ((⟨m, hm⟩ : P.primeCompl) • y) := by
    rw [← ht, IsScalarTower.algebraMap_apply R T, mul_comm, IsLocalization.mk'_spec]
  have hint₁ : IsIntegral R
      (algebraMap T (Localization (Algebra.algebraMapSubmonoid T P.primeCompl)) t) := by
    rw [hut]
    exact (isIntegral_algebraMap).mul hmy
  obtain ⟨m', hm', hm't⟩ :=
    IsLocalization.exists_isIntegral_smul_of_isIntegral_map P.primeCompl hint₁
  obtain ⟨b, hb⟩ := hint _ hm't
  have hden : m' * (u * m) ∈ P.primeCompl :=
    P.primeCompl.mul_mem hm' (P.primeCompl.mul_mem hu hm)
  refine ⟨IsLocalization.mk' _ b (⟨algebraMap R S (m' * (u * m)), ⟨_, hden, rfl⟩⟩ :
    Algebra.algebraMapSubmonoid S P.primeCompl), ?_⟩
  change IsLocalization.map (M := Algebra.algebraMapSubmonoid S P.primeCompl)
    (S := Localization (Algebra.algebraMapSubmonoid S P.primeCompl))
    (Localization (Algebra.algebraMapSubmonoid T P.primeCompl)) ι.toRingHom
    (algebraMapSubmonoid_le_comap ι P) (IsLocalization.mk' _ b _) = y
  rw [IsLocalization.map_mk', IsLocalization.mk'_eq_iff_eq_mul]
  have hb' : ι b = m' • t := hb
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [hb', Algebra.smul_def, map_mul, hut, Submonoid.smul_def, Algebra.smul_def,
    ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_mul, map_mul]
  ring

end LocalizationTransfer

section Conductor

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

/-- **A conductor element in a given prime, avoiding finitely many primes.** Let `B` be a finite
`R`-algebra, `(𝔭ᵢ)` a finite family of primes such that `B` agrees with `R` at each `𝔭ᵢ` (every
`b ∈ B` has `t b ∈ R` for some `t ∉ 𝔭ᵢ`), and `P` an ideal contained in no `𝔭ᵢ`. Then some
`s ∈ P` outside all `𝔭ᵢ` satisfies `s B ⊆ R`. (For the normalization of a reduced curve and the
prime `P` of a closed point, the `𝔭ᵢ` are the primes of the generic points.) -/
theorem exists_conductor_mem [Module.Finite R B] {ι : Type*} [Finite ι] (p : ι → Ideal R)
    [∀ i, (p i).IsPrime]
    (hsep : ∀ i (b : B), ∃ t : R, t ∉ p i ∧ t • b ∈ LinearMap.range (Algebra.linearMap R B))
    (P : Ideal R) (hP : ∀ i, ¬ P ≤ p i) :
    ∃ s ∈ P, (∀ i, s ∉ p i) ∧ ∀ b : B, ∃ a : R, s • b = algebraMap R B a := by
  classical
  have := Fintype.ofFinite ι
  -- the conductor `J = {a | a B ⊆ R}`, not contained in any `𝔭ᵢ`
  obtain ⟨J, hJ, hJi⟩ : ∃ J : Ideal R, (∀ a ∈ J, ∀ b : B,
      a • b ∈ LinearMap.range (Algebra.linearMap R B)) ∧ ∀ i, ¬ J ≤ p i := by
    let N := LinearMap.range (Algebra.linearMap R B)
    refine ⟨N.colon ⊤, fun a ha b => Submodule.mem_colon.1 ha b (Submodule.mem_top (R := R)),
      fun i hle => ?_⟩
    obtain ⟨G, hG⟩ := Module.Finite.fg_top (R := R) (M := B)
    choose t ht using hsep i
    have hmem : ∀ b ∈ Submodule.span R (G : Set B), (∏ g ∈ G, t g) • b ∈ N := by
      intro b hb
      induction hb using Submodule.span_induction with
      | mem x hx =>
        have hx' : x ∈ G := hx
        have e : (∏ g ∈ G, t g) = (∏ g ∈ G.erase x, t g) * t x :=
          (Finset.prod_erase_mul G t hx').symm
        rw [e, mul_smul]
        exact N.smul_mem _ (ht x).2
      | zero => rw [smul_zero]; exact N.zero_mem
      | add x y _ _ hx hy => rw [smul_add]; exact N.add_mem hx hy
      | smul a x _ hx => rw [smul_comm]; exact N.smul_mem _ hx
    have hprod : (∏ g ∈ G, t g) ∈ N.colon ⊤ := Submodule.mem_colon.2 fun b _ =>
      hmem b (hG ▸ Submodule.mem_top)
    have := hle hprod
    rw [(inferInstance : (p i).IsPrime).prod_mem_iff] at this
    obtain ⟨g, -, hg⟩ := this
    exact (ht g).1 hg
  -- prime avoidance for `J * P`
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · exact ⟨0, P.zero_mem, fun i => (IsEmpty.false i).elim, fun b => ⟨0, by simp⟩⟩
  have hJP : ¬ ((J * P : Ideal R) : Set R) ⊆
      ⋃ i ∈ ((Finset.univ : Finset ι) : Set ι), (p i : Set R) := by
    rw [Ideal.subset_union_prime (s := Finset.univ) (f := p) i₀ i₀ fun i _ _ _ => inferInstance]
    rintro ⟨i, -, hi⟩
    rcases (Ideal.IsPrime.mul_le (inferInstance : (p i).IsPrime)).1 hi with h | h
    · exact hJi i h
    · exact hP i h
  obtain ⟨s, hsJP, hs⟩ := Set.not_subset.1 hJP
  have hs' : ∀ i, s ∉ p i := fun i hi =>
    hs (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ i)) hi)
  have hsJ : s ∈ J := Ideal.mul_le_left hsJP
  have hsP : s ∈ P := Ideal.mul_le_right hsJP
  refine ⟨s, hsP, hs', fun b => ?_⟩
  obtain ⟨a, ha⟩ := hJ s hsJ b
  exact ⟨a, ha.symm⟩

end Conductor

section Dimension

/-- The scalar tower `k → R_M → B_M` of localizations (an instance form of
`Genus.isScalarTower_localization`). -/
instance isScalarTower_localization_localization (k : Type*) [CommRing k] {R B : Type*}
    [CommRing R] [CommRing B] [Algebra k R] [Algebra R B] [Algebra k B] [IsScalarTower k R B]
    (M : Submonoid R) :
    IsScalarTower k (Localization M) (Localization (Algebra.algebraMapSubmonoid B M)) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k R (Localization M),
      ← IsScalarTower.algebraMap_apply R (Localization M),
      IsScalarTower.algebraMap_apply R B (Localization (Algebra.algebraMapSubmonoid B M)),
      ← IsScalarTower.algebraMap_apply k R B, ← IsScalarTower.algebraMap_apply k B]

/-- Localization at a prime does not increase the Krull dimension. -/
lemma krullDimLE_localization {R : Type*} [CommRing R] {n : ℕ} [Ring.KrullDimLE n R]
    (P : Ideal R) [P.IsPrime] : Ring.KrullDimLE n (Localization.AtPrime P) := by
  rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height P]
  exact P.height_le_ringKrullDim_of_isPrime.trans (Ring.krullDimLE_iff.1 inferInstance)

end Dimension

section Chart

/-! ### The local theorems on an affine chart

Let `R = Γ(V, 𝒪_C)`, `L` the ring of the generic points of `C` in `V` and `B` the normalization
sections over `V` (integrally closed in `L` over `R`), and let `P` be the prime of a closed point.
The following theorems apply `CurvesField.OrdinaryCompletion` to the localizations at `P`. -/

variable {k : Type*} [Field k] {R : Type*} {B : Type*} {L : Type*} [CommRing R] [CommRing B]
  [CommRing L] [Algebra k R] [Algebra R B] [Algebra k B] [IsScalarTower k R B] [Algebra R L]
  [Module.Finite R B] (ι : B →ₐ[R] L) (hι : Function.Injective ι)
  (hRB : Function.Injective (algebraMap R B))
  (hint : ∀ y : L, IsIntegral R y → y ∈ ι.range)
  {I : Type*} [Finite I] (p : I → Ideal R) [∀ i, (p i).IsPrime]
  (hsep : ∀ i (b : B), ∃ t : R, t ∉ p i ∧ t • b ∈ LinearMap.range (Algebra.linearMap R B))
  (hunit : ∀ r : R, (∀ i, r ∉ p i) → IsUnit (algebraMap R L r))
  (P : Ideal R) [P.IsPrime] (hP : ∀ i, ¬ P ≤ p i)

include hι hRB hint hsep hunit hP in
/-- **An ordinary double point on a chart has `δ = 1` and two branches.** -/
theorem chart_node [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    (e : Completion (Localization.AtPrime P) ≃ₐ[k] FormalUV k) :
    delta k (rangeIn k (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid B P.primeCompl))) = 1 ∧
      Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid B P.primeCompl))) = 2 := by
  have : Ring.KrullDimLE 1 (Localization.AtPrime P) := krullDimLE_localization P
  obtain ⟨s, hsP, hs, hsB⟩ := exists_conductor_mem p hsep P hP
  have hsm : algebraMap R (Localization.AtPrime P) s ∈ maximalIdeal (Localization.AtPrime P) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P s).2 hsP
  have hAB := algebraMap_localization_injective P hRB
  have hsB' := exists_smul_eq_algebraMap_localization P hsB
  have hι' := localizedAlgHom_injective ι P hι
  have hsL := isUnit_algebraMap_localization (T := L) P (hunit s hs)
  have hint' := mem_range_localizedAlgHom_of_isIntegral ι P hint
  exact ⟨(delta_eq_one_of_formalNode e hAB hsm hsB' (localizedAlgHom ι P) hι' hsL hint').2,
    card_maximalSpectrum_eq_two_of_formalNode e hAB hsm hsB' (localizedAlgHom ι P) hι' hsL
      hint'⟩

include hι hRB hsep hunit hP in
/-- **A point with integrally closed local ring (a smooth point) on a chart has `δ = 0` and one
branch.** -/
theorem chart_smooth [IsDomain (Localization.AtPrime P)]
    [IsIntegrallyClosed (Localization.AtPrime P)] :
    delta k (rangeIn k (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid B P.primeCompl))) = 0 ∧
      Nat.card (MaximalSpectrum (Localization (Algebra.algebraMapSubmonoid B P.primeCompl))) = 1 := by
  obtain ⟨s, -, hs, hsB⟩ := exists_conductor_mem p hsep P hP
  have hAB := algebraMap_localization_injective P hRB
  have hsB' := exists_smul_eq_algebraMap_localization P hsB
  have hι' := localizedAlgHom_injective ι P hι
  have hsL := isUnit_algebraMap_localization (T := L) P (hunit s hs)
  have hreg := smul_eq_zero_of_isUnit hι' hsL
  have hs0 : algebraMap R (Localization.AtPrime P) s ≠ 0 := by
    intro h0
    have : Nontrivial (Localization (Algebra.algebraMapSubmonoid B P.primeCompl)) :=
      hAB.nontrivial
    exact one_ne_zero (hreg 1 (by rw [h0, zero_smul]))
  obtain ⟨-, h1, h2⟩ := delta_eq_zero_of_isIntegrallyClosed (k := k) hAB hs0 hsB' hreg
  exact ⟨h1, h2⟩

end Chart

end

end DeJongAlterations.StableModification.CurvesField.OrdinaryCompletion
