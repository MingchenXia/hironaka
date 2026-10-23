/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.GenusEuler
import DeJongAlterations.StableModification.CurvesField.Delta
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.LinearCombination

/-!
# Local algebra of the genus formula

The skyscraper part of the proof of Lemma B.1 of M. Temkin, *Stable modification of relative
curves*, J. Algebraic Geom. 19 (2010) (`references/temkin10-stable-modification`, `semi-stable.tex`,
lines 4417–4421: "the sheaf `π_*𝒪_{C̃}/𝒪_C` is a skyscraper because `π` is an isomorphism over
non-closed points"). In affine terms: for a ring map `A → B` of `k`-algebras with
finite-dimensional cokernel `Q = B / A`, the dimension of `Q` is the sum over the points of
`Spec A` of the local contributions `dim_k Q_𝔭`, finitely many of them nonzero and all at maximal
ideals; and these local contributions do not change when `A → B` is localized at an element
`f ∈ A` (the passage to a basic open subset).

## Main definitions

* `localFinrank k M p = dim_k M_𝔭` for an `A`-module `M` with compatible `k`-structure.
* `Coker A B = B ⧸ A` (the cokernel of the structure map `A → B`, an `A`-module).

## Main results

* `finrank_eq_finsum_localFinrank`, `hasFiniteSupport_localFinrank`, `isMaximal_of_localFinrank`:
  for `M` finite-dimensional over `k`, `dim_k M = ∑ᶠ 𝔭, dim_k M_𝔭`, with finite support
  consisting of maximal ideals (a finite-length module is the sum of its localizations).
* `isLocalizedModule_atPrime_comp`: localizing at a prime `𝔭'` of `A_f` is localizing at the
  contraction `𝔭` of `𝔭'` in `A`.
* `isLocalizedModule_cokerMap_of_submonoid`, `isLocalizedModule_cokerMap`: the cokernel of a
  localization `S⁻¹A → S⁻¹B` of `A → B` is the localization of the cokernel.
* `localFinrank_coker_away`: `dim_k (B_f / A_f)_{𝔭'} = dim_k (B / A)_𝔭`.
* `localFinrank_coker_eq_finrank_coker`, `delta_range_eq_finrank_coker`, `deltaAt_eq_delta`:
  `dim_k (B / A)_𝔭 = dim_k (B_𝔭 / A_𝔭)`, the δ-invariant `CurvesField.delta` of the local rings
  (Temkin's `g(x) = dim_k 𝒪_{C̃,x̃}/𝒪_{C,x}`).
* `IsFiniteCoker`, `cokerFinrank`, `deltaAt`, `cokerFinrank_eq_finsum`, `deltaAt_away`: the same
  statements for algebra structures given by explicit ring maps `k → A → B`.

Blueprint: `sm-curves-fields-genus.tex`, `lem:sm-skyscraper-decomposition`,
`lem:sm-skyscraper-localization`.
-/

namespace DeJongAlterations.StableModification.CurvesField.Genus

open Module

set_option autoImplicit false

universe u v w

section Decomposition

variable (k : Type u) [Field k] {A : Type v} [CommRing A] [Algebra k A]

/-- The local contribution `dim_k M_𝔭` of a module at a point `𝔭 ∈ Spec A`. -/
noncomputable def localFinrank (M : Type w) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] (p : PrimeSpectrum A) : ℕ :=
  finrank k (LocalizedModule p.asIdeal.primeCompl M)

variable {k}

/-- Localizations of a module at primes contracted from `k` carry the obvious `k`-structure. -/
lemma localFinrank_def (M : Type w) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] (p : PrimeSpectrum A) :
    localFinrank k M p = finrank k (LocalizedModule p.asIdeal.primeCompl M) := rfl

/-- The local data of a module in the decomposition: localizations finite-dimensional, finitely
many nonzero, at maximal ideals, with sum the dimension. -/
structure IsLocalDecomposition (k : Type u) [Field k] (A : Type v) [CommRing A] [Algebra k A]
    (M : Type w) [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M] : Prop where
  finiteDimensional : ∀ p : PrimeSpectrum A,
    FiniteDimensional k (LocalizedModule p.asIdeal.primeCompl M)
  hasFiniteSupport : Function.HasFiniteSupport (localFinrank k M : PrimeSpectrum A → ℕ)
  isMaximal : ∀ p : PrimeSpectrum A, localFinrank k M p ≠ 0 → p.asIdeal.IsMaximal
  finrank_eq : finrank k M = ∑ᶠ p : PrimeSpectrum A, localFinrank k M p

section Simple

variable (N : Type w) [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- If every element of `S` acts bijectively on `N`, the identity is a localization at `S`. -/
lemma isLocalizedModule_id_of_bijective (S : Submonoid A)
    (h : ∀ s ∈ S, Function.Bijective (fun n : N => s • n)) :
    IsLocalizedModule S (LinearMap.id : N →ₗ[A] N) where
  map_units s := (Module.End.isUnit_iff _).2 (h s.1 s.2)
  surj y := ⟨⟨y, 1⟩, by simp⟩
  exists_of_eq {x₁ x₂} e := ⟨1, by simpa using e⟩

/-- The local decomposition of a simple module: it is concentrated at its annihilator. -/
theorem isLocalDecomposition_of_isSimpleModule [IsSimpleModule A N] [FiniteDimensional k N] :
    IsLocalDecomposition k A N := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.1 (inferInstance : IsSimpleModule A N)
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  -- elements of `I` kill `N`
  have hkill : ∀ a ∈ I, ∀ n : N, a • n = 0 := by
    intro a ha n
    apply e.injective
    rw [map_smul, map_zero, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
  -- elements outside `I` act bijectively
  have hbij : ∀ s ∉ I, Function.Bijective (fun n : N => s • n) := by
    intro s hs
    have hs' : Ideal.Quotient.mk I s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
    constructor
    · intro n₁ n₂ h
      apply e.injective
      have h' : e (s • n₁) = e (s • n₂) := congrArg e h
      rw [map_smul, map_smul, Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
        at h'
      exact mul_left_cancel₀ hs' h'
    · intro n
      refine ⟨e.symm ((Ideal.Quotient.mk I s)⁻¹ * e n), ?_⟩
      apply e.injective
      change e (s • e.symm _) = e n
      rw [map_smul, LinearEquiv.apply_symm_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        ← mul_assoc, mul_inv_cancel₀ hs', one_mul]
  set m : PrimeSpectrum A := ⟨I, hI.isPrime⟩
  have hsub : ∀ p : PrimeSpectrum A, p ≠ m →
      Subsingleton (LocalizedModule p.asIdeal.primeCompl N) := by
    intro p hp
    have hnot : ¬ I ≤ p.asIdeal := fun hle =>
      hp (PrimeSpectrum.ext (hI.eq_of_le p.isPrime.ne_top hle).symm)
    obtain ⟨a, haI, hap⟩ := Set.not_subset.1 hnot
    refine ⟨fun x y => ?_⟩
    suffices hz : ∀ z : LocalizedModule p.asIdeal.primeCompl N, z = 0 by rw [hz x, hz y]
    intro z
    induction z using LocalizedModule.induction_on with
    | h n s =>
      rw [← LocalizedModule.zero_mk s]
      refine LocalizedModule.mk_eq.2 ⟨⟨a, hap⟩, ?_⟩
      simp only [smul_zero]
      change a • s • n = 0
      rw [smul_comm, hkill a haI n, smul_zero]
  have hloc : IsLocalizedModule m.asIdeal.primeCompl (LinearMap.id : N →ₗ[A] N) :=
    isLocalizedModule_id_of_bijective N _ fun s hs => hbij s hs
  let eN : LocalizedModule m.asIdeal.primeCompl N ≃ₗ[A] N :=
    IsLocalizedModule.iso m.asIdeal.primeCompl (LinearMap.id : N →ₗ[A] N)
  have hm : localFinrank k N m = finrank k N := (eN.restrictScalars k).finrank_eq
  have hzero : ∀ p : PrimeSpectrum A, p ≠ m → localFinrank k N p = 0 := fun p hp => by
    have := hsub p hp
    exact finrank_zero_of_subsingleton
  refine ⟨fun p => ?_, ?_, fun p hp => ?_, ?_⟩
  · by_cases hp : p = m
    · subst hp
      exact Module.Finite.equiv (eN.restrictScalars k).symm
    · have := hsub p hp
      infer_instance
  · refine (Set.finite_singleton m).subset fun p hp => ?_
    by_contra h
    exact hp (hzero p h)
  · by_contra h
    have : p = m := by
      by_contra h'
      exact hp (hzero p h')
    exact h (this ▸ hI)
  · rw [finsum_eq_single _ m hzero, hm]

end Simple

section Extension

variable {M : Type w} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]

/-- Localization of the inclusion of a submodule at `𝔭`. -/
noncomputable abbrev locSubtype (N : Submodule A M) (p : PrimeSpectrum A) :
    LocalizedModule p.asIdeal.primeCompl N →ₗ[A] LocalizedModule p.asIdeal.primeCompl M :=
  IsLocalizedModule.map p.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ N)
    (LocalizedModule.mkLinearMap _ M) N.subtype

/-- Localization of the projection onto a quotient at `𝔭`. -/
noncomputable abbrev locMkQ (N : Submodule A M) (p : PrimeSpectrum A) :
    LocalizedModule p.asIdeal.primeCompl M →ₗ[A] LocalizedModule p.asIdeal.primeCompl (M ⧸ N) :=
  IsLocalizedModule.map p.asIdeal.primeCompl (LocalizedModule.mkLinearMap _ M)
    (LocalizedModule.mkLinearMap _ (M ⧸ N)) N.mkQ

/-- Localization is exact: the local contributions are additive in `0 → N → M → M/N → 0`. -/
theorem localFinrank_add (N : Submodule A M) (p : PrimeSpectrum A)
    [FiniteDimensional k (LocalizedModule p.asIdeal.primeCompl N)]
    [FiniteDimensional k (LocalizedModule p.asIdeal.primeCompl (M ⧸ N))] :
    FiniteDimensional k (LocalizedModule p.asIdeal.primeCompl M) ∧
      localFinrank k M p = localFinrank k N p + localFinrank k (M ⧸ N) p := by
  have hex : Function.Exact (locSubtype N p) (locMkQ N p) :=
    IsLocalizedModule.map_exact _ _ _ _ _ _ (LinearMap.exact_subtype_mkQ N)
  have hinj : Function.Injective (locSubtype N p) :=
    IsLocalizedModule.map_injective _ _ _ _ Subtype.val_injective
  have hsurj : Function.Surjective (locMkQ N p) :=
    IsLocalizedModule.map_surjective _ _ _ _ (Submodule.mkQ_surjective N)
  have hex' : Function.Exact ((locSubtype N p).restrictScalars k)
      ((locMkQ N p).restrictScalars k) := hex
  have hfd : FiniteDimensional k (LocalizedModule p.asIdeal.primeCompl M) :=
    finiteDimensional_of_exact hex'
  refine ⟨hfd, ?_⟩
  rw [localFinrank_def, localFinrank_def, localFinrank_def, finrank_eq_add_of_exact hex',
    LinearMap.finrank_range_of_inj (f := (locSubtype N p).restrictScalars k) hinj]
  congr 1
  have htop : LinearMap.range ((locMkQ N p).restrictScalars k) = ⊤ := LinearMap.range_eq_top.2 hsurj
  rw [htop, finrank_top]

end Extension

/-- **A finite-dimensional module is the sum of its localizations** (the skyscraper
decomposition): for an `A`-module `M` which is finite-dimensional over `k`, every localization
`M_𝔭` is finite-dimensional, only finitely many are nonzero, these sit at maximal ideals, and
`dim_k M = ∑ᶠ 𝔭, dim_k M_𝔭`. -/
theorem isLocalDecomposition (M : Type w) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] [FiniteDimensional k M] : IsLocalDecomposition k A M := by
  induction h : finrank k M using Nat.strong_induction_on generalizing M with
  | _ n ih =>
  by_cases hM : Subsingleton M
  · have hz : ∀ p : PrimeSpectrum A, localFinrank k M p = 0 := fun p => finrank_zero_of_subsingleton
    refine ⟨fun p => inferInstance, ?_, fun p hp => absurd (hz p) hp, ?_⟩
    · have : Function.support (localFinrank k M : PrimeSpectrum A → ℕ) = ∅ :=
        Function.support_eq_empty_iff.2 (funext hz)
      simp [Function.HasFiniteSupport, this]
    · simp [hz, finrank_zero_of_subsingleton]
  rw [not_subsingleton_iff_nontrivial] at hM
  have : IsArtinian A M := isArtinian_of_tower k inferInstance
  have : IsAtomic (Submodule A M) := isAtomic_of_orderBot_wellFounded_lt (wellFounded_lt)
  obtain ⟨N, hN, -⟩ := (eq_bot_or_exists_atom_le (⊤ : Submodule A M)).resolve_left top_ne_bot
  have : IsSimpleModule A N := isSimpleModule_iff_isAtom.2 hN
  have : FiniteDimensional k N :=
    Module.Finite.of_injective ((N.subtype).restrictScalars k) Subtype.val_injective
  have hdN := isLocalDecomposition_of_isSimpleModule (k := k) (A := A) N
  have hNpos : 0 < finrank k N := by
    have : Nontrivial N := (Submodule.nontrivial_iff_ne_bot).2 hN.1
    exact Module.finrank_pos
  have hrank : finrank k (M ⧸ N) + finrank k N = finrank k M := by
    have := Submodule.finrank_quotient_add_finrank (N.restrictScalars k)
    exact this
  have hdQ := ih (finrank k (M ⧸ N)) (by omega) (M ⧸ N) rfl
  have hadd := fun p => @localFinrank_add k _ A _ _ M _ _ _ _ N p (hdN.finiteDimensional p)
    (hdQ.finiteDimensional p)
  have hsum : localFinrank k M = fun p => localFinrank k N p + localFinrank k (M ⧸ N) p :=
    funext fun p => (hadd p).2
  refine ⟨fun p => (hadd p).1, ?_, fun p hp => ?_, ?_⟩
  · rw [hsum]
    exact (hdN.hasFiniteSupport.union hdQ.hasFiniteSupport).subset
      (Function.support_add _ _)
  · rw [hsum] at hp
    by_cases hp' : localFinrank k N p = 0
    · exact hdQ.isMaximal p (by simpa [hp'] using hp)
    · exact hdN.isMaximal p hp'
  · rw [hsum, finsum_add_distrib hdN.hasFiniteSupport hdQ.hasFiniteSupport, ← hdN.finrank_eq,
      ← hdQ.finrank_eq]
    omega

end Decomposition

section Transfer

variable {A : Type v} [CommRing A] {A' : Type w} [CommRing A'] [Algebra A A'] (f : A)
  [IsLocalization.Away f A']

/-- Elements of `A` outside the contraction of a prime of `A_f` map outside it. -/
lemma algebraMap_mem_primeCompl {p' : Ideal A'} [p'.IsPrime] {s : A}
    (hs : s ∈ (p'.comap (algebraMap A A')).primeCompl) : algebraMap A A' s ∈ p'.primeCompl := hs

/-- Powers of `f` lie outside the contraction of any prime of `A_f`. -/
lemma pow_mem_primeCompl_comap (p' : Ideal A') [p'.IsPrime] (n : ℕ) :
    f ^ n ∈ (p'.comap (algebraMap A A')).primeCompl := by
  intro h
  have hu : IsUnit (algebraMap A A' (f ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit f).pow n
  exact (inferInstance : p'.IsPrime).ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)

variable {M : Type*} [AddCommGroup M] [Module A M] {M' : Type*} [AddCommGroup M'] [Module A' M']
  [Module A M'] [IsScalarTower A A' M'] (g : M →ₗ[A] M') [IsLocalizedModule (Submonoid.powers f) g]

include f in
/-- **Localization at a prime of a localization.** If `M → M'` is the localization of `M` at
`f` and `𝔭'` is a prime of `A_f` with contraction `𝔭`, then `M → M' → M'_{𝔭'}` is the
localization of `M` at `𝔭`. -/
theorem isLocalizedModule_atPrime_comp (p' : Ideal A') [p'.IsPrime] :
    IsLocalizedModule (p'.comap (algebraMap A A')).primeCompl
      (((LocalizedModule.mkLinearMap p'.primeCompl M').restrictScalars A) ∘ₗ g) where
  map_units s := by
    have hu := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap p'.primeCompl M')
      ⟨_, algebraMap_mem_primeCompl (p' := p') s.2⟩
    rw [Module.End.isUnit_iff] at hu ⊢
    convert hu using 1
    funext z
    change (s : A) • z = algebraMap A A' s • z
    rw [algebraMap_smul]
  surj y := by
    induction y using LocalizedModule.induction_on with
    | h m' t =>
    obtain ⟨⟨m, ⟨_, n, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers f) g m'
    obtain ⟨⟨a, ⟨_, l, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers f) (t : A')
    simp only at hm ha
    have hfn := pow_mem_primeCompl_comap f p' n
    have hfl := pow_mem_primeCompl_comap f p' l
    have haP : a ∈ (p'.comap (algebraMap A A')).primeCompl := by
      intro h
      apply t.2
      have : (t : A') * algebraMap A A' (f ^ l) ∈ p' := by rw [ha]; exact h
      exact ((inferInstance : p'.IsPrime).mem_or_mem this).resolve_right hfl
    refine ⟨⟨f ^ l • m, ⟨a * f ^ n, mul_mem haP hfn⟩⟩, ?_⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LocalizedModule.mkLinearMap_apply, map_smul]
    rw [Submonoid.smul_def, LocalizedModule.smul'_mk, LocalizedModule.smul'_mk,
      LocalizedModule.mk_eq]
    refine ⟨1, ?_⟩
    simp only [one_smul, Submonoid.smul_def] at hm ⊢
    rw [← hm, ← algebraMap_smul A' (a * f ^ n) m', ← algebraMap_smul A' (f ^ l),
      ← algebraMap_smul A' (f ^ n) m', smul_smul, smul_smul, map_mul, ← ha]
  exists_of_eq {m₁ m₂} e := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars,
      LocalizedModule.mkLinearMap_apply] at e
    obtain ⟨t, ht⟩ := LocalizedModule.mk_eq.1 e
    simp only [one_smul] at ht
    obtain ⟨⟨a, ⟨_, l, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers f) (t : A')
    simp only at ha
    have hfl := pow_mem_primeCompl_comap f p' l
    have haP : a ∈ (p'.comap (algebraMap A A')).primeCompl := by
      intro h
      apply t.2
      have : (t : A') * algebraMap A A' (f ^ l) ∈ p' := by rw [ha]; exact h
      exact ((inferInstance : p'.IsPrime).mem_or_mem this).resolve_right hfl
    have hga : g (a • m₁) = g (a • m₂) := by
      rw [map_smul, map_smul, ← algebraMap_smul A' a, ← algebraMap_smul A' a, ← ha, mul_comm,
        mul_smul, mul_smul]
      simp only [Submonoid.smul_def] at ht
      rw [ht]
    obtain ⟨⟨_, n, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) hga
    refine ⟨⟨f ^ n * a, mul_mem (pow_mem_primeCompl_comap f p' n) haP⟩, ?_⟩
    simp only [Submonoid.smul_def] at hc ⊢
    rw [mul_smul, mul_smul]
    exact hc

end Transfer

section Coker

variable (A : Type v) [CommRing A] (B : Type w) [CommRing B] [Algebra A B]

/-- The cokernel `B / A` of the structure map of an `A`-algebra, as an `A`-module. -/
abbrev Coker : Type w := B ⧸ LinearMap.range (Algebra.linearMap A B)

variable {A B} {A' B' : Type*} [CommRing A'] [CommRing B'] [Algebra A' B'] [Algebra A A']
  [Algebra B B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']

variable (A' B') in
/-- The map of cokernels induced by a commutative square `A → B`, `A' → B'`. -/
noncomputable def cokerMap : Coker A B →ₗ[A] Coker A' B' :=
  (LinearMap.range (Algebra.linearMap A B)).liftQ
    (((LinearMap.range (Algebra.linearMap A' B')).mkQ.restrictScalars A) ∘ₗ
      (IsScalarTower.toAlgHom A B B').toLinearMap) (by
    rintro _ ⟨a, rfl⟩
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, IsScalarTower.coe_toAlgHom',
      Algebra.linearMap_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨algebraMap A A' a, ?_⟩
    simp only [Algebra.linearMap_apply]
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply])

lemma cokerMap_mk (b : B) :
    cokerMap A' B' (Submodule.Quotient.mk b : Coker A B) =
      Submodule.Quotient.mk (algebraMap B B' b) := rfl

variable (S : Submonoid A) [IsLocalization S A']
  [IsLocalization (Algebra.algebraMapSubmonoid B S) B']

/-- **Cokernels commute with localization**: if `A → A'` and `B → B'` are the localizations at a
submonoid `S ⊆ A` (and its image in `B`), the induced map `B / A → B' / A'` is the localization of
`B / A` at `S`. -/
theorem isLocalizedModule_cokerMap_of_submonoid :
    IsLocalizedModule S (cokerMap A' B' : Coker A B →ₗ[A] Coker A' B') where
  map_units x := by
    have hu : IsUnit (algebraMap A A' x) := IsLocalization.map_units A' x
    rw [Module.End.isUnit_iff]
    have hu' := (Module.End.isUnit_iff _).1
      (hu.map (algebraMap A' (Module.End A' (Coker A' B'))))
    convert hu' using 1
    funext z
    change (x : A) • z = algebraMap A A' x • z
    rw [algebraMap_smul]
  surj y := by
    induction y using Submodule.Quotient.induction_on with
    | H b' =>
    obtain ⟨⟨b, ⟨_, s, hs, rfl⟩⟩, hb⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid B S) b'
    refine ⟨⟨Submodule.Quotient.mk b, ⟨s, hs⟩⟩, ?_⟩
    simp only at hb
    rw [cokerMap_mk, ← hb, Submonoid.smul_def, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [Algebra.smul_def, mul_comm, IsScalarTower.algebraMap_apply A B B' s]
  exists_of_eq {x₁ x₂} e := by
    suffices H : ∀ z : Coker A B, cokerMap A' B' z = 0 → ∃ c : S, (c : A) • z = 0 by
      obtain ⟨c, hc⟩ := H (x₁ - x₂) (by rw [map_sub, e, sub_self])
      exact ⟨c, by rw [Submonoid.smul_def, Submonoid.smul_def, ← sub_eq_zero, ← smul_sub, hc]⟩
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | H b =>
    rw [cokerMap_mk, Submodule.Quotient.mk_eq_zero] at hz
    obtain ⟨a', ha'⟩ := hz
    simp only [Algebra.linearMap_apply] at ha'
    obtain ⟨⟨a, ⟨s, hs⟩⟩, ha⟩ := IsLocalization.surj S a'
    simp only at ha
    have h0 : algebraMap B B' (b * algebraMap A B s - algebraMap A B a) = 0 := by
      rw [map_sub, map_mul, ← ha', ← IsScalarTower.algebraMap_apply,
        ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A A' B',
        IsScalarTower.algebraMap_apply A A' B' a, ← map_mul, ha, sub_self]
    obtain ⟨⟨_, t, ht, rfl⟩, hl⟩ := (IsLocalization.map_eq_zero_iff
      (Algebra.algebraMapSubmonoid B S) B' _).1 h0
    refine ⟨⟨t * s, mul_mem ht hs⟩, ?_⟩
    simp only
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨t * a, ?_⟩
    simp only [Algebra.linearMap_apply, Algebra.smul_def]
    rw [mul_sub, sub_eq_zero] at hl
    simp only [map_mul] at hl ⊢
    linear_combination -hl

/-- **Cokernels commute with localization at an element**: if `A → A'` and `B → B'` are the
localizations at `f` and `f|_B`, then `B / A → B' / A'` is the localization of `B / A` at `f`. -/
theorem isLocalizedModule_cokerMap (f : A) [IsLocalization.Away f A']
    [IsLocalization.Away (algebraMap A B f) B'] :
    IsLocalizedModule (Submonoid.powers f) (cokerMap A' B' : Coker A B →ₗ[A] Coker A' B') := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers f)) B' := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  exact isLocalizedModule_cokerMap_of_submonoid (Submonoid.powers f)

end Coker

section CokerLocal

variable (k : Type u) [Field k] {A : Type v} [CommRing A] {B : Type w} [CommRing B] [Algebra A B]
  {A' B' : Type*} [CommRing A'] [CommRing B'] [Algebra A' B'] [Algebra A A']
  [Algebra B B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']
  [Algebra k A] [Algebra k A'] [IsScalarTower k A A'] [Algebra k B] [IsScalarTower k A B]
  [Algebra k B'] [IsScalarTower k A' B']
  (f : A) [IsLocalization.Away f A'] [IsLocalization.Away (algebraMap A B f) B']

include f in
/-- **The local contributions of `B / A` are unchanged by localizing at `f`**: for a prime
`𝔭'` of `A_f` with contraction `𝔭` in `A`, `dim_k (B_f / A_f)_{𝔭'} = dim_k (B / A)_𝔭`. -/
theorem localFinrank_coker_away (p' : PrimeSpectrum A') :
    localFinrank k (Coker A' B') p' =
      localFinrank k (Coker A B) ⟨p'.asIdeal.comap (algebraMap A A'), inferInstance⟩ := by
  have : IsLocalizedModule (Submonoid.powers f) (cokerMap A' B' : Coker A B →ₗ[A] Coker A' B') :=
    isLocalizedModule_cokerMap f
  have hloc := isLocalizedModule_atPrime_comp f (cokerMap A' B' : Coker A B →ₗ[A] Coker A' B')
    p'.asIdeal
  let e := IsLocalizedModule.iso (p'.asIdeal.comap (algebraMap A A')).primeCompl
    (((LocalizedModule.mkLinearMap p'.asIdeal.primeCompl (Coker A' B')).restrictScalars A) ∘ₗ
      (cokerMap A' B' : Coker A B →ₗ[A] Coker A' B'))
  let e' : LocalizedModule (p'.asIdeal.comap (algebraMap A A')).primeCompl
      (Coker A B) ≃ₗ[k] LocalizedModule p'.asIdeal.primeCompl (Coker A' B') :=
    { e.toAddEquiv with
      map_smul' := fun c z => by
        change e (c • z) = c • e z
        rw [← algebraMap_smul A c z, map_smul, ← algebraMap_smul A' c (e z),
          ← algebraMap_smul A' (algebraMap k A c) (e z), ← IsScalarTower.algebraMap_apply] }
  exact e'.finrank_eq.symm

end CokerLocal

section AtPrime

variable (k : Type u) [Field k] {A : Type v} [CommRing A] {B : Type w} [CommRing B] [Algebra A B]
  {A' B' : Type*} [CommRing A'] [CommRing B'] [Algebra A' B'] [Algebra A A']
  [Algebra B B'] [Algebra A B'] [IsScalarTower A A' B'] [IsScalarTower A B B']
  [Algebra k A] [Algebra k A'] [IsScalarTower k A A'] [Algebra k B] [IsScalarTower k A B]
  [Algebra k B'] [IsScalarTower k A' B']
  (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime A' p]
  [IsLocalization (Algebra.algebraMapSubmonoid B p.primeCompl) B']

include p in
/-- **The local contribution is the δ-invariant of the local rings**: for `A_𝔭 = A'` and
`B_𝔭 = B'` the localizations at `𝔭` (for `A = Γ(V, 𝒪_C)`, `B` its normalization: the local ring
`𝒪_{C,x}` and the semilocal ring `𝒪_{C̃,x̃}`), `dim_k (B / A)_𝔭 = dim_k (B_𝔭 / A_𝔭)`. -/
theorem localFinrank_coker_eq_finrank_coker :
    localFinrank k (Coker A B) ⟨p, inferInstance⟩ = finrank k (Coker A' B') := by
  have : IsLocalizedModule p.primeCompl (cokerMap A' B' : Coker A B →ₗ[A] Coker A' B') :=
    isLocalizedModule_cokerMap_of_submonoid p.primeCompl
  let e := IsLocalizedModule.iso p.primeCompl (cokerMap A' B' : Coker A B →ₗ[A] Coker A' B')
  let e' : LocalizedModule p.primeCompl (Coker A B) ≃ₗ[k] Coker A' B' :=
    { e.toAddEquiv with
      map_smul' := fun c z => by
        change e (c • z) = c • e z
        rw [← algebraMap_smul A c z, map_smul, ← algebraMap_smul A' c (e z),
          ← algebraMap_smul A' (algebraMap k A c) (e z), ← IsScalarTower.algebraMap_apply] }
  exact e'.finrank_eq

/-- The cokernel `B' / A'` is the quotient of `B'` by the image of `A'` as a `k`-subalgebra, so
its dimension is the δ-invariant `CurvesField.delta` of that subalgebra (Temkin's `g(x)`). -/
theorem delta_range_eq_finrank_coker :
    delta k (IsScalarTower.toAlgHom k A' B').range = finrank k (Coker A' B') := by
  have h : Subalgebra.toSubmodule (IsScalarTower.toAlgHom k A' B').range =
      (LinearMap.range (Algebra.linearMap A' B')).restrictScalars k := by
    ext b
    simp
  rw [delta, h]
  exact (Submodule.Quotient.restrictScalarsEquiv k
    (LinearMap.range (Algebra.linearMap A' B'))).finrank_eq

end AtPrime

section RingHom

/-! ### Ring-homomorphism versions

For the application to schemes the algebra structures come from explicit ring maps
`ψ : k → A` and `φ : A → B` (restriction maps and `π^♯`); these wrappers fix the instances. -/

variable {k : Type u} [Field k] {A : Type v} [CommRing A] {B : Type w} [CommRing B]

/-- `B / A` is finite-dimensional over `k`, for ring maps `ψ : k → A` and `φ : A → B`. -/
def IsFiniteCoker (ψ : k →+* A) (φ : A →+* B) : Prop :=
  letI := ψ.toAlgebra
  letI := φ.toAlgebra
  letI := (φ.comp ψ).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  FiniteDimensional k (Coker A B)

/-- `dim_k (B / A)` for ring maps `ψ : k → A` and `φ : A → B`. -/
noncomputable def cokerFinrank (ψ : k →+* A) (φ : A →+* B) : ℕ :=
  letI := ψ.toAlgebra
  letI := φ.toAlgebra
  letI := (φ.comp ψ).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  finrank k (Coker A B)

/-- The local contribution `dim_k (B / A)_𝔭` for ring maps `ψ : k → A` and `φ : A → B`
(for `A = 𝒪_{C,x}`-charts and `B` the normalization: the δ-invariant of the point `𝔭`). -/
noncomputable def deltaAt (ψ : k →+* A) (φ : A →+* B) (p : PrimeSpectrum A) : ℕ :=
  letI := ψ.toAlgebra
  letI := φ.toAlgebra
  letI := (φ.comp ψ).toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  localFinrank k (Coker A B) p

/-- **The skyscraper decomposition, ring-map form**: `dim_k (B / A) = ∑ᶠ 𝔭, dim_k (B / A)_𝔭`,
with finitely many nonzero terms, all at maximal ideals. -/
theorem cokerFinrank_eq_finsum (ψ : k →+* A) (φ : A →+* B) (h : IsFiniteCoker ψ φ) :
    Function.HasFiniteSupport (deltaAt ψ φ) ∧
      (∀ p, deltaAt ψ φ p ≠ 0 → p.asIdeal.IsMaximal) ∧
      cokerFinrank ψ φ = ∑ᶠ p, deltaAt ψ φ p := by
  let := ψ.toAlgebra
  let := φ.toAlgebra
  let := (φ.comp ψ).toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional k (Coker A B) := h
  have hd := isLocalDecomposition (k := k) (A := A) (Coker A B)
  exact ⟨hd.hasFiniteSupport, hd.isMaximal, hd.finrank_eq⟩

/-- **The local contributions are unchanged by localization at an element**, ring-map form:
if `ρ : A → A'` and `σ : B → B'` are the localizations at `f` and at `φ f`, and
`φ' : A' → B'` is compatible, then `dim_k (B'/A')_{𝔭'} = dim_k (B/A)_{ρ⁻¹𝔭'}`. -/
theorem deltaAt_away {A' : Type*} [CommRing A'] {B' : Type*} [CommRing B'] (ψ : k →+* A)
    (φ : A →+* B) (ρ : A →+* A') (σ : B →+* B') (φ' : A' →+* B')
    (hcomm : φ'.comp ρ = σ.comp φ) (f : A)
    (hρ : letI := ρ.toAlgebra; IsLocalization.Away f A')
    (hσ : letI := σ.toAlgebra; IsLocalization.Away (φ f) B') (p' : PrimeSpectrum A') :
    deltaAt (ρ.comp ψ) φ' p' = deltaAt ψ φ ⟨p'.asIdeal.comap ρ, Ideal.comap_isPrime ρ p'.asIdeal⟩ := by
  let := ψ.toAlgebra
  let := φ.toAlgebra
  let := (φ.comp ψ).toAlgebra
  let := ρ.toAlgebra
  let := σ.toAlgebra
  let := φ'.toAlgebra
  let := (ρ.comp ψ).toAlgebra
  let := (φ'.comp (ρ.comp ψ)).toAlgebra
  let : Algebra A B' := (σ.comp φ).toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k A A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k A' B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A A' B' :=
    IsScalarTower.of_algebraMap_eq fun a => (RingHom.congr_fun hcomm a).symm
  have : IsLocalization.Away f A' := hρ
  have : IsLocalization.Away (algebraMap A B f) B' := hσ
  exact localFinrank_coker_away k f p'

/-- The scalar tower `k → A_M → B_M` of localizations. -/
theorem isScalarTower_localization (k : Type*) [Field k] {A B : Type*} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B] (M : Submonoid A) :
    IsScalarTower k (Localization M) (Localization (Algebra.algebraMapSubmonoid B M)) :=
  IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k A (Localization M),
      ← IsScalarTower.algebraMap_apply A (Localization M),
      IsScalarTower.algebraMap_apply A B (Localization (Algebra.algebraMapSubmonoid B M)),
      ← IsScalarTower.algebraMap_apply k A B, ← IsScalarTower.algebraMap_apply k B]

/-- **The local contribution of a point is the δ-invariant of its local rings** (ring-map
form): `dim_k (B / A)_𝔭 = δ(A_𝔭 ⊆ B_𝔭)`, the codimension of the image of `A_𝔭` in
`B_𝔭 = B ⊗_A A_𝔭` (`CurvesField.delta`; for `A = Γ(V, 𝒪_C)` and `B` the normalization this is
Temkin's `g(x) = dim_k 𝒪_{C̃,x̃}/𝒪_{C,x}`). -/
theorem deltaAt_eq_delta (ψ : k →+* A) (φ : A →+* B) (p : PrimeSpectrum A) :
    letI := ψ.toAlgebra
    letI := φ.toAlgebra
    letI := (φ.comp ψ).toAlgebra
    haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI := isScalarTower_localization k (A := A) (B := B) p.asIdeal.primeCompl
    deltaAt ψ φ p = delta k (IsScalarTower.toAlgHom k (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl))).range := by
  let _ := ψ.toAlgebra
  let _ := φ.toAlgebra
  let _ := (φ.comp ψ).toAlgebra
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := isScalarTower_localization k (A := A) (B := B) p.asIdeal.primeCompl
  rw [delta_range_eq_finrank_coker]
  exact localFinrank_coker_eq_finrank_coker k p.asIdeal

end RingHom

end DeJongAlterations.StableModification.CurvesField.Genus
