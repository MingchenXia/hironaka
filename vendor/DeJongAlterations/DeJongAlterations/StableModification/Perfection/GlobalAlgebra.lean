/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane PL-GLOBAL)
-/
import DeJongAlterations.StableModification.Perfection.Residue

/-!
# Local algebra for the global purely inseparable smoothing

Blueprint chapter `sm-dj-perfection-global`, nodes `lem:sm-dj-perfection-global-transport`,
`lem:sm-dj-perfection-global-localization`, `lem:sm-dj-perfection-global-integrally-closed` (new
route, not in de Jong 1996; it replaces de Jong 4.11 (ii) (c), (d) when generic étaleness of the
alteration is not required). This file contains the commutative algebra used to read
smoothness and separability of residue fields of the generic fibre of the global construction
off the ring-level results of `Perfection/Residue.lean`.

All rings live inside a field `M`; a local ring of a scheme is replaced by its image in `M`.

* `formallySmooth_of_range`, `isSeparable_residueField_map_of_range`: if a local ring map
  `φ : R → S` from a field becomes, after an injection `ρ : S ↪ M` and an isomorphism
  `R ≅ E`, the inclusion of a field `E ⊆ M` into an `E`-subalgebra `T ⊆ M`, then `φ` is formally
  smooth as soon as `T` is formally smooth over `E`, and the residue field extension of `φ` is
  separable as soon as the residue field of `T` is separable over `E`.
* `isLocalization_of_le`: if `B ≤ T` are `E`-subalgebras of `M`, `T` is local, and every
  element of `T` is a fraction `b / c` with `b, c ∈ B` and `c` a unit of `T`, then `T` is the
  localization of `B` at the contraction of the maximal ideal of `T`. Consequently
  (`formallySmooth_of_le`, `isSeparable_residueField_of_le`) formal smoothness of `B` over `E`,
  and separability of `B / Q` over `E` at a maximal contraction `Q`, pass to `T`.
* `mem_of_isIntegral_of_isIntegrallyClosed`: an integrally closed subring `T ⊆ M` contains every
  fraction of elements of `T` which is integral over `T`.
* `isGeometricallyReduced_of_forall_isDomain`: a field extension which stays a domain after every
  base field extension is geometrically reduced.
-/

noncomputable section

open IsLocalRing TensorProduct

namespace DeJongAlterations.StableModification.Perfection

universe u

section Transport

variable {E M R S : Type u} [Field E] [Field M] [Algebra E M] [CommRing R] [CommRing S]

/-- The image `ρ(S)` of a ring map `ρ : S → M`, as an `E`-subalgebra of `M` when it contains the
image of `E`. -/
def rangeSubalgebra (ρ : S →+* M) (hE : ∀ e : E, algebraMap E M e ∈ ρ.range) :
    Subalgebra E M :=
  { ρ.range with algebraMap_mem' := hE }

theorem mem_rangeSubalgebra {ρ : S →+* M} {hE : ∀ e : E, algebraMap E M e ∈ ρ.range} {x : M} :
    x ∈ rangeSubalgebra ρ hE ↔ x ∈ ρ.range := Iff.rfl

/-- An injective ring map `ρ : S → M` identifies `S` with `ρ(S)`. -/
def rangeSubalgebraEquiv (ρ : S →+* M) (hρ : Function.Injective ρ)
    (hE : ∀ e : E, algebraMap E M e ∈ ρ.range) : S ≃+* rangeSubalgebra ρ hE :=
  RingEquiv.ofBijective (ρ.codRestrict (rangeSubalgebra ρ hE).toSubring fun s => ⟨s, rfl⟩)
    ⟨fun _ _ h => hρ (congrArg Subtype.val h), fun ⟨_, s, hs⟩ => ⟨s, Subtype.ext hs⟩⟩

@[simp]
theorem coe_rangeSubalgebraEquiv (ρ : S →+* M) (hρ : Function.Injective ρ)
    (hE : ∀ e : E, algebraMap E M e ∈ ρ.range) (s : S) :
    (rangeSubalgebraEquiv ρ hρ hE s : M) = ρ s := rfl

variable (φ : R →+* S) (ρ : S →+* M) (hρ : Function.Injective ρ) (α : R →+* E)
  (hα : Function.Bijective α) (hcomp : ρ.comp φ = (algebraMap E M).comp α)
include hcomp hα

theorem algebraMap_mem_range_of_comp (e : E) : algebraMap E M e ∈ ρ.range := by
  obtain ⟨r, rfl⟩ := hα.2 e
  exact ⟨φ r, by simpa using congrArg (fun g : R →+* M => g r) hcomp⟩

include hρ in
theorem rangeSubalgebraEquiv_comp :
    (rangeSubalgebraEquiv (E := E) ρ hρ
        (algebraMap_mem_range_of_comp φ ρ α hα hcomp)).toRingHom.comp φ =
      (algebraMap E _).comp α := by
  ext r
  simpa using congrArg (fun g : R →+* M => g r) hcomp

include hρ in
/-- **Formal smoothness through the image in `M`.** If `ρ ∘ φ = (E → M) ∘ α` with `ρ`
injective and `α` bijective, and the image `ρ(S)` is formally smooth over `E`, then `φ` is
formally smooth. -/
theorem formallySmooth_of_range
    [Algebra.FormallySmooth E (rangeSubalgebra ρ (algebraMap_mem_range_of_comp φ ρ α hα hcomp))] :
    φ.FormallySmooth := by
  set T := rangeSubalgebra ρ (algebraMap_mem_range_of_comp φ ρ α hα hcomp)
  let j : S ≃+* T := rangeSubalgebraEquiv ρ hρ _
  let a : R ≃+* E := RingEquiv.ofBijective α hα
  have h1 : (algebraMap E T).FormallySmooth := RingHom.formallySmooth_algebraMap.2 inferInstance
  have h2 : ((algebraMap E T).comp a.toRingHom).FormallySmooth :=
    RingHom.FormallySmooth.respectsIso.2 _ a h1
  have h3 : (j.symm.toRingHom.comp ((algebraMap E T).comp a.toRingHom)).FormallySmooth :=
    RingHom.FormallySmooth.respectsIso.1 _ j.symm h2
  have hj : j.toRingHom.comp φ = (algebraMap E T).comp a.toRingHom :=
    rangeSubalgebraEquiv_comp φ ρ hρ α hα hcomp
  have : j.symm.toRingHom.comp ((algebraMap E T).comp a.toRingHom) = φ := by
    rw [← hj]
    ext r
    simp
  rwa [this] at h3

include hρ in
/-- **Separable residue fields through the image in `M`.** In the situation of
`formallySmooth_of_range`, with `S` local and `φ` local, if the residue field of `ρ(S)` is
separable over `E`, then the residue field extension of `φ` is separable. -/
theorem isSeparable_residueField_map_of_range [IsLocalRing R] [IsLocalRing S] [IsLocalHom φ]
    [IsLocalRing (rangeSubalgebra ρ (algebraMap_mem_range_of_comp φ ρ α hα hcomp))]
    [Algebra.IsSeparable E
      (ResidueField (rangeSubalgebra ρ (algebraMap_mem_range_of_comp φ ρ α hα hcomp)))] :
    letI := (ResidueField.map φ).toAlgebra
    Algebra.IsSeparable (ResidueField R) (ResidueField S) := by
  let := (ResidueField.map φ).toAlgebra
  set T := rangeSubalgebra ρ (algebraMap_mem_range_of_comp φ ρ α hα hcomp)
  let j : S ≃+* T := rangeSubalgebraEquiv ρ hρ _
  let a : R ≃+* E := RingEquiv.ofBijective α hα
  have hRfield : IsField R := a.toMulEquiv.isField (Field.toIsField E)
  have hres : Function.Bijective (residue R) := by
    refine ⟨fun x y h => ?_, residue_surjective⟩
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      IsLocalRing.isField_iff_maximalIdeal_eq.1 hRfield, Ideal.mem_bot, sub_eq_zero] at h
    exact h
  let r : R ≃+* ResidueField R := RingEquiv.ofBijective _ hres
  let e₁ : E ≃+* ResidueField R := a.symm.trans r
  let e₂ : ResidueField T ≃+* ResidueField S := (ResidueField.mapEquiv j).symm
  refine Algebra.IsSeparable.of_equiv_equiv e₁ e₂ ?_
  ext e
  obtain ⟨x, rfl⟩ := a.surjective e
  change ResidueField.map φ (residue R (a.symm (a x))) =
    (ResidueField.mapEquiv j).symm (algebraMap E (ResidueField T) (a x))
  rw [RingEquiv.symm_apply_apply, ResidueField.map_residue, RingEquiv.eq_symm_apply,
    ResidueField.mapEquiv_apply, ResidueField.map_residue, IsScalarTower.algebraMap_apply E T]
  congr 1
  exact (congrArg (fun g : R →+* T => g x) (rangeSubalgebraEquiv_comp φ ρ hρ α hα hcomp))

end Transport

section Localization

variable {E M : Type u} [Field E] [Field M] [Algebra E M] {B T : Subalgebra E M} (hBT : B ≤ T)

/-- The prime of `B` below the maximal ideal of the local ring `T ⊇ B`. -/
abbrev contraction [IsLocalRing T] : Ideal B :=
  (maximalIdeal T).comap (Subalgebra.inclusion hBT)

instance [IsLocalRing T] : (contraction hBT).IsPrime := Ideal.comap_isPrime _ _

/-- **Localization criterion.** Let `B ≤ T` be `E`-subalgebras of a field, with `T` local. If
every element `t ∈ T` satisfies `t c ∈ B` for some `c ∈ B` which is a unit of `T`, then `T` is
the localization of `B` at the contraction of the maximal ideal of `T`. -/
theorem isLocalization_of_le [IsLocalRing T]
    (hsurj : ∀ t : T, ∃ c : B, IsUnit (Subalgebra.inclusion hBT c) ∧ (t : M) * c ∈ B) :
    letI := (Subalgebra.inclusion hBT).toRingHom.toAlgebra
    IsLocalization.AtPrime T (contraction hBT) := by
  let := (Subalgebra.inclusion hBT).toRingHom.toAlgebra
  refine ⟨fun y => ?_, fun t => ?_, fun {x y} h => ?_⟩
  · have hy : Subalgebra.inclusion hBT (y : B) ∉ maximalIdeal T := y.2
    exact (IsLocalRing.notMem_maximalIdeal.1 hy)
  · obtain ⟨c, hc, hmem⟩ := hsurj t
    have hcQ : c ∈ (contraction hBT).primeCompl := fun h => (mem_maximalIdeal _).1 h hc
    refine ⟨(⟨_, hmem⟩, ⟨c, hcQ⟩), Subtype.ext ?_⟩
    rfl
  · refine ⟨1, ?_⟩
    have : x = y := Subalgebra.inclusion_injective hBT h
    rw [this]

theorem isScalarTower_inclusion :
    letI := (Subalgebra.inclusion hBT).toRingHom.toAlgebra
    IsScalarTower E B T := by
  let := (Subalgebra.inclusion hBT).toRingHom.toAlgebra
  exact IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- Formal smoothness passes from `B` to its localization `T`. -/
theorem formallySmooth_of_le [IsLocalRing T]
    (hsurj : ∀ t : T, ∃ c : B, IsUnit (Subalgebra.inclusion hBT c) ∧ (t : M) * c ∈ B)
    [Algebra.FormallySmooth E B] : Algebra.FormallySmooth E T := by
  let := (Subalgebra.inclusion hBT).toRingHom.toAlgebra
  have := isLocalization_of_le hBT hsurj
  have := isScalarTower_inclusion hBT
  have : Algebra.FormallySmooth B T :=
    Algebra.FormallySmooth.of_isLocalization (contraction hBT).primeCompl
  exact Algebra.FormallySmooth.comp E B T

/-- Separability of the residue field passes from `B / Q` to the localization `T = B_Q`, for
`Q` maximal. -/
theorem isSeparable_residueField_of_le [IsLocalRing T]
    (hsurj : ∀ t : T, ∃ c : B, IsUnit (Subalgebra.inclusion hBT c) ∧ (t : M) * c ∈ B)
    [hmax : (contraction hBT).IsMaximal] [Algebra.IsSeparable E (B ⧸ contraction hBT)] :
    Algebra.IsSeparable E (ResidueField T) := by
  let := (Subalgebra.inclusion hBT).toRingHom.toAlgebra
  have := isLocalization_of_le hBT hsurj
  let e := IsLocalization.AtPrime.equivQuotMaximalIdeal (contraction hBT) T
  let e' : (B ⧸ contraction hBT) ≃ₐ[E] ResidueField T :=
    AlgEquiv.ofRingEquiv (f := e) fun x => by
      change e (Ideal.Quotient.mk _ (algebraMap E B x)) = _
      rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
      rfl
  let := Ideal.Quotient.field (contraction hBT)
  exact Algebra.IsSeparable.of_algHom E (B ⧸ contraction hBT) e'.symm.toAlgHom

end Localization

section IntegrallyClosed

variable {M : Type u} [Field M]

/-- An integrally closed subring `T` of a field contains every fraction of elements of `T` which
is integral over `T`. -/
theorem mem_of_isIntegral_of_isIntegrallyClosed (T : Subring M) [IsIntegrallyClosed T] {b : M}
    (hb : IsIntegral T b) {c₁ c₂ : M} (h₁ : c₁ ∈ T) (h₂ : c₂ ∈ T) (h0 : c₂ ≠ 0)
    (hbc : b * c₂ = c₁) : b ∈ T := by
  let F := FractionRing T
  have hinj : Function.Injective (algebraMap T M) := Subtype.val_injective
  let ι : F →ₐ[T] M :=
    { IsFractionRing.lift hinj with commutes' := IsFractionRing.lift_algebraMap hinj }
  have hc₂ : (⟨c₂, h₂⟩ : T) ∈ nonZeroDivisors T :=
    mem_nonZeroDivisors_of_ne_zero fun h => h0 (congrArg Subtype.val h)
  let y : F := IsLocalization.mk' F (⟨c₁, h₁⟩ : T) ⟨⟨c₂, h₂⟩, hc₂⟩
  have hy : ι y = b := by
    have hmk := IsFractionRing.lift_mk' (K := F) hinj (⟨c₁, h₁⟩ : T) ⟨⟨c₂, h₂⟩, hc₂⟩
    change IsFractionRing.lift hinj y = b
    rw [hmk]
    change c₁ / c₂ = b
    rw [← hbc, mul_div_assoc, div_self h0, mul_one]
  have hyint : IsIntegral T y := by
    rw [← isIntegral_algHom_iff ι ι.toRingHom.injective, hy]
    exact hb
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.1 hyint
  rw [← hy, ← ht]
  change IsFractionRing.lift hinj (algebraMap T F t) ∈ T
  rw [IsFractionRing.lift_algebraMap]
  exact t.2

end IntegrallyClosed

section GeometricallyReduced

/-- A field extension `F / K` such that `F ⊗_K K'` is a domain for every field extension `K'` of
`K` is geometrically reduced. -/
theorem isGeometricallyReduced_of_forall_isDomain {K F : Type u} [Field K] [Field F] [Algebra K F]
    (h : ∀ (K' : Type u) [Field K'] [Algebra K K'], IsDomain (F ⊗[K] K')) :
    Algebra.IsGeometricallyReduced K F := by
  rw [Algebra.isGeometricallyReduced_field_iff]
  have := h (AlgebraicClosure K)
  exact isReduced_of_injective _ (Algebra.TensorProduct.comm K (AlgebraicClosure K) F).injective

end GeometricallyReduced

end DeJongAlterations.StableModification.Perfection

end
