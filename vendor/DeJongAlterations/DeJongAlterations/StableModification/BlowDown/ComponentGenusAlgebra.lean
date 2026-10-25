/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.NoClosedExc

/-!
# Local algebra of the δ-invariant of a component

Let `k → R → B` be ring maps and `ρ : B → B₁` a surjective ring map. Temkin's
`g(x) = dim_k 𝒪_{C̃,x̃}/𝒪_{C,x}` (M. Temkin, *Stable modification of relative curves*,
J. Algebraic Geom. 19 (2010), `references/temkin10-stable-modification/source/semi-stable.tex`,
App. B, l. 4376–4378), in its affine form `CurvesField.Genus.deltaAt`, can only drop when `B` is
replaced by the quotient `B₁` (`deltaAt_comp_le`), and it drops by at least one if `B` splits off
a nonzero factor at `𝔭` which is not seen by `B₁` (`deltaAt_comp_add_one_le`): an idempotent `e`
of `B` with `ρ e = 0`, neither `e` nor `1 - e` vanishing at `𝔭`, is not in the image of the local
ring `R_𝔭` (`R → B` injective, and a local ring has no nontrivial idempotents). For the
normalization `B = B₁ × B₂` of a reduced curve at a point `x` lying on two components, with `B₁`
the normalization of one of them, this is the inequality `δ_{Z}(x) + 1 ≤ δ_C(x)` used for
`NoClosedExc.NodalComponentGenus`.

The δ-invariant is also unchanged when `R` is replaced by a quotient `R ⧸ I` through which
`R → B` factors (`deltaAt_comp_surjective`): the cokernel is the same module, and localizing at
`𝔭 ⊇ I` over `R` or over `R ⧸ I` is the same.

Blueprint: `sm-blow-down-unconditional.tex`, `lem:sm-bdu-delta-split`.
-/

noncomputable section

open Module

namespace DeJongAlterations.StableModification.BlowDown.ComponentGenus

open CurvesField.Genus

set_option autoImplicit false

section Algebra

variable {k : Type*} [Field k] {R B B₁ : Type*} [CommRing R] [CommRing B] [CommRing B₁]

/-- **An idempotent splitting off a factor at `𝔭` is not a fraction of the base.** Let
`φ : R → B` be injective, `𝔭` a prime of `R` and `e` an idempotent of `B` such that neither
`φ(s) e` nor `φ(s) (1 - e)` vanishes for `s ∉ 𝔭`. Then `φ(s) e ∉ φ(R)` for all `s ∉ 𝔭`. -/
theorem not_mul_idempotent_mem_range (φ : R →+* B) (hinj : Function.Injective φ) (P : Ideal R)
    [P.IsPrime] (e : B) (he : IsIdempotentElem e) (h₁ : ∀ s ∉ P, φ s * e ≠ 0)
    (h₂ : ∀ s ∉ P, φ s * (1 - e) ≠ 0) {s r : R} (hs : s ∉ P) (hr : φ r = φ s * e) : False := by
  have hrr : r * r = s * r := by
    apply hinj
    rw [map_mul, map_mul, hr]
    calc φ s * e * (φ s * e) = φ s * φ s * (e * e) := by ring
      _ = φ s * (φ s * e) := by rw [he.eq]; ring
  by_cases hrP : r ∈ P
  · have hrs : r - s ∉ P := fun h => hs (by simpa using P.sub_mem hrP h)
    have hu : (r - s) * s ∉ P := fun h =>
      (Ideal.IsPrime.mem_or_mem ‹_› h).elim hrs hs
    refine h₁ _ hu ?_
    rw [map_mul, mul_assoc, ← hr, ← map_mul, sub_mul, hrr, sub_self, map_zero]
  · have hu : r * s ∉ P := fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hrP hs
    refine h₂ _ hu ?_
    rw [map_mul, mul_assoc, mul_sub, mul_one, ← hr, ← map_sub, ← map_mul, mul_sub, hrr,
      mul_comm r s, sub_self, map_zero]

/-- The `R`-linear map `B → B₁` underlying `ρ`, for the algebra structures `φ` and `ρ ∘ φ`. -/
def linearOfComp (φ : R →+* B) (ρ : B →+* B₁) :
    letI := φ.toAlgebra
    letI := (ρ.comp φ).toAlgebra
    B →ₗ[R] B₁ :=
  letI := φ.toAlgebra
  letI := (ρ.comp φ).toAlgebra
  { toFun := ρ
    map_add' := ρ.map_add
    map_smul' := fun r b => by
      simp only [Algebra.smul_def, map_mul, RingHom.id_apply]
      rfl }

/-- The map of cokernels `B / R → B₁ / R` induced by `ρ`. -/
def cokerOfComp (φ : R →+* B) (ρ : B →+* B₁) :
    letI := φ.toAlgebra
    letI := (ρ.comp φ).toAlgebra
    Coker R B →ₗ[R] Coker R B₁ :=
  letI := φ.toAlgebra
  letI := (ρ.comp φ).toAlgebra
  (LinearMap.range (Algebra.linearMap R B)).liftQ
    ((LinearMap.range (Algebra.linearMap R B₁)).mkQ ∘ₗ linearOfComp φ ρ) (by
      rintro _ ⟨a, rfl⟩
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨a, rfl⟩)

theorem cokerOfComp_mk (φ : R →+* B) (ρ : B →+* B₁) (b : B) :
    letI := φ.toAlgebra
    letI := (ρ.comp φ).toAlgebra
    cokerOfComp φ ρ (Submodule.Quotient.mk b) = Submodule.Quotient.mk (ρ b) := rfl

theorem cokerOfComp_surjective (φ : R →+* B) (ρ : B →+* B₁) (hρ : Function.Surjective ρ) :
    Function.Surjective (cokerOfComp φ ρ) := by
  letI := φ.toAlgebra
  letI := (ρ.comp φ).toAlgebra
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H b₁ =>
    obtain ⟨b, rfl⟩ := hρ b₁
    exact ⟨Submodule.Quotient.mk b, rfl⟩

/-- The localized map of cokernels, as a `k`-linear map. -/
def localCokerOfComp (ψ : k →+* R) (φ : R →+* B) (ρ : B →+* B₁) (p : PrimeSpectrum R) :
    letI := ψ.toAlgebra
    letI := φ.toAlgebra
    letI := (φ.comp ψ).toAlgebra
    letI := (ρ.comp φ).toAlgebra
    letI := ((ρ.comp φ).comp ψ).toAlgebra
    haveI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower k R B₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    LocalizedModule p.asIdeal.primeCompl (Coker R B) →ₗ[k]
      LocalizedModule p.asIdeal.primeCompl (Coker R B₁) :=
  letI := ψ.toAlgebra
  letI := φ.toAlgebra
  letI := (φ.comp ψ).toAlgebra
  letI := (ρ.comp φ).toAlgebra
  letI := ((ρ.comp φ).comp ψ).toAlgebra
  haveI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k R B₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  (((LocalizedModule.map p.asIdeal.primeCompl) (cokerOfComp φ ρ)).restrictScalars R).restrictScalars k

theorem localCokerOfComp_mk (ψ : k →+* R) (φ : R →+* B) (ρ : B →+* B₁) (p : PrimeSpectrum R)
    (b : B) (s : p.asIdeal.primeCompl) :
    letI := ψ.toAlgebra
    letI := φ.toAlgebra
    letI := (φ.comp ψ).toAlgebra
    letI := (ρ.comp φ).toAlgebra
    letI := ((ρ.comp φ).comp ψ).toAlgebra
    haveI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    haveI : IsScalarTower k R B₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
    localCokerOfComp ψ φ ρ p (LocalizedModule.mk (Submodule.Quotient.mk b) s) =
      LocalizedModule.mk (Submodule.Quotient.mk (ρ b)) s := by
  letI := ψ.toAlgebra
  letI := φ.toAlgebra
  letI := (φ.comp ψ).toAlgebra
  letI := (ρ.comp φ).toAlgebra
  letI := ((ρ.comp φ).comp ψ).toAlgebra
  exact LocalizedModule.map_mk _ _ _ _

theorem localCokerOfComp_surjective (ψ : k →+* R) (φ : R →+* B) (ρ : B →+* B₁)
    (hρ : Function.Surjective ρ) (p : PrimeSpectrum R) :
    Function.Surjective (localCokerOfComp ψ φ ρ p) := by
  letI := ψ.toAlgebra
  letI := φ.toAlgebra
  letI := (φ.comp ψ).toAlgebra
  letI := (ρ.comp φ).toAlgebra
  letI := ((ρ.comp φ).comp ψ).toAlgebra
  exact LocalizedModule.map_surjective _ _ (cokerOfComp_surjective φ ρ hρ)

/-- Finite-dimensionality of the localized cokernel, from that of the cokernel. -/
theorem finiteDimensional_localCoker (ψ : k →+* R) (φ : R →+* B) (h : IsFiniteCoker ψ φ)
    (p : PrimeSpectrum R) :
    letI := ψ.toAlgebra
    letI := φ.toAlgebra
    letI := (φ.comp ψ).toAlgebra
    haveI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
    FiniteDimensional k (LocalizedModule p.asIdeal.primeCompl (Coker R B)) := by
  letI := ψ.toAlgebra
  letI := φ.toAlgebra
  letI := (φ.comp ψ).toAlgebra
  haveI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional k (Coker R B) := h
  exact (isLocalDecomposition (k := k) (A := R) (Coker R B)).finiteDimensional p

/-- **The δ-invariant does not grow under a quotient of `B`**: for a surjective `ρ : B → B₁`,
`dim_k (B₁ / R)_𝔭 ≤ dim_k (B / R)_𝔭` (if `B / R` is finite-dimensional). -/
theorem deltaAt_comp_le (ψ : k →+* R) (φ : R →+* B) (ρ : B →+* B₁) (hρ : Function.Surjective ρ)
    (h : IsFiniteCoker ψ φ) (p : PrimeSpectrum R) :
    deltaAt ψ (ρ.comp φ) p ≤ deltaAt ψ φ p := by
  letI := ψ.toAlgebra
  letI := φ.toAlgebra
  letI := (φ.comp ψ).toAlgebra
  letI := (ρ.comp φ).toAlgebra
  letI := ((ρ.comp φ).comp ψ).toAlgebra
  haveI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k R B₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := finiteDimensional_localCoker ψ φ h p
  exact LinearMap.finrank_le_finrank_of_surjective (localCokerOfComp_surjective ψ φ ρ hρ p)

/-- **Splitting off a factor lowers the δ-invariant by at least one** (blueprint
`lem:sm-bdu-delta-split`). Let `φ : R → B` be injective with finite-dimensional cokernel,
`ρ : B → B₁` surjective, and `e ∈ B` an idempotent with `ρ e = 0` such that `φ(s) e ≠ 0` and
`φ(s) (1 - e) ≠ 0` for all `s ∉ 𝔭`. Then `dim_k (B₁ / R)_𝔭 + 1 ≤ dim_k (B / R)_𝔭`: the localized
map of cokernels is onto, and the class of `e` is a nonzero element of its kernel
(`not_mul_idempotent_mem_range`). -/
theorem deltaAt_comp_add_one_le (ψ : k →+* R) (φ : R →+* B) (hinj : Function.Injective φ)
    (ρ : B →+* B₁) (hρ : Function.Surjective ρ) (h : IsFiniteCoker ψ φ) (p : PrimeSpectrum R)
    (e : B) (he : IsIdempotentElem e) (hρe : ρ e = 0) (h₁ : ∀ s ∉ p.asIdeal, φ s * e ≠ 0)
    (h₂ : ∀ s ∉ p.asIdeal, φ s * (1 - e) ≠ 0) :
    deltaAt ψ (ρ.comp φ) p + 1 ≤ deltaAt ψ φ p := by
  letI := ψ.toAlgebra
  letI := φ.toAlgebra
  letI := (φ.comp ψ).toAlgebra
  letI := (ρ.comp φ).toAlgebra
  letI := ((ρ.comp φ).comp ψ).toAlgebra
  haveI : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k R B₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI := finiteDimensional_localCoker ψ φ h p
  set F := localCokerOfComp ψ φ ρ p with hF
  have hsurj : Function.Surjective F := localCokerOfComp_surjective ψ φ ρ hρ p
  set x : LocalizedModule p.asIdeal.primeCompl (Coker R B) :=
    LocalizedModule.mk (Submodule.Quotient.mk e) 1 with hx
  have hxker : x ∈ LinearMap.ker F := by
    rw [LinearMap.mem_ker, hx, hF, localCokerOfComp_mk, hρe, Submodule.Quotient.mk_zero,
      LocalizedModule.zero_mk]
  have hx0 : x ≠ 0 := by
    intro h0
    rw [hx, ← LocalizedModule.zero_mk (1 : p.asIdeal.primeCompl), LocalizedModule.mk_eq] at h0
    obtain ⟨u, hu⟩ := h0
    simp only [one_smul, smul_zero] at hu
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hu
    obtain ⟨r, hr⟩ := hu
    have hr' : φ r = φ u.1 * e := by
      have h0 : (Algebra.linearMap R B) r = φ r := rfl
      rw [h0, Submonoid.smul_def, Algebra.smul_def] at hr
      exact hr
    exact not_mul_idempotent_mem_range φ hinj p.asIdeal e he h₁ h₂ u.2 hr'
  have hker : 0 < finrank k (LinearMap.ker F) := by
    exact (Module.finrank_pos_iff_exists_ne_zero (R := k) (M := LinearMap.ker F)).mpr
      ⟨⟨x, hxker⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  have hrn := LinearMap.finrank_range_add_finrank_ker F
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrn
  change finrank k (LocalizedModule p.asIdeal.primeCompl (Coker R B₁)) + 1 ≤
    finrank k (LocalizedModule p.asIdeal.primeCompl (Coker R B))
  omega

end Algebra

section Surjective

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A']

/-- **Localizing along a surjection of the base**: for a surjective `A → A'`, a prime `𝔮` of
`A'` and an `A'`-module `M`, the localization `M → M_𝔮` is also the localization of `M`, as an
`A`-module, at the contraction of `𝔮`. -/
theorem isLocalizedModule_restrictScalars_of_surjective
    (hα : Function.Surjective (algebraMap A A')) (M : Type*) [AddCommGroup M] [Module A' M]
    [Module A M] [IsScalarTower A A' M] (q : Ideal A') [q.IsPrime] :
    IsLocalizedModule (q.comap (algebraMap A A')).primeCompl
      ((LocalizedModule.mkLinearMap q.primeCompl M).restrictScalars A) where
  map_units s := by
    have hs : algebraMap A A' s ∈ q.primeCompl := s.2
    have hu := IsLocalizedModule.map_units (LocalizedModule.mkLinearMap q.primeCompl M)
      ⟨algebraMap A A' s, hs⟩
    rw [Module.End.isUnit_iff] at hu ⊢
    convert hu using 1
    funext z
    change (s : A) • z = algebraMap A A' s • z
    rw [algebraMap_smul]
  surj y := by
    induction y using LocalizedModule.induction_on with
    | h m t =>
      obtain ⟨s, hs⟩ := hα t.1
      have hs' : s ∈ (q.comap (algebraMap A A')).primeCompl := by
        change algebraMap A A' s ∉ q
        rw [hs]
        exact t.2
      refine ⟨⟨m, ⟨s, hs'⟩⟩, ?_⟩
      change (s : A) • LocalizedModule.mk m t = LocalizedModule.mk m 1
      rw [← algebraMap_smul A' s, hs, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
      refine ⟨1, ?_⟩
      simp only [one_smul, Submonoid.smul_def]
  exists_of_eq {m₁ m₂} h := by
    change LocalizedModule.mk m₁ 1 = LocalizedModule.mk m₂ 1 at h
    rw [LocalizedModule.mk_eq] at h
    obtain ⟨u, hu⟩ := h
    obtain ⟨s, hs⟩ := hα u.1
    have hs' : s ∈ (q.comap (algebraMap A A')).primeCompl := by
      change algebraMap A A' s ∉ q
      rw [hs]
      exact u.2
    refine ⟨⟨s, hs'⟩, ?_⟩
    simp only [one_smul] at hu
    change (s : A) • m₁ = (s : A) • m₂
    rw [← algebraMap_smul A' s, ← algebraMap_smul A' s m₂, hs]
    exact hu

end Surjective

section DeltaSurjective

variable {k : Type*} [Field k] {A A' B : Type*} [CommRing A] [CommRing A'] [CommRing B]

/-- **The δ-invariant is unchanged by passing to a quotient of the base** (blueprint
`lem:sm-bdu-delta-split`): for a surjective `α : A → A'` and `φ : A' → B`,
`dim_k (B / A')_𝔮 = dim_k (B / A)_{α⁻¹𝔮}` (the two cokernels agree, and so do the
localizations, `isLocalizedModule_restrictScalars_of_surjective`). -/
theorem deltaAt_comp_surjective (ψ : k →+* A) (α : A →+* A') (hα : Function.Surjective α)
    (φ : A' →+* B) (q : PrimeSpectrum A') :
    deltaAt (α.comp ψ) φ q =
      deltaAt ψ (φ.comp α) ⟨q.asIdeal.comap α, Ideal.comap_isPrime α q.asIdeal⟩ := by
  let _ : Algebra k A := ψ.toAlgebra
  let _ : Algebra A A' := α.toAlgebra
  let _ : Algebra k A' := (α.comp ψ).toAlgebra
  let _ : Algebra A' B := φ.toAlgebra
  let _ : Algebra A B := (φ.comp α).toAlgebra
  let _ : Algebra k B := (φ.comp (α.comp ψ)).toAlgebra
  have : IsScalarTower k A A' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k A' B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A A' B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- the two cokernels agree
  have hinj : Function.Injective (cokerMap A' B : Coker A B →ₗ[A] Coker A' B) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro z hz
    induction z using Submodule.Quotient.induction_on with
    | H b =>
      rw [LinearMap.mem_ker, cokerMap_mk, Submodule.Quotient.mk_eq_zero] at hz
      obtain ⟨a', ha'⟩ := hz
      obtain ⟨a, rfl⟩ := hα a'
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      refine ⟨a, ?_⟩
      exact ha'
  have hsurj : Function.Surjective (cokerMap A' B : Coker A B →ₗ[A] Coker A' B) := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H b => exact ⟨Submodule.Quotient.mk b, rfl⟩
  let c := LinearEquiv.ofBijective (cokerMap A' B : Coker A B →ₗ[A] Coker A' B) ⟨hinj, hsurj⟩
  have hloc := isLocalizedModule_restrictScalars_of_surjective (A := A) (A' := A') hα
    (Coker A' B) q.asIdeal
  have hloc' : IsLocalizedModule (q.asIdeal.comap (algebraMap A A')).primeCompl
      (((LocalizedModule.mkLinearMap q.asIdeal.primeCompl (Coker A' B)).restrictScalars A) ∘ₗ
        c.toLinearMap) := IsLocalizedModule.of_linearEquiv_right _ _ c
  let e := IsLocalizedModule.iso (q.asIdeal.comap (algebraMap A A')).primeCompl
    (((LocalizedModule.mkLinearMap q.asIdeal.primeCompl (Coker A' B)).restrictScalars A) ∘ₗ
        c.toLinearMap)
  let e' : LocalizedModule (q.asIdeal.comap (algebraMap A A')).primeCompl (Coker A B) ≃ₗ[k]
      LocalizedModule q.asIdeal.primeCompl (Coker A' B) :=
    { e.toAddEquiv with
      map_smul' := fun r z => by
        change e (r • z) = r • e z
        rw [← algebraMap_smul A r z, map_smul, ← algebraMap_smul A' r (e z),
          ← algebraMap_smul A' (algebraMap k A r) (e z), ← IsScalarTower.algebraMap_apply] }
  change finrank k (LocalizedModule q.asIdeal.primeCompl (Coker A' B)) =
    finrank k (LocalizedModule (q.asIdeal.comap (algebraMap A A')).primeCompl (Coker A B))
  exact e'.finrank_eq.symm

end DeltaSurjective

end DeJongAlterations.StableModification.BlowDown.ComponentGenus
