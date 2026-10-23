import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.RingTheory.Etale.Kaehler

/-!
# The universal derivation of an affine scheme with values in `(Ω_{A/R})^~`

Let `R → A` be a ring map. At a prime `x` of `A` the Kähler differentials localize:
`(Ω_{A/R})_x ≅ Ω_{A_x/R}` (`localKaehlerEquiv`, from Mathlib's
`KaehlerDifferential.isLocalizedModule_map`), so there is an `R`-derivation
`localDerivation R x : A_x → (Ω_{A/R})_x` extending `d : A → Ω_{A/R}`; it satisfies the quotient
rule `d(a/g) = (g·da − a·dg)/g²` (`localDerivation_mk`).

Sections of `𝒪_{Spec A}` and of the quasi-coherent module `(Ω_{A/R})^~` over an open `U` are the
functions on `U` which are locally fractions (Mathlib's structure sheaf), so applying
`localDerivation` pointwise gives a derivation `specDerivation U : Γ(Spec A, U) → Γ(Ω^~, U)`
(`specDerivation_mul`, `specDerivation_map`) extending `d` (`specDerivation_algebraMap`) and
killing `R` (`specDerivation_algebraMap_base`). It is the local model of the universal derivation
of `Ω¹_{X/S}` on an affine open (blueprint `sm-omega.tex`, `lem:sm-omega-spec-derivation`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace DeJongAlterations.StableModification.Omega

section Local

variable (R : Type u) {A : Type u} [CommRing R] [CommRing A] [Algebra R A]

/-- The localization of Kähler differentials at a prime: `(Ω_{A/R})_x ≅ Ω_{A_x/R}`. -/
def localKaehlerEquiv (x : PrimeSpectrum A) :
    LocalizedModule x.asIdeal.primeCompl Ω[A⁄R] ≃ₗ[LocalizedModule x.asIdeal.primeCompl A]
      Ω[(LocalizedModule x.asIdeal.primeCompl A)⁄R] :=
  LinearEquiv.extendScalarsOfIsLocalization x.asIdeal.primeCompl _
    (IsLocalizedModule.iso x.asIdeal.primeCompl
      (KaehlerDifferential.map R R A (LocalizedModule x.asIdeal.primeCompl A)))

theorem localKaehlerEquiv_symm_map (x : PrimeSpectrum A) (ω : Ω[A⁄R]) :
    (localKaehlerEquiv R x).symm
      (KaehlerDifferential.map R R A (LocalizedModule x.asIdeal.primeCompl A) ω) =
      LocalizedModule.mk ω 1 :=
  IsLocalizedModule.iso_symm_apply _ _ _

/-- The `R`-derivation `A_x → (Ω_{A/R})_x` extending `d : A → Ω_{A/R}`. -/
def localDerivation (x : PrimeSpectrum A) :
    Derivation R (LocalizedModule x.asIdeal.primeCompl A)
      (LocalizedModule x.asIdeal.primeCompl Ω[A⁄R]) :=
  (localKaehlerEquiv R x).symm.toLinearMap.compDer (KaehlerDifferential.D R _)

theorem localDerivation_apply (x : PrimeSpectrum A) (y : LocalizedModule x.asIdeal.primeCompl A) :
    localDerivation R x y = (localKaehlerEquiv R x).symm (KaehlerDifferential.D R _ y) :=
  rfl

theorem localDerivation_algebraMap (x : PrimeSpectrum A) (a : A) :
    localDerivation R x (algebraMap A _ a) =
      LocalizedModule.mk (KaehlerDifferential.D R A a) 1 := by
  rw [localDerivation_apply, ← KaehlerDifferential.map_D R R A, localKaehlerEquiv_symm_map]

/-- The quotient rule for the local derivation. -/
theorem localDerivation_mk (x : PrimeSpectrum A) (a : A) (g : x.asIdeal.primeCompl) :
    localDerivation R x (LocalizedModule.mk a g) =
      LocalizedModule.mk ((g : A) • KaehlerDifferential.D R A a - a • KaehlerDifferential.D R A g)
        (g * g) := by
  set y : LocalizedModule x.asIdeal.primeCompl A := LocalizedModule.mk a g
  set G : LocalizedModule x.asIdeal.primeCompl A := algebraMap A _ (g : A)
  have hG : IsUnit G := IsLocalization.map_units _ g
  have h1 : y * G = algebraMap A _ a := by
    simp only [y, G]
    rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap]
    change Localization.mk a g * Localization.mk (g : A) 1 = Localization.mk a 1
    rw [Localization.mk_mul, mul_comm, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp⟩
  have h2 := congrArg (localDerivation R x) h1
  rw [Derivation.leibniz, localDerivation_algebraMap, localDerivation_algebraMap] at h2
  apply (hG.smul_left_cancel).mp
  rw [eq_sub_of_add_eq' h2]
  simp only [y, G]
  rw [← Localization.mk_one_eq_algebraMap]
  rw [LocalizedModule.mk_smul_mk]
  change _ - (Localization.mk a g • LocalizedModule.mk _ 1) = _
  rw [LocalizedModule.mk_smul_mk, sub_eq_add_neg, ← LocalizedModule.mk_neg,
    LocalizedModule.mk_add_mk, LocalizedModule.mk_eq]
  refine ⟨1, ?_⟩
  simp only [one_smul, Submonoid.smul_def, Submonoid.coe_mul, OneMemClass.coe_one, smul_add,
    smul_sub, smul_neg, smul_smul]
  module

/-- The local derivation kills the image of `R`. -/
theorem localDerivation_algebraMap_base (x : PrimeSpectrum A) (r : R) :
    localDerivation R x (algebraMap A _ (algebraMap R A r)) = 0 := by
  rw [localDerivation_algebraMap, Derivation.map_algebraMap, LocalizedModule.zero_mk]

end Local

section Spec

variable (R : Type u) [CommRing R] {A : CommRingCat.{u}} [Algebra R A]

/-- The `A`-module `Ω_{A/R}`. -/
abbrev kaehlerModule : ModuleCat.{u} A := ModuleCat.of A Ω[A⁄R]

/-- The quasi-coherent sheaf `(Ω_{A/R})^~` on `Spec A`. -/
abbrev kaehlerTilde : (Spec A).Modules := tilde (kaehlerModule R (A := A))

/-- The derivation `Γ(Spec A, U) → Γ((Ω_{A/R})^~, U)`, applying `localDerivation` pointwise. -/
def specDerivation (U : (Spec A).Opens) (s : Γ(Spec A, U)) : Γ(kaehlerTilde R (A := A), U) :=
  ⟨fun y => localDerivation R y.1 (s.1 y), fun y => by
    obtain ⟨V, hyV, i, a, g, h⟩ := s.2 y
    refine ⟨V, hyV, i, g • KaehlerDifferential.D R A a - a • KaehlerDifferential.D R A g, g * g,
      fun z => ⟨fun hmem => (h z).1 ((z.1.2.mem_or_mem hmem).elim id id), ?_⟩⟩
    obtain ⟨hs, hz⟩ := h z
    change localDerivation R _ (s.1 (i z)) = _
    rw [show s.1 (i z) = LocalizedModule.mk a ⟨g, hs⟩ from hz]
    exact localDerivation_mk R _ a ⟨g, hs⟩⟩

theorem specDerivation_apply (U : (Spec A).Opens) (s : Γ(Spec A, U)) (y : U) :
    (specDerivation R U s).1 y = localDerivation R y.1 (s.1 y) :=
  rfl

theorem specDerivation_add (U : (Spec A).Opens) (s t : Γ(Spec A, U)) :
    specDerivation R U (s + t) = specDerivation R U s + specDerivation R U t :=
  Subtype.ext (funext fun y => map_add (localDerivation R y.1) (s.1 y) (t.1 y))

theorem specDerivation_zero (U : (Spec A).Opens) :
    specDerivation R U 0 = 0 :=
  Subtype.ext (funext fun y => map_zero (localDerivation R y.1))

/-- `specDerivation` as an additive map. -/
def specDerivationHom (U : (Spec A).Opens) :
    Γ(Spec A, U) →+ Γ(kaehlerTilde R (A := A), U) where
  toFun := specDerivation R U
  map_zero' := specDerivation_zero R U
  map_add' := specDerivation_add R U

@[simp]
theorem specDerivationHom_apply (U : (Spec A).Opens) (s : Γ(Spec A, U)) :
    specDerivationHom R U s = specDerivation R U s :=
  rfl

theorem specDerivation_mul (U : (Spec A).Opens) (s t : Γ(Spec A, U)) :
    specDerivation R U (s * t) = s • specDerivation R U t + t • specDerivation R U s :=
  Subtype.ext (funext fun y => Derivation.leibniz (localDerivation R y.1) (s.1 y) (t.1 y))

theorem specDerivation_map {U V : (Spec A).Opens} (i : V ⟶ U) (s : Γ(Spec A, U)) :
    specDerivation R V ((Spec A).presheaf.map i.op s) =
      (kaehlerTilde R (A := A)).presheaf.map i.op (specDerivation R U s) :=
  rfl

/-- On constant sections, `specDerivation` is `d`. -/
theorem specDerivation_algebraMap (U : (Spec A).Opens) (a : A) :
    specDerivation R U (algebraMap A Γ(Spec A, U) a) =
      (tilde.toOpen (kaehlerModule R (A := A)) U).hom (KaehlerDifferential.D R A a) :=
  Subtype.ext (funext fun y => localDerivation_algebraMap R y.1 a)

/-- `specDerivation` kills the image of `R`. -/
theorem specDerivation_algebraMap_base (U : (Spec A).Opens) (r : R) :
    specDerivation R U (algebraMap A Γ(Spec A, U) (algebraMap R A r)) = 0 :=
  Subtype.ext (funext fun y => localDerivation_algebraMap_base R y.1 r)

end Spec

end DeJongAlterations.StableModification.Omega
