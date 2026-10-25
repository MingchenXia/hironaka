/-
Copyright (c) 2026 DeJongAlterations contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DeJongAlterations contributors (Claude team, lane OM3E)
-/
import DeJongAlterations.StableModification.CurvesField.AmplePositiveIntegral

/-!
# The degree on the normalization of an integral curve

Let `ν : Y → X` be an affine morphism such that `ν^♯ : Γ(W, 𝒪_X) → Γ(ν⁻¹W, 𝒪_Y)` is injective with
finite-dimensional cokernel for every affine open `W` (for `X` an integral curve over a field and
`Y` its normalization, Codex's `NormalizationGluing.normalizationStructure`: lane COH3's
`Genus.normalization_app_injective`, `Genus.normalization_isFiniteCoker`). Then for line-bundle data
`𝓛` on `X` with a two-chart presentation (`Presentation`, e.g. `X` integral and projective,
`exists_presentation_of_isIntegral`), the degrees agree (`degree_pullback_eq`):

  `deg ν^*𝓛 = χ(ν^*𝓛) - χ(𝒪_Y) = χ(𝓛) - χ(𝒪_X) = deg 𝓛`.

So positivity of the degree on the normalization `Ṽ` of a component, the form in which lane OM1D
computes the degree of the dualizing sheaf (`Omega.RosenlichtComponent.degree_eq_of_simplePoles`),
gives positivity on the component itself, and hence (`exists_section_of_degree_pos_of_isIntegral`)
a section of a power of `𝓛` with a zero (`exists_section_of_degree_pullback_pos`). This replaces
the "δ-bounded descent" of the plan: no sections are compared, only Euler characteristics.

## The argument (blueprint `sm-curves-fields-ample-positive.tex`, `lem:sm-ample-positive-normalization`)

The presentation pulls back to `Y` (`Presentation.pullback`), with transition function `ν^♯ g`. The
two-term complexes of `𝓛^k` on `X` and of `ν^*𝓛^k` on `Y` are related by the injective maps `ν^♯`
on `U`, `V`, `U ∩ V` (`twistDiff_pullLin`), and for such a map of two-term complexes
`χ(target) = χ(source) + dim (cokernel in degree 0) - dim (cokernel in degree 1)`
(`finrank_twoTerm`, a snake-lemma count). The correction does not depend on `k`, so it cancels in
the degree. This is the δ-invariance of the degree, `χ(ν_*ν^*𝓛) - χ(𝓛) = Σ δ_x = χ(ν_*𝒪) - χ(𝒪)`,
as in the genus formula (M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010), Lemma B.1, `references/temkin10-stable-modification/source/semi-stable.tex`,
lines 4413--4433).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits Module
open DeJongAlterations.StableModification.Cohomology
open DeJongAlterations.StableModification.Projectivity

namespace DeJongAlterations.StableModification.CurvesField.Positive

noncomputable section

open Ample Ample.LineBundleData Projectivity.LineBundleData

/-! ### Two-term complexes under injective maps with finite-dimensional cokernels -/

section TwoTerm

variable {K : Type*} [Field K]

section Exact

variable {A B C : Type*} [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]
  [AddCommGroup C] [Module K C]

/-- A short exact sequence `0 → A → B → C → 0` with finite-dimensional ends: `B` is
finite-dimensional and `dim B = dim A + dim C`. -/
theorem finrank_eq_of_shortExact [FiniteDimensional K A] [FiniteDimensional K C]
    {f : A →ₗ[K] B} {g : B →ₗ[K] C} (hf : Function.Injective f) (hg : Function.Surjective g)
    (h : Function.Exact f g) :
    FiniteDimensional K B ∧ finrank K B = finrank K A + finrank K C := by
  have hB : FiniteDimensional K B := Module.Finite.of_exact h hg
  refine ⟨hB, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker g, LinearMap.range_eq_top.mpr hg, finrank_top,
    LinearMap.exact_iff.mp h, LinearMap.finrank_range_of_inj hf, add_comm]

end Exact

variable {P R P' R' : Type*} [AddCommGroup P] [Module K P] [AddCommGroup R] [Module K R]
  [AddCommGroup P'] [Module K P'] [AddCommGroup R'] [Module K R']

section ChangeTarget

variable (d : P →ₗ[K] R) {h : R →ₗ[K] R'} (hh : Function.Injective h)

include hh in
lemma ker_comp_of_injective : LinearMap.ker (h ∘ₗ d) = LinearMap.ker d := by
  ext x
  simp only [LinearMap.mem_ker, LinearMap.comp_apply]
  exact ⟨fun hx => hh (by rw [hx, map_zero]), fun hx => by rw [hx, map_zero]⟩

/-- The map `R / im d → R' / im (h d)` induced by `h`. -/
def cokerMapTarget : (R ⧸ LinearMap.range d) →ₗ[K] (R' ⧸ LinearMap.range (h ∘ₗ d)) :=
  (LinearMap.range d).mapQ _ h (by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩)

/-- The projection `R' / im (h d) → R' / im h`. -/
def cokerProjTarget : (R' ⧸ LinearMap.range (h ∘ₗ d)) →ₗ[K] (R' ⧸ LinearMap.range h) :=
  (LinearMap.range (h ∘ₗ d)).mapQ _ LinearMap.id (by
    rintro _ ⟨x, rfl⟩
    exact ⟨d x, rfl⟩)

include hh in
lemma cokerMapTarget_injective : Function.Injective (cokerMapTarget (h := h) d) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro y hy
  induction y using Submodule.Quotient.induction_on with
  | H r =>
  rw [LinearMap.mem_ker] at hy
  change Submodule.Quotient.mk (h r) = 0 at hy
  rw [Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨x, hx⟩ := hy
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  exact ⟨x, hh hx⟩

lemma cokerProjTarget_surjective : Function.Surjective (cokerProjTarget (h := h) d) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H r => exact ⟨Submodule.Quotient.mk r, rfl⟩

lemma exact_cokerTarget : Function.Exact (cokerMapTarget (h := h) d) (cokerProjTarget d) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H r =>
  constructor
  · intro hy
    change Submodule.Quotient.mk r = 0 at hy
    rw [Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  · rintro ⟨z, hz⟩
    rw [← hz]
    induction z using Submodule.Quotient.induction_on with
    | H x =>
    change Submodule.Quotient.mk (h x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩

end ChangeTarget

section ChangeSource

variable (d' : P' →ₗ[K] R') (f : P →ₗ[K] P') (hf : Function.Injective f)

/-- `δ : P' / im f → R' / im (d' f)`, induced by `d'`. -/
def deltaSource : (P' ⧸ LinearMap.range f) →ₗ[K] (R' ⧸ LinearMap.range (d' ∘ₗ f)) :=
  (LinearMap.range f).mapQ _ d' (by
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩)

/-- `ker (d' f) → ker d'`, induced by `f`. -/
def kerMapSource : LinearMap.ker (d' ∘ₗ f) →ₗ[K] LinearMap.ker d' :=
  f.restrict (fun x hx => by simpa using hx)

/-- `ker d' → ker δ`. -/
def kerProjSource : LinearMap.ker d' →ₗ[K] LinearMap.ker (deltaSource d' f) :=
  ((LinearMap.range f).mkQ ∘ₗ (LinearMap.ker d').subtype).codRestrict _ (by
    rintro ⟨x, hx⟩
    rw [LinearMap.mem_ker] at hx ⊢
    change Submodule.Quotient.mk (d' x) = 0
    rw [hx]
    rfl)

include hf in
lemma kerMapSource_injective : Function.Injective (kerMapSource d' f) := by
  intro x y hxy
  apply Subtype.ext
  exact hf (congrArg Subtype.val hxy)

lemma kerProjSource_surjective : Function.Surjective (kerProjSource d' f) := by
  rintro ⟨q, hq⟩
  induction q using Submodule.Quotient.induction_on with
  | H x =>
  rw [LinearMap.mem_ker] at hq
  change Submodule.Quotient.mk (d' x) = 0 at hq
  rw [Submodule.Quotient.mk_eq_zero] at hq
  obtain ⟨p, hp⟩ := hq
  refine ⟨⟨x - f p, ?_⟩, ?_⟩
  · rw [LinearMap.mem_ker, map_sub]
    change d' x - d' (f p) = 0
    rw [← LinearMap.comp_apply, hp, sub_self]
  · apply Subtype.ext
    change Submodule.Quotient.mk (x - f p) = Submodule.Quotient.mk x
    rw [Submodule.Quotient.eq, sub_sub_cancel_left]
    exact neg_mem ⟨p, rfl⟩

lemma exact_kerSource : Function.Exact (kerMapSource d' f) (kerProjSource d' f) := by
  rintro ⟨x, hx⟩
  constructor
  · intro h0
    have h1 : (Submodule.Quotient.mk x : P' ⧸ LinearMap.range f) = 0 :=
      congrArg Subtype.val h0
    rw [Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨p, rfl⟩ := h1
    refine ⟨⟨p, ?_⟩, rfl⟩
    rw [LinearMap.mem_ker] at hx ⊢
    exact hx
  · rintro ⟨⟨p, hp⟩, hpx⟩
    apply Subtype.ext
    have : f p = x := congrArg Subtype.val hpx
    change Submodule.Quotient.mk x = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨p, this⟩

/-- The projection `R' / im (d' f) → R' / im d'`. -/
def cokerProjSource : (R' ⧸ LinearMap.range (d' ∘ₗ f)) →ₗ[K] (R' ⧸ LinearMap.range d') :=
  (LinearMap.range (d' ∘ₗ f)).mapQ _ LinearMap.id (by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, rfl⟩)

lemma cokerProjSource_surjective : Function.Surjective (cokerProjSource d' f) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H r => exact ⟨Submodule.Quotient.mk r, rfl⟩

lemma exact_deltaSource : Function.Exact (deltaSource d' f) (cokerProjSource d' f) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H r =>
  constructor
  · intro hy
    change Submodule.Quotient.mk r = 0 at hy
    rw [Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  · rintro ⟨z, hz⟩
    rw [← hz]
    induction z using Submodule.Quotient.induction_on with
    | H x =>
    change Submodule.Quotient.mk (d' x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩

end ChangeSource

/-- **The Euler characteristic of a two-term complex under an injective map with
finite-dimensional cokernels**: for a commutative square `h ∘ d = d' ∘ f` with `f`, `h` injective,
`χ(d') = χ(d) + dim (P' / im f) - dim (R' / im h)`, where `χ(d) = dim ker d - dim coker d`. -/
theorem finrank_twoTerm (d : P →ₗ[K] R) (d' : P' →ₗ[K] R') (f : P →ₗ[K] P') (h : R →ₗ[K] R')
    (hf : Function.Injective f) (hh : Function.Injective h) (hcomm : h ∘ₗ d = d' ∘ₗ f)
    [FiniteDimensional K (LinearMap.ker d)] [FiniteDimensional K (R ⧸ LinearMap.range d)]
    [FiniteDimensional K (P' ⧸ LinearMap.range f)] [FiniteDimensional K (R' ⧸ LinearMap.range h)] :
    FiniteDimensional K (LinearMap.ker d') ∧ FiniteDimensional K (R' ⧸ LinearMap.range d') ∧
      (finrank K (LinearMap.ker d') : ℤ) - finrank K (R' ⧸ LinearMap.range d') =
        (finrank K (LinearMap.ker d) : ℤ) - finrank K (R ⧸ LinearMap.range d) +
          finrank K (P' ⧸ LinearMap.range f) - finrank K (R' ⧸ LinearMap.range h) := by
  -- step A: the complex `h ∘ d`
  obtain ⟨hA, eA⟩ := finrank_eq_of_shortExact (cokerMapTarget_injective d hh)
    (cokerProjTarget_surjective d) (exact_cokerTarget d)
  have hker : LinearMap.ker (h ∘ₗ d) = LinearMap.ker d := ker_comp_of_injective d hh
  -- step B: from `d' ∘ f = h ∘ d` to `d'`
  rw [hcomm] at hA eA hker
  have : FiniteDimensional K (LinearMap.ker (d' ∘ₗ f)) := by rw [hker]; infer_instance
  have eker : finrank K (LinearMap.ker (d' ∘ₗ f)) = finrank K (LinearMap.ker d) := by rw [hker]
  have : FiniteDimensional K (LinearMap.ker (deltaSource d' f)) := inferInstance
  obtain ⟨hK, eK⟩ := finrank_eq_of_shortExact (kerMapSource_injective d' f hf)
    (kerProjSource_surjective d' f) (exact_kerSource d' f)
  have hC : FiniteDimensional K (R' ⧸ LinearMap.range d') :=
    Module.Finite.of_surjective _ (cokerProjSource_surjective d' f)
  have eC := LinearMap.finrank_range_add_finrank_ker (cokerProjSource d' f)
  rw [LinearMap.range_eq_top.mpr (cokerProjSource_surjective d' f), finrank_top,
    LinearMap.exact_iff.mp (exact_deltaSource d' f)] at eC
  have eQ := LinearMap.finrank_range_add_finrank_ker (deltaSource d' f)
  refine ⟨hK, hC, ?_⟩
  omega

section Prod

variable {A₁ A₂ B₁ B₂ : Type*} [AddCommGroup A₁] [Module K A₁] [AddCommGroup A₂] [Module K A₂]
  [AddCommGroup B₁] [Module K B₁] [AddCommGroup B₂] [Module K B₂]
  (f₁ : A₁ →ₗ[K] B₁) (f₂ : A₂ →ₗ[K] B₂)

/-- `B₁ / im f₁ → (B₁ × B₂) / im (f₁ × f₂)`. -/
def quotInl : (B₁ ⧸ LinearMap.range f₁) →ₗ[K] ((B₁ × B₂) ⧸ LinearMap.range (f₁.prodMap f₂)) :=
  (LinearMap.range f₁).mapQ _ (LinearMap.inl K B₁ B₂) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨(x, 0), by simp⟩)

/-- `(B₁ × B₂) / im (f₁ × f₂) → B₂ / im f₂`. -/
def quotSnd : ((B₁ × B₂) ⧸ LinearMap.range (f₁.prodMap f₂)) →ₗ[K] (B₂ ⧸ LinearMap.range f₂) :=
  (LinearMap.range (f₁.prodMap f₂)).mapQ _ (LinearMap.snd K B₁ B₂) (by
    rintro _ ⟨x, rfl⟩
    exact ⟨x.2, rfl⟩)

/-- **The cokernel of a product map** is the product of the cokernels (dimension count). -/
theorem finrank_quotient_prodMap [FiniteDimensional K (B₁ ⧸ LinearMap.range f₁)]
    [FiniteDimensional K (B₂ ⧸ LinearMap.range f₂)] :
    FiniteDimensional K ((B₁ × B₂) ⧸ LinearMap.range (f₁.prodMap f₂)) ∧
      finrank K ((B₁ × B₂) ⧸ LinearMap.range (f₁.prodMap f₂)) =
        finrank K (B₁ ⧸ LinearMap.range f₁) + finrank K (B₂ ⧸ LinearMap.range f₂) := by
  apply finrank_eq_of_shortExact (f := quotInl f₁ f₂) (g := quotSnd f₁ f₂)
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H b =>
    rw [LinearMap.mem_ker] at hy
    change Submodule.Quotient.mk ((b, 0) : B₁ × B₂) = 0 at hy
    rw [Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨x, hx⟩ := hy
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact ⟨x.1, congrArg Prod.fst hx⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H b => exact ⟨Submodule.Quotient.mk (0, b), rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H b =>
    constructor
    · intro hy
      change Submodule.Quotient.mk b.2 = 0 at hy
      rw [Submodule.Quotient.mk_eq_zero] at hy
      obtain ⟨x, hx⟩ := hy
      refine ⟨Submodule.Quotient.mk b.1, ?_⟩
      change Submodule.Quotient.mk ((b.1, 0) : B₁ × B₂) = Submodule.Quotient.mk b
      rw [Submodule.Quotient.eq]
      refine ⟨(0, -x), ?_⟩
      simp only [LinearMap.prodMap_apply, map_zero, map_neg, hx]
      ext <;> simp
    · rintro ⟨z, hz⟩
      rw [← hz]
      induction z using Submodule.Quotient.induction_on with
      | H x =>
      change Submodule.Quotient.mk (0 : B₂) = 0
      rfl

end Prod

end TwoTerm

/-! ### Pulling back a presentation along an affine morphism -/

section Pullback

variable {X Y : Scheme.{u}} (ν : Y ⟶ X)

lemma structureCoeff_comp {K : Type u} [CommRing K] (p : X ⟶ Spec (.of K)) :
    structureCoeff (ν ≫ p) = ν.appTop.hom.comp (structureCoeff p) := by
  ext r
  simp only [structureCoeff, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]

lemma sectionsRingHom_comp_appTop {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤)) (W : X.Opens)
    (r : K) : sectionsRingHom (ν.appTop.hom.comp c) (le_top : ν ⁻¹ᵁ W ≤ ⊤) r =
      ν.app W (sectionsRingHom c (le_top : W ≤ ⊤) r) :=
  (NatTrans.naturality_apply ν.c (homOfLE (le_top : W ≤ ⊤)).op (c r)).symm

/-- `ν^♯ : Γ(W, 𝒪_X) → Γ(ν⁻¹W, 𝒪_Y)` as a linear map over the field of constants. -/
def pullLin {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤)) (W : X.Opens) :
    sectionsModuleCat (unitModule X) c W le_top →ₗ[K]
      sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c) (ν ⁻¹ᵁ W) le_top where
  toFun a := (ν.app W).hom a
  map_add' a b := map_add (ν.app W).hom a b
  map_smul' r a := by
    have e : ∀ x : Γ(X, W), (ν.app W).hom (sectionsRingHom c le_top r * x) =
        sectionsRingHom (ν.appTop.hom.comp c) le_top r * (ν.app W).hom x := fun x => by
      rw [map_mul, sectionsRingHom_comp_appTop]
    exact e a

lemma pullLin_apply {K : Type u} [CommRing K] (c : K →+* Γ(X, ⊤)) (W : X.Opens)
    (a : sectionsModuleCat (unitModule X) c W le_top) :
    (pullLin ν c W a : Γ(Y, ν ⁻¹ᵁ W)) = (ν.app W).hom a := rfl

/-- Pullback of sections is semilinear over `ν^♯`. -/
lemma Sections.pullback_smul' {L : Projectivity.LineBundleData X} {m : ℤ} {W : X.Opens}
    (r : Γ(X, W)) (s : L.Sections m W) : (r • s).pullback ν = ν.app W r • s.pullback ν := by
  ext i
  change ν.app (W ⊓ L.U i) (res (inf_le_left : W ⊓ L.U i ≤ W) r * s.coeff i) =
    res (ν.preimage_mono (inf_le_left : W ⊓ L.U i ≤ W)) (ν.app W r) *
      ν.app (W ⊓ L.U i) (s.coeff i)
  rw [map_mul, LineBundleData.app_res]

/-- Pullback of sections commutes with restriction. -/
lemma Sections.pullback_restrict' {L : Projectivity.LineBundleData X} {m : ℤ} {W W' : X.Opens}
    (h : W' ≤ W) (s : L.Sections m W) :
    (s.restrict h).pullback ν = (s.pullback ν).restrict (ν.preimage_mono h) := by
  ext i
  simp only [Sections.coeff_restrict]
  exact LineBundleData.app_res ν _ _

variable [IsAffineHom ν] {L : Projectivity.LineBundleData X}

/-- The **pullback of a two-chart presentation** along an affine morphism. -/
def Presentation.pullback (P : Presentation L) : Presentation (L.pullback ν) where
  U := ν ⁻¹ᵁ P.U
  V := ν ⁻¹ᵁ P.V
  isAffineOpen_U := P.isAffineOpen_U.preimage ν
  isAffineOpen_V := P.isAffineOpen_V.preimage ν
  sup_eq := by rw [← Scheme.Hom.preimage_sup, P.sup_eq, Scheme.Hom.preimage_top]
  f := ν.app P.V P.f
  basicOpen_f := by rw [← Scheme.preimage_basicOpen, P.basicOpen_f]; rfl
  τ := P.τ.pullback ν
  nonvanishingLocus_τ := by rw [Sections.nonvanishingLocus_pullback, P.nonvanishingLocus_τ]
  σ := P.σ.pullback ν
  nonvanishingLocus_σ := by rw [Sections.nonvanishingLocus_pullback, P.nonvanishingLocus_σ]

omit [IsAffineHom ν] in
/-- The transition function is characterized by `τ| = g σ|`. -/
lemma transFun_eq_of_eq_smul {Z : Scheme.{u}} {M : Projectivity.LineBundleData Z} {N : ℤ}
    {U V : Z.Opens} {τ : M.Sections N U} {σ : M.Sections N V} (hσ : σ.nonvanishingLocus = V)
    {r : Γ(Z, U ⊓ V)}
    (h : τ.restrict (inf_le_left : U ⊓ V ≤ U) = r • σ.restrict (inf_le_right : U ⊓ V ≤ V)) :
    transFun τ hσ = r := by
  unfold transFun
  rw [h, ← mulSec_unit]
  exact (mulSecEquiv (unitModule Z) _).symm_apply_apply r

/-- The transition function of the pulled-back presentation is the pullback of the transition
function. -/
lemma Presentation.coe_pullback_g (P : Presentation L) :
    ((P.pullback ν).g : Γ(Y, (P.pullback ν).U ⊓ (P.pullback ν).V)) =
      ν.app (P.U ⊓ P.V) (P.g : Γ(X, P.U ⊓ P.V)) := by
  rw [Presentation.g, coe_transUnit]
  apply transFun_eq_of_eq_smul
  have h := congrArg (Sections.pullback ν) (restrict_eq_transFun_smul P.τ P.nonvanishingLocus_σ)
  rw [Sections.pullback_smul', Sections.pullback_restrict', Sections.pullback_restrict'] at h
  have hg : (P.g : Γ(X, P.U ⊓ P.V)) = transFun P.τ P.nonvanishingLocus_σ :=
    coe_transUnit P.nonvanishingLocus_σ P.nonvanishingLocus_τ
  rw [hg]
  exact h


/-! ### The comparison of the two-term complexes -/

section Comparison

variable {K : Type u} [Field K] (c : K →+* Γ(X, ⊤)) (P : Presentation L)

/-- `ν^♯` on `U ∩ V`, with the target written as the intersection of the pulled-back charts. -/
abbrev pullLinInf : sectionsModuleCat (unitModule X) c (P.U ⊓ P.V) le_top →ₗ[K]
    sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c)
      ((P.pullback ν).U ⊓ (P.pullback ν).V) le_top :=
  pullLin ν c (P.U ⊓ P.V)

/-- `ν^♯` on `U`, with the target written as the pulled-back chart. -/
abbrev pullLinU : sectionsModuleCat (unitModule X) c P.U le_top →ₗ[K]
    sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c) (P.pullback ν).U le_top :=
  pullLin ν c P.U

/-- `ν^♯` on `V`, with the target written as the pulled-back chart. -/
abbrev pullLinV : sectionsModuleCat (unitModule X) c P.V le_top →ₗ[K]
    sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c) (P.pullback ν).V le_top :=
  pullLin ν c P.V

/-- **`ν^♯` is a map of the twisted two-term complexes** of `𝓛^k` on `X` and of `ν^*𝓛^k` on
`Y`. -/
lemma twistDiff_pullLin (k : ℕ) :
    pullLinInf ν c P ∘ₗ twistDiff (resUV (unitModule X) P.U P.V c)
        (resVU (unitModule X) P.U P.V c)
        (smulLin (unitModule X) c ((P.g ^ (k : ℤ) : Γ(X, P.U ⊓ P.V)ˣ) : Γ(X, P.U ⊓ P.V))) =
      twistDiff (resUV (unitModule Y) (P.pullback ν).U (P.pullback ν).V (ν.appTop.hom.comp c))
        (resVU (unitModule Y) (P.pullback ν).U (P.pullback ν).V (ν.appTop.hom.comp c))
        (smulLin (unitModule Y) (ν.appTop.hom.comp c)
          (((P.pullback ν).g ^ (k : ℤ) : Γ(Y, (P.pullback ν).U ⊓ (P.pullback ν).V)ˣ) :
            Γ(Y, (P.pullback ν).U ⊓ (P.pullback ν).V))) ∘ₗ
        (pullLinU ν c P).prodMap (pullLinV ν c P) := by
  apply LinearMap.ext
  rintro ⟨a, b⟩
  have hg := P.coe_pullback_g ν
  change ν.app (P.U ⊓ P.V) (X.presheaf.map (homOfLE (inf_le_right : P.U ⊓ P.V ≤ P.V)).op b -
      ((P.g ^ (k : ℤ) : Γ(X, P.U ⊓ P.V)ˣ) : Γ(X, P.U ⊓ P.V)) *
        X.presheaf.map (homOfLE (inf_le_left : P.U ⊓ P.V ≤ P.U)).op a) =
    Y.presheaf.map (homOfLE (inf_le_right : (P.pullback ν).U ⊓ (P.pullback ν).V ≤
        (P.pullback ν).V)).op (ν.app P.V b) -
      (((P.pullback ν).g ^ (k : ℤ) : Γ(Y, (P.pullback ν).U ⊓ (P.pullback ν).V)ˣ) :
        Γ(Y, (P.pullback ν).U ⊓ (P.pullback ν).V)) *
        Y.presheaf.map (homOfLE (inf_le_left : (P.pullback ν).U ⊓ (P.pullback ν).V ≤
          (P.pullback ν).U)).op (ν.app P.U a)
  have hb : ν.app (P.U ⊓ P.V) (X.presheaf.map (homOfLE (inf_le_right : P.U ⊓ P.V ≤ P.V)).op b) =
      Y.presheaf.map (homOfLE (inf_le_right : (P.pullback ν).U ⊓ (P.pullback ν).V ≤
        (P.pullback ν).V)).op (ν.app P.V b) := LineBundleData.app_res ν _ _
  have ha : ν.app (P.U ⊓ P.V) (X.presheaf.map (homOfLE (inf_le_left : P.U ⊓ P.V ≤ P.U)).op a) =
      Y.presheaf.map (homOfLE (inf_le_left : (P.pullback ν).U ⊓ (P.pullback ν).V ≤
        (P.pullback ν).U)).op (ν.app P.U a) := LineBundleData.app_res ν _ _
  rw [map_sub, map_mul, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, map_pow, hg, hb, ha]
  rfl

omit [IsAffineHom ν] in
/-- A finite cokernel of `ν^♯` on `W` (in the form of the genus formula, `Genus.IsFiniteCoker`) is
a finite cokernel of `pullLin`. -/
lemma finiteDimensional_coker_pullLin {W : X.Opens}
    (h : Genus.IsFiniteCoker (sectionsRingHom c (le_top : W ≤ ⊤)) (ν.app W).hom) :
    FiniteDimensional K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c) (ν ⁻¹ᵁ W) le_top ⧸
      LinearMap.range (pullLin ν c W)) := by
  let := (sectionsRingHom c (le_top : W ≤ ⊤)).toAlgebra
  let := (ν.app W).hom.toAlgebra
  let := ((ν.app W).hom.comp (sectionsRingHom c (le_top : W ≤ ⊤))).toAlgebra
  have : IsScalarTower K Γ(X, W) Γ(Y, ν ⁻¹ᵁ W) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have h' : FiniteDimensional K (Genus.Coker Γ(X, W) Γ(Y, ν ⁻¹ᵁ W)) := h
  set p := LinearMap.range (Algebra.linearMap Γ(X, W) Γ(Y, ν ⁻¹ᵁ W))
  have h'' : FiniteDimensional K (Γ(Y, ν ⁻¹ᵁ W) ⧸ p.restrictScalars K) :=
    Module.Finite.equiv (Submodule.Quotient.restrictScalarsEquiv K p).symm
  let φ : Γ(Y, ν ⁻¹ᵁ W) →ₗ[K]
      sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c) (ν ⁻¹ᵁ W) le_top :=
    { toFun := fun b => b
      map_add' := fun _ _ => rfl
      map_smul' := fun r b => by
        change (ν.app W).hom (sectionsRingHom c le_top r) * b =
          sectionsRingHom (ν.appTop.hom.comp c) le_top r * b
        rw [sectionsRingHom_comp_appTop]
        rfl }
  let ψ := (LinearMap.range (pullLin ν c W)).mkQ ∘ₗ φ
  have hker : p.restrictScalars K ≤ LinearMap.ker ψ := by
    rintro _ ⟨a, rfl⟩
    rw [LinearMap.mem_ker]
    apply (Submodule.Quotient.mk_eq_zero _).mpr
    exact ⟨(show sectionsModuleCat (unitModule X) c W le_top from a), rfl⟩
  have hsurj : Function.Surjective ((p.restrictScalars K).liftQ ψ hker) := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ z
    exact ⟨Submodule.Quotient.mk (show Γ(Y, ν ⁻¹ᵁ W) from y), rfl⟩
  exact Module.Finite.of_surjective _ hsurj

/-- **The Euler characteristics of `𝓛^k` and `ν^*𝓛^k` differ by a constant**: for the two-term
complexes, `χ_Y(k) = χ_X(k) + dim coker_U + dim coker_V - dim coker_{U ∩ V}`, the cokernels of
`ν^♯` on the charts. -/
theorem Presentation.euler_pullback (k : ℕ)
    [FiniteDimensional K (H0 (resUV (unitModule X) P.U P.V c) (resVU (unitModule X) P.U P.V c)
      (smulLin (unitModule X) c ((P.g ^ (k : ℤ) : Γ(X, P.U ⊓ P.V)ˣ) : Γ(X, P.U ⊓ P.V))))]
    [FiniteDimensional K (H1 (resUV (unitModule X) P.U P.V c) (resVU (unitModule X) P.U P.V c)
      (smulLin (unitModule X) c ((P.g ^ (k : ℤ) : Γ(X, P.U ⊓ P.V)ˣ) : Γ(X, P.U ⊓ P.V))))]
    (hinjU : Function.Injective (ν.app P.U).hom) (hinjV : Function.Injective (ν.app P.V).hom)
    (hinjUV : Function.Injective (ν.app (P.U ⊓ P.V)).hom)
    [FiniteDimensional K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c)
      (P.pullback ν).U le_top ⧸ LinearMap.range (pullLinU ν c P))]
    [FiniteDimensional K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c)
      (P.pullback ν).V le_top ⧸ LinearMap.range (pullLinV ν c P))]
    [FiniteDimensional K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c)
      ((P.pullback ν).U ⊓ (P.pullback ν).V) le_top ⧸ LinearMap.range (pullLinInf ν c P))] :
    FiniteDimensional K (H0 (resUV (unitModule Y) (P.pullback ν).U (P.pullback ν).V
        (ν.appTop.hom.comp c)) (resVU (unitModule Y) (P.pullback ν).U (P.pullback ν).V
        (ν.appTop.hom.comp c)) (smulLin (unitModule Y) (ν.appTop.hom.comp c)
          (((P.pullback ν).g ^ (k : ℤ) : Γ(Y, (P.pullback ν).U ⊓ (P.pullback ν).V)ˣ) :
            Γ(Y, (P.pullback ν).U ⊓ (P.pullback ν).V)))) ∧
    FiniteDimensional K (H1 (resUV (unitModule Y) (P.pullback ν).U (P.pullback ν).V
        (ν.appTop.hom.comp c)) (resVU (unitModule Y) (P.pullback ν).U (P.pullback ν).V
        (ν.appTop.hom.comp c)) (smulLin (unitModule Y) (ν.appTop.hom.comp c)
          (((P.pullback ν).g ^ (k : ℤ) : Γ(Y, (P.pullback ν).U ⊓ (P.pullback ν).V)ˣ) :
            Γ(Y, (P.pullback ν).U ⊓ (P.pullback ν).V)))) ∧
    euler (resUV (unitModule Y) (P.pullback ν).U (P.pullback ν).V (ν.appTop.hom.comp c))
        (resVU (unitModule Y) (P.pullback ν).U (P.pullback ν).V (ν.appTop.hom.comp c))
        (smulLin (unitModule Y) (ν.appTop.hom.comp c)
          (((P.pullback ν).g ^ (k : ℤ) : Γ(Y, (P.pullback ν).U ⊓ (P.pullback ν).V)ˣ) :
            Γ(Y, (P.pullback ν).U ⊓ (P.pullback ν).V))) =
      euler (resUV (unitModule X) P.U P.V c) (resVU (unitModule X) P.U P.V c)
        (smulLin (unitModule X) c ((P.g ^ (k : ℤ) : Γ(X, P.U ⊓ P.V)ˣ) : Γ(X, P.U ⊓ P.V))) +
        finrank K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c) (P.pullback ν).U
          le_top ⧸ LinearMap.range (pullLinU ν c P)) +
        finrank K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c) (P.pullback ν).V
          le_top ⧸ LinearMap.range (pullLinV ν c P)) -
        finrank K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c)
          ((P.pullback ν).U ⊓ (P.pullback ν).V) le_top ⧸ LinearMap.range (pullLinInf ν c P)) := by
  obtain ⟨hPf, ePf⟩ := finrank_quotient_prodMap (pullLinU ν c P) (pullLinV ν c P)
  obtain ⟨h0, h1, e⟩ := finrank_twoTerm _ _ ((pullLinU ν c P).prodMap (pullLinV ν c P))
    (pullLinInf ν c P) (Function.Injective.prodMap hinjU hinjV) hinjUV (twistDiff_pullLin ν c P k)
  refine ⟨h0, h1, ?_⟩
  unfold euler
  rw [e, ePf]
  push_cast
  ring

end Comparison

/-! ### Equality of degrees -/

section Degree

variable {Z : Scheme.{u}} [CompactSpace Z]
  [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Z))] {M : Projectivity.LineBundleData Z}
  {K : Type u} [Field K] (c : K →+* Γ(Z, ⊤)) (Q : Presentation M)

omit [IsAffineHom ν] in
/-- `χ(𝓛^k)` is the Euler characteristic of the twisted two-term complex of a presentation. -/
lemma Presentation.eulerCharOf_eq_euler (k : ℕ) :
    DualityScheme.eulerCharOf (M.twist (unitModule Z) k) c =
      euler (resUV (unitModule Z) Q.U Q.V c) (resVU (unitModule Z) Q.U Q.V c)
        (smulLin (unitModule Z) c ((Q.g ^ (k : ℤ) : Γ(Z, Q.U ⊓ Q.V)ˣ) : Γ(Z, Q.U ⊓ Q.V))) := by
  rw [DualityScheme.eulerCharOf_eq_of_pair _ c Q.sup_eq Q.isAffineOpen_U Q.isAffineOpen_V
    Q.isAffineOpen_inf, LinearEquiv.finrank_eq (Q.cohomologyZeroEquiv c k),
    LinearEquiv.finrank_eq (Q.cohomologyOneEquiv c k)]
  rfl

omit [IsAffineHom ν] in
/-- `χ(𝒪) = χ(𝓛^0)`. -/
lemma Presentation.eulerCharOf_unit_eq (Q : Presentation M) (k : ℕ) (hk : k = 0) :
    DualityScheme.eulerCharOf (unitModule Z) c =
      DualityScheme.eulerCharOf (M.twist (unitModule Z) k) c := by
  subst hk
  have e : M.twist (unitModule Z) ((0 : ℕ) : ℤ) ≅ unitModule Z :=
    M.twistCongr (unitModule Z) (by simp) ≪≫ M.twistZeroIso (unitModule Z)
  rw [DualityScheme.eulerCharOf_eq_of_pair _ c Q.sup_eq Q.isAffineOpen_U Q.isAffineOpen_V
      Q.isAffineOpen_inf,
    DualityScheme.eulerCharOf_eq_of_pair _ c Q.sup_eq Q.isAffineOpen_U Q.isAffineOpen_V
      Q.isAffineOpen_inf,
    LinearEquiv.finrank_eq (cohomologyIsoOfIso e c 0).toLinearEquiv,
    LinearEquiv.finrank_eq (cohomologyIsoOfIso e c 1).toLinearEquiv]

omit [IsAffineHom ν] in
/-- On a projective scheme the two-term complexes of the twists have finite-dimensional cohomology. -/
lemma Presentation.finiteDimensional_H01 {p : Z ⟶ Spec (.of K)} (hp : IsProjectiveOver p)
    (k : ℕ) :
    FiniteDimensional K (H0 (resUV (unitModule Z) Q.U Q.V (structureCoeff p))
      (resVU (unitModule Z) Q.U Q.V (structureCoeff p)) (smulLin (unitModule Z) (structureCoeff p)
        ((Q.g ^ (k : ℤ) : Γ(Z, Q.U ⊓ Q.V)ˣ) : Γ(Z, Q.U ⊓ Q.V)))) ∧
    FiniteDimensional K (H1 (resUV (unitModule Z) Q.U Q.V (structureCoeff p))
      (resVU (unitModule Z) Q.U Q.V (structureCoeff p)) (smulLin (unitModule Z) (structureCoeff p)
        ((Q.g ^ (k : ℤ) : Γ(Z, Q.U ⊓ Q.V)ˣ) : Γ(Z, Q.U ⊓ Q.V)))) := by
  have hfs : ∀ W : Z.Opens, IsAffineOpen W →
      Module.Finite Γ(Z, W) Γ(M.twist (unitModule Z) k, W) := fun W hW =>
    finite_sections_twist M (unitModule Z) (fun W _ => Module.Finite.self _) k hW
  have h0 := finite_cohomology_of_isProjectiveOver hp (M.twist (unitModule Z) k) hfs 0
  have h1 := finite_cohomology_of_isProjectiveOver hp (M.twist (unitModule Z) k) hfs 1
  exact ⟨Module.Finite.equiv (Q.cohomologyZeroEquiv (structureCoeff p) k),
    Module.Finite.equiv (Q.cohomologyOneEquiv (structureCoeff p) k)⟩

end Degree

variable [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  [CompactSpace Y] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from Y))]

/-- **The degree does not change under a finite birational map** (blueprint
`lem:sm-ample-positive-normalization`): if `ν : Y → X` is affine and `ν^♯` is injective with
finite-dimensional cokernel on every affine open (e.g. the normalization of an integral curve), and
`𝓛` has a two-chart presentation on the projective `X`, then `deg ν^*𝓛 = deg 𝓛`. -/
theorem degree_pullback_eq {K : Type u} [Field K] {p : X ⟶ Spec (.of K)}
    (hp : IsProjectiveOver p) (P : Presentation L)
    (hinj : ∀ W : X.Opens, IsAffineOpen W → Function.Injective (ν.app W).hom)
    (hfin : ∀ W : X.Opens, IsAffineOpen W →
      Genus.IsFiniteCoker (sectionsRingHom (structureCoeff p) (le_top : W ≤ ⊤)) (ν.app W).hom) :
    degree (L.pullback ν) (ν.appTop.hom.comp (structureCoeff p)) =
      degree L (structureCoeff p) := by
  set c := structureCoeff p
  have : FiniteDimensional K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c)
      (P.pullback ν).U le_top ⧸ LinearMap.range (pullLinU ν c P)) :=
    finiteDimensional_coker_pullLin ν c (hfin P.U P.isAffineOpen_U)
  have : FiniteDimensional K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c)
      (P.pullback ν).V le_top ⧸ LinearMap.range (pullLinV ν c P)) :=
    finiteDimensional_coker_pullLin ν c (hfin P.V P.isAffineOpen_V)
  have : FiniteDimensional K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c)
      ((P.pullback ν).U ⊓ (P.pullback ν).V) le_top ⧸ LinearMap.range (pullLinInf ν c P)) :=
    finiteDimensional_coker_pullLin ν c (hfin (P.U ⊓ P.V) P.isAffineOpen_inf)
  have key : ∀ k : ℕ, DualityScheme.eulerCharOf ((L.pullback ν).twist (unitModule Y) k)
      (ν.appTop.hom.comp c) = DualityScheme.eulerCharOf (L.twist (unitModule X) k) c +
        finrank K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c) (P.pullback ν).U
          le_top ⧸ LinearMap.range (pullLinU ν c P)) +
        finrank K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c) (P.pullback ν).V
          le_top ⧸ LinearMap.range (pullLinV ν c P)) -
        finrank K (sectionsModuleCat (unitModule Y) (ν.appTop.hom.comp c)
          ((P.pullback ν).U ⊓ (P.pullback ν).V) le_top ⧸ LinearMap.range (pullLinInf ν c P)) := by
    intro k
    obtain ⟨h0, h1⟩ := P.finiteDimensional_H01 hp k
    obtain ⟨-, -, e⟩ := P.euler_pullback ν c k (hinj _ P.isAffineOpen_U) (hinj _ P.isAffineOpen_V)
      (hinj _ P.isAffineOpen_inf)
    rw [(P.pullback ν).eulerCharOf_eq_euler, P.eulerCharOf_eq_euler, e]
  unfold degree
  rw [Presentation.eulerCharOf_unit_eq c P 0 rfl,
    Presentation.eulerCharOf_unit_eq _ (P.pullback ν) 0 rfl]
  have k1 := key 1
  have k0 := key 0
  simp only [Nat.cast_one, Nat.cast_zero] at k1 k0 ⊢
  linarith

/-- **Positive degree on the normalization gives a section with a zero** (blueprint
`thm:sm-ample-positive-normalization`): let `X` be an integral projective curve over an infinite
field and `ν : Y → X` affine with `ν^♯` injective with finite-dimensional cokernel on affine opens
(the normalization). If `deg ν^*𝓛 > 0`, some `𝓛^n`, `n > 0`, has a global section which does not
vanish at the non-closed points and vanishes at a specialization of each of them. -/
theorem exists_section_of_degree_pullback_pos {K : Type u} [Field K] [Infinite K] [IsIntegral X]
    {p : X ⟶ Spec (.of K)} (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1)
    (hinj : ∀ W : X.Opens, IsAffineOpen W → Function.Injective (ν.app W).hom)
    (hfin : ∀ W : X.Opens, IsAffineOpen W →
      Genus.IsFiniteCoker (sectionsRingHom (structureCoeff p) (le_top : W ≤ ⊤)) (ν.app W).hom)
    (hdeg : 0 < degree (L.pullback ν) (ν.appTop.hom.comp (structureCoeff p))) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : L.Sections n ⊤,
      (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) := by
  obtain ⟨P, -⟩ := exists_presentation_of_isIntegral hp hdim L
  rw [degree_pullback_eq ν hp P hinj hfin] at hdeg
  exact exists_section_of_degree_pos_of_isIntegral hp hdim L hdeg

end Pullback

/-! ### The normalization of an integral curve -/

open Geometry.NormalizationGluing in
/-- **Positive degree on the normalization of an integral curve gives a section with a zero**
(blueprint `thm:sm-ample-positive-normalization`), for Codex's normalization
`ν = normalizationStructure X : X̃ → X`: if `deg ν^*𝓛 = χ(ν^*𝓛) - χ(𝒪_{X̃}) > 0`, some `𝓛^n`,
`n > 0`, has a global section which does not vanish at the non-closed points and vanishes at a
specialization of each of them. -/
theorem exists_section_of_degree_normalization_pos {K : Type u} [Field K] [Infinite K]
    {X : Scheme.{u}} [IsIntegral X] {p : X ⟶ Spec (.of K)} [LocallyOfFiniteType p]
    (hp : IsProjectiveOver p) (hdim : topologicalKrullDim X ≤ 1) [CompactSpace X]
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
    (L : Projectivity.LineBundleData X)
    (hdeg :
      haveI := Genus.normalization_isAffineHom p
      haveI := Genus.compactSpace_of_isAffineHom (normalizationStructure X)
      haveI := Genus.isAffineHom_diagonal_of_isAffineHom (normalizationStructure X)
      0 < degree (L.pullback (normalizationStructure X))
        ((normalizationStructure X).appTop.hom.comp (structureCoeff p))) :
    ∃ n : ℕ, 0 < n ∧ ∃ s : L.Sections n ⊤,
      (∀ x : X, ¬ IsClosed ({x} : Set X) → x ∈ s.nonvanishingLocus) ∧
      (∀ x : X, ¬ IsClosed ({x} : Set X) → ∃ z, x ⤳ z ∧ z ∉ s.nonvanishingLocus) := by
  have := Genus.normalization_isAffineHom p
  have := Genus.compactSpace_of_isAffineHom (normalizationStructure X)
  have := Genus.isAffineHom_diagonal_of_isAffineHom (normalizationStructure X)
  exact exists_section_of_degree_pullback_pos (normalizationStructure X) hp hdim
    Genus.normalization_app_injective (fun W hW => Genus.normalization_isFiniteCoker p hdim W hW)
    hdeg

end

end DeJongAlterations.StableModification.CurvesField.Positive
