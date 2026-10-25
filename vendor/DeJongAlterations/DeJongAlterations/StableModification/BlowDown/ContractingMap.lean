/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.BlowDown.Stable
import DeJongAlterations.StableModification.BlowDown.ClosureComponent
import DeJongAlterations.StableModification.Projectivity.SectionsMap
import DeJongAlterations.Geometry.ProjectiveSpaceBaseChange
import DeJongAlterations.Geometry.ChowLemmaProduct

/-!
# The contracting morphism `h̄ : C′ → ℙ¹_C` from two sections (Temkin, Prop. 4.4.6)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Prop. 4.4.6 (T:3203–3226): from a section `h ∈ H⁰(C′, 𝓛)` of `𝓛 = 𝒪(m ∑ P̄ᵢ)` which together with
the canonical section of `𝓛` generates `𝓛`, one gets `h : C′ → ℙ¹_S` and
`h̄ = (h, f) : C′ → ℙ¹_C`, which "contracts `Z` to a point and `Z` is the only component of `C′_s`
contracted by `h̄`" (T:3224–3226). This file proves that last step for the morphism given by two
generating sections `s₀`, `s₁` of a line bundle (OM3A's `LineBundleData.toProjectiveSpace`), under
three conditions on the zero locus of `s₀` (the divisor `m ∑ P̄ᵢ`):

* `closure {Z}` does not meet the zero locus of `s₀` (the points `pᵢ` are on the other
  components);
* no generic point of the closed fibre lies on it;
* every other component of the closed fibre meets it.

Then (`contractsExactlyAt_contractingMap`) `g = (h, β) : Y → ℙ¹_V ×_V C` contracts exactly `Z`
among the components of the closed fibre (`ContractsExactlyAt`):

* on a component `W ≠ Z` the map `h` takes the value `∞` at a zero of `s₀` and a finite value at
  the generic point, so `g` is not constant on `closure {W}`;
* on `Z`, the reduced closure `closure {Z}` (`ClosureComponent.closureScheme`) is integral and
  proper over the residue field, so its global sections form a field
  (Mathlib's `isField_of_universallyClosed`); `h` maps it into the affine chart `D₊(x₀)` and `β`
  maps it to a point, so `g` factors through `Spec Γ(closure {Z}, 𝒪)`, a single point
  (`apply_eq_of_isField`). No identification `closure {Z} ≅ ℙ¹` and no computation of
  `H⁰(closure {Z}, 𝒪)` beyond its being a field is needed.

The target `P = ℙ¹_V ×_V C` is projective over `V` when `C` is
(`Geometry.ChowLemmaProduct.isProjectiveOver_product`) and of finite presentation over `V`
(`locallyOfFinitePresentation_projectiveSpaceStructure`, by the coordinate charts). The result is
`exists_contracting_of_sections`, the conclusion of `ContractingMorphismExists` for one
exceptional component. Blueprint `sm-blow-down-contracting.tex`, `lem:sm-bdc-map-contracts`.
-/

namespace DeJongAlterations.StableModification.BlowDown.ContractingMap

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open DeJongAlterations.Geometry.ProjectiveIdeal DeJongAlterations.Geometry.ProjectiveSpaceBaseChange
open DeJongAlterations.StableModification.Projectivity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

universe u

noncomputable section

section Constant

/-- The prime ideals of a field are `⊥`: the spectrum of a field is a single point. -/
theorem subsingleton_spec_of_isField {X : Scheme.{u}} (hX : IsField Γ(X, ⊤)) :
    Subsingleton (Spec Γ(X, ⊤)) := by
  have key : ∀ p : PrimeSpectrum Γ(X, ⊤), p.asIdeal = ⊥ := by
    intro p
    rw [eq_bot_iff]
    intro x hx
    by_contra hx0
    obtain ⟨y, hy⟩ := hX.mul_inv_cancel hx0
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx (IsUnit.of_mul_eq_one y hy))
  constructor
  intro a b
  exact PrimeSpectrum.ext ((key a).trans (key b).symm)

/-- If `Γ(X, 𝒪_X)` is a field, `X → Spec Γ(X, 𝒪_X)` is constant. -/
theorem toSpecΓ_apply_eq {X : Scheme.{u}} (hX : IsField Γ(X, ⊤)) (x x' : X) :
    X.toSpecΓ x = X.toSpecΓ x' := by
  have := subsingleton_spec_of_isField hX
  exact Subsingleton.elim _ _

/-- A morphism into an affine scheme factors through `X.toSpecΓ`. -/
theorem toSpecΓ_comp_eq {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) :
    X.toSpecΓ ≫ Spec.map f.appTop ≫ Y.isoSpec.inv = f := by
  rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, Scheme.isoSpec,
    asIso_inv, IsIso.hom_inv_id, Category.comp_id]

/-- A morphism with image in an affine open factors through `X.toSpecΓ`. -/
theorem exists_toSpecΓ_comp {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens} (hU : IsAffineOpen U)
    (hf : Set.range f ⊆ U) : ∃ k : Spec Γ(X, ⊤) ⟶ Y, X.toSpecΓ ≫ k = f := by
  have hr : Set.range f ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  let f' := IsOpenImmersion.lift U.ι f hr
  have : IsAffine U.toScheme := hU
  refine ⟨Spec.map f'.appTop ≫ U.toScheme.isoSpec.inv ≫ U.ι, ?_⟩
  rw [← Category.assoc, ← Category.assoc, Category.assoc X.toSpecΓ, toSpecΓ_comp_eq,
    IsOpenImmersion.lift_fac]

/-- Two morphisms `Spec Γ(X) → S` into an affine scheme agreeing after `X.toSpecΓ` agree. -/
theorem eq_of_toSpecΓ_comp_eq {X S : Scheme.{u}} [IsAffine S] {a b : Spec Γ(X, ⊤) ⟶ S}
    (h : X.toSpecΓ ≫ a = X.toSpecΓ ≫ b) : a = b := by
  apply ext_of_isAffine
  have h' := congrArg Scheme.Hom.appTop h
  simp only [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop] at h'
  exact (cancel_mono _).mp h'

/-- **Constancy on schemes with a field of global sections.** If `Γ(X, 𝒪_X)` is a field and `g`
maps `X` into a fibre product `Y₁ ×_S Y₂` over an affine `S` such that both projections of `g`
land in affine opens, then `g` is constant: it factors through `Spec Γ(X, 𝒪_X)`. -/
theorem apply_eq_of_isField {X Y₁ Y₂ S : Scheme.{u}} [IsAffine S] (hX : IsField Γ(X, ⊤))
    {a : Y₁ ⟶ S} {b : Y₂ ⟶ S} (g : X ⟶ pullback a b) {U₁ : Y₁.Opens} {U₂ : Y₂.Opens}
    (hU₁ : IsAffineOpen U₁) (hU₂ : IsAffineOpen U₂)
    (h₁ : Set.range (g ≫ pullback.fst a b) ⊆ U₁) (h₂ : Set.range (g ≫ pullback.snd a b) ⊆ U₂)
    (x x' : X) : g x = g x' := by
  obtain ⟨k₁, hk₁⟩ := exists_toSpecΓ_comp _ hU₁ h₁
  obtain ⟨k₂, hk₂⟩ := exists_toSpecΓ_comp _ hU₂ h₂
  have hk : k₁ ≫ a = k₂ ≫ b := by
    apply eq_of_toSpecΓ_comp_eq
    rw [← Category.assoc, hk₁, ← Category.assoc, hk₂, Category.assoc, Category.assoc,
      pullback.condition]
  have hg : X.toSpecΓ ≫ pullback.lift k₁ k₂ hk = g := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, hk₁]
    · rw [Category.assoc, pullback.lift_snd, hk₂]
  rw [← hg, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, toSpecΓ_apply_eq hX x x']

end Constant

section ProjectiveSpace

/-- **Projective space is of finite presentation** over any ring: it is covered by the coordinate
charts `D₊(x_j) ≅ Spec R[x_i / x_j]` (`nativeCoordinateSchemeIso`). -/
theorem locallyOfFinitePresentation_projectiveSpaceStructure (R : Type u) [CommRing R] (n : ℕ) :
    LocallyOfFinitePresentation (projectiveSpaceStructure R n) := by
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
    (iSup_nativeCoordinateOpen_eq_top (R := R) (n := n))]
  intro j
  have e : (nativeCoordinateOpen (R := R) j).ι ≫ projectiveSpaceStructure R n =
      (nativeCoordinateSchemeIso j).hom ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (CoordinateRing R j))) := by
    rw [← nativeCoordinateChart_over_base, nativeCoordinateInclusion, ← Category.assoc,
      Iso.hom_inv_id_assoc]
  rw [e, MorphismProperty.cancel_left_of_respectsIso (P := @LocallyOfFinitePresentation),
    HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

end ProjectiveSpace

section Field

variable {V : Type u} [CommRing V] {X : Scheme.{u}} [CompactSpace X]
  (p : X ⟶ Spec (CommRingCat.of V)) (z : X)

/-- **The global sections of the reduced closure of a point over a closed point form a field**:
if `p(z)` is a closed point of `Spec V` and `X` is projective over `V`, then `closure {z}` (with
its reduced structure) is integral and projective over the field `V ⧸ 𝔭_{p z}`, so
`Γ(closure {z}, 𝒪)` is a field (Mathlib's `isField_of_universallyClosed`). -/
theorem isField_closureScheme (hp : IsProjectiveOver p) (hmax : (p z).asIdeal.IsMaximal) :
    IsField Γ(ClosureComponent.closureScheme z, ⊤) := by
  let : Field (ClosureComponent.BaseRing p z) := Ideal.Quotient.field _
  have hproj := ClosureComponent.isProjectiveOver_closureToBase p z hp
  have : IsProper (ClosureComponent.closureToBase p z) := hproj.isProper
  exact isField_of_universallyClosed (ClosureComponent.BaseRing p z)
    (ClosureComponent.closureToBase p z)

end Field

section Map

variable {V : Type u} [CommRing V] [IsLocalRing V] {C Y : Scheme.{u}}
  (φ : C ⟶ Spec (CommRingCat.of V)) (β : Y ⟶ C)

local notation "s₀" => IsLocalRing.closedPoint V

/-- The target `P = ℙ¹_V ×_V C` of Temkin's contracting morphism. -/
abbrev contractingTarget : Scheme.{u} := pullback (projectiveSpaceStructure V 1) φ

/-- The projection `π : ℙ¹_C → C`. -/
abbrev contractingProj : contractingTarget φ ⟶ C := pullback.snd (projectiveSpaceStructure V 1) φ

variable {L : LineBundleData Y} {m : ℤ} {s : Fin 2 → L.Sections m ⊤}

/-- **Temkin's `h̄ = (h, β) : Y → ℙ¹_C`** for two generating sections `s` of `𝓛^m`
(T:3223–3226): `h : Y → ℙ¹_V` is OM3A's `LineBundleData.toProjectiveSpace`. -/
def contractingMap (hs : LineBundleData.Generates s) : Y ⟶ contractingTarget φ :=
  pullback.lift (LineBundleData.toProjectiveSpace (β ≫ φ) hs) β
    (LineBundleData.toProjectiveSpace_structure (β ≫ φ) hs)

@[reassoc (attr := simp)]
lemma contractingMap_fst (hs : LineBundleData.Generates s) :
    contractingMap φ β hs ≫ pullback.fst _ _ = LineBundleData.toProjectiveSpace (β ≫ φ) hs :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma contractingMap_snd (hs : LineBundleData.Generates s) :
    contractingMap φ β hs ≫ contractingProj φ = β :=
  pullback.lift_snd _ _ _

/-- A point lies in the zero locus of `s 0` iff `h` maps it to the hyperplane `x₀ = 0`. -/
lemma mem_nonvanishingLocus_iff (hs : LineBundleData.Generates s) (y : Y) :
    y ∈ (s 0).nonvanishingLocus ↔
      LineBundleData.toProjectiveSpace (β ≫ φ) hs y ∈ nativeCoordinateOpen (R := V) (n := 1) 0 := by
  rw [← LineBundleData.toProjectiveSpace_preimage_coordinate (β ≫ φ) hs 0]
  rfl

/-- **`h̄` contracts exactly `Z`** (T:3224–3226): if `β` contracts `closure {Z}`, the zero locus
of `s 0` misses `closure {Z}` and the generic points of the closed fibre, and meets the closure of
every other component of the closed fibre, then `h̄ = (h, β)` contracts exactly `Z` among the
components of the closed fibre. -/
theorem contractsExactlyAt_contractingMap (hs : LineBundleData.Generates s)
    [CompactSpace Y] (hp : IsProjectiveOver (β ≫ φ)) (Z : (β ≫ φ).fiber s₀)
    (hβZ : (β '' closure {(β ≫ φ).fiberι s₀ Z}).Subsingleton)
    (hZ : closure {(β ≫ φ).fiberι s₀ Z} ⊆ ((s 0).nonvanishingLocus : Set Y))
    (hgen : ∀ w ∈ genericPoints ((β ≫ φ).fiber s₀),
      (β ≫ φ).fiberι s₀ w ∈ (s 0).nonvanishingLocus)
    (hmeet : ∀ w ∈ genericPoints ((β ≫ φ).fiber s₀), w ≠ Z →
      ∃ y ∈ closure {(β ≫ φ).fiberι s₀ w}, y ∉ (s 0).nonvanishingLocus) :
    ContractsExactlyAt (β ≫ φ) (contractingMap φ β hs) Z := by
  intro w hw
  constructor
  · intro hsub
    by_contra hne
    obtain ⟨y, hy, hyn⟩ := hmeet w hw hne
    have hw' := hgen w hw
    have heq := hsub ⟨y, hy, rfl⟩ ⟨_, subset_closure rfl, rfl⟩
    have hH : LineBundleData.toProjectiveSpace (β ≫ φ) hs y =
        LineBundleData.toProjectiveSpace (β ≫ φ) hs ((β ≫ φ).fiberι s₀ w) := by
      rw [← contractingMap_fst φ β hs, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, heq]
    rw [mem_nonvanishingLocus_iff φ β hs] at hyn hw'
    exact hyn (hH ▸ hw')
  · rintro rfl
    set z := (β ≫ φ).fiberι s₀ w with hz
    have hmax : ((β ≫ φ) z).asIdeal.IsMaximal := by
      rw [hz, BlowDown.apply_fiberι]
      exact IsLocalRing.maximalIdeal.isMaximal V
    have hfield := isField_closureScheme (β ≫ φ) z hp hmax
    obtain ⟨W, hW, hcW, -⟩ := exists_isAffineOpen_mem_and_subset (x := β z)
      (U := ⊤) trivial
    have hrange : Set.range (ClosureComponent.closureι z) = closure {z} :=
      ClosureComponent.range_closureι z
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    rw [← hrange] at hy₁ hy₂
    obtain ⟨t₁, rfl⟩ := hy₁
    obtain ⟨t₂, rfl⟩ := hy₂
    have key := apply_eq_of_isField hfield (ClosureComponent.closureι z ≫ contractingMap φ β hs)
      (nativeCoordinateOpen_isAffine (R := V) (n := 1) 0) hW ?_ ?_ t₁ t₂
    · simpa only [Scheme.Hom.comp_apply] using key
    · rintro _ ⟨t, rfl⟩
      rw [Category.assoc, contractingMap_fst, Scheme.Hom.comp_apply]
      refine (mem_nonvanishingLocus_iff φ β hs _).mp (hZ ?_)
      rw [← hrange]
      exact ⟨t, rfl⟩
    · rintro _ ⟨t, rfl⟩
      rw [Category.assoc, contractingMap_snd, Scheme.Hom.comp_apply]
      have ht : ClosureComponent.closureι z t ∈ closure {z} := by
        rw [← hrange]
        exact ⟨t, rfl⟩
      have := hβZ ⟨_, ht, rfl⟩ ⟨z, subset_closure rfl, rfl⟩
      change β (ClosureComponent.closureι z t) ∈ (W : Set C)
      rw [this]
      exact hcW

/-- **Temkin's contracting morphism from two sections** (T:3203–3226, last step): under the
hypotheses of `contractsExactlyAt_contractingMap` and `C` projective over `V`, the target
`P = ℙ¹_C` and `g = h̄` satisfy the conclusion of `ContractingMorphismExists` for `Z`. -/
theorem exists_contracting_of_sections (hC : IsProjectiveOver φ) [LocallyOfFinitePresentation φ]
    (hs : LineBundleData.Generates s) [CompactSpace Y] (hp : IsProjectiveOver (β ≫ φ))
    (Z : (β ≫ φ).fiber s₀)
    (hβZ : (β '' closure {(β ≫ φ).fiberι s₀ Z}).Subsingleton)
    (hZ : closure {(β ≫ φ).fiberι s₀ Z} ⊆ ((s 0).nonvanishingLocus : Set Y))
    (hgen : ∀ w ∈ genericPoints ((β ≫ φ).fiber s₀),
      (β ≫ φ).fiberι s₀ w ∈ (s 0).nonvanishingLocus)
    (hmeet : ∀ w ∈ genericPoints ((β ≫ φ).fiber s₀), w ≠ Z →
      ∃ y ∈ closure {(β ≫ φ).fiberι s₀ w}, y ∉ (s 0).nonvanishingLocus) :
    ∃ (P : Scheme.{u}) (π : P ⟶ C) (g : Y ⟶ P), g ≫ π = β ∧ IsSeparated (π ≫ φ) ∧
      LocallyOfFinitePresentation (π ≫ φ) ∧ IsProjectiveOver (π ≫ φ) ∧
      ContractsExactlyAt (β ≫ φ) g Z := by
  have hP : IsProjectiveOver (contractingProj φ ≫ φ) := by
    have h := Geometry.ChowLemmaProduct.isProjectiveOver_product (projectiveSpaceStructure V 1) φ
      (isProjectiveOver_projectiveSpaceStructure V 1) hC
    rwa [pullback.condition] at h
  have : LocallyOfFinitePresentation (projectiveSpaceStructure V 1) :=
    locallyOfFinitePresentation_projectiveSpaceStructure V 1
  have : IsProper (contractingProj φ ≫ φ) := hP.isProper
  exact ⟨contractingTarget φ, contractingProj φ, contractingMap φ β hs, contractingMap_snd φ β hs,
    inferInstance, inferInstance, hP,
    contractsExactlyAt_contractingMap φ β hs hp Z hβZ hZ hgen hmeet⟩

end Map

end

end DeJongAlterations.StableModification.BlowDown.ContractingMap
