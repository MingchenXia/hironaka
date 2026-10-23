/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.SteinProjective
import DeJongAlterations.StableModification.Cohomology.SteinReduced
import DeJongAlterations.Geometry.NormalCurveModification
import DeJongAlterations.Geometry.NormalCurveModificationFunctionField
import DeJongAlterations.Geometry.NodeNormal

/-!
# Normalizations dominated by a normal curve (replacing Temkin's Lemma 4.4.1)

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), §4.4
uses normalizations and compactifications with geometrically reduced fibres (Lemma 4.4.1,
`compaclem`, T:3089–3104), which rest on the reduced fibre theorem and through it on the
Grauert–Remmert finiteness theorem. In the blowing-down argument every normalization is that of
a curve `Y` dominated by a normal curve `B` (a semi-stable modification), and then it is the
relative normalization `π.normalization` of `Y` in `B` (Mathlib's `Spec` of the integral closure
of `𝒪_Y` in `π_* 𝒪_B`; plan `PLAN-SM-GEOM.md`, S8). This file proves the properties of it that
the blowing-down lemmas use (blueprint `prop:sm-normalization-reduced`, `sm-blow-down.tex`).

## Main results

* `exists_germToFunctionField_eq`: on an integral scheme, a rational function regular at every
  point of an open `W` comes from `Γ(W, 𝒪)`.
* `isIntegrallyClosed_sections`: on a normal integral scheme, `Γ(W, 𝒪)` is integrally closed for
  every nonempty open `W` (not only for affine ones).
* `isIntegrallyClosed_integralClosure`: the integral closure of a ring in an integrally closed
  domain is integrally closed.
* `isNormalScheme_normalization`: **the relative normalization of `Y` in a normal integral `B`
  is normal**; `isProper_toNormalization`: `B → Nor_B(Y)` is proper if `π` is.
* `algebraMap_integralClosure_bijective_of_isNormalScheme`,
  `isIso_fromNormalization_of_isNormalScheme`: if `Y` is normal and `π` is birational, the
  integral closure of `Γ(U, 𝒪_Y)` in `Γ(π⁻¹U, 𝒪_B)` is `Γ(U, 𝒪_Y)`, i.e. `π.normalization = Y`.
* `app_bijective_of_isNormalScheme`: if moreover `Γ(π⁻¹U, 𝒪_B)` is integral over `Γ(U, 𝒪_Y)`
  (Stein finiteness, `Cohomology.SteinFinite`), then `π^♯ : Γ(U, 𝒪_Y) → Γ(π⁻¹U, 𝒪_B)` is
  bijective: `π_* 𝒪_B = 𝒪_Y` ("Zariski's main theorem in Stein form" for a normal target).
* `isRadical_map_maximalIdeal_of_isNormalScheme`: **a normal curve `Y` over a valuation ring `V`
  which is dominated by a relatively projective birational `π : B → Y` with `B` flat over `V`
  with reduced closed fibre has reduced closed fibre** on every affine open (this is the input of
  Temkin's Lemma 4.4.2 that his Lemma 4.4.1 provides, T:3120–3121; ERRATA T13, DJA-H6).

The normality of `π.normalization` and the identification `π.normalization = Y` for normal `Y`
are the points (ii) left open in `rem:sm-stein-not-proved` (`sm-cohomology-stein.tex`).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace IsLocalRing
open scoped TensorProduct

namespace DeJongAlterations.StableModification.BlowDown

universe u

section Sections

variable {X : Scheme.{u}} [IsIntegral X]

/-- Restricting a section does not change its image in the function field. -/
theorem germToFunctionField_map {U W : X.Opens} [Nonempty U] [Nonempty W] (h : W ≤ U)
    (s : Γ(X, U)) :
    X.germToFunctionField W (X.presheaf.map (homOfLE h).op s) = X.germToFunctionField U s := by
  change (X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField W) s = _
  rw [show X.presheaf.map (homOfLE h).op ≫ X.germToFunctionField W = X.germToFunctionField U from
    X.presheaf.germ_res (homOfLE h) _ _]

/-- **Sections of an integral scheme as rational functions**: a rational function which lies in
the image of every local ring `𝒪_{X,x}`, `x ∈ W`, is the image of a section over `W`. -/
theorem exists_germToFunctionField_eq (W : X.Opens) [Nonempty W] (f : X.functionField)
    (hf : ∀ x ∈ W, ∃ g : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField g = f) :
    ∃ s : Γ(X, W), X.germToFunctionField W s = f := by
  classical
  -- local sections representing `f`
  have hloc : ∀ x : W, ∃ (V : X.Opens) (_ : (x : X) ∈ V) (_ : V ≤ W) (t : Γ(X, V)),
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ V x ‹_› t) = f := by
    intro x
    obtain ⟨g, hg⟩ := hf x x.2
    obtain ⟨V, hxV, t, ht⟩ := X.presheaf.exists_germ_eq (x := (x : X)) g
    refine ⟨V ⊓ W, ⟨hxV, x.2⟩, inf_le_right, X.presheaf.map (homOfLE inf_le_left).op t, ?_⟩
    rw [← hg, ← ht]
    congr 1
    exact X.presheaf.germ_res_apply (homOfLE inf_le_left) _ _ t
  choose V hxV hVW t ht using hloc
  have hne : ∀ x : W, Nonempty (V x) := fun x => ⟨⟨x, hxV x⟩⟩
  have hgerm : ∀ x : W, haveI := hne x; X.germToFunctionField (V x) (t x) = f := by
    intro x
    have := hne x
    rw [← X.algebraMap_germ_eq_germToFunctionField (hxV x)]
    exact ht x
  -- the local sections are compatible
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.obj V t := by
    intro x y
    by_cases hxy : Nonempty ((V x ⊓ V y : X.Opens) : Set X)
    · have : Nonempty (V x ⊓ V y : X.Opens) := hxy
      have := hne x
      have := hne y
      apply X.germToFunctionField_injective (V x ⊓ V y)
      change X.germToFunctionField _ (X.presheaf.map (homOfLE inf_le_left).op (t x)) =
        X.germToFunctionField _ (X.presheaf.map (homOfLE inf_le_right).op (t y))
      rw [germToFunctionField_map, germToFunctionField_map, hgerm, hgerm]
    · have hempty : V x ⊓ V y = ⊥ := by
        ext z
        simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        exact fun hz => hxy ⟨z, hz⟩
      have : Subsingleton (X.sheaf.obj.obj (Opposite.op (V x ⊓ V y))) :=
        CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hempty)
      exact Subsingleton.elim _ _
  have hcover : W ≤ iSup V := fun z hz => Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hxV ⟨z, hz⟩⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' V W (fun x => homOfLE (hVW x)) hcover t hcompat
  refine ⟨s, ?_⟩
  obtain ⟨z, hz⟩ := ‹Nonempty W›
  let x : W := ⟨z, hz⟩
  have := hne x
  rw [← germToFunctionField_map (hVW x) s]
  change X.germToFunctionField (V x) (X.sheaf.obj.map (homOfLE (hVW x)).op s) = f
  rw [hs x, hgerm]

/-- **Sections of a normal integral scheme over any nonempty open are integrally closed**
(for affine opens this is Codex's
`Geometry.NormalCurveModification.affineSections_isIntegrallyClosed`). -/
theorem isIntegrallyClosed_sections (hX : IsNormalScheme X) (W : X.Opens) [Nonempty W] :
    IsIntegrallyClosed Γ(X, W) := by
  let R := Γ(X, W)
  let K := FractionRing R
  let φ : K →+* X.functionField :=
    IsFractionRing.lift (X.germToFunctionField_injective W)
  rw [isIntegrallyClosed_iff K]
  intro x hx
  -- the image of `x` in the function field is integral over every local ring
  let : Algebra R X.functionField := (X.germToFunctionField W).hom.toAlgebra
  have hφ : ∀ r : R, φ (algebraMap R K r) = X.germToFunctionField W r :=
    fun r => IsFractionRing.lift_algebraMap _ r
  have hint : IsIntegral R (φ x) := by
    let : Algebra K X.functionField := φ.toAlgebra
    have : IsScalarTower R K X.functionField := IsScalarTower.of_algebraMap_eq fun r => (hφ r).symm
    exact hx.map (IsScalarTower.toAlgHom R K X.functionField)
  obtain ⟨s, hs⟩ := exists_germToFunctionField_eq W (φ x) fun y hy => by
    have := (hX y).1
    have := (hX y).2
    let : Algebra R (X.presheaf.stalk y) := (X.presheaf.germ W y hy).hom.toAlgebra
    have htower : IsScalarTower R (X.presheaf.stalk y) X.functionField :=
      IsScalarTower.of_algebraMap_eq fun r =>
        (X.algebraMap_germ_eq_germToFunctionField hy r).symm
    have hint' : IsIntegral (X.presheaf.stalk y) (φ x) := hint.tower_top
    exact IsIntegrallyClosed.isIntegral_iff.mp hint'
  refine ⟨s, φ.injective ?_⟩
  rw [hφ, hs]

end Sections

section Algebra

/-- **The integral closure in an integrally closed domain is integrally closed.** -/
theorem isIntegrallyClosed_integralClosure (A R : Type*) [CommRing A] [CommRing R] [Algebra A R]
    [IsDomain R] [IsIntegrallyClosed R] : IsIntegrallyClosed (integralClosure A R) := by
  have : FaithfulSMul (integralClosure A R) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr Subtype.val_injective
  have : IsIntegrallyClosedIn (integralClosure A R) R := by
    rw [isIntegrallyClosedIn_iff]
    refine ⟨Subtype.val_injective, fun {x} hx => ?_⟩
    exact ⟨⟨x, isIntegral_trans x hx⟩, rfl⟩
  exact IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn _ R

end Algebra

section Normalization

variable {B Y : Scheme.{u}} (π : B ⟶ Y) [QuasiCompact π] [QuasiSeparated π]

/-- **The relative normalization of `Y` in a normal integral scheme is normal**: it is covered by
the spectra of the integral closures of `Γ(U, 𝒪_Y)` in the integrally closed domains
`Γ(π⁻¹U, 𝒪_B)` (`isIntegrallyClosed_sections`, `isIntegrallyClosed_integralClosure`). -/
theorem isNormalScheme_normalization [IsIntegral B] (hB : IsNormalScheme B) :
    IsNormalScheme π.normalization := by
  refine Geometry.NodeNormal.isNormalScheme_of_openCover _ π.normalizationOpenCover fun U => ?_
  change IsNormalScheme (Spec (π.normalizationDiagram.obj (.op U.1)))
  let := (π.app U.1).hom.toAlgebra
  change IsNormalScheme (Spec (CommRingCat.of (integralClosure Γ(Y, U.1) Γ(B, π ⁻¹ᵁ U.1))))
  by_cases h : Nonempty (π ⁻¹ᵁ U.1)
  · have := isIntegrallyClosed_sections hB (π ⁻¹ᵁ U.1)
    have := isIntegrallyClosed_integralClosure Γ(Y, U.1) Γ(B, π ⁻¹ᵁ U.1)
    exact isNormalScheme_spec _
  · intro x
    have hempty : π ⁻¹ᵁ U.1 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => h ⟨⟨z, hz⟩⟩
    have : Subsingleton Γ(B, π ⁻¹ᵁ U.1) :=
      CommRingCat.subsingleton_of_isTerminal (B.sheaf.isTerminalOfEqEmpty hempty)
    have : Subsingleton (integralClosure Γ(Y, U.1) Γ(B, π ⁻¹ᵁ U.1)) :=
      Subtype.val_injective.subsingleton
    exact ((x : PrimeSpectrum _).isPrime.ne_top (Subsingleton.elim _ _)).elim

/-- `π` factors through its relative normalization by a proper morphism `B → Nor_B(Y)` when
`π` is proper (`π = toNormalization ≫ fromNormalization` with `fromNormalization` integral,
hence separated). -/
theorem isProper_toNormalization [IsProper π] : IsProper π.toNormalization := by
  have : IsProper (π.toNormalization ≫ π.fromNormalization) := by
    rw [π.toNormalization_fromNormalization]
    infer_instance
  exact IsProper.of_comp _ π.fromNormalization

variable [IsIntegral B] [IsIntegral Y]

omit [QuasiCompact π] [QuasiSeparated π] [IsIntegral B] [IsIntegral Y] in
/-- A birational morphism has nonempty preimages of nonempty opens. -/
theorem nonempty_preimage_of_birationalOver (hbir : Scheme.BirationalOver π (𝟙 Y))
    (U : Y.Opens) [Nonempty U] : Nonempty (π ⁻¹ᵁ U) := by
  have := isDominant_of_birationalOver_id π hbir
  obtain ⟨x, hx⟩ := π.denseRange.exists_mem_open U.2 (Set.nonempty_coe_sort.mp ‹_›)
  exact ⟨⟨x, hx⟩⟩

omit [QuasiCompact π] [QuasiSeparated π] in
/-- The function field square `Γ(U, 𝒪_Y) → Γ(π⁻¹U, 𝒪_B) → K(B)` and
`Γ(U, 𝒪_Y) → K(Y) → K(B)` of a birational morphism (Codex's
`Geometry.NormalCurveModification.functionFieldMap_sections`). -/
theorem functionFieldMap_germ (hbir : Scheme.BirationalOver π (𝟙 Y)) (U : Y.Opens) [Nonempty U]
    [Nonempty (π ⁻¹ᵁ U)] (a : Γ(Y, U)) :
    (Geometry.NormalCurveModification.functionFieldMap π hbir).hom (Y.germToFunctionField U a) =
      B.germToFunctionField (π ⁻¹ᵁ U) (π.app U a) :=
  congrArg (fun g => g.hom a) (Geometry.NormalCurveModification.functionFieldMap_sections π hbir U)

omit [QuasiCompact π] [QuasiSeparated π] in
/-- **Over a normal target the integral closure of `𝒪_Y` in `π_* 𝒪_B` is `𝒪_Y`** when `π` is
birational: an element of `Γ(π⁻¹U, 𝒪_B)` integral over `Γ(U, 𝒪_Y)` is a rational function on `Y`
integral over the integrally closed `Γ(U, 𝒪_Y)`. -/
theorem algebraMap_integralClosure_bijective_of_isNormalScheme (hY : IsNormalScheme Y)
    (hbir : Scheme.BirationalOver π (𝟙 Y)) {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U] :
    letI := (π.app U).hom.toAlgebra
    Function.Bijective (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(B, π ⁻¹ᵁ U))) := by
  let := (π.app U).hom.toAlgebra
  have := nonempty_preimage_of_birationalOver π hbir U
  let φ := Geometry.NormalCurveModification.functionFieldMap π hbir
  have := Geometry.NormalCurveModification.functionFieldMap_isIso π hbir
  let e : Y.functionField ≃+* B.functionField := (asIso φ).commRingCatIsoToRingEquiv
  have he : ∀ k, e k = φ.hom k := fun _ => rfl
  have hinj : Function.Injective (π.app U).hom := by
    intro a b hab
    apply Y.germToFunctionField_injective U
    apply e.injective
    rw [he, he, functionFieldMap_germ π hbir, functionFieldMap_germ π hbir, hab]
  refine ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun r => ?_⟩
  obtain ⟨r, hr⟩ := r
  -- the rational function of `r` comes from `K(Y)` and is integral over `Γ(U, 𝒪_Y)`
  set y := e.symm (B.germToFunctionField (π ⁻¹ᵁ U) r) with hy
  have hyint : IsIntegral Γ(Y, U) y := by
    obtain ⟨p, hp, hpr⟩ := hr
    refine ⟨p, hp, ?_⟩
    have hcomp : ((e.symm.toRingHom.comp (B.germToFunctionField (π ⁻¹ᵁ U)).hom).comp
        (π.app U).hom) = algebraMap Γ(Y, U) Y.functionField := by
      ext a
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
      rw [← functionFieldMap_germ π hbir, ← he, RingEquiv.symm_apply_apply]
      rfl
    have h0 := congrArg (e.symm.toRingHom.comp (B.germToFunctionField (π ⁻¹ᵁ U)).hom) hpr
    rw [Polynomial.hom_eval₂, map_zero] at h0
    rw [← hcomp, hy]
    exact h0
  have hic := Geometry.NormalCurveModification.affineSections_isIntegrallyClosed hY U hU
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff Y.functionField).mp hic hyint
  refine ⟨a, Subtype.ext ?_⟩
  change (π.app U).hom a = r
  apply B.germToFunctionField_injective (π ⁻¹ᵁ U)
  rw [← functionFieldMap_germ π hbir, ← he]
  change e (algebraMap Γ(Y, U) Y.functionField a) = _
  rw [ha, hy, RingEquiv.apply_symm_apply]

omit [QuasiCompact π] [QuasiSeparated π] in
/-- **`π_* 𝒪_B = 𝒪_Y` over a normal target** (Stein form of Zariski's main theorem): if `Y` is
normal, `π` is birational and `Γ(π⁻¹U, 𝒪_B)` is integral over `Γ(U, 𝒪_Y)` (for instance finite,
by Stein finiteness `Cohomology.finite_sections_preimage_of_isRelativelyProjective`), then
`π^♯ : Γ(U, 𝒪_Y) → Γ(π⁻¹U, 𝒪_B)` is bijective. -/
theorem app_bijective_of_isNormalScheme (hY : IsNormalScheme Y)
    (hbir : Scheme.BirationalOver π (𝟙 Y)) {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (hint : letI := (π.app U).hom.toAlgebra; Algebra.IsIntegral Γ(Y, U) Γ(B, π ⁻¹ᵁ U)) :
    Function.Bijective (π.app U).hom := by
  let := (π.app U).hom.toAlgebra
  have h := algebraMap_integralClosure_bijective_of_isNormalScheme π hY hbir hU
  refine ⟨fun a b hab => h.1 (Subtype.ext hab), fun r => ?_⟩
  obtain ⟨a, ha⟩ := h.2 ⟨r, hint.isIntegral r⟩
  exact ⟨a, congrArg Subtype.val ha⟩

set_option backward.isDefEq.respectTransparency false in
/-- **The relative normalization of a normal target is the target**: if `Y` is normal and `π` is
birational, `π.fromNormalization : π.normalization → Y` is an isomorphism. -/
theorem isIso_fromNormalization_of_isNormalScheme (hY : IsNormalScheme Y)
    (hbir : Scheme.BirationalOver π (𝟙 Y)) : IsIso π.fromNormalization := by
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) _
      (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (π.fromNormalization ⁻¹ᵁ U).ι
    (π.normalizationOpenCover.f U)
      (by simpa using congr($(π.fromNormalization_preimage U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso (MorphismProperty.isomorphisms Scheme) e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso (MorphismProperty.isomorphisms Scheme) _
      U.2.isoSpec.hom]
  have : IsIso (π.normalizationDiagramMap.app (.op U)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    let := (π.app U).hom.toAlgebra
    change Function.Bijective (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(B, π ⁻¹ᵁ U)))
    by_cases hU : Nonempty (U : Y.Opens)
    · exact algebraMap_integralClosure_bijective_of_isNormalScheme π hY hbir U.2
    · have hempty : (U : Y.Opens) = ⊥ := by
        ext z
        simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
        exact fun hz => hU ⟨⟨z, hz⟩⟩
      have hempty' : π ⁻¹ᵁ (U : Y.Opens) = ⊥ := by rw [hempty]; rfl
      have : Subsingleton Γ(Y, (U : Y.Opens)) :=
        CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty hempty)
      have : Subsingleton Γ(B, π ⁻¹ᵁ (U : Y.Opens)) :=
        CommRingCat.subsingleton_of_isTerminal (B.sheaf.isTerminalOfEqEmpty hempty')
      have : Subsingleton (integralClosure Γ(Y, U) Γ(B, π ⁻¹ᵁ U)) :=
        Subtype.val_injective.subsingleton
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun b => ⟨0, Subsingleton.elim _ _⟩⟩
  refine (MorphismProperty.isomorphisms.iff _).mpr ?_
  convert! (inferInstance : IsIso (Spec.map (π.normalizationDiagramMap.app (.op U))))
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]

end Normalization

section ReducedFibre

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y) (pY : Y ⟶ Spec (CommRingCat.of V))

omit [IsDomain V] [ValuationRing V] in
/-- The coefficients of `π ≫ pY` on `π⁻¹U` are those of `pY` on `U` followed by `π^♯`. -/
theorem sectionsRingHom_comp (U : Y.Opens) :
    Cohomology.sectionsRingHom (Cohomology.structureCoeff (π ≫ pY)) (le_top : π ⁻¹ᵁ U ≤ ⊤) =
      (π.app U).hom.comp (Cohomology.sectionsRingHom (Cohomology.structureCoeff pY)
        (le_top : U ≤ ⊤)) := by
  have h : Y.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ π.app U =
      π.appLE ⊤ (π ⁻¹ᵁ U) le_top := by
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]
  ext a
  simp only [Cohomology.sectionsRingHom, Cohomology.structureCoeff, RingHom.comp_apply,
    Scheme.Hom.comp_appTop]
  exact (congrArg (fun g => g.hom ((pY.appTop).hom
    ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a))) h).symm

/-- **Reduced closed fibre of a normal curve dominated by a curve with reduced closed fibre**
(the input of Temkin's Lemma 4.4.2 provided by his Lemma 4.4.1, T:3120–3121, here without the
reduced fibre theorem; ERRATA T13, DJA-H6): let `pY : Y → Spec V` be locally of finite
presentation over a valuation ring `V`, `Y` integral and normal, and `π : B → Y` birational and
projective relative to `pY`, with `B` integral, flat over `V` and with reduced closed fibre.
Then `𝔪 Γ(U, 𝒪_Y)` is a radical ideal for every affine open `U ⊆ Y`: by Stein finiteness and
normality, `Γ(U, 𝒪_Y) = Γ(π⁻¹U, 𝒪_B)` (`app_bijective_of_isNormalScheme`), and
`𝔪 Γ(π⁻¹U, 𝒪_B)` is radical (`Cohomology.isRadical_map_maximalIdeal_preimage_of_isReduced`). -/
theorem isRadical_map_maximalIdeal_of_isNormalScheme [IsIntegral B] [IsIntegral Y]
    [LocallyOfFinitePresentation pY] [Flat (π ≫ pY)] [QuasiCompact π] [QuasiSeparated π]
    [IsReduced (pullback (π ≫ pY) (Spec.map (CommRingCat.ofHom (residue V))))]
    (hπ : DeJong.IsRelativelyProjective pY π) (hY : IsNormalScheme Y)
    (hbir : Scheme.BirationalOver π (𝟙 Y)) {U : Y.Opens} (hU : IsAffineOpen U) :
    (Ideal.map (Cohomology.sectionsRingHom (Cohomology.structureCoeff pY) (le_top : U ≤ ⊤))
      (maximalIdeal V)).IsRadical := by
  by_cases hne : Nonempty U
  · let := (π.app U).hom.toAlgebra
    have hfin := Cohomology.finite_sections_preimage_of_isRelativelyProjective V π pY hπ hU
    have hbij := app_bijective_of_isNormalScheme π hY hbir hU inferInstance
    have hrad := Cohomology.isRadical_map_maximalIdeal_preimage_of_isReduced π pY hU.isCompact
    rw [sectionsRingHom_comp, ← Ideal.map_map] at hrad
    let ψ := RingEquiv.ofBijective (π.app U).hom hbij
    have hcomap := hrad.comap ψ.toRingHom
    have key := Ideal.comap_map_of_bijective (f := ψ.toRingHom) ψ.bijective
      (I := Ideal.map (Cohomology.sectionsRingHom (Cohomology.structureCoeff pY) (le_top : U ≤ ⊤))
        (maximalIdeal V))
    rw [← key]
    exact hcomap
  · have hempty : U = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hne ⟨⟨z, hz⟩⟩
    have : Subsingleton Γ(Y, U) :=
      CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty hempty)
    intro x _
    exact Subsingleton.elim x 0 ▸ Ideal.zero_mem _

end ReducedFibre

section ClosedFibre

set_option backward.isDefEq.respectTransparency false

variable {V : Type u} [CommRing V] [IsLocalRing V] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of V))

/-- The sections of the closed fibre over the preimage of an affine open `W` are reduced when
`𝔪 Γ(W, 𝒪_X)` is radical (`Γ(W_k, 𝒪) = Γ(W, 𝒪) ⊗_V k = Γ(W, 𝒪)/𝔪`, lane COH2's
`isPushout_baseChange_sections`). -/
theorem isReduced_sections_closedFibre {W : X.Opens} (hW : IsAffineOpen W)
    (h : (Ideal.map (Cohomology.sectionsRingHom (Cohomology.structureCoeff p) (le_top : W ≤ ⊤))
      (maximalIdeal V)).IsRadical) :
    _root_.IsReduced Γ(pullback p (Spec.map (CommRingCat.ofHom (residue V))),
      Cohomology.bcFst (residue V) p ⁻¹ᵁ W) := by
  have H := Cohomology.isPushout_baseChange_sections (residue V) p hW
  let A := Γ(X, W)
  let S' := Γ(pullback p (Spec.map (CommRingCat.ofHom (residue V))),
    Cohomology.bcFst (residue V) p ⁻¹ᵁ W)
  let fA : CommRingCat.of V ⟶ Γ(X, W) :=
    (Scheme.ΓSpecIso (CommRingCat.of V)).inv ≫ p.appLE ⊤ W le_top
  let fk : CommRingCat.of (ResidueField V) ⟶ S' :=
    (Scheme.ΓSpecIso (CommRingCat.of (ResidueField V))).inv ≫
      (Cohomology.bcSnd (residue V) p).appLE ⊤ (Cohomology.bcFst (residue V) p ⁻¹ᵁ W) le_top
  let g : Γ(X, W) ⟶ S' :=
    (Cohomology.bcFst (residue V) p).appLE W (Cohomology.bcFst (residue V) p ⁻¹ᵁ W) le_rfl
  let : Algebra V A := fA.hom.toAlgebra
  let : Algebra (ResidueField V) S' := fk.hom.toAlgebra
  let : Algebra A S' := g.hom.toAlgebra
  let : Algebra V S' := (g.hom.comp fA.hom).toAlgebra
  have : IsScalarTower V A S' := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower V (ResidueField V) S' := IsScalarTower.of_algebraMap_eq' (by
    have := congrArg CommRingCat.Hom.hom H.w
    simp only [CommRingCat.hom_comp] at this
    exact this.symm)
  have hpush : Algebra.IsPushout V (ResidueField V) A S' :=
    CommRingCat.isPushout_iff_isPushout.mp H
  have hfA : fA.hom = Cohomology.sectionsRingHom (Cohomology.structureCoeff p)
      (le_top : W ≤ ⊤) := by
    ext a
    simp [fA, Cohomology.sectionsRingHom, Cohomology.structureCoeff, Scheme.Hom.appLE]
  have hred : _root_.IsReduced (A ⧸ Ideal.map (algebraMap V A) (maximalIdeal V)) := by
    rw [← Ideal.isRadical_iff_quotient_reduced]
    change (Ideal.map fA.hom (maximalIdeal V)).IsRadical
    rw [hfA]
    exact h
  let e1 : ResidueField V ⊗[V] A ≃ₐ[ResidueField V] S' :=
    Algebra.IsPushout.equiv (R := V) (S := ResidueField V) (R' := A) (S' := S')
  let e2 : A ⊗[V] ResidueField V ≃ₐ[V] ResidueField V ⊗[V] A :=
    Algebra.TensorProduct.comm V A (ResidueField V)
  let e3 := Algebra.TensorProduct.quotIdealMapEquivTensorQuot A (maximalIdeal V)
  let ψ : S' →+* A ⧸ Ideal.map (algebraMap V A) (maximalIdeal V) :=
    e3.symm.toRingHom.comp (e2.symm.toRingHom.comp e1.symm.toRingHom)
  have hψ : Function.Injective ψ :=
    e3.symm.injective.comp (e2.symm.injective.comp e1.symm.injective)
  exact isReduced_of_injective ψ hψ

/-- **Reduced closed fibre from radical ideals**: if `𝔪 Γ(W, 𝒪_X)` is radical for every affine
open `W ⊆ X`, the closed fibre `X_k = X ×_V k` is a reduced scheme (its stalks are localizations
of the reduced rings `Γ(W_k, 𝒪)`, `isReduced_sections_closedFibre`). This is the converse of
COH3B's `Cohomology.isRadical_map_maximalIdeal_of_isReduced`. -/
theorem isReduced_closedFibre_of_isRadical
    (h : ∀ W : X.Opens, IsAffineOpen W →
      (Ideal.map (Cohomology.sectionsRingHom (Cohomology.structureCoeff p) (le_top : W ≤ ⊤))
        (maximalIdeal V)).IsRadical) :
    IsReduced (pullback p (Spec.map (CommRingCat.ofHom (residue V)))) := by
  refine @isReduced_of_isReduced_stalk _ fun x => ?_
  obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset
    (x := Cohomology.bcFst (residue V) p x) (U := ⊤) trivial
  have hW' : IsAffineOpen (Cohomology.bcFst (residue V) p ⁻¹ᵁ W) := hW.preimage _
  have hred := isReduced_sections_closedFibre p hW (h W hW)
  let := TopCat.Presheaf.algebra_section_stalk
    (pullback p (Spec.map (CommRingCat.ofHom (residue V)))).presheaf
    (⟨x, hxW⟩ : (Cohomology.bcFst (residue V) p ⁻¹ᵁ W : Opens _))
  have := hW'.isLocalization_stalk ⟨x, hxW⟩
  have key : _root_.IsReduced
      ((pullback p (Spec.map (CommRingCat.ofHom (residue V)))).presheaf.stalk
        ((⟨x, hxW⟩ : (Cohomology.bcFst (residue V) p ⁻¹ᵁ W : Opens _)) : _)) :=
    isReduced_localizationPreserves (hW'.primeIdealOf ⟨x, hxW⟩).asIdeal.primeCompl _ hred
  exact key

end ClosedFibre

section NormalTarget

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y) (pY : Y ⟶ Spec (CommRingCat.of V))

/-- **The closed fibre of a normal curve dominated by a curve with reduced closed fibre is
reduced** (blueprint `prop:sm-normalization-reduced`, (iii); the use of Temkin's Lemma 4.4.1 in
Lemma 4.4.2, T:3120–3121, without the reduced fibre theorem): `Y → Spec V` locally of finite
presentation, `Y` normal and integral, `π : B → Y` birational and projective relative to `pY`,
`B` integral and flat over `V` with reduced closed fibre. -/
theorem isReduced_closedFibre_of_isNormalScheme [IsIntegral B] [IsIntegral Y]
    [LocallyOfFinitePresentation pY] [Flat (π ≫ pY)] [QuasiCompact π] [QuasiSeparated π]
    [IsReduced (pullback (π ≫ pY) (Spec.map (CommRingCat.ofHom (residue V))))]
    (hπ : DeJong.IsRelativelyProjective pY π) (hY : IsNormalScheme Y)
    (hbir : Scheme.BirationalOver π (𝟙 Y)) :
    IsReduced (pullback pY (Spec.map (CommRingCat.ofHom (residue V)))) :=
  isReduced_closedFibre_of_isRadical pY fun _ hW =>
    isRadical_map_maximalIdeal_of_isNormalScheme π pY hπ hY hbir hW

end NormalTarget

end DeJongAlterations.StableModification.BlowDown
