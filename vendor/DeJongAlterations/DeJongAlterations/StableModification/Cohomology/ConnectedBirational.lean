/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.ConnectedBirationalCech
import DeJongAlterations.StableModification.Cohomology.ConnectedBirationalCharts
import DeJongAlterations.StableModification.Cohomology.SteinProjective
import DeJongAlterations.StableModification.BlowDown.Normalization
import DeJongAlterations.Geometry.ModificationCenterOpen
import DeJongAlterations.Geometry.ModificationCenter
import DeJongAlterations.StableModification.ValCurves.ModificationsFiniteness
import DeJongAlterations.StableModification.ValCurves.ModificationsGamma

/-!
# Zariski's connectedness theorem for birational morphisms onto normal curves

M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010)
(`references/temkin10-stable-modification/source/semi-stable.tex`, cited `T:<line>`), proof of
Lemma 4.4.2 (T:3133): for a modification `f : C' → C` of a normal curve over a valuation ring and a
point `x` of the closed fibre, "`Z = f⁻¹(x)` is connected because otherwise `C` is not normal at
`x` by Zariski connectedness theorem". Temkin applies the noetherian theorem (EGA III 4.3.1) to a
noetherian model, where normality is not available (ERRATA T54). This file proves the statement
directly over the valuation ring (blueprint `sm-cohomology-connected-birational.tex`).

## Setting

`pY : Y → Spec V` is locally of finite presentation over a valuation ring `V`, `Y` is integral and
normal, and `π : B → Y` is birational and projective relative to `pY`
(`DeJong.IsRelativelyProjective`, a closed immersion `B ↪ Y ×_V ℙⁿ_V` over `Y`) with `B` integral
and flat over `V`.

## Main results

* `isPreconnected_preimage_zeroLocus_of_twoCharts_birational` (blueprint
  `thm:sm-connbir-geometric`): for a nonempty affine open `U ⊆ Y` with `π⁻¹U` the union of two
  affine opens, a finite `s ⊆ Γ(Y, U)` with `π⁻¹(D(q))` affine for `q ∈ s`, and all primes
  containing `s` inside one proper ideal, the preimage of the vanishing locus of `s` in `U` is
  preconnected. This is the general form; it applies to the whole set of generizations of `x` in
  the modification locus.
* `exists_twoCharts` (blueprint `lem:sm-connbir-charts`): over a closed point with infinite residue
  field whose fibre is a curve, `π⁻¹U` is the union of two affine opens for small affine `U ∋ x`.
* `isConnected_preimage_singleton_of_isIso` (blueprint `thm:sm-connbir-point`): if `π` is an
  isomorphism over a punctured neighbourhood of the closed point `x` (residue field infinite, fibre
  a curve) and `x` is cut out by finitely many functions, then `π⁻¹(x)` is connected.
* `isConnected_preimage_singleton_of_generizations` (blueprint `thm:sm-connbir-finite-height`):
  over a valuation ring of finite height, for `Y` separated of relative dimension one, `π⁻¹(x)` is
  connected for every closed point `x` with infinite residue field such that no other point of the
  modification locus specializes to `x`.
* `isConnected_preimage_singleton_of_heightOne` (blueprint `cor:sm-connbir-height-one`): over a
  valuation ring of height one this condition always holds
  (`eq_of_mem_center_of_specializes_of_heightOne`), so every fibre over a closed point with
  infinite residue field is connected.

Auxiliary: `mem_basicOpen_iff_notMem_toSpecΓ`, `infinite_quotient_of_infinite_residueField`,
`isClosed_singleton_toSpecΓ`, `noetherianSpace_of_finite`, `exists_finset_zeroLocus_eq_singleton`,
`eq_or_eq_of_specializes_of_fiberTrdeg_le_one` (fibres of a modification of a relative curve over
closed points are curves), `surjective_of_isRelativelyProjective`,
`isModification_of_isRelativelyProjective`.

## Not proved here

Over a valuation ring of height `≥ 2`, the modification locus may contain points `y ≠ x` over
smaller primes which specialize to `x`; then the general form gives the connectedness of the
preimage of the set of all of them, but not of `π⁻¹(x)` alone (blueprint remark
`rem:sm-connbir-generizations`).
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Limits

namespace DeJongAlterations.StableModification.Cohomology.ConnectedBirational

noncomputable section

set_option backward.isDefEq.respectTransparency false

section Points

variable {Y : Scheme.{u}} {U : Y.Opens}

/-- A point `y ∈ U` lies in `D(r)`, `r ∈ Γ(Y, U)`, iff `r` is not in the prime of `y`. -/
theorem mem_basicOpen_iff_notMem_toSpecΓ (r : Γ(Y, U)) {y : Y} (hy : y ∈ U) :
    y ∈ Y.basicOpen r ↔ r ∉ (U.toSpecΓ ⟨y, hy⟩).asIdeal := by
  have h := congrArg (fun W : U.toScheme.Opens => (⟨y, hy⟩ : U) ∈ W)
    (Scheme.Opens.toSpecΓ_preimage_basicOpen U r)
  simp only [eq_iff_iff] at h
  exact h.symm

end Points

section Geometric

variable {V : Type u} [CommRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y) (pY : Y ⟶ Spec (CommRingCat.of V))

/-- The structure coefficients of `π⁻¹U → Spec Γ(Y, U)` composed with the `V`-algebra
structure of `Γ(Y, U)` are those of `π⁻¹U → Spec V`. -/
theorem appTop_ι_comp_eq_structureCoeff {U : Y.Opens} (v : V) :
    letI := Cohomology.sectionsAlgebra V pY U
    ((π ⁻¹ᵁ U).ι ≫ π ≫ pY).appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) =
      structureCoeff (A := Γ(Y, U)) (π ∣_ U ≫ U.toSpecΓ) (algebraMap V Γ(Y, U) v) := by
  rw [Cohomology.structureCoeff_morphismRestrict_toSpecΓ]
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, RingHom.algebraMap_toAlgebra,
    sectionsRingHom, structureCoeff]
  have hnat := congrArg (fun g => g.hom (pY.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v)))
    (π.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  erw [hnat, ← CommRingCat.comp_apply (B.presheaf.map _) (B.presheaf.map _),
    ← Functor.map_comp]
  rfl

variable [IsDomain V] [ValuationRing V] [IsIntegral B] [IsIntegral Y]
  [LocallyOfFinitePresentation pY] [Flat (π ≫ pY)]

/-- **Zariski connectedness for a birational morphism onto a normal curve, two-chart form**
(blueprint `thm:sm-connbir-geometric`). Let `pY : Y → Spec V` be locally of finite presentation
over a valuation ring `V`, `Y` integral and normal, and `π : B → Y` birational and projective
relative to `pY` (`DeJong.IsRelativelyProjective`) with `B` integral and flat over `V`. Let
`U ⊆ Y` be a nonempty affine open such that `π⁻¹U` is the union of two affine opens, `s ⊆ Γ(Y, U)`
a finite set such that `π⁻¹(D(q))` is affine for `q ∈ s` (for instance `π` is an isomorphism over
`D(q)`), and `m` a proper ideal of `Γ(Y, U)` containing all primes which contain `s`. Then the
preimage under `π` of the vanishing locus `V(s) ⊆ U` is preconnected. -/
theorem isPreconnected_preimage_zeroLocus_of_twoCharts_birational
    (hπ : DeJong.IsRelativelyProjective pY π) (hY : IsNormalScheme Y)
    (hbir : Scheme.BirationalOver π (𝟙 Y)) {U : Y.Opens} (hU : IsAffineOpen U) [Nonempty U]
    (W₁ W₂ : B.Opens) (hW₁ : IsAffineOpen W₁) (hW₂ : IsAffineOpen W₂)
    (hcov : W₁ ⊔ W₂ = π ⁻¹ᵁ U) (s : Finset Γ(Y, U))
    (hs : ∀ q ∈ s, IsAffineOpen (π ⁻¹ᵁ Y.basicOpen q)) (m : Ideal Γ(Y, U)) (hm : m ≠ ⊤)
    (hsm : ∀ P : Ideal Γ(Y, U), P.IsPrime → (s : Set Γ(Y, U)) ⊆ P → P ≤ m) :
    _root_.IsPreconnected {b : B | ∃ hb : π b ∈ U,
      U.toSpecΓ ⟨π b, hb⟩ ∈ PrimeSpectrum.zeroLocus (s : Set Γ(Y, U))} := by
  let _ : Algebra V Γ(Y, U) := Cohomology.sectionsAlgebra V pY U
  have : Algebra.FinitePresentation V Γ(Y, U) :=
    Cohomology.finitePresentation_sectionsAlgebra V pY hU
  obtain ⟨n, i, hi, hcomp⟩ := id hπ
  let ι := (π ⁻¹ᵁ U).ι
  let f : (π ⁻¹ᵁ U).toScheme ⟶ Spec (CommRingCat.of Γ(Y, U)) := π ∣_ U ≫ U.toSpecΓ
  have hf : IsProjectiveOver f :=
    Cohomology.isProjectiveOver_morphismRestrict_toSpecΓ π pY i hcomp hU
  have htf : ∀ v : V, v ≠ 0 → ∀ (U' : (π ⁻¹ᵁ U).toScheme.Opens) (s' : Γ((π ⁻¹ᵁ U).toScheme, U')),
      sectionsRingHom (structureCoeff f) (le_top : U' ≤ ⊤) (algebraMap V Γ(Y, U) v) * s' = 0 →
        s' = 0 := by
    intro v hv U' s' hs'
    refine Cohomology.eq_zero_of_mul_eq_zero_of_flat ((π ⁻¹ᵁ U).ι ≫ π ≫ pY)
      (a := (Scheme.ΓSpecIso (CommRingCat.of V)).inv v) ?_ s' ?_
    · intro h0
      apply hv
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom h0
      simpa using this
    · rw [appTop_ι_comp_eq_structureCoeff]
      exact hs'
  -- the two charts, as opens of `π⁻¹U`
  have himage : ∀ W : B.Opens, W ≤ π ⁻¹ᵁ U → ι ''ᵁ (ι ⁻¹ᵁ W) = W := fun W hW =>
    Opens.ext (Set.image_preimage_eq_of_subset (by rw [Scheme.Opens.range_ι]; exact hW))
  have hW₁U : W₁ ≤ π ⁻¹ᵁ U := hcov ▸ le_sup_left
  have hW₂U : W₂ ≤ π ⁻¹ᵁ U := hcov ▸ le_sup_right
  have hW₁' : IsAffineOpen (ι ⁻¹ᵁ W₁) := by
    rw [← ι.isAffineOpen_iff_of_isOpenImmersion, himage W₁ hW₁U]
    exact hW₁
  have hW₂' : IsAffineOpen (ι ⁻¹ᵁ W₂) := by
    rw [← ι.isAffineOpen_iff_of_isOpenImmersion, himage W₂ hW₂U]
    exact hW₂
  have hcov' : ι ⁻¹ᵁ W₁ ⊔ ι ⁻¹ᵁ W₂ = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hcov, Scheme.Opens.ι_preimage_self]
  -- the Stein property `Γ(U, 𝒪_Y) = Γ(π⁻¹U, 𝒪_B)`
  have hstr : ∀ q : Γ(Y, U), structureCoeff f q = (π ⁻¹ᵁ U).topIso.inv (π.app U q) := by
    intro q
    rw [Cohomology.structureCoeff_morphismRestrict_toSpecΓ]
    rfl
  have hS : Function.Surjective (structureCoeff f) := by
    have hfin := Cohomology.finite_sections_preimage_of_isRelativelyProjective V π pY hπ hU
    let _ := (π.app U).hom.toAlgebra
    have : Algebra.IsIntegral Γ(Y, U) Γ(B, π ⁻¹ᵁ U) := Algebra.IsIntegral.of_finite _ _
    have hbij := BlowDown.app_bijective_of_isNormalScheme π hY hbir hU this
    intro t
    obtain ⟨q, hq⟩ := hbij.2 ((π ⁻¹ᵁ U).topIso.hom t)
    refine ⟨q, ?_⟩
    rw [hstr, hq]
    exact congrArg (fun g => g.hom t) (π ⁻¹ᵁ U).topIso.hom_inv_id
  -- the basic opens of `s`
  have hs' : ∀ q ∈ s, IsAffineOpen ((π ⁻¹ᵁ U).toScheme.basicOpen (structureCoeff f q)) := by
    intro q hq
    rw [← ι.isAffineOpen_iff_of_isOpenImmersion, hstr,
      Scheme.Opens.ι_image_basicOpen_topIso_inv, ← Scheme.preimage_basicOpen]
    exact hs q hq
  have h := isPreconnected_preimage_zeroLocus_of_isProjectiveOver f V hf htf _ _ hW₁' hW₂' hcov'
    hS s hs' m hm hsm
  -- transport to `B`
  have himg : ι '' (f ⁻¹' PrimeSpectrum.zeroLocus (s : Set Γ(Y, U))) =
      {b : B | ∃ hb : π b ∈ U,
        U.toSpecΓ ⟨π b, hb⟩ ∈ PrimeSpectrum.zeroLocus (s : Set Γ(Y, U))} := by
    ext b
    constructor
    · rintro ⟨b', hb', rfl⟩
      refine ⟨b'.2, ?_⟩
      have : (π ∣_ U) b' = ⟨π b'.1, b'.2⟩ := Subtype.ext (morphismRestrict_base_coe π U b')
      rw [Set.mem_preimage, Scheme.Hom.comp_apply, this] at hb'
      exact hb'
    · rintro ⟨hb, hbZ⟩
      refine ⟨⟨b, hb⟩, ?_, rfl⟩
      have : (π ∣_ U) ⟨b, hb⟩ = ⟨π b, hb⟩ := Subtype.ext (morphismRestrict_base_coe π U _)
      rw [Set.mem_preimage, Scheme.Hom.comp_apply, this]
      exact hbZ
  rw [← himg]
  exact h.image _ ι.continuous.continuousOn

end Geometric

section Shrink

attribute [local instance] MvPolynomial.gradedAlgebra

variable {V : Type u} [CommRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y) (pY : Y ⟶ Spec (CommRingCat.of V))

/-- The residue field of a closed point `x` of an affine open `U` is `Γ(U) ⧸ 𝔭ₓ`; in particular
`Γ(U) ⧸ 𝔭ₓ` is infinite if the residue field is. -/
theorem infinite_quotient_of_infinite_residueField {U : Y.Opens} (hU : IsAffineOpen U) {x : Y}
    (hxU : x ∈ U) (hx : IsClosed ({x} : Set Y)) [Infinite (Y.residueField x)] :
    Infinite (Γ(Y, U) ⧸ (U.toSpecΓ ⟨x, hxU⟩).asIdeal) := by
  set P := U.toSpecΓ ⟨x, hxU⟩
  -- `P` is a closed point of `Spec Γ(Y, U)`
  have hclU : IsClosed ({(⟨x, hxU⟩ : U)} : Set U) := by
    have : ({(⟨x, hxU⟩ : U)} : Set U) = U.ι ⁻¹' {x} := by
      ext ⟨y, hy⟩
      simp only [Set.mem_singleton_iff, Set.mem_preimage, Scheme.Opens.ι_apply]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [this]
    exact hx.preimage U.ι.continuous
  have hclP : IsClosed ({P} : Set (PrimeSpectrum Γ(Y, U))) := by
    have h := hU.isoSpec.hom.homeomorph.isClosedMap _ hclU
    rwa [Set.image_singleton] at h
  have hmax : P.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).mp hclP
  -- the residue fields
  have e₁ : Function.Bijective (U.ι.residueFieldMap ⟨x, hxU⟩) :=
    ConcreteCategory.bijective_of_isIso _
  have e₂ : Function.Bijective (hU.isoSpec.hom.residueFieldMap ⟨x, hxU⟩) :=
    ConcreteCategory.bijective_of_isIso _
  have e₃ : Function.Bijective (Scheme.Spec.residueFieldIso (CommRingCat.of Γ(Y, U)) P).hom :=
    ConcreteCategory.bijective_of_isIso _
  have e₄ := P.asIdeal.bijective_algebraMap_quotient_residueField
  have : Infinite (Y.residueField (U.ι ⟨x, hxU⟩)) := ‹Infinite (Y.residueField x)›
  have : Infinite (U.toScheme.residueField ⟨x, hxU⟩) := Infinite.of_injective _ e₁.1
  have : Infinite ((Spec (CommRingCat.of Γ(Y, U))).residueField P) :=
    Infinite.of_surjective _ e₂.2
  have : Infinite P.asIdeal.ResidueField := Infinite.of_injective _ e₃.1
  exact Infinite.of_surjective _ e₄.2

/-- The image of a closed point `x ∈ U` in `Spec Γ(Y, U)`, `U` affine, is closed. -/
theorem isClosed_singleton_toSpecΓ {U : Y.Opens} (hU : IsAffineOpen U) {x : Y} (hxU : x ∈ U)
    (hx : IsClosed ({x} : Set Y)) :
    IsClosed ({U.toSpecΓ ⟨x, hxU⟩} : Set (PrimeSpectrum Γ(Y, U))) := by
  have hclU : IsClosed ({(⟨x, hxU⟩ : U)} : Set U) := by
    have : ({(⟨x, hxU⟩ : U)} : Set U) = U.ι ⁻¹' {x} := by
      ext ⟨y, hy⟩
      simp only [Set.mem_singleton_iff, Set.mem_preimage, Scheme.Opens.ι_apply]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [this]
    exact hx.preimage U.ι.continuous
  have h := hU.isoSpec.hom.homeomorph.isClosedMap _ hclU
  rwa [Set.image_singleton] at h

/-- **Two affine charts over a neighbourhood of a closed point** (blueprint
`lem:sm-connbir-charts`). Let `π : B → Y` be projective relative to `pY : Y → Spec V`, and `x` a
closed point of `Y` with infinite residue field such that the fibre `π⁻¹(x)` has no chains
`b ⤳ b' ⤳ b''` of three distinct points (it is a curve). Then every open `U' ∋ x` contains an
affine open `U ∋ x` such that `π⁻¹U` is the union of two affine opens. -/
theorem exists_twoCharts (hπ : DeJong.IsRelativelyProjective pY π) (x : Y)
    (hx : IsClosed ({x} : Set Y)) [Infinite (Y.residueField x)]
    (hdim : ∀ b b' b'' : B, π b = x → b ⤳ b' → b' ⤳ b'' → b = b' ∨ b' = b'')
    (U' : Y.Opens) (hxU' : x ∈ U') :
    ∃ U : Y.Opens, IsAffineOpen U ∧ x ∈ U ∧ U ≤ U' ∧
      ∃ W₁ W₂ : B.Opens, IsAffineOpen W₁ ∧ IsAffineOpen W₂ ∧ W₁ ⊔ W₂ = π ⁻¹ᵁ U := by
  classical
  obtain ⟨U₀, hU₀, hxU₀, hU₀U'⟩ := exists_isAffineOpen_mem_and_subset hxU'
  obtain ⟨n, i, hi, hcomp⟩ := id hπ
  have hproj := Cohomology.isProjectiveOver_morphismRestrict_toSpecΓ π pY i hcomp hU₀
  have : IsProper (π ∣_ U₀ ≫ U₀.toSpecΓ) := hproj.isProper
  obtain ⟨m, j, hj, hjcomp⟩ := hproj
  set P := U₀.toSpecΓ ⟨x, hxU₀⟩ with hPdef
  have hinf := infinite_quotient_of_infinite_residueField hU₀ hxU₀ hx
  have hclP := isClosed_singleton_toSpecΓ hU₀ hxU₀ hx
  have hinj : Function.Injective U₀.toSpecΓ := hU₀.isoSpec.hom.homeomorph.injective
  have hpt : ∀ a : (π ⁻¹ᵁ U₀).toScheme,
      (π ∣_ U₀ ≫ U₀.toSpecΓ) a = U₀.toSpecΓ ⟨π a.1, a.2⟩ := by
    intro a
    rw [Scheme.Hom.comp_apply]
    congr 1
    exact Subtype.ext (morphismRestrict_base_coe π U₀ a)
  have hfib : ∀ a : (π ⁻¹ᵁ U₀).toScheme, (π ∣_ U₀ ≫ U₀.toSpecΓ) a = P → π a.1 = x := by
    intro a ha
    rw [hpt] at ha
    exact congrArg Subtype.val (hinj ha)
  have hdim' : ∀ a b c : (π ⁻¹ᵁ U₀).toScheme,
      (j ≫ projectiveSpaceStructure Γ(Y, U₀) m) a = P → a ⤳ b → b ⤳ c → a = b ∨ b = c := by
    intro a b c ha hab hbc
    rw [hjcomp] at ha
    rcases hdim a.1 b.1 c.1 (hfib a ha) (hab.map (π ⁻¹ᵁ U₀).ι.continuous)
      (hbc.map (π ⁻¹ᵁ U₀).ι.continuous) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  obtain ⟨f, hf, g, hg, hcovP⟩ := exists_linearForms_fibre j P hclP hdim'
  let O : (π ⁻¹ᵁ U₀).toScheme.Opens :=
    j ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading Γ(Y, U₀) m) f ⊔
      j ⁻¹ᵁ Proj.basicOpen (projectiveSpaceGrading Γ(Y, U₀) m) g
  have hWc : IsClosed ((π ∣_ U₀ ≫ U₀.toSpecΓ) '' (O : Set (π ⁻¹ᵁ U₀).toScheme)ᶜ) :=
    (π ∣_ U₀ ≫ U₀.toSpecΓ).isClosedMap _ O.isOpen.isClosed_compl
  have hPWc : P ∉ (π ∣_ U₀ ≫ U₀.toSpecΓ) '' (O : Set (π ⁻¹ᵁ U₀).toScheme)ᶜ := by
    rintro ⟨a, ha, haP⟩
    apply ha
    have := hcovP a (by rw [hjcomp]; exact haP)
    exact this
  obtain ⟨_, ⟨h, rfl⟩, hPh, hhsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hPWc
      hWc.isOpen_compl
  refine ⟨Y.basicOpen h, hU₀.basicOpen h, ?_, (Y.basicOpen_le h).trans hU₀U', ?_⟩
  · rw [mem_basicOpen_iff_notMem_toSpecΓ h hxU₀]
    exact hPh
  let ι₀ := (π ⁻¹ᵁ U₀).ι
  have hres : ∀ A : B.Opens, A ≤ π ⁻¹ᵁ U₀ → IsAffineOpen A →
      IsAffineOpen (A ⊓ π ⁻¹ᵁ Y.basicOpen h) := by
    intro A hA hAff
    have e : A ⊓ π ⁻¹ᵁ Y.basicOpen h =
        B.basicOpen (B.presheaf.map (homOfLE hA).op (π.app U₀ h)) := by
      rw [Scheme.basicOpen_res, Scheme.preimage_basicOpen]
    rw [e]
    exact hAff.basicOpen _
  have hAf := (isAffineOpen_preimage_basicOpen j f hf one_pos).image_of_isOpenImmersion ι₀
  have hAg := (isAffineOpen_preimage_basicOpen j g hg one_pos).image_of_isOpenImmersion ι₀
  refine ⟨_, _, hres _ (Scheme.Opens.ι_image_le _ _) hAf, hres _ (Scheme.Opens.ι_image_le _ _) hAg,
    le_antisymm (sup_le inf_le_right inf_le_right) ?_⟩
  intro b hb
  have hbU₀ : b ∈ π ⁻¹ᵁ U₀ := Y.basicOpen_le h hb
  let b' : (π ⁻¹ᵁ U₀).toScheme := ⟨b, hbU₀⟩
  have hfb : (π ∣_ U₀ ≫ U₀.toSpecΓ) b' ∈ PrimeSpectrum.basicOpen h := by
    rw [hpt, PrimeSpectrum.mem_basicOpen, ← mem_basicOpen_iff_notMem_toSpecΓ]
    exact hb
  have hbO : b' ∈ O := by
    by_contra hc
    exact hhsub hfb ⟨b', hc, rfl⟩
  rcases Opens.mem_sup.mp hbO with h1 | h1
  · exact Opens.mem_sup.mpr (Or.inl ⟨⟨b', h1, rfl⟩, hb⟩)
  · exact Opens.mem_sup.mpr (Or.inr ⟨⟨b', h1, rfl⟩, hb⟩)

end Shrink

section Auxiliary

variable {V : Type u} [CommRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y) (pY : Y ⟶ Spec (CommRingCat.of V))

/-- A birational morphism which is projective relative to `pY` is surjective. -/
theorem surjective_of_isRelativelyProjective (hπ : DeJong.IsRelativelyProjective pY π)
    (hbir : Scheme.BirationalOver π (𝟙 Y)) : Function.Surjective π := by
  have : IsProper π := hπ.isProper
  have : IsDominant π := isDominant_of_birationalOver_id π hbir
  exact (surjective_of_isDominant_of_isClosed_range π π.isClosedMap.isClosed_range).surj

/-- A birational morphism which is projective relative to `pY` between integral schemes is a
modification. -/
theorem isModification_of_isRelativelyProjective [IsIntegral B] [IsIntegral Y] (hπ : DeJong.IsRelativelyProjective pY π)
    (hbir : Scheme.BirationalOver π (𝟙 Y)) : IsModification π :=
  { toIsProper := hπ.isProper
    sourceIntegral := inferInstance
    targetIntegral := inferInstance
    birational := hbir }

/-- **Schemes of finite type over a base with finitely many points are Noetherian spaces**: the
space is the finite union of the fibres, which are of finite type over fields. -/
theorem noetherianSpace_of_finite {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of V))
    [LocallyOfFiniteType q] [QuasiCompact q] [Finite (PrimeSpectrum V)] :
    NoetherianSpace X := by
  have h : ∀ P : PrimeSpectrum V, NoetherianSpace (q ⁻¹' {P}) := fun P =>
    noetherianSpace_fibre q P
  have hU := NoetherianSpace.iUnion (fun P : PrimeSpectrum V => q ⁻¹' {P})
  have heq : (⋃ P : PrimeSpectrum V, q ⁻¹' {P}) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact ⟨q z, rfl⟩
  rw [heq] at hU
  exact noetherian_univ_iff.mp hU

/-- **Closed points are cut out by finitely many functions** over a valuation ring of finite height:
if `Y` is locally of finite type over `V` with `Spec V` finite and `x ∈ U₀` is a closed point of
`Y`, `U₀` affine, then `x` is the common zero locus in `U₀` of finitely many functions on `U₀`. -/
theorem exists_finset_zeroLocus_eq_singleton [LocallyOfFiniteType pY] [Finite (PrimeSpectrum V)]
    (x : Y) (hx : IsClosed ({x} : Set Y)) {U₀ : Y.Opens} (hU₀ : IsAffineOpen U₀)
    (hxU₀ : x ∈ U₀) :
    ∃ s₀ : Finset Γ(Y, U₀), ∀ y ∈ U₀, (∀ q ∈ s₀, y ∉ Y.basicOpen q) ↔ y = x := by
  classical
  have : IsAffine U₀.toScheme := hU₀
  have := noetherianSpace_of_finite (U₀.ι ≫ pY)
  -- `U₀ ∖ {x}` is compact
  have hK : IsCompact (U₀.ι '' ({(⟨x, hxU₀⟩ : U₀)}ᶜ : Set U₀)) :=
    (NoetherianSpace.isCompact _).image U₀.ι.continuous
  let T := {q : Γ(Y, U₀) // x ∉ Y.basicOpen q}
  have hcover : U₀.ι '' ({(⟨x, hxU₀⟩ : U₀)}ᶜ : Set U₀) ⊆ ⋃ q : T, (Y.basicOpen q.1 : Set Y) := by
    rintro _ ⟨⟨y, hy⟩, hyx, rfl⟩
    have hyx' : y ≠ x := fun h => hyx (Subtype.ext h)
    let O : Y.Opens := ⟨({x} : Set Y)ᶜ, hx.isOpen_compl⟩
    obtain ⟨q, hqO, hyq⟩ := hU₀.exists_basicOpen_le (V := O) ⟨y, hyx'⟩ hy
    refine Set.mem_iUnion.mpr ⟨⟨q, fun hxq => hqO hxq rfl⟩, hyq⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun q : T => (Y.basicOpen q.1 : Set Y))
    (fun q => (Y.basicOpen q.1).isOpen) hcover
  refine ⟨t.image Subtype.val, fun y hy => ⟨fun h => ?_, ?_⟩⟩
  · by_contra hyx
    have hmem : y ∈ U₀.ι '' ({(⟨x, hxU₀⟩ : U₀)}ᶜ : Set U₀) :=
      ⟨⟨y, hy⟩, fun h' => hyx (congrArg Subtype.val h'), rfl⟩
    obtain ⟨q, hq, hyq⟩ := Set.mem_iUnion₂.mp (ht hmem)
    exact h q.1 (Finset.mem_image_of_mem _ hq) hyq
  · rintro rfl q hq
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.mp hq
    exact q'.2

/-- **Fibres of a modification of a relative curve over a closed point are curves**: if the
generic point of `Y` has transcendence degree at most one over `Spec V` and `π` is a
modification, the fibre over a closed point `x` contains no chain `b ⤳ b' ⤳ b''` of three
distinct points (each proper specialization in a fibre drops the transcendence degree,
`ValCurves.one_add_fiberTrdeg_le_of_specializes`). -/
theorem eq_or_eq_of_specializes_of_fiberTrdeg_le_one [IsIntegral B] [IsIntegral Y]
    [IsModification π]
    (hcurve : ValuationRing.fiberTrdeg pY (genericPoint Y) ≤ 1) [IsDomain V] [ValuationRing V]
    (x : Y) (hx : IsClosed ({x} : Set Y)) (b b' b'' : B) (hb : π b = x) (h₁ : b ⤳ b')
    (h₂ : b' ⤳ b'') : b = b' ∨ b' = b'' := by
  by_contra hne
  push Not at hne
  have hb' : π b' = x := by
    have := (h₁.map π.continuous).mem_closed hx (by rw [hb]; rfl)
    exact this
  have hb'' : π b'' = x := by
    have := (h₂.map π.continuous).mem_closed hx (by rw [hb']; rfl)
    exact this
  have e₁ := ValCurves.one_add_fiberTrdeg_le_of_specializes (π ≫ pY) h₁ hne.1
    (by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hb, hb'])
  have e₂ := ValCurves.one_add_fiberTrdeg_le_of_specializes (π ≫ pY) h₂ hne.2
    (by rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hb', hb''])
  have e₀ := ValCurves.fiberTrdeg_le_one pY hcurve π b
  have h0 : ValuationRing.fiberTrdeg (π ≫ pY) b' = 0 :=
    ValCurves.Cardinal.eq_zero_of_one_add_le_one (e₁.trans e₀)
  rw [h0] at e₂
  have : (1 : Cardinal) ≤ 0 := le_self_add.trans e₂
  exact absurd this (by simp)

end Auxiliary

section Point

attribute [local instance] MvPolynomial.gradedAlgebra

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y) (pY : Y ⟶ Spec (CommRingCat.of V))
  [IsIntegral B] [IsIntegral Y] [LocallyOfFinitePresentation pY] [Flat (π ≫ pY)]

/-- **Zariski connectedness for a birational morphism onto a normal curve, point form**
(blueprint `thm:sm-connbir-point`, Temkin, proof of Lemma 4.4.2, T:3133). Let `pY : Y → Spec V`
be locally of finite presentation over a valuation ring `V`, `Y` integral and normal, and
`π : B → Y` birational and projective relative to `pY` with `B` integral and flat over `V`. Let
`x` be a closed point of `Y` with infinite residue field such that the fibre `π⁻¹(x)` is a curve
(no chains `b ⤳ b' ⤳ b''` of three distinct points), and `U₀ ∋ x` an open such that
* `π` is an isomorphism over a neighbourhood of every point of `U₀ ∖ {x}`, and
* `x` is the common zero locus in `U₀` of finitely many functions `s₀ ⊆ Γ(Y, U₀)`.
Then the fibre `π⁻¹(x)` is connected. -/
theorem isConnected_preimage_singleton_of_isIso
    (hπ : DeJong.IsRelativelyProjective pY π) (hY : IsNormalScheme Y)
    (hbir : Scheme.BirationalOver π (𝟙 Y)) (x : Y) (hx : IsClosed ({x} : Set Y))
    [Infinite (Y.residueField x)]
    (hdim : ∀ b b' b'' : B, π b = x → b ⤳ b' → b' ⤳ b'' → b = b' ∨ b' = b'')
    {U₀ : Y.Opens} (hxU₀ : x ∈ U₀)
    (hiso : ∀ y ∈ U₀, y ≠ x → y ∈ Geometry.ModificationCenter.isomorphismOpen π)
    (s₀ : Finset Γ(Y, U₀)) (hs₀ : ∀ y ∈ U₀, (∀ q ∈ s₀, y ∉ Y.basicOpen q) ↔ y = x) :
    _root_.IsConnected (π ⁻¹' {x}) := by
  classical
  obtain ⟨U, hU, hxU, hUU₀, W₁, W₂, hW₁, hW₂, hcov⟩ := exists_twoCharts π pY hπ x hx hdim U₀ hxU₀
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let ρ : Γ(Y, U₀) →+* Γ(Y, U) := (Y.presheaf.map (homOfLE hUU₀).op).hom
  let s : Finset Γ(Y, U) := s₀.image ρ
  have hbo : ∀ q : Γ(Y, U₀), Y.basicOpen (ρ q) = U ⊓ Y.basicOpen q := fun q =>
    Scheme.basicOpen_res Y q (homOfLE hUU₀).op
  -- the vanishing locus of `s` in `U` is `{x}`
  have hzero : ∀ y ∈ U, (∀ q ∈ s, y ∉ Y.basicOpen q) ↔ y = x := by
    intro y hy
    rw [← hs₀ y (hUU₀ hy)]
    constructor
    · intro h q hq hyq
      exact h (ρ q) (Finset.mem_image_of_mem ρ hq) (by rw [hbo]; exact ⟨hy, hyq⟩)
    · intro h q hq hyq
      obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hq
      rw [hbo] at hyq
      exact h q₀ hq₀ hyq.2
  have hxs : ∀ q ∈ s, x ∉ Y.basicOpen q := (hzero x hxU).mpr rfl
  -- `π` is an isomorphism over the basic opens of `s`
  have hs : ∀ q ∈ s, IsAffineOpen (π ⁻¹ᵁ Y.basicOpen q) := by
    intro q hq
    have hle : Y.basicOpen q ≤ Geometry.ModificationCenter.isomorphismOpen π := by
      intro y hy
      refine hiso y (hUU₀ (Y.basicOpen_le q hy)) ?_
      rintro rfl
      exact hxs q hq hy
    have : IsIso (π ∣_ Y.basicOpen q) :=
      (Geometry.ModificationCenter.le_isomorphismOpen_iff π _).mp hle
    have : IsAffine (Y.basicOpen q).toScheme := hU.basicOpen q
    exact IsAffine.of_isIso (π ∣_ Y.basicOpen q)
  -- the prime of `x`
  set m := (U.toSpecΓ ⟨x, hxU⟩).asIdeal
  have hsm : ∀ P : Ideal Γ(Y, U), P.IsPrime → (s : Set Γ(Y, U)) ⊆ P → P ≤ m := by
    intro P hP hsP
    obtain ⟨⟨y, hy⟩, hyP⟩ := hU.isoSpec.hom.homeomorph.surjective ⟨P, hP⟩
    have hyP' : U.toSpecΓ ⟨y, hy⟩ = ⟨P, hP⟩ := hyP
    have hyx : y = x := by
      refine (hzero y hy).mp fun q hq => ?_
      rw [mem_basicOpen_iff_notMem_toSpecΓ q hy, hyP', not_not]
      exact hsP hq
    subst hyx
    rw [show m = P from congrArg PrimeSpectrum.asIdeal hyP']
  have h := isPreconnected_preimage_zeroLocus_of_twoCharts_birational π pY hπ hY hbir hU W₁ W₂
    hW₁ hW₂ hcov s hs m (U.toSpecΓ ⟨x, hxU⟩).isPrime.ne_top hsm
  have hset : {b : B | ∃ hb : π b ∈ U,
      U.toSpecΓ ⟨π b, hb⟩ ∈ PrimeSpectrum.zeroLocus (s : Set Γ(Y, U))} = π ⁻¹' {x} := by
    ext b
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hb, hbs⟩
      refine (hzero (π b) hb).mp fun q hq => ?_
      rw [mem_basicOpen_iff_notMem_toSpecΓ q hb, not_not]
      exact hbs hq
    · intro hb
      have hbU : π b ∈ U := hb ▸ hxU
      refine ⟨hbU, fun q hq => ?_⟩
      have := (hzero (π b) hbU).mpr hb q hq
      rw [mem_basicOpen_iff_notMem_toSpecΓ q hbU, not_not] at this
      exact this
  rw [hset] at h
  obtain ⟨b, hb⟩ := surjective_of_isRelativelyProjective π pY hπ hbir x
  exact ⟨⟨b, hb⟩, h⟩

end Point

section FiniteHeight

attribute [local instance] MvPolynomial.gradedAlgebra

open Geometry.ModificationCenter

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y) (pY : Y ⟶ Spec (CommRingCat.of V))
  [IsIntegral B] [IsIntegral Y] [LocallyOfFinitePresentation pY] [Flat (π ≫ pY)]
  [QuasiCompact pY] [IsSeparated pY]

/-- **Zariski connectedness for a birational morphism onto a normal curve over a valuation ring
of finite height** (blueprint `thm:sm-connbir-finite-height`). Let `V` be a valuation ring with
finitely many primes, `pY : Y → Spec V` of finite presentation and separated with `Y` integral,
normal and of relative dimension at most one (`trdeg κ(η_Y)/κ(pY η_Y) ≤ 1`), and `π : B → Y`
birational and projective relative to `pY` with `B` integral and flat over `V`. Let `x` be a closed
point of `Y` with infinite residue field such that no other point of the modification locus
(`center π`, the complement of the open over which `π` is an isomorphism) specializes to `x`. Then
`π⁻¹(x)` is connected. -/
theorem isConnected_preimage_singleton_of_generizations [Finite (PrimeSpectrum V)]
    (hπ : DeJong.IsRelativelyProjective pY π) (hY : IsNormalScheme Y)
    (hbir : Scheme.BirationalOver π (𝟙 Y))
    (hcurve : ValuationRing.fiberTrdeg pY (genericPoint Y) ≤ 1) (x : Y)
    (hx : IsClosed ({x} : Set Y)) [Infinite (Y.residueField x)]
    (hgen : ∀ y ∈ center π, y ⤳ x → y = x) : _root_.IsConnected (π ⁻¹' {x}) := by
  classical
  have := isModification_of_isRelativelyProjective π pY hπ hbir
  have : Finite (Spec (CommRingCat.of V)) := inferInstanceAs (Finite (PrimeSpectrum V))
  have hfin : (center π : Set Y).Finite := ValCurves.finite_center pY hY hcurve π
  -- an open neighbourhood of `x` meeting the modification locus only in `x`
  set K := closure ((center π : Set Y) \ {x})
  have hxK : x ∉ K := by
    have hK : K = ⋃ y ∈ (center π : Set Y) \ {x}, closure {y} := by
      rw [← (hfin.sdiff (t := {x})).closure_biUnion (fun y => ({y} : Set Y)),
        Set.biUnion_of_singleton]
    rw [hK, Set.mem_iUnion₂]
    rintro ⟨y, ⟨hy, hyx⟩, hxy⟩
    exact hyx (hgen y hy (specializes_iff_mem_closure.mpr hxy))
  let U₀ : Y.Opens := ⟨Kᶜ, isClosed_closure.isOpen_compl⟩
  have hiso : ∀ y ∈ U₀, y ≠ x → y ∈ isomorphismOpen π := by
    intro y hy hyx
    by_contra h
    exact hy (subset_closure ⟨h, hyx⟩)
  obtain ⟨U₁, hU₁, hxU₁, hU₁U₀⟩ := exists_isAffineOpen_mem_and_subset (U := U₀) hxK
  obtain ⟨s₀, hs₀⟩ := exists_finset_zeroLocus_eq_singleton pY x hx hU₁ hxU₁
  exact isConnected_preimage_singleton_of_isIso π pY hπ hY hbir x hx
    (fun b b' b'' hb h₁ h₂ => eq_or_eq_of_specializes_of_fiberTrdeg_le_one π pY hcurve x hx
      b b' b'' hb h₁ h₂) hxU₁ (fun y hy hyx => hiso y (hU₁U₀ hy) hyx) s₀ hs₀

omit [LocallyOfFinitePresentation pY] [Flat (π ≫ pY)] [QuasiCompact pY] in
/-- **Over a valuation ring of height one there is no restriction**: if `V` has only the primes `0`
and the maximal ideal, no point of the modification locus other than `x` specializes to a closed
point `x` of `Y`. (Points of the locus over the closed point are closed, being algebraic over the
residue field; over the generic point `π` is an isomorphism, since the points of `B` over a closed
point of the generic fibre of `Y` other than the generic point are algebraic, so that `π` is finite,
hence an isomorphism, over a neighbourhood.) -/
theorem eq_of_mem_center_of_specializes_of_heightOne
    (hπ : DeJong.IsRelativelyProjective pY π) (hY : IsNormalScheme Y)
    (hbir : Scheme.BirationalOver π (𝟙 Y))
    (hcurve : ValuationRing.fiberTrdeg pY (genericPoint Y) ≤ 1)
    (hV : ∀ P : Ideal V, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal V) (x : Y)
    (y : Y) (hy : y ∈ center π) (hyx : y ⤳ x) : y = x := by
  classical
  have := isModification_of_isRelativelyProjective π pY hπ hbir
  have h0 := ValCurves.fiberTrdeg_eq_zero_of_mem_center pY hY hcurve π hy
  have halg : ValCurves.IsAlgebraicAt pY y :=
    (ValCurves.isAlgebraicAt_iff_fiberTrdeg_eq_zero pY y).mpr h0
  rcases hV (pY y).asIdeal (pY y).isPrime with hbot | hmax
  · -- `y` over the generic point: `π` is an isomorphism near `y`
    exfalso
    apply hy
    have hgenY : genericPoint Y ∈ isomorphismOpen π := by
      obtain ⟨w⟩ := nonempty_isomorphismOpen π
      exact ((genericPoint_spec Y).mem_open_set_iff (isomorphismOpen π).isOpen).mpr
        ⟨w.1, trivial, w.2⟩
    have hpYgen : pY (genericPoint Y) = pY y := by
      have hsp : pY (genericPoint Y) ⤳ pY y :=
        ((genericPoint_spec Y).specializes (Set.mem_univ y)).map pY.continuous
      apply PrimeSpectrum.ext
      apply le_antisymm
      · exact (PrimeSpectrum.le_iff_specializes _ _).mpr hsp
      · rw [hbot]
        exact bot_le
    have halgπ : ∀ b : B, π b = y → ValCurves.IsAlgebraicAt π b := by
      intro b hb
      rw [ValCurves.isAlgebraicAt_iff_fiberTrdeg_eq_zero]
      have hne : genericPoint B ≠ b := by
        intro h
        apply hy
        rw [← hb, ← h, Geometry.NormalCurveModification.genericPoint_map π hbir]
        exact hgenY
      have hfib : (π ≫ pY) (genericPoint B) = (π ≫ pY) b := by
        rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
          Geometry.NormalCurveModification.genericPoint_map π hbir, hb, hpYgen]
      have e₁ := ValCurves.one_add_fiberTrdeg_le_of_specializes (π ≫ pY)
        ((genericPoint_spec B).specializes (Set.mem_univ b)) hne hfib
      have e₂ := ValCurves.fiberTrdeg_le_one pY hcurve π (genericPoint B)
      have h1 := ValCurves.Cardinal.eq_zero_of_one_add_le_one (e₁.trans e₂)
      rw [ValCurves.fiberTrdeg_comp, hb, h0, zero_add] at h1
      exact h1
    obtain ⟨W, hyW, hfinW, -⟩ := ValCurves.exists_isFinite_morphismRestrict_of_isAlgebraicAt π y
      halgπ
    have : Nonempty W := ⟨⟨y, hyW⟩⟩
    have hn : IsNormalScheme W.toScheme :=
      Geometry.CurveCompactification.isNormalScheme_of_isOpenImmersion W.ι hY
    have hr := Geometry.CurveCompactification.isModification_morphismRestrict π W
    have := hr.sourceIntegral
    have := hr.targetIntegral
    have : IsIso (π ∣_ W) :=
      Geometry.NormalCurveModification.isIso_of_finite_birational (π ∣_ W) hr.birational hn
    exact le_isomorphismOpen_of_isIso π W hyW
  · -- `y` over the closed point: `y` is a closed point of `Y`
    have hyc : pY y = IsLocalRing.closedPoint V := PrimeSpectrum.ext hmax
    have hF : IsClosed (pY ⁻¹' {IsLocalRing.closedPoint V}) :=
      (IsLocalRing.isClosed_singleton_closedPoint V).preimage pY.continuous
    have hcl := ValCurves.isClosed_singleton_preimage_of_isAlgebraicAt pY hyc halg
    have hcl' : IsClosed ({y} : Set Y) := by
      have := hF.isClosedMap_subtype_val _ hcl
      rwa [Set.image_singleton] at this
    have := hyx.mem_closed hcl' rfl
    exact (Set.mem_singleton_iff.mp this).symm

/-- **Zariski connectedness for a birational morphism onto a normal curve over a valuation ring of
height one** (blueprint `cor:sm-connbir-height-one`): every fibre of `π` over a closed point of `Y`
with infinite residue field is connected. -/
theorem isConnected_preimage_singleton_of_heightOne
    (hπ : DeJong.IsRelativelyProjective pY π) (hY : IsNormalScheme Y)
    (hbir : Scheme.BirationalOver π (𝟙 Y))
    (hcurve : ValuationRing.fiberTrdeg pY (genericPoint Y) ≤ 1)
    (hV : ∀ P : Ideal V, P.IsPrime → P = ⊥ ∨ P = IsLocalRing.maximalIdeal V) (x : Y)
    (hx : IsClosed ({x} : Set Y)) [Infinite (Y.residueField x)] :
    _root_.IsConnected (π ⁻¹' {x}) := by
  have : Finite (PrimeSpectrum V) := by
    refine Finite.of_injective (fun P : PrimeSpectrum V => decide (P.asIdeal = ⊥)) ?_
    intro P Q hPQ
    have key : ∀ R : PrimeSpectrum V, R.asIdeal ≠ ⊥ → R.asIdeal = IsLocalRing.maximalIdeal V :=
      fun R hR => (hV R.asIdeal R.isPrime).resolve_left hR
    simp only [decide_eq_decide] at hPQ
    apply PrimeSpectrum.ext
    by_cases hP : P.asIdeal = ⊥
    · rw [hP, hPQ.mp hP]
    · rw [key P hP, key Q fun h => hP (hPQ.mpr h)]
  exact isConnected_preimage_singleton_of_generizations π pY hπ hY hbir hcurve x hx
    (fun y hy hyx => eq_of_mem_center_of_specializes_of_heightOne π pY hπ hY hbir hcurve hV x y
      hy hyx)

end FiniteHeight

end

end DeJongAlterations.StableModification.Cohomology.ConnectedBirational

