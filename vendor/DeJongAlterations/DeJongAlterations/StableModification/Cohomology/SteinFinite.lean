/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.SteinCoherent
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finiteness of `π_* 𝒪_B` over a valuation ring (Stein finiteness)

Let `V` be a valuation ring. This file proves the finiteness half of the plan's
`thm:sm-stein-finite-valuation` (`PLAN-SM-GEOM.md`, chapter F and S8), which replaces Temkin's
Lemma 4.4.1 (Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`semi-stable.tex` lines 3089–3104) and its use of the reduced fibre theorem (Grauert–Remmert):

* `eq_zero_of_mul_eq_zero_of_flat`: if `q : X → Y` is flat and `Y` is integral, a nonzero
  function on `Y` is a nonzerodivisor on the functions on every open of `X` (so a flat
  `V`-scheme has no `V`-torsion);
* `ProjectiveCoordinates.finitePresentation_globalSections_fp`: if `X` has projective
  coordinates over a finitely presented `V`-algebra `R` and `𝒪_X` has no `V`-torsion on the
  charts, then `Γ(X, 𝒪_X)` is a finitely presented `R`-module (`Ȟ⁰ = Γ` and
  `SteinCoherent.lean`);
* `isFinite_fromNormalization`: for a quasi-compact quasi-separated `π : B → Y` such that
  `Γ(π⁻¹U, 𝒪_B)` is a finite `Γ(U, 𝒪_Y)`-module for every affine open `U ⊆ Y`, the relative
  normalization `π.normalization → Y` (Mathlib's `Spec` of the integral closure of `𝒪_Y` in
  `π_* 𝒪_B`) is a finite morphism; since the integral closure is everything
  (`integralClosure_eq_top_of_finite`), `π.normalization = Spec π_* 𝒪_B`;
* `finite_sections_preimage_of_isProjectiveOver`, `isFinite_fromNormalization_of_isProjectiveOver`
  (blueprint `thm:sm-stein-finite-valuation`): for `pY : Y → Spec V` locally of finite
  presentation, `B` flat over `V` and `π⁻¹U` projective over `Γ(U, 𝒪_Y)` for every affine open
  `U`, the module `Γ(π⁻¹U, 𝒪_B)` is finite over `Γ(U, 𝒪_Y)` and `π.normalization → Y` is finite.
  The relatively projective case (`B ↪ Y ×_V ℙⁿ_V`) is in `SteinProjective.lean`.

Blueprint: `sm-cohomology-stein.tex`, `lem:sm-flat-torsion-free`,
`thm:sm-stein-finite-sections`, `lem:sm-normalization-finite`, `thm:sm-stein-finite-valuation`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

/-- The structure sheaf `𝒪_X`, as a module over itself, is quasi-coherent (it is free of rank
one). -/
instance isQuasicoherent_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsQuasicoherent := by
  have h : (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}).IsQuasicoherent :=
    inferInstance
  obtain ⟨⟨q⟩⟩ := h
  let e : SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1} ≅
      SheafOfModules.unit X.ringCatSheaf :=
    Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf)
  exact (SheafOfModules.QuasicoherentData.ofIsIso.{u, u, u, u} e.hom q).isQuasicoherent

section Torsion

/-- **Flat schemes over an integral base have no torsion**: if `q : X → Y` is flat and `Y` is
integral, a nonzero function `a` on `Y` is a nonzerodivisor on the functions on every open of `X`.
(At a point `x`, the germ of `a` is a nonzero element of the domain `𝒪_{Y, q x}`, and `𝒪_{X, x}`
is flat over it.) -/
theorem eq_zero_of_mul_eq_zero_of_flat {X Y : Scheme.{u}} (q : X ⟶ Y) [Flat q] [IsIntegral Y]
    {a : Γ(Y, ⊤)} (ha : a ≠ 0) {W : X.Opens} (s : Γ(X, W))
    (hs : X.presheaf.map (homOfLE le_top).op (q.appTop a) * s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext X.sheaf W s 0 fun x hx => ?_
  have hq : q x ∈ (⊤ : Y.Opens) := by simp
  have h1 := congrArg (X.presheaf.germ W x hx) hs
  rw [map_mul, map_zero] at h1
  have h2 : X.presheaf.germ W x hx (X.presheaf.map (homOfLE le_top).op (q.appTop a)) =
      q.stalkMap x (Y.presheaf.germ ⊤ (q x) hq a) := by
    rw [TopCat.Presheaf.germ_res_apply, Scheme.Hom.germ_stalkMap_apply]
    rfl
  rw [h2] at h1
  have hne : Y.presheaf.germ ⊤ (q x) hq a ≠ 0 := fun h =>
    ha (germ_injective_of_isIntegral Y (q x) hq (h.trans (map_zero _).symm))
  have hflat := Flat.stalkMap q x
  algebraize [(q.stalkMap x).hom]
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := X.presheaf.stalk x)
    (mem_nonZeroDivisors_of_ne_zero hne)
  have h3 : (Y.presheaf.germ ⊤ (q x) hq a) • (X.presheaf.germ W x hx s) =
      (Y.presheaf.germ ⊤ (q x) hq a) • (0 : X.presheaf.stalk x) := by
    rw [Algebra.smul_def, smul_zero]
    exact h1
  rw [map_zero]
  exact hreg h3

end Torsion

section GlobalSections

set_option backward.isDefEq.respectTransparency false

variable (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
variable {X : Scheme.{u}} {R : Type u} [CommRing R] [Algebra V R] [Algebra.FinitePresentation V R]
  {c : R →+* Γ(X, ⊤)}

namespace ProjectiveCoordinates

variable (D : ProjectiveCoordinates X R c)

/-- **Global functions on a projective scheme over a finitely presented `V`-algebra are finitely
presented** (blueprint `thm:sm-stein-finite-sections`): if `X` has projective coordinates over a
finitely presented algebra `R` over a valuation ring `V`, and the functions on the charts have no
`V`-torsion (e.g. `X` flat over `V`), then `Γ(X, 𝒪_X)` is a finitely presented `R`-module. -/
theorem finitePresentation_globalSections_fp
    (htf : ∀ i, ∀ v : V, v ≠ 0 → ∀ s : Γ(X, D.U i), D.const i (algebraMap V R v) * s = 0 → s = 0) :
    Module.FinitePresentation R
      (sectionsModuleCat (SheafOfModules.unit X.ringCatSheaf : X.Modules) c ⊤ le_top) := by
  have h := D.finitePresentation_cechCohomology_fp V (SheafOfModules.unit X.ringCatSheaf)
    (fun _ => Module.Finite.self _) htf 0
  exact Module.FinitePresentation.of_equiv
    (cechCohomologyZeroIso (F := (SheafOfModules.unit X.ringCatSheaf : X.Modules)) (U := D.U)
      (c := c) D.iSup_eq_top).toLinearEquiv.symm

end ProjectiveCoordinates

end GlobalSections

section Normalization

variable {B Y : Scheme.{u}} (π : B ⟶ Y) [QuasiCompact π] [QuasiSeparated π]

/-- If `S` is a finite `R`-algebra, the integral closure of `R` in `S` is all of `S`. -/
theorem integralClosure_eq_top_of_finite {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S] : integralClosure R S = ⊤ :=
  integralClosure_eq_top_iff.mpr inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- **The relative normalization is finite** (blueprint `lem:sm-normalization-finite`): if
`Γ(π⁻¹U, 𝒪_B)` is a finite `Γ(U, 𝒪_Y)`-module for every affine open `U ⊆ Y`, then
`π.normalization → Y` is a finite morphism. -/
theorem isFinite_fromNormalization
    (h : ∀ U : Y.Opens, IsAffineOpen U →
      letI := (π.app U).hom.toAlgebra
      Module.Finite Γ(Y, U) Γ(B, π ⁻¹ᵁ U)) :
    IsFinite π.fromNormalization := by
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @IsFinite) _
    (iSup_affineOpens_eq_top _)]
  intro U
  let e := IsOpenImmersion.isoOfRangeEq (π.fromNormalization ⁻¹ᵁ U).ι
    (π.normalizationOpenCover.f U)
      (by simpa using congr($(π.fromNormalization_preimage U).1))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso @IsFinite _ U.2.isoSpec.hom]
  have : (π.normalizationDiagramMap.app (.op U)).hom.Finite := by
    let := (π.app U).hom.toAlgebra
    change (algebraMap Γ(Y, U) (integralClosure Γ(Y, U) Γ(B, π ⁻¹ᵁ U))).Finite
    have := h U U.2
    rw [RingHom.finite_algebraMap]
    exact Module.Finite.equiv ((Subalgebra.equivOfEq _ _ integralClosure_eq_top_of_finite).trans
      Subalgebra.topEquiv).toLinearEquiv.symm
  convert! (IsFinite.SpecMap_iff _).mpr this
  rw [← cancel_mono U.2.fromSpec]
  simp [IsAffineOpen.isoSpec_hom, e, Scheme.Hom.ι_fromNormalization]

end Normalization

section Relative

set_option backward.isDefEq.respectTransparency false

variable (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
variable {B Y : Scheme.{u}} (π : B ⟶ Y)

/-- The structure coefficients of `π|_{π⁻¹U} : π⁻¹U → Spec Γ(Y, U)` are `π^♯` followed by the
identification `Γ(B, π⁻¹U) = Γ(π⁻¹U, ⊤)`. -/
theorem structureCoeff_morphismRestrict_toSpecΓ (U : Y.Opens) :
    structureCoeff (A := Γ(Y, U)) (π ∣_ U ≫ U.toSpecΓ) =
      ((π ⁻¹ᵁ U).topIso.inv.hom).comp (π.app U).hom := by
  rw [← Scheme.Opens.toSpecΓ_naturality]
  ext a
  simp only [structureCoeff, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
  rw [Scheme.Opens.toSpecΓ_appTop]
  have h := congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_inv_naturality (π.app U))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  rw [← h]
  simp

/-- The `V`-algebra structure on the functions on an open `U` of a `V`-scheme `pY : Y → Spec V`. -/
abbrev sectionsAlgebra (pY : Y ⟶ Spec (CommRingCat.of V)) (U : Y.Opens) : Algebra V Γ(Y, U) :=
  (sectionsRingHom (structureCoeff pY) (le_top : U ≤ ⊤)).toAlgebra

omit [IsDomain V] [ValuationRing V] in
/-- The functions on an affine open of a `V`-scheme locally of finite presentation form a finitely
presented `V`-algebra. -/
theorem finitePresentation_sectionsAlgebra (pY : Y ⟶ Spec (CommRingCat.of V))
    [LocallyOfFinitePresentation pY] {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra V pY U
    Algebra.FinitePresentation V Γ(Y, U) := by
  have h := HasRingHomProperty.appLE @LocallyOfFinitePresentation pY inferInstance
    ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top
  have h₂ : RingHom.FinitePresentation (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom :=
    RingHom.FinitePresentation.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).inv)
  have h₃ := h.comp h₂
  have heq : (pY.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom =
      sectionsRingHom (structureCoeff pY) (le_top : U ≤ ⊤) := by
    ext a
    simp [sectionsRingHom, structureCoeff, Scheme.Hom.appLE]
  rw [heq] at h₃
  exact h₃

/-- **Stein finiteness over a valuation ring, local form** (blueprint
`thm:sm-stein-finite-valuation`): let `pY : Y → Spec V` be locally of finite presentation over a
valuation ring `V`, `π : B → Y` with `B` flat over `V`, and `U ⊆ Y` an affine open over which `π`
is projective (`π⁻¹U` is a closed subscheme of `ℙⁿ_{Γ(Y, U)}`). Then `Γ(π⁻¹U, 𝒪_B)` is a finite
`Γ(U, 𝒪_Y)`-module. -/
theorem finite_sections_preimage_of_isProjectiveOver (pY : Y ⟶ Spec (CommRingCat.of V))
    [LocallyOfFinitePresentation pY] [Flat (π ≫ pY)] {U : Y.Opens} (hU : IsAffineOpen U)
    (hπ : IsProjectiveOver (k := Γ(Y, U)) (π ∣_ U ≫ U.toSpecΓ)) :
    letI := (π.app U).hom.toAlgebra
    Module.Finite Γ(Y, U) Γ(B, π ⁻¹ᵁ U) := by
  let alg : Algebra V Γ(Y, U) := sectionsAlgebra V pY U
  have : Algebra.FinitePresentation V Γ(Y, U) := finitePresentation_sectionsAlgebra V pY hU
  obtain ⟨D⟩ := nonempty_projectiveCoordinates_of_isProjectiveOver hπ
  have key : ∀ v : V, ((π ⁻¹ᵁ U).ι ≫ π ≫ pY).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v) =
      structureCoeff (A := Γ(Y, U)) (π ∣_ U ≫ U.toSpecΓ) (algebraMap V Γ(Y, U) v) := by
    intro v
    rw [structureCoeff_morphismRestrict_toSpecΓ]
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      Scheme.Opens.ι_appTop, Scheme.Opens.topIso_inv, RingHom.algebraMap_toAlgebra,
      sectionsRingHom, structureCoeff]
    have hnat := congrArg (fun g => g.hom (pY.appTop ((Scheme.ΓSpecIso (CommRingCat.of V)).inv v)))
      (π.naturality (homOfLE (le_top : U ≤ ⊤)).op)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
    erw [hnat, ← CommRingCat.comp_apply (B.presheaf.map _) (B.presheaf.map _),
      ← Functor.map_comp]
    rfl
  have htf : ∀ i, ∀ v : V, v ≠ 0 → ∀ s : Γ((π ⁻¹ᵁ U).toScheme, D.U i),
      D.const i (algebraMap V Γ(Y, U) v) * s = 0 → s = 0 := by
    intro i v hv s hs
    refine eq_zero_of_mul_eq_zero_of_flat ((π ⁻¹ᵁ U).ι ≫ π ≫ pY)
      (a := (Scheme.ΓSpecIso (CommRingCat.of V)).inv v) ?_ s ?_
    · intro h0
      apply hv
      have := congrArg (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom h0
      simpa using this
    · rw [key]
      exact hs
  have hfp := D.finitePresentation_globalSections_fp V htf
  let := (π.app U).hom.toAlgebra
  let M := sectionsModuleCat (SheafOfModules.unit (π ⁻¹ᵁ U).toScheme.ringCatSheaf :
    (π ⁻¹ᵁ U).toScheme.Modules) (structureCoeff (A := Γ(Y, U)) (π ∣_ U ≫ U.toSpecΓ)) ⊤ le_top
  have hid : (π ⁻¹ᵁ U).toScheme.presheaf.map
      (homOfLE (le_top : (⊤ : (π ⁻¹ᵁ U).toScheme.Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show homOfLE (le_top : (⊤ : (π ⁻¹ᵁ U).toScheme.Opens) ≤ ⊤) = 𝟙 _ from rfl, op_id,
      CategoryTheory.Functor.map_id]
  let e : M ≃ₗ[Γ(Y, U)] Γ(B, π ⁻¹ᵁ U) :=
    { toFun := fun s => (π ⁻¹ᵁ U).topIso.hom.hom (show Γ((π ⁻¹ᵁ U).toScheme, ⊤) from s)
      invFun := fun t => (show M from (π ⁻¹ᵁ U).topIso.inv.hom t)
      map_add' := fun s t => map_add _ _ _
      map_smul' := fun r s => by
        change (π ⁻¹ᵁ U).topIso.hom.hom ((π ⁻¹ᵁ U).toScheme.presheaf.map
          (homOfLE le_top).op (structureCoeff (A := Γ(Y, U)) (π ∣_ U ≫ U.toSpecΓ) r) *
            (show Γ((π ⁻¹ᵁ U).toScheme, ⊤) from s)) = _
        rw [hid, structureCoeff_morphismRestrict_toSpecΓ, map_mul]
        simp only [CommRingCat.id_apply, RingHom.comp_apply, RingHom.id_apply, Algebra.smul_def,
          RingHom.algebraMap_toAlgebra]
        congr 1
        exact congrArg (fun g => g.hom (π.app U r)) (π ⁻¹ᵁ U).topIso.inv_hom_id
      left_inv := fun s => congrArg (fun g => g.hom (show Γ((π ⁻¹ᵁ U).toScheme, ⊤) from s))
        (π ⁻¹ᵁ U).topIso.hom_inv_id
      right_inv := fun t => congrArg (fun g => g.hom t) (π ⁻¹ᵁ U).topIso.inv_hom_id }
  exact Module.Finite.equiv e

/-- **Stein finiteness over a valuation ring** (blueprint `thm:sm-stein-finite-valuation`): let
`pY : Y → Spec V` be locally of finite presentation over a valuation ring `V` and `π : B → Y`
quasi-compact, quasi-separated and projective over every affine open of `Y`, with `B` flat over
`V`. Then `π_* 𝒪_B` is a finite `𝒪_Y`-algebra: the relative normalization
`π.normalization = Spec π_* 𝒪_B` is finite over `Y`. -/
theorem isFinite_fromNormalization_of_isProjectiveOver (pY : Y ⟶ Spec (CommRingCat.of V))
    [LocallyOfFinitePresentation pY] [Flat (π ≫ pY)] [QuasiCompact π] [QuasiSeparated π]
    (hπ : ∀ U : Y.Opens, IsAffineOpen U → IsProjectiveOver (k := Γ(Y, U)) (π ∣_ U ≫ U.toSpecΓ)) :
    IsFinite π.fromNormalization :=
  isFinite_fromNormalization π fun U hU =>
    finite_sections_preimage_of_isProjectiveOver V π pY hU (hπ U hU)

end Relative

end

end DeJongAlterations.StableModification.Cohomology
