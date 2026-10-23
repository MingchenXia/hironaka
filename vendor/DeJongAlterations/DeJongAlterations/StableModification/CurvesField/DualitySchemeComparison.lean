/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.CurvesField.DualityCurve
import DeJongAlterations.StableModification.CurvesField.CohomologyTwoCover
import DeJongAlterations.StableModification.CurvesField.GenusFormula
import DeJongAlterations.StableModification.Omega.Affine
import DeJongAlterations.StableModification.Cohomology.PullbackQcoh
import DeJongAlterations.StableModification.Cohomology.BaseChange

/-!
# The two-chart complexes compute the cohomology of `𝒪_X` and `Ω¹_{X/R}`

Let `f : X → Spec R` and let `U₀`, `U₁` be affine opens covering `X` with affine intersection.
This file identifies `H⁰` and `H¹` of `𝒪_X` and of the sheaf of relative differentials
`Ω¹_{X/R}` (lane OM1, `Omega.relativeDifferentials`) with the kernel and the cokernel of the
two-chart complexes `A × B → W` and `Ω_{A/R} × Ω_{B/R} → Ω_{W/R}` (`A = Γ(X, U₀)`,
`B = Γ(X, U₁)`, `W = Γ(X, U₀ ∩ U₁)`) of lane OM2 (`Duality.resO`, `Duality.resΩ`), so that the
numerical Serre duality of `DualityCurve` applies to the cohomology of a curve.

## Main results

* `isQuasicoherent_relativeDifferentials`: `Ω¹_{X/S}` is quasi-coherent for every `f : X → S`
  (on affine opens it is `(Ω_{A/R})^~`, `Omega.restrictIso`).
* `kaehlerBaseEquiv`: `Ω_{A/R} ≅ Ω_{A/R'}` when `R → R'` is surjective (used for
  `R ≅ Γ(Spec R, ⊤)`).
* `sectionsKaehlerEquiv`: `Γ(U, Ω¹_{X/R}) ≅ Ω_{Γ(X, U)/R}` for affine `U`, `R`-linearly,
  compatibly with restriction (`sectionsKaehlerEquiv_restrict`).
* `cohomologyZeroEquivKaehler`, `cohomologyOneEquivKaehler`, `cohomologyZeroEquivStructure`,
  `cohomologyOneEquivStructure`, `isZero_cohomology_kaehler`: the comparison of `H⁰`, `H¹` with
  the two-chart complexes, and `Hᵖ(X, Ω¹_{X/R}) = 0` for `p ≥ 2`.

The `R`-algebra structures on the rings of sections are instance arguments together with
equations identifying them with the structure maps (`sectionsRingHom`, restriction), so that the
consumer can use any convenient instances (e.g. `RingHom.toAlgebra`).

Reference: M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19 (2010),
`references/temkin10-stable-modification/source/semi-stable.tex`, Thm 1.1, lines 1717–1741 (the
degree of `ω` on the components). Blueprint: `sm-omega-degree-scheme.tex`,
`lem:sm-omega-qcoh`, `lem:sm-kaehler-base-surjective`, `lem:sm-omega-chart-comparison-scheme`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.StableModification.Cohomology DeJongAlterations.StableModification.Omega

namespace DeJongAlterations.StableModification.CurvesField.DualityScheme

noncomputable section

/-! ### Quasi-coherence of `Ω¹_{X/S}` -/

section Qcoh

variable {X S : Scheme.{u}} (f : X ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- A presentation of the restriction of `Ω¹_{X/S}` to an affine open `W ⊆ f⁻¹ V`, `V` affine:
it is `(Ω_{A/R})^~` (`Omega.restrictIso`) and modules `M^~` have presentations. -/
def presentationRestrict {W : X.Opens} (hW : IsAffineOpen W) {V : S.Opens} (hV : IsAffineOpen V)
    (hWV : W ≤ f ⁻¹ᵁ V) : ((relativeDifferentials f).restrict W.ι).Presentation :=
  let P : (affineTilde f hWV).Presentation :=
    presentationTilde.{u} _ .univ (by simp) _ (Submodule.span_eq _)
  let P' : ((relativeDifferentials f).restrict hW.fromSpec).Presentation :=
    P.ofIsIso (restrictIso f hW hV hWV).inv
  (Scheme.Modules.presentationRestrict hW.isoSpec.hom P').ofIsIso
    (((Scheme.Modules.restrictFunctorComp hW.isoSpec.hom hW.fromSpec).app _).inv ≫
      ((Scheme.Modules.restrictFunctorCongr hW.isoSpec_hom_fromSpec).app _).hom)

/-- **`Ω¹_{X/S}` is quasi-coherent** (blueprint `lem:sm-omega-qcoh`). -/
theorem isQuasicoherent_relativeDifferentials : (relativeDifferentials f).IsQuasicoherent := by
  let ι := {p : X.affineOpens × S.affineOpens // (p.1 : X.Opens) ≤ f ⁻¹ᵁ (p.2 : S.Opens)}
  refine isQuasicoherent_of_presentation_restrict _ (fun i : ι => (i.1.1 : X.Opens)) ?_
    (fun i => presentationRestrict f i.1.1.2 i.1.2.2 i.2)
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hfxV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (f ⁻¹ᵁ V : X.Opens)
      from hfxV) (f ⁻¹ᵁ V).isOpen
  exact Opens.mem_iSup.mpr ⟨⟨(⟨W, hW⟩, ⟨V, hV⟩), hWV⟩, hxW⟩

instance (f : X ⟶ S) : (relativeDifferentials f).IsQuasicoherent :=
  isQuasicoherent_relativeDifferentials f

end Qcoh

/-! ### Changing the base ring of a Kähler module along a surjection -/

section BaseChange

variable (R R' A : Type*) [CommRing R] [CommRing R'] [CommRing A] [Algebra R R'] [Algebra R' A]
  [Algebra R A] [IsScalarTower R R' A]

/-- For `R → R'` surjective, `d : A → Ω_{A/R}` is an `R'`-derivation. -/
def baseDerivation (h : Function.Surjective (algebraMap R R')) : Derivation R' A Ω[A⁄R] where
  toFun := KaehlerDifferential.D R A
  map_add' := map_add _
  map_smul' r' a := by
    obtain ⟨r, rfl⟩ := h r'
    rw [RingHom.id_apply, algebraMap_smul (A := R') r a, (KaehlerDifferential.D R A).map_smul,
      algebraMap_smul (A := R') r]
  map_one_eq_zero' := (KaehlerDifferential.D R A).map_one_eq_zero
  leibniz' a b := (KaehlerDifferential.D R A).leibniz a b

/-- **Base change of Kähler modules along a surjection** (blueprint
`lem:sm-kaehler-base-surjective`): for `R → R' → A` with `R → R'` surjective,
`Ω_{A/R} ≅ Ω_{A/R'}`, `da ↦ da`. -/
def kaehlerBaseEquiv (h : Function.Surjective (algebraMap R R')) : Ω[A⁄R] ≃ₗ[A] Ω[A⁄R'] :=
  LinearEquiv.ofLinearMap (KaehlerDifferential.map R R' A A)
    (baseDerivation R R' A h).liftKaehlerDifferential
    (by
      ext a
      simp [baseDerivation])
    (by
      ext a
      simp [baseDerivation])

@[simp]
lemma kaehlerBaseEquiv_D (h : Function.Surjective (algebraMap R R')) (a : A) :
    kaehlerBaseEquiv R R' A h (KaehlerDifferential.D R A a) = KaehlerDifferential.D R' A a :=
  KaehlerDifferential.map_D R R' A A a

@[simp]
lemma kaehlerBaseEquiv_symm_D (h : Function.Surjective (algebraMap R R')) (a : A) :
    (kaehlerBaseEquiv R R' A h).symm (KaehlerDifferential.D R' A a) =
      KaehlerDifferential.D R A a := by
  rw [LinearEquiv.symm_apply_eq, kaehlerBaseEquiv_D]

end BaseChange

/-! ### Sections of `Ω¹_{X/R}` over affine opens as Kähler modules over `R` -/

section Sections

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))

/-- The ring `Γ(Spec R, ⊤)` as an `R`-algebra through `Γ(Spec R, ⊤) ≅ R`. -/
abbrev specTopAlgebra : Algebra R Γ(Spec (CommRingCat.of R), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.toAlgebra

lemma specTop_surjective :
    Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
  (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2

lemma le_preimage_top (W : X.Opens) : W ≤ f ⁻¹ᵁ ⊤ := fun _ _ => trivial

/-- The ring map `R → Γ(X, W)` of the structure morphism is `appLE` after `R ≅ Γ(Spec R, ⊤)`. -/
lemma sectionsRingHom_structureCoeff (W : X.Opens) :
    sectionsRingHom (structureCoeff f) (le_top : W ≤ ⊤) =
      (f.appLE ⊤ W (le_preimage_top f W)).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
  ext r
  simp only [sectionsRingHom, structureCoeff, RingHom.coe_comp, Function.comp_apply,
    Scheme.Hom.appLE]
  rfl

variable {W : X.Opens} (hW : IsAffineOpen W) [Algebra R Γ(X, W)]
  (hA : algebraMap R Γ(X, W) = sectionsRingHom (structureCoeff f) (le_top : W ≤ ⊤))

include hA in
lemma isScalarTower_specTop :
    letI := specTopAlgebra (R := R)
    letI := (f.appLE ⊤ W (le_preimage_top f W)).hom.toAlgebra
    IsScalarTower R Γ(Spec (CommRingCat.of R), ⊤) Γ(X, W) := by
  let := specTopAlgebra (R := R)
  let := (f.appLE ⊤ W (le_preimage_top f W)).hom.toAlgebra
  refine IsScalarTower.of_algebraMap_eq fun r => ?_
  rw [hA, sectionsRingHom_structureCoeff]
  rfl

/-- The `Γ(X, W)`-linear identification `Γ(W, Ω¹_{X/R}) ≅ Ω_{Γ(X, W)/R}` for affine `W`
(Omega's `sectionsEquiv` and `kaehlerBaseEquiv`). -/
def sectionsKaehlerEquivAux : Γ(relativeDifferentials f, W) ≃ₗ[Γ(X, W)] Ω[Γ(X, W)⁄R] :=
  letI := specTopAlgebra (R := R)
  letI := (f.appLE ⊤ W (le_preimage_top f W)).hom.toAlgebra
  haveI := isScalarTower_specTop f hA
  (sectionsEquiv f hW (isAffineOpen_top _) (le_preimage_top f W)).symm.trans
    (kaehlerBaseEquiv R Γ(Spec (CommRingCat.of R), ⊤) Γ(X, W) specTop_surjective).symm

include hA in
lemma sectionsKaehlerEquivAux_d (a : Γ(X, W)) :
    sectionsKaehlerEquivAux f hW hA ((universalDerivation f).d a) = KaehlerDifferential.D R _ a := by
  let := specTopAlgebra (R := R)
  let := (f.appLE ⊤ W (le_preimage_top f W)).hom.toAlgebra
  have := isScalarTower_specTop f hA
  change (kaehlerBaseEquiv R Γ(Spec (CommRingCat.of R), ⊤) Γ(X, W) specTop_surjective).symm
    ((sectionsEquiv f hW (isAffineOpen_top _) (le_preimage_top f W)).symm
      ((universalDerivation f).d a)) = _
  rw [← sectionsEquiv_d f hW (isAffineOpen_top _) (le_preimage_top f W) a,
    LinearEquiv.symm_apply_apply]
  exact kaehlerBaseEquiv_symm_D R Γ(Spec (CommRingCat.of R), ⊤) Γ(X, W) specTop_surjective a

/-- **Sections of `Ω¹_{X/R}` over an affine open** (blueprint
`lem:sm-omega-chart-comparison-scheme`): `Γ(W, Ω¹_{X/R}) ≅ Ω_{Γ(X, W)/R}` as `R`-modules, the
`R`-module structure on the left being that of `sectionsModuleCat` for the structure
coefficients `structureCoeff f`. -/
def sectionsKaehlerEquiv :
    sectionsModuleCat (relativeDifferentials f) (structureCoeff f) W le_top ≃ₗ[R]
      Ω[Γ(X, W)⁄R] where
  toFun m := sectionsKaehlerEquivAux f hW hA m
  invFun x := (sectionsKaehlerEquivAux f hW hA).symm x
  map_add' m n := map_add (sectionsKaehlerEquivAux f hW hA) m n
  map_smul' r m := by
    rw [sectionsModuleCat_smul_def, RingHom.id_apply, ← algebraMap_smul (A := Γ(X, W)) r, hA]
    exact (sectionsKaehlerEquivAux f hW hA).map_smul _ _
  left_inv m := (sectionsKaehlerEquivAux f hW hA).symm_apply_apply m
  right_inv x := (sectionsKaehlerEquivAux f hW hA).apply_symm_apply x

lemma sectionsKaehlerEquiv_apply (m) :
    sectionsKaehlerEquiv f hW hA m = sectionsKaehlerEquivAux f hW hA m := rfl

lemma sectionsKaehlerEquiv_d (a : Γ(X, W)) :
    sectionsKaehlerEquiv f hW hA ((universalDerivation f).d a) = KaehlerDifferential.D R _ a :=
  sectionsKaehlerEquivAux_d f hW hA a

variable {W' : X.Opens} (hW' : IsAffineOpen W') (hle : W' ≤ W) [Algebra R Γ(X, W')]
  (hA' : algebraMap R Γ(X, W') = sectionsRingHom (structureCoeff f) (le_top : W' ≤ ⊤))
  [Algebra Γ(X, W) Γ(X, W')] [IsScalarTower R Γ(X, W) Γ(X, W')]
  (hres : algebraMap Γ(X, W) Γ(X, W') = (X.presheaf.map (homOfLE hle).op).hom)

include hres in
/-- The identification `sectionsKaehlerEquivAux` is compatible with restriction. -/
lemma sectionsKaehlerEquivAux_restrict (m : Γ(relativeDifferentials f, W)) :
    sectionsKaehlerEquivAux f hW' hA' ((relativeDifferentials f).presheaf.map (homOfLE hle).op m) =
      KaehlerDifferential.map R R Γ(X, W) Γ(X, W') (sectionsKaehlerEquivAux f hW hA m) := by
  obtain ⟨x, rfl⟩ := (sectionsKaehlerEquivAux f hW hA).symm.surjective m
  rw [LinearEquiv.apply_symm_apply]
  have hx : x ∈ Submodule.span Γ(X, W) (Set.range (KaehlerDifferential.D R Γ(X, W))) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    have h1 : (sectionsKaehlerEquivAux f hW hA).symm (KaehlerDifferential.D R _ a) =
        (universalDerivation f).d a :=
      (sectionsKaehlerEquivAux f hW hA).symm_apply_eq.mpr (sectionsKaehlerEquivAux_d f hW hA a).symm
    rw [h1, ← RelDerivation.d_map, sectionsKaehlerEquivAux_d, KaehlerDifferential.map_D, hres]
  | zero => simp
  | add y z _ _ hy hz => rw [map_add, map_add, map_add, hy, hz, map_add]
  | smul a y _ hy =>
    rw [LinearEquiv.map_smul, Scheme.Modules.map_smul, LinearEquiv.map_smul, hy,
      LinearMap.map_smul]
    change (X.presheaf.map (homOfLE hle).op).hom a • _ = _
    rw [← hres, algebraMap_smul]

include hres in
/-- The identification of `sectionsKaehlerEquiv` is compatible with restriction. -/
lemma sectionsKaehlerEquiv_restrict (m) :
    sectionsKaehlerEquiv f hW' hA'
        (sectionsRestrict (relativeDifferentials f) (structureCoeff f) le_top le_top hle m) =
      KaehlerDifferential.map R R Γ(X, W) Γ(X, W') (sectionsKaehlerEquiv f hW hA m) :=
  sectionsKaehlerEquivAux_restrict f hW hA hW' hle hA' hres m

end Sections

/-! ### The two-chart complexes compute the cohomology -/

section Cohomology

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The difference map of a pair of opens is the untwisted two-term differential of the
restriction maps. -/
lemma pairDiff_eq_twistDiff (U₀ U₁ : X.Opens) (F : X.Modules) (c : R →+* Γ(X, ⊤)) :
    pairDiff U₀ U₁ F c = twistDiff (sectionsRestrict F c le_top le_top inf_le_left).hom
      (sectionsRestrict F c le_top le_top inf_le_right).hom LinearMap.id :=
  LinearMap.ext fun _ => rfl

/-- The sections of the structure sheaf as an `R`-module: the ring of sections with its
`R`-algebra structure. -/
def sectionsUnitEquiv (c : R →+* Γ(X, ⊤)) (U : X.Opens) [Algebra R Γ(X, U)]
    (hA : algebraMap R Γ(X, U) = sectionsRingHom c (le_top : U ≤ ⊤)) :
    sectionsModuleCat (SheafOfModules.unit X.ringCatSheaf) c U le_top ≃ₗ[R] Γ(X, U) where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' r x := by
    rw [RingHom.id_apply]
    refine Eq.trans ?_ (Algebra.smul_def r (show Γ(X, U) from x)).symm
    rw [hA]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable {k : Type u} [Field k] (f : X ⟶ Spec (CommRingCat.of k))
  [CompactSpace X] [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))]
  {U₀ U₁ : X.Opens} (h : U₀ ⊔ U₁ = ⊤) (h₀ : IsAffineOpen U₀) (h₁ : IsAffineOpen U₁)
  (h₀₁ : IsAffineOpen (U₀ ⊓ U₁))
  [Algebra k Γ(X, U₀)] [Algebra k Γ(X, U₁)] [Algebra k Γ(X, U₀ ⊓ U₁)]
  (hA₀ : algebraMap k Γ(X, U₀) = sectionsRingHom (structureCoeff f) (le_top : U₀ ≤ ⊤))
  (hA₁ : algebraMap k Γ(X, U₁) = sectionsRingHom (structureCoeff f) (le_top : U₁ ≤ ⊤))
  (hA₀₁ : algebraMap k Γ(X, U₀ ⊓ U₁) =
    sectionsRingHom (structureCoeff f) (le_top : U₀ ⊓ U₁ ≤ ⊤))
  [Algebra Γ(X, U₀) Γ(X, U₀ ⊓ U₁)] [Algebra Γ(X, U₁) Γ(X, U₀ ⊓ U₁)]
  [IsScalarTower k Γ(X, U₀) Γ(X, U₀ ⊓ U₁)] [IsScalarTower k Γ(X, U₁) Γ(X, U₀ ⊓ U₁)]
  (hr₀ : algebraMap Γ(X, U₀) Γ(X, U₀ ⊓ U₁) =
    (X.presheaf.map (homOfLE (inf_le_left : U₀ ⊓ U₁ ≤ U₀)).op).hom)
  (hr₁ : algebraMap Γ(X, U₁) Γ(X, U₀ ⊓ U₁) =
    (X.presheaf.map (homOfLE (inf_le_right : U₀ ⊓ U₁ ≤ U₁)).op).hom)

/-- **`H⁰(X, Ω¹_{X/R})` from two charts** (blueprint `lem:sm-omega-chart-comparison-scheme`):
the kernel of `Ω_{A/R} × Ω_{B/R} → Ω_{W/R}`. -/
def cohomologyZeroEquivKaehler :
    cohomology (relativeDifferentials f) (structureCoeff f) 0 ≃ₗ[k]
      H0 (Duality.resΩ k Γ(X, U₀) Γ(X, U₀ ⊓ U₁)) (Duality.resΩ k Γ(X, U₁) Γ(X, U₀ ⊓ U₁))
        LinearMap.id :=
  (cohomologyPairZeroEquiv (relativeDifferentials f) (structureCoeff f) h h₀ h₁ h₀₁).trans
    ((LinearEquiv.ofEq _ _ (congrArg LinearMap.ker (pairDiff_eq_twistDiff _ _ _ _))).trans
      (H0Congr (sectionsKaehlerEquiv f h₀ hA₀) (sectionsKaehlerEquiv f h₁ hA₁)
        (sectionsKaehlerEquiv f h₀₁ hA₀₁)
        (fun a => sectionsKaehlerEquiv_restrict f h₀ hA₀ h₀₁ inf_le_left hA₀₁ hr₀ a)
        (fun b => sectionsKaehlerEquiv_restrict f h₁ hA₁ h₀₁ inf_le_right hA₀₁ hr₁ b)
        (fun _ => rfl)))

/-- **`H¹(X, Ω¹_{X/R})` from two charts** (blueprint `lem:sm-omega-chart-comparison-scheme`):
the cokernel of `Ω_{A/R} × Ω_{B/R} → Ω_{W/R}`. -/
def cohomologyOneEquivKaehler :
    cohomology (relativeDifferentials f) (structureCoeff f) 1 ≃ₗ[k]
      H1 (Duality.resΩ k Γ(X, U₀) Γ(X, U₀ ⊓ U₁)) (Duality.resΩ k Γ(X, U₁) Γ(X, U₀ ⊓ U₁))
        LinearMap.id :=
  (cohomologyPairOneEquiv (relativeDifferentials f) (structureCoeff f) h h₀ h₁ h₀₁).trans
    ((Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range (pairDiff_eq_twistDiff _ _ _ _))).trans
      (H1Congr (sectionsKaehlerEquiv f h₀ hA₀) (sectionsKaehlerEquiv f h₁ hA₁)
        (sectionsKaehlerEquiv f h₀₁ hA₀₁)
        (fun a => sectionsKaehlerEquiv_restrict f h₀ hA₀ h₀₁ inf_le_left hA₀₁ hr₀ a)
        (fun b => sectionsKaehlerEquiv_restrict f h₁ hA₁ h₀₁ inf_le_right hA₀₁ hr₁ b)
        (fun _ => rfl)))

omit [Algebra k Γ(X, U₀)] [Algebra k Γ(X, U₁)] [Algebra k Γ(X, U₀ ⊓ U₁)]
  [Algebra Γ(X, U₀) Γ(X, U₀ ⊓ U₁)] [Algebra Γ(X, U₁) Γ(X, U₀ ⊓ U₁)]
  [IsScalarTower k Γ(X, U₀) Γ(X, U₀ ⊓ U₁)] [IsScalarTower k Γ(X, U₁) Γ(X, U₀ ⊓ U₁)] in
include h h₀ h₁ h₀₁ in
/-- `Hᵖ(X, Ω¹_{X/R}) = 0` for `p ≥ 2` on a scheme covered by two affine opens with affine
intersection. -/
theorem isZero_cohomology_kaehler (p : ℕ) (hp : 2 ≤ p) :
    Limits.IsZero (cohomology (relativeDifferentials f) (structureCoeff f) p) :=
  isZero_cohomology_pair _ _ h h₀ h₁ h₀₁ p hp

/-- **`H⁰(X, 𝒪_X)` from two charts**: the kernel of `A × B → W`. -/
def cohomologyZeroEquivStructure :
    cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 0 ≃ₗ[k]
      H0 (Duality.resO k Γ(X, U₀) Γ(X, U₀ ⊓ U₁)) (Duality.resO k Γ(X, U₁) Γ(X, U₀ ⊓ U₁))
        LinearMap.id :=
  (cohomologyPairZeroEquiv (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) h h₀ h₁
    h₀₁).trans
    ((LinearEquiv.ofEq _ _ (congrArg LinearMap.ker (pairDiff_eq_twistDiff _ _ _ _))).trans
      (H0Congr (sectionsUnitEquiv _ U₀ hA₀) (sectionsUnitEquiv _ U₁ hA₁)
        (sectionsUnitEquiv _ (U₀ ⊓ U₁) hA₀₁)
        (fun a => by
          change _ = algebraMap Γ(X, U₀) Γ(X, U₀ ⊓ U₁) a
          rw [hr₀]
          rfl)
        (fun b => by
          change _ = algebraMap Γ(X, U₁) Γ(X, U₀ ⊓ U₁) b
          rw [hr₁]
          rfl)
        (fun _ => rfl)))

/-- **`H¹(X, 𝒪_X)` from two charts**: the cokernel of `A × B → W`. -/
def cohomologyOneEquivStructure :
    cohomology (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) 1 ≃ₗ[k]
      H1 (Duality.resO k Γ(X, U₀) Γ(X, U₀ ⊓ U₁)) (Duality.resO k Γ(X, U₁) Γ(X, U₀ ⊓ U₁))
        LinearMap.id :=
  (cohomologyPairOneEquiv (SheafOfModules.unit X.ringCatSheaf) (structureCoeff f) h h₀ h₁
    h₀₁).trans
    ((Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range (pairDiff_eq_twistDiff _ _ _ _))).trans
      (H1Congr (sectionsUnitEquiv _ U₀ hA₀) (sectionsUnitEquiv _ U₁ hA₁)
        (sectionsUnitEquiv _ (U₀ ⊓ U₁) hA₀₁)
        (fun a => by
          change _ = algebraMap Γ(X, U₀) Γ(X, U₀ ⊓ U₁) a
          rw [hr₀]
          rfl)
        (fun b => by
          change _ = algebraMap Γ(X, U₁) Γ(X, U₀ ⊓ U₁) b
          rw [hr₁]
          rfl)
        (fun _ => rfl)))

end Cohomology

end

end DeJongAlterations.StableModification.CurvesField.DualityScheme
