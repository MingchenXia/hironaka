/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.Geometry.ProperSteinProjectiveCechSubset
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Čech complexes of sheaves of modules for finite families of opens

This file starts the Čech cohomology library of the Claude team's route to Temkin's stable
modification theorem (M. Temkin, *Stable modification of relative curves*, J. Algebraic Geom. 19
(2010)). Temkin uses coherent cohomology of curves over a base (Lemma 4.4.2: constancy of the
Euler characteristic and of the arithmetic genus, via EGA III 7.9.4; Proposition 4.4.6:
semicontinuity and base change; Lemma B.1: the long exact sequence of a normalization). Following
plan decision D4 (curves-only Čech library, `.archon-horizon/scratch/dja/PLAN-SM-GEOM.md`,
chapter F), cohomology is *defined* as the cohomology of the alternating Čech complex of a finite
affine cover; the comparison theorems are proved directly. Blueprint: `sm-cohomology-cech.tex`
(`def:sm-cech`, `lem:sm-cech-basic`).

## Conventions

* `X : Scheme.{u}`, `F : X.Modules`, and a ring `R : Type u` with `c : R →+* Γ(X, ⊤)` giving the
  coefficients: every section module `Γ(F, V)` is an `R`-module through
  `R → Γ(X, ⊤) → Γ(X, V)` (`sectionsModuleCat`). Take `c = RingHom.id _` for `Γ(X, ⊤)`-modules,
  or `c` the structure map of `X → Spec A` for `A`-modules.
* A family of opens is `U : ι → X.Opens` with `ι : Type u` linearly ordered; for a finite subset
  `T : Finset ι` the intersection is `T.inf U` (so the empty intersection is `⊤`).
* The Čech complex is Codex's alternating subset complex
  `ProperSteinProjectiveCech.subsetCechComplex` of the diagram `T ↦ Γ(F, T.inf U)` on finite
  subsets: degree `p` consists of the families `(c_T)` indexed by the subsets `T` of cardinality
  `p + 1` (stored as functions on all finite subsets vanishing off cardinality `p + 1`), with
  differential `(dc)_T = ∑_{i ∈ T} (-1)^{#{j ∈ T | j < i}} c_{T ∖ i}|_{U_T}`. This keeps the
  complexes compatible with Codex's projective Čech complexes (`ProperSteinProjectiveCech*`).

## Main definitions

* `sectionsModuleCat F c V hV`, `sectionsRestrict`, `sectionsMap`: sections as `R`-modules.
* `sectionsDiagram F c W hW hW₀`: the diagram `T ↦ Γ(F, W T)` of an antitone family of opens.
* `cechDiagram F U c`, `cechComplex F U c`, `cechCohomology F U c p`: the Čech diagram, complex
  and cohomology `Ȟ^p(U, F)` as `R`-modules.
* `cechComplexMap c U φ` (functoriality in `F`, packaged as `cechComplexFunctor U c`).
* `subsetCechComplexMapOfCube`: a cochain map from a linear map of total cubes that preserves
  cardinality and commutes with the differentials.
* `cechRestrict F W e c`: the restriction `Č(W, F) ⟶ Č(W ∘ e, F)` to a subfamily along an order
  embedding `e : ι ↪o κ` (used for refinements and the independence of the cover).

## Main results

* `cechCohomologyZeroIso`: for a covering family, `Ȟ⁰(U, F) ≅ Γ(X, F)` (sheaf axiom).
* `isZero_cechCohomology_of_card_le`: `Ȟ^p(U, F) = 0` for `p ≥ #ι`.
* `cechRestrict_comp`, `cechRestrict_naturality`, `isIso_cechRestrict_of_surjective`.

## API for the later cohomology lanes

The companion files (umbrella `StableModification.Cohomology.Cech`) give: `CechAcyclic`
(exactness of the Čech complex of a quasi-coherent module on an affine scheme), `CechRefinement`
(restriction to a covering subfamily is a quasi-isomorphism; independence of the cover),
`CechLongExact` (short exact sequences of quasi-coherent modules give long exact sequences of `Ȟ`),
`CechCover` (finite affine covers and the cover-free `H^p(X, F)`), `CechPushforward` (pushforward
along affine morphisms). Later lanes should state finiteness, Euler characteristics and base change
for `cohomology F c p` (or `cechCohomology F U c p` for a finite affine cover `U` with affine
intersections) and move between covers with `cohomologyIsoCech` / `cechCohomologyIsoOfCovers`.
-/

universe u

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.Geometry.ProperSteinProjectiveCech

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

section Sections

variable (F : X.Modules) {V₀ : X.Opens} (c : R →+* Γ(X, V₀))

/-- The ring map `R → Γ(X, V)` obtained from `c : R →+* Γ(X, V₀)` and restriction, `V ≤ V₀`. -/
def sectionsRingHom {V : X.Opens} (hV : V ≤ V₀) : R →+* Γ(X, V) :=
  (X.presheaf.map (homOfLE hV).op).hom.comp c

/-- The sections `Γ(F, V)` over an open `V ≤ V₀`, as an `R`-module through `sectionsRingHom`. -/
def sectionsModuleCat (V : X.Opens) (hV : V ≤ V₀) : ModuleCat.{u} R :=
  letI := Module.compHom Γ(F, V) (sectionsRingHom c hV)
  ModuleCat.of R Γ(F, V)

lemma sectionsModuleCat_smul_def {V : X.Opens} (hV : V ≤ V₀) (r : R)
    (s : sectionsModuleCat F c V hV) :
    r • s = (show Γ(F, V) from sectionsRingHom c hV r • (show Γ(F, V) from s)) :=
  rfl

/-- Restriction of sections along `W ≤ V`, as an `R`-linear map. -/
def sectionsRestrict {V W : X.Opens} (hV : V ≤ V₀) (hW : W ≤ V₀) (hWV : W ≤ V) :
    sectionsModuleCat F c V hV ⟶ sectionsModuleCat F c W hW :=
  letI := Module.compHom Γ(F, V) (sectionsRingHom c hV)
  letI := Module.compHom Γ(F, W) (sectionsRingHom c hW)
  ModuleCat.ofHom
  { toFun := F.presheaf.map (homOfLE hWV).op
    map_add' := map_add _
    map_smul' := by
      intro r s
      change F.presheaf.map (homOfLE hWV).op (sectionsRingHom c hV r • s) =
        sectionsRingHom c hW r • F.presheaf.map (homOfLE hWV).op s
      rw [Scheme.Modules.map_smul]
      congr 1
      simp only [sectionsRingHom, RingHom.coe_comp, Function.comp_apply]
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl }

@[simp]
lemma sectionsRestrict_apply {V W : X.Opens} (hV : V ≤ V₀) (hW : W ≤ V₀) (hWV : W ≤ V)
    (s : sectionsModuleCat F c V hV) :
    sectionsRestrict F c hV hW hWV s = F.presheaf.map (homOfLE hWV).op s :=
  rfl

@[simp]
lemma sectionsRestrict_id {V : X.Opens} (hV : V ≤ V₀) :
    sectionsRestrict F c hV hV le_rfl = 𝟙 _ := by
  ext s
  change F.presheaf.map (homOfLE le_rfl).op s = s
  rw [show (homOfLE (le_refl V)) = 𝟙 V from rfl, op_id, F.presheaf.map_id]
  rfl

@[reassoc (attr := simp)]
lemma sectionsRestrict_comp {V W W' : X.Opens} (hV : V ≤ V₀) (hW : W ≤ V₀) (hW' : W' ≤ V₀)
    (hWV : W ≤ V) (hW'W : W' ≤ W) :
    sectionsRestrict F c hV hW hWV ≫ sectionsRestrict F c hW hW' hW'W =
      sectionsRestrict F c hV hW' (hW'W.trans hWV) := by
  ext s
  change (F.presheaf.map (homOfLE hWV).op ≫ F.presheaf.map (homOfLE hW'W).op)
      (show Γ(F, V) from s) = F.presheaf.map (homOfLE (hW'W.trans hWV)).op (show Γ(F, V) from s)
  rw [← Functor.map_comp]
  rfl

lemma sectionsRestrict_restrict {V W W' : X.Opens} (hV : V ≤ V₀) (hW : W ≤ V₀)
    (hW' : W' ≤ V₀) (hWV : W ≤ V) (hW'W : W' ≤ W) (s : sectionsModuleCat F c V hV) :
    sectionsRestrict F c hW hW' hW'W (sectionsRestrict F c hV hW hWV s) =
      sectionsRestrict F c hV hW' (hW'W.trans hWV) s := by
  rw [← sectionsRestrict_comp F c hV hW hW' hWV hW'W]
  rfl

/-- Restriction along an equality of opens is bijective. -/
lemma sectionsRestrict_bijective_of_eq {V W : X.Opens} (hV : V ≤ V₀) (hW : W ≤ V₀)
    (hWV : W = V) :
    Function.Bijective (sectionsRestrict F c hV hW hWV.le) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨sectionsRestrict F c hW hV hWV.ge, fun s => ?_, fun s => ?_⟩
  · have h := sectionsRestrict_comp F c hV hW hV hWV.le hWV.ge
    rw [sectionsRestrict_id] at h
    exact ConcreteCategory.congr_hom h s
  · have h := sectionsRestrict_comp F c hW hV hW hWV.ge hWV.le
    rw [sectionsRestrict_id] at h
    exact ConcreteCategory.congr_hom h s

/-- Restriction of a family of sections indexed by finite subsets is compatible with equality of
the indices. -/
lemma sectionsRestrict_congr_index {μ : Type u} {A : Finset μ → X.Opens} (hA : ∀ S, A S ≤ V₀)
    (x : ∀ S, sectionsModuleCat F c (A S) (hA S)) {S S' : Finset μ} (h : S = S') {V : X.Opens}
    (hV : V ≤ V₀) (hS : V ≤ A S) (hS' : V ≤ A S') :
    sectionsRestrict F c (hA S) hV hS (x S) = sectionsRestrict F c (hA S') hV hS' (x S') := by
  subst h
  rfl

/-- Restriction of sections between two coefficient rings, as an additive map. -/
def sectionsRestrictAdd {A : Type u} [CommRing A] {V₁ : X.Opens} (c₁ : A →+* Γ(X, V₁))
    {V W : X.Opens} (hV : V ≤ V₀) (hW : W ≤ V₁) (hWV : W ≤ V) :
    sectionsModuleCat F c V hV →+ sectionsModuleCat F c₁ W hW :=
  (F.presheaf.map (homOfLE hWV).op).hom

lemma sectionsRestrictAdd_apply {A : Type u} [CommRing A] {V₁ : X.Opens} (c₁ : A →+* Γ(X, V₁))
    {V W : X.Opens} (hV : V ≤ V₀) (hW : W ≤ V₁) (hWV : W ≤ V) (s : sectionsModuleCat F c V hV) :
    sectionsRestrictAdd F c c₁ hV hW hWV s = F.presheaf.map (homOfLE hWV).op s :=
  rfl

lemma sectionsRestrictAdd_sectionsRestrict {A : Type u} [CommRing A] {V₁ : X.Opens}
    (c₁ : A →+* Γ(X, V₁)) {V V' W : X.Opens} (hV : V ≤ V₀) (hV' : V' ≤ V₀) (hW : W ≤ V₁)
    (hV'V : V' ≤ V) (hWV' : W ≤ V') (s : sectionsModuleCat F c V hV) :
    sectionsRestrictAdd F c c₁ hV' hW hWV' (sectionsRestrict F c hV hV' hV'V s) =
      sectionsRestrictAdd F c c₁ hV hW (hWV'.trans hV'V) s := by
  change F.presheaf.map _ (F.presheaf.map _ (show Γ(F, V) from s)) = F.presheaf.map _ _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma sectionsRestrict_sectionsRestrictAdd {A : Type u} [CommRing A] {V₁ : X.Opens}
    (c₁ : A →+* Γ(X, V₁)) {V W W' : X.Opens} (hV : V ≤ V₀) (hW : W ≤ V₁) (hW' : W' ≤ V₁)
    (hWV : W ≤ V) (hW'W : W' ≤ W) (s : sectionsModuleCat F c V hV) :
    sectionsRestrict F c₁ hW hW' hW'W (sectionsRestrictAdd F c c₁ hV hW hWV s) =
      sectionsRestrictAdd F c c₁ hV hW' (hW'W.trans hWV) s := by
  change F.presheaf.map _ (F.presheaf.map _ (show Γ(F, V) from s)) = F.presheaf.map _ _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma sectionsRestrictAdd_sectionsRestrictAdd {A : Type u} [CommRing A] {V₁ : X.Opens}
    (c₁ : A →+* Γ(X, V₁)) {V W : X.Opens} (hV : V ≤ V₀) (hW : W ≤ V₁) (hWV : W = V)
    (s : sectionsModuleCat F c V hV) :
    sectionsRestrictAdd F c₁ c hW hV hWV.ge (sectionsRestrictAdd F c c₁ hV hW hWV.le s) = s := by
  change F.presheaf.map _ (F.presheaf.map _ (show Γ(F, V) from s)) = s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  change F.presheaf.map (𝟙 _) _ = _
  rw [F.presheaf.map_id]
  rfl

lemma sectionsRestrictAdd_congr_index {A : Type u} [CommRing A] {V₁ : X.Opens}
    (c₁ : A →+* Γ(X, V₁)) {μ : Type u} {B : Finset μ → X.Opens} (hB : ∀ S, B S ≤ V₀)
    (x : ∀ S, sectionsModuleCat F c (B S) (hB S)) {S S' : Finset μ} (h : S = S') {V : X.Opens}
    (hV : V ≤ V₁) (hS : V ≤ B S) (hS' : V ≤ B S') :
    sectionsRestrictAdd F c c₁ (hB S) hV hS (x S) = sectionsRestrictAdd F c c₁ (hB S') hV hS' (x S') := by
  subst h
  rfl

lemma sectionsRestrictAdd_sectionsRestrictAdd' {A B : Type u} [CommRing A] [CommRing B]
    {V₁ V₂ : X.Opens} (c₁ : A →+* Γ(X, V₁)) (c₂ : B →+* Γ(X, V₂)) {V W W' : X.Opens}
    (hV : V ≤ V₀) (hW : W ≤ V₁) (hW' : W' ≤ V₂) (hWV : W ≤ V) (hW'W : W' ≤ W)
    (s : sectionsModuleCat F c V hV) :
    sectionsRestrictAdd F c₁ c₂ hW hW' hW'W (sectionsRestrictAdd F c c₁ hV hW hWV s) =
      sectionsRestrictAdd F c c₂ hV hW' (hW'W.trans hWV) s := by
  change F.presheaf.map _ (F.presheaf.map _ (show Γ(F, V) from s)) = F.presheaf.map _ _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma sectionsRestrictAdd_self {V : X.Opens} (hV : V ≤ V₀) (h : V ≤ V)
    (s : sectionsModuleCat F c V hV) : sectionsRestrictAdd F c c hV hV h s = s := by
  change F.presheaf.map (𝟙 _) (show Γ(F, V) from s) = s
  rw [F.presheaf.map_id]
  rfl

/-- A morphism of modules on sections, as an `R`-linear map. -/
def sectionsMap {F G : X.Modules} (φ : F ⟶ G) (V : X.Opens) (hV : V ≤ V₀) :
    sectionsModuleCat F c V hV ⟶ sectionsModuleCat G c V hV :=
  letI := Module.compHom Γ(F, V) (sectionsRingHom c hV)
  letI := Module.compHom Γ(G, V) (sectionsRingHom c hV)
  ModuleCat.ofHom
  { toFun := φ.app V
    map_add' := map_add _
    map_smul' := fun r s => Scheme.Modules.Hom.app_smul φ (sectionsRingHom c hV r) s }

@[simp]
lemma sectionsMap_apply {F G : X.Modules} (φ : F ⟶ G) (V : X.Opens) (hV : V ≤ V₀)
    (s : sectionsModuleCat F c V hV) : sectionsMap c φ V hV s = φ.app V s :=
  rfl

@[reassoc]
lemma sectionsMap_restrict {F G : X.Modules} (φ : F ⟶ G) {V W : X.Opens} (hV : V ≤ V₀)
    (hW : W ≤ V₀) (hWV : W ≤ V) :
    sectionsMap c φ V hV ≫ sectionsRestrict G c hV hW hWV =
      sectionsRestrict F c hV hW hWV ≫ sectionsMap c φ W hW := by
  ext s
  exact (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hWV).op) s).symm

@[simp]
lemma sectionsMap_id (V : X.Opens) (hV : V ≤ V₀) : sectionsMap c (𝟙 F) V hV = 𝟙 _ :=
  rfl

@[simp]
lemma sectionsMap_comp {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (V : X.Opens)
    (hV : V ≤ V₀) : sectionsMap c (φ ≫ ψ) V hV = sectionsMap c φ V hV ≫ sectionsMap c ψ V hV :=
  rfl

variable {ι : Type u}

/-- The diagram `T ↦ Γ(F, W T)` of `R`-modules on finite subsets, for an antitone family `W` of
opens below `V₀`, with the restriction maps. -/
abbrev sectionsDiagram (W : Finset ι → X.Opens) (hW : Antitone W) (hW₀ : ∀ T, W T ≤ V₀) :
    Finset ι ⥤ ModuleCat.{u} R where
  obj T := sectionsModuleCat F c (W T) (hW₀ T)
  map {S T} h := sectionsRestrict F c (hW₀ S) (hW₀ T) (hW (leOfHom h))
  map_id T := sectionsRestrict_id F c (hW₀ T)
  map_comp {S T T'} _ _ := (sectionsRestrict_comp F c (hW₀ S) (hW₀ T) (hW₀ T') _ _).symm

lemma sectionsDiagram_map_apply (W : Finset ι → X.Opens) (hW : Antitone W)
    (hW₀ : ∀ T, W T ≤ V₀) {S T : Finset ι} (h : S ⟶ T)
    (s : (sectionsDiagram F c W hW hW₀).obj S) :
    (sectionsDiagram F c W hW hW₀).map h s = F.presheaf.map (homOfLE (hW (leOfHom h))).op s :=
  rfl

/-- A morphism of modules induces a morphism of section diagrams. -/
def sectionsDiagramMap {F G : X.Modules} (φ : F ⟶ G) (W : Finset ι → X.Opens) (hW : Antitone W)
    (hW₀ : ∀ T, W T ≤ V₀) : sectionsDiagram F c W hW hW₀ ⟶ sectionsDiagram G c W hW hW₀ where
  app T := sectionsMap c φ (W T) (hW₀ T)
  naturality {S T} _ := (sectionsMap_restrict c φ (hW₀ S) (hW₀ T) _).symm

end Sections

section CubeMap

variable {ι κ : Type u} [LinearOrder ι] [LinearOrder κ]
  {D : Finset ι ⥤ ModuleCat.{u} R} {D' : Finset κ ⥤ ModuleCat.{u} R}

/-- A linear map of total Čech cubes which preserves the cardinality pieces and commutes with the
alternating differentials induces a map of Čech complexes. -/
def subsetCechComplexMapOfCube (Φ : subsetCechCube D →ₗ[R] subsetCechCube D')
    (hΦ : ∀ n, ∀ x ∈ subsetCechCardPiece D n, Φ x ∈ subsetCechCardPiece D' n)
    (hd : ∀ x, Φ (subsetCechDifferential D x) = subsetCechDifferential D' (Φ x)) :
    subsetCechComplex D ⟶ subsetCechComplex D' :=
  CochainComplex.ofHom
    (fun p => ModuleCat.ofHom (Φ.restrict (hΦ (p + 1)))) (by
      intro p
      simp only [subsetCechComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      exact (hd x.val).symm)

@[simp]
lemma subsetCechComplexMapOfCube_f_apply (Φ : subsetCechCube D →ₗ[R] subsetCechCube D')
    (hΦ : ∀ n, ∀ x ∈ subsetCechCardPiece D n, Φ x ∈ subsetCechCardPiece D' n)
    (hd : ∀ x, Φ (subsetCechDifferential D x) = subsetCechDifferential D' (Φ x)) (p : ℕ)
    (x : subsetCechCardPiece D (p + 1)) :
    ((subsetCechComplexMapOfCube Φ hΦ hd).f p x).val = Φ x.val :=
  rfl

end CubeMap

section Cech

variable (F : X.Modules) {ι : Type u} [LinearOrder ι] (U : ι → X.Opens) (c : R →+* Γ(X, ⊤))

/-- The Čech diagram `T ↦ Γ(F, U_T)` of a family of opens, `U_T = T.inf U`, as `R`-modules. -/
abbrev cechDiagram : Finset ι ⥤ ModuleCat.{u} R :=
  sectionsDiagram F c (fun T => T.inf U) (fun _ _ h => Finset.inf_mono h) (fun _ => le_top)

/-- The alternating Čech complex `Č(U, F)` of the family `U`, with `R`-coefficients: degree `p`
is `∏_{#T = p+1} Γ(F, U_T)` (blueprint `def:sm-cech`). -/
def cechComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  subsetCechComplex (cechDiagram F U c)

/-- Čech cohomology `Ȟ^p(U, F)` as an `R`-module. -/
abbrev cechCohomology (p : ℕ) : ModuleCat.{u} R :=
  (cechComplex F U c).homology p

variable {F} in
/-- Functoriality of the Čech complex in the module. -/
def cechComplexMap {G : X.Modules} (φ : F ⟶ G) : cechComplex F U c ⟶ cechComplex G U c :=
  subsetCechComplexMap (sectionsDiagramMap c φ _ _ _)

@[simp]
lemma cechComplexMap_f_apply {G : X.Modules} (φ : F ⟶ G) (p : ℕ)
    (x : subsetCechCardPiece (cechDiagram F U c) (p + 1)) (T : Finset ι) :
    ((cechComplexMap U c φ).f p x).val T = φ.app (T.inf U) (x.val T) :=
  rfl

lemma cechComplexMap_id : cechComplexMap U c (𝟙 F) = 𝟙 _ := by
  ext p x
  apply Subtype.ext
  funext T
  rfl

lemma cechComplexMap_comp {G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) :
    cechComplexMap U c (φ ≫ ψ) = cechComplexMap U c φ ≫ cechComplexMap U c ψ := by
  ext p x
  apply Subtype.ext
  funext T
  rfl

/-- The Čech complex as a functor of the module. -/
@[simps]
def cechComplexFunctor : X.Modules ⥤ CochainComplex (ModuleCat.{u} R) ℕ where
  obj F := cechComplex F U c
  map φ := cechComplexMap U c φ
  map_id F := cechComplexMap_id F U c
  map_comp φ ψ := cechComplexMap_comp _ U c φ ψ

/-- Čech cohomology vanishes in degrees `p ≥ #ι`: there are no subsets of cardinality `p + 1`. -/
theorem isZero_cechCohomology_of_card_le [Fintype ι] (p : ℕ) (hp : Fintype.card ι ≤ p) :
    Limits.IsZero (cechCohomology F U c p) := by
  apply ShortComplex.isZero_homology_of_isZero_X₂
  change Limits.IsZero (ModuleCat.of R (subsetCechCardPiece (cechDiagram F U c) (p + 1)))
  rw [subsetCechCardPiece_eq_bot _ _ (by omega)]
  exact ModuleCat.isZero_of_subsingleton _

end Cech

section HomologyCriteria

variable (C : CochainComplex (ModuleCat.{u} R) ℕ)

/-- Degree-zero cohomology of an `ℕ`-indexed cochain complex of modules vanishes iff the first
differential is injective. -/
lemma isZero_homology_zero_iff :
    Limits.IsZero (C.homology 0) ↔ Function.Injective (C.d 0 1).hom := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' C 0 0 1 (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  have h0 : C.d 0 0 = 0 := C.shape 0 0 (by simp)
  constructor
  · intro h
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := h x hx
    rw [← hy]
    change (C.d 0 0).hom y = 0
    rw [h0]
    rfl
  · intro h x hx
    refine ⟨0, ?_⟩
    change (C.d 0 0).hom 0 = x
    rw [map_zero]
    exact (h (hx.trans (map_zero _).symm)).symm

/-- Cohomology of an `ℕ`-indexed cochain complex of modules vanishes in degree `p + 1` iff every
cocycle of degree `p + 1` is a coboundary. -/
lemma isZero_homology_succ_iff (p : ℕ) :
    Limits.IsZero (C.homology (p + 1)) ↔
      ∀ x : C.X (p + 1), (C.d (p + 1) (p + 2)).hom x = 0 → ∃ y, (C.d p (p + 1)).hom y = x := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' C p (p + 1) (p + 2) (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  rfl

variable {ι : Type u} [LinearOrder ι] (D : Finset ι ⥤ ModuleCat.{u} R)

lemma subsetCechComplex_d (p : ℕ) :
    (subsetCechComplex D).d p (p + 1) = ModuleCat.ofHom (subsetCechCardDifferential D (p + 1)) :=
  CochainComplex.of_d (fun p => ModuleCat.of R (subsetCechCardPiece D (p + 1)))
    (fun p => ModuleCat.ofHom (subsetCechCardDifferential D (p + 1))) p

/-- The projection of the total cube onto the cardinality piece `n`. -/
def cubeCardProj (n : ℕ) (x : subsetCechCube D) : subsetCechCube D :=
  fun T => if T.card = n then x T else 0

omit [LinearOrder ι] in
lemma cubeCardProj_mem (n : ℕ) (x : subsetCechCube D) :
    cubeCardProj D n x ∈ subsetCechCardPiece D n := by
  intro T hT
  simp [cubeCardProj, hT]

lemma subsetCechDifferential_cubeCardProj (n : ℕ) (x : subsetCechCube D) :
    subsetCechDifferential D (cubeCardProj D n x) =
      cubeCardProj D (n + 1) (subsetCechDifferential D x) := by
  funext T
  simp only [subsetCechDifferential_apply, cubeCardProj]
  by_cases hT : T.card = n + 1
  · rw [if_pos hT]
    apply Finset.sum_congr rfl
    intro i hi
    have : (T.erase i).card = n := by
      have := Finset.card_erase_add_one hi
      omega
    rw [if_pos this]
  · rw [if_neg hT]
    apply Finset.sum_eq_zero
    intro i hi
    have : (T.erase i).card ≠ n := by
      have := Finset.card_erase_add_one hi
      omega
    rw [if_neg this, map_zero, smul_zero]

/-- If the alternating differential on the total cube is exact, the Čech complex of `D` is exact
in every positive degree. -/
theorem isZero_subsetCechComplex_homology_succ_of_exact
    (h : Function.Exact (subsetCechDifferential D) (subsetCechDifferential D)) (p : ℕ) :
    Limits.IsZero ((subsetCechComplex D).homology (p + 1)) := by
  rw [isZero_homology_succ_iff]
  intro x hx
  rw [subsetCechComplex_d] at hx
  have hx' : subsetCechDifferential D (x : subsetCechCardPiece D (p + 1 + 1)).val = 0 :=
    congrArg Subtype.val hx
  obtain ⟨y, hy⟩ := (h _).mp hx'
  refine ⟨(⟨cubeCardProj D (p + 1) y, cubeCardProj_mem D (p + 1) y⟩ :
    subsetCechCardPiece D (p + 1)), ?_⟩
  rw [subsetCechComplex_d]
  apply Subtype.ext
  change subsetCechDifferential D (cubeCardProj D (p + 1) y) =
    (x : subsetCechCardPiece D (p + 1 + 1)).val
  rw [subsetCechDifferential_cubeCardProj, hy]
  funext T
  simp only [cubeCardProj]
  split_ifs with hT
  · rfl
  · exact ((x : subsetCechCardPiece D (p + 1 + 1)).property T hT).symm

end HomologyCriteria

section Restrict

variable (F : X.Modules) {ι κ : Type u} [LinearOrder ι] [LinearOrder κ] (W : κ → X.Opens)
  (e : ι ↪o κ) (c : R →+* Γ(X, ⊤))

lemma inf_map_orderEmbedding (T : Finset ι) : (T.map e.toEmbedding).inf W = T.inf (W ∘ e) :=
  Finset.inf_map _ _ _

/-- Two restrictions compose to one. -/
lemma presheaf_map_map {V₁ V₂ V₃ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (h₃ : V₃ ≤ V₁)
    (s : Γ(F, V₁)) :
    F.presheaf.map (homOfLE h₂).op (F.presheaf.map (homOfLE h₁).op s) =
      F.presheaf.map (homOfLE h₃).op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restricting along an inclusion and back along the reverse inclusion is the identity. -/
lemma presheaf_map_map_self {V₁ V₂ : X.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₁ ≤ V₂) (s : Γ(F, V₁)) :
    F.presheaf.map (homOfLE h₂).op (F.presheaf.map (homOfLE h₁).op s) = s := by
  rw [presheaf_map_map F h₁ h₂ le_rfl]
  change F.presheaf.map (𝟙 _) s = s
  rw [F.presheaf.map_id]
  rfl

/-- Restricting a family of sections indexed by finite subsets is compatible with equality of
indices. -/
lemma presheaf_map_congr_index {μ : Type u} {A : Finset μ → X.Opens} (x : ∀ S, Γ(F, A S))
    {S S' : Finset μ} (h : S = S') {V : X.Opens} (hS : V ≤ A S) (hS' : V ≤ A S') :
    F.presheaf.map (homOfLE hS).op (x S) = F.presheaf.map (homOfLE hS').op (x S') := by
  subst h
  rfl

lemma subsetCechSign_map (T : Finset ι) (i : ι) :
    subsetCechSign (T.map e.toEmbedding) (e.toEmbedding i) = subsetCechSign T i := by
  unfold subsetCechSign
  rw [Finset.filter_map, Finset.card_map]
  congr 2
  apply Finset.filter_congr
  intro j _
  simp

/-- The restriction of total Čech cubes along an order embedding `e : ι ↪o κ`:
`(r x)_T = x_{e(T)}|_{U_T}`. -/
def cechRestrictCube :
    subsetCechCube (cechDiagram F W c) →ₗ[R] subsetCechCube (cechDiagram F (W ∘ e) c) where
  toFun x T := sectionsRestrict F c le_top le_top (inf_map_orderEmbedding W e T).ge
    (x (T.map e.toEmbedding))
  map_add' x y := by
    funext T
    exact (sectionsRestrict F c _ _ _).hom.map_add _ _
  map_smul' r x := by
    funext T
    exact (sectionsRestrict F c _ _ _).hom.map_smul _ _

lemma cechRestrictCube_apply (x : subsetCechCube (cechDiagram F W c)) (T : Finset ι) :
    cechRestrictCube F W e c x T = F.presheaf.map
      (homOfLE (inf_map_orderEmbedding W e T).ge).op (x (T.map e.toEmbedding)) :=
  rfl

lemma cechRestrictCube_apply' (x : subsetCechCube (cechDiagram F W c)) (T : Finset ι) :
    cechRestrictCube F W e c x T = sectionsRestrict F c le_top le_top
      (inf_map_orderEmbedding W e T).ge (x (T.map e.toEmbedding)) :=
  rfl

lemma cechRestrictCube_differential (x : subsetCechCube (cechDiagram F W c)) :
    cechRestrictCube F W e c (subsetCechDifferential _ x) =
      subsetCechDifferential _ (cechRestrictCube F W e c x) := by
  funext T
  rw [cechRestrictCube_apply', subsetCechDifferential_apply, subsetCechDifferential_apply,
    map_sum, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, subsetCechSign_map]
  congr 1
  simp only [subsetCechRestriction, cechRestrictCube_apply']
  rw [sectionsRestrict_restrict, sectionsRestrict_restrict]
  exact sectionsRestrict_congr_index F c (A := fun S => S.inf W) (fun _ => le_top) x
    (Finset.map_erase _ _ _).symm le_top _ _

lemma cechRestrictCube_mem (n : ℕ) (x : subsetCechCube (cechDiagram F W c))
    (hx : x ∈ subsetCechCardPiece (cechDiagram F W c) n) :
    cechRestrictCube F W e c x ∈ subsetCechCardPiece (cechDiagram F (W ∘ e) c) n := by
  intro T hT
  rw [cechRestrictCube_apply, hx (T.map e.toEmbedding) (by rwa [Finset.card_map])]
  exact map_zero _

/-- The restriction `Č(W, F) ⟶ Č(W ∘ e, F)` of Čech complexes along an order embedding
`e : ι ↪o κ` of index sets. -/
def cechRestrict : cechComplex F W c ⟶ cechComplex F (W ∘ e) c :=
  subsetCechComplexMapOfCube (cechRestrictCube F W e c) (cechRestrictCube_mem F W e c)
    (cechRestrictCube_differential F W e c)

lemma cechRestrict_f_apply (p : ℕ) (x : subsetCechCardPiece (cechDiagram F W c) (p + 1))
    (T : Finset ι) :
    ((cechRestrict F W e c).f p x).val T = F.presheaf.map
      (homOfLE (inf_map_orderEmbedding W e T).ge).op (x.val (T.map e.toEmbedding)) :=
  rfl

variable {F} in
/-- Restriction to a subfamily is natural in the module. -/
@[reassoc]
lemma cechRestrict_naturality {G : X.Modules} (φ : F ⟶ G) :
    cechComplexMap W c φ ≫ cechRestrict G W e c =
      cechRestrict F W e c ≫ cechComplexMap (W ∘ e) c φ := by
  ext p x
  apply Subtype.ext
  funext T
  exact (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality
    (homOfLE (inf_map_orderEmbedding W e T).ge).op) (x.val (T.map e.toEmbedding))).symm

/-- Restrictions along composable order embeddings compose. -/
lemma cechRestrict_comp {μ : Type u} [LinearOrder μ] (W : μ → X.Opens) (e₂ : κ ↪o μ)
    (e₁ : ι ↪o κ) :
    cechRestrict F W e₂ c ≫ cechRestrict F (W ∘ e₂) e₁ c = cechRestrict F W (e₁.trans e₂) c := by
  ext p x
  apply Subtype.ext
  funext T
  have h₃ : T.inf ((W ∘ e₂) ∘ e₁) ≤ ((T.map e₁.toEmbedding).map e₂.toEmbedding).inf W :=
    (inf_map_orderEmbedding W (e₁.trans e₂) T).ge.trans (le_of_eq (by rw [Finset.map_map]; rfl))
  refine (presheaf_map_map F _ _ h₃ _).trans ?_
  exact presheaf_map_congr_index F x.val (Finset.map_map _ _ _) _ _

/-- A preimage of the cube of the subfamily: the cochain `x` with `x_{e(T)} = y_T` and `x_S = 0`
if `S` is not contained in the image of `e`. -/
def cechRestrictCubeSection (y : subsetCechCube (cechDiagram F (W ∘ e) c)) :
    subsetCechCube (cechDiagram F W c) := fun S =>
  if h : (S.preimage e e.injective.injOn).map e.toEmbedding = S then
    sectionsRestrict F c le_top le_top
      (le_of_eq (by
        show S.inf W = (S.preimage e e.injective.injOn).inf (W ∘ e)
        rw [← inf_map_orderEmbedding, h]))
      (y (S.preimage e e.injective.injOn))
  else 0

lemma cechRestrictCubeSection_mem (n : ℕ) (y : subsetCechCube (cechDiagram F (W ∘ e) c))
    (hy : y ∈ subsetCechCardPiece (cechDiagram F (W ∘ e) c) n) :
    cechRestrictCubeSection F W e c y ∈ subsetCechCardPiece (cechDiagram F W c) n := by
  intro S hS
  simp only [cechRestrictCubeSection]
  split_ifs with h
  · rw [hy _ (by rw [← Finset.card_map e.toEmbedding, h]; exact hS)]
    exact map_zero _
  · rfl

lemma cechRestrictCube_section (y : subsetCechCube (cechDiagram F (W ∘ e) c)) :
    cechRestrictCube F W e c (cechRestrictCubeSection F W e c y) = y := by
  funext T
  have hpre : (T.map e.toEmbedding).preimage e e.injective.injOn = T :=
    Finset.preimage_map e.toEmbedding T
  have h : ((T.map e.toEmbedding).preimage e e.injective.injOn).map e.toEmbedding =
      T.map e.toEmbedding := by
    rw [hpre]
  rw [cechRestrictCube_apply']
  simp only [cechRestrictCubeSection, dif_pos h]
  rw [sectionsRestrict_restrict]
  rw [sectionsRestrict_congr_index F c (A := fun S => S.inf (W ∘ e)) (fun _ => le_top) y hpre
    le_top _ le_rfl, sectionsRestrict_id]
  rfl

/-- The restriction to a subfamily is degreewise surjective. -/
lemma cechRestrict_f_surjective (p : ℕ) : Function.Surjective ((cechRestrict F W e c).f p) := by
  intro y
  refine ⟨⟨cechRestrictCubeSection F W e c y.val,
    cechRestrictCubeSection_mem F W e c _ y.val y.property⟩, ?_⟩
  apply Subtype.ext
  exact cechRestrictCube_section F W e c y.val

/-- For a surjective (hence bijective) order embedding the restriction is an isomorphism of
complexes. -/
theorem isIso_cechRestrict_of_surjective (he : Function.Surjective e) :
    IsIso (cechRestrict F W e c) := by
  suffices h : ∀ p, IsIso ((cechRestrict F W e c).f p) from
    HomologicalComplex.Hom.isIso_of_components _
  intro p
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨?_, cechRestrict_f_surjective F W e c p⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  apply Subtype.ext
  funext S
  obtain ⟨T, rfl⟩ : ∃ T : Finset ι, T.map e.toEmbedding = S := by
    refine ⟨S.preimage e e.injective.injOn, ?_⟩
    rw [Finset.map_eq_image]
    exact Finset.image_preimage_of_bijective S ⟨e.injective, he⟩
  have h := congrArg (fun z => z.val T) hx
  change F.presheaf.map _ (x.val _) = 0 at h
  have hinj := sectionsRestrict_bijective_of_eq F c (le_top : (T.map e.toEmbedding).inf W ≤ ⊤)
    (le_top : T.inf (W ∘ e) ≤ ⊤) (inf_map_orderEmbedding W e T).symm
  exact hinj.1 (h.trans (map_zero _).symm)

end Restrict

section ZeroCohomology

variable {ι : Type u} [LinearOrder ι]

/-- The alternating differential on a two-element subset `{i, j}`, `i < j`, is the difference of
the two restrictions (adapted from Codex's `ProperSteinProjectiveCech.subsetCechDifferential_pair`,
file `ProperSteinProjectiveCechSheafSections.lean`). -/
theorem subsetCechDifferential_pair' (D : Finset ι ⥤ ModuleCat.{u} R) (x : subsetCechCube D)
    {i j : ι} (hij : i < j) :
    subsetCechDifferential D x {i, j} =
      subsetCechRestriction D (by simp : ({j} : Finset ι) ⊆ {i, j}) (x {j}) -
      subsetCechRestriction D (by simp : ({i} : Finset ι) ⊆ {i, j}) (x {i}) := by
  classical
  simp [subsetCechDifferential, subsetCechSign, Finset.filter_insert, Finset.filter_singleton,
    ne_of_lt hij, hij, not_lt_of_ge (le_of_lt hij), sub_eq_add_neg]
  exact congrArg₂ (fun a b => a + -b)
    (subsetCechRestriction_value_congr D x (Finset.erase_subset i {i, j})
      (by simp : ({j} : Finset ι) ⊆ {i, j}) (Finset.erase_insert (by simp [ne_of_lt hij])))
    (subsetCechRestriction_value_congr D x (Finset.erase_subset j {i, j})
      (by simp : ({i} : Finset ι) ⊆ {i, j})
      (by rw [Finset.erase_insert_of_ne (ne_of_lt hij), Finset.erase_singleton]; rfl))

/-- Degree-zero cohomology of an `ℕ`-indexed cochain complex of modules is the kernel of the first
differential (as in Codex's `ProperSteinProjectiveCech.nativeCochainZeroCocyclesIso`, file
`ProperSteinProjectiveCechFiniteGraded.lean`). -/
def cochainZeroCocyclesIso (C : CochainComplex (ModuleCat.{u} R) ℕ) :
    ModuleCat.of R (LinearMap.ker (C.d 0 1).hom) ≅ C.homology 0 :=
  (C.sc' 0 0 1).moduleCatCyclesIso.symm ≪≫
    (C.cyclesIsoSc' 0 0 1 (by simp) (by simp)).symm ≪≫ C.isoHomologyπ₀

/-- Degree-zero cohomology of an alternating subset complex is the kernel of the first
differential (as in Codex's `ProperSteinProjectiveCech.actualSubsetCechZeroCocyclesIso`). -/
def subsetCechZeroCocyclesIso (D : Finset ι ⥤ ModuleCat.{u} R) :
    ModuleCat.of R (LinearMap.ker (subsetCechCardDifferential D 1)) ≅
      (subsetCechComplex D).homology 0 := by
  have hker : LinearMap.ker ((subsetCechComplex D).d 0 1).hom =
      LinearMap.ker (subsetCechCardDifferential D 1) := by
    rw [subsetCechComplex_d D 0]
    rfl
  exact (LinearEquiv.ofEq _ _ hker.symm).toModuleIso ≪≫ cochainZeroCocyclesIso (subsetCechComplex D)

variable (F : X.Modules) (U : ι → X.Opens) (c : R →+* Γ(X, ⊤))

/-- The cube element `(s|_{U_i})_i` of a global section, extended by zero. -/
def cechAugmentationCube (s : sectionsModuleCat F c ⊤ le_top) :
    subsetCechCube (cechDiagram F U c) := fun T =>
  if T.card = 1 then sectionsRestrict F c le_top le_top le_top s else 0

/-- The augmentation `Γ(X, F) → Č⁰(U, F)`, `s ↦ (s|_{U_i})_i`. -/
def cechAugmentation :
    sectionsModuleCat F c ⊤ le_top →ₗ[R] subsetCechCardPiece (cechDiagram F U c) 1 where
  toFun s := ⟨cechAugmentationCube F U c s, by
    intro T hT
    simp only [cechAugmentationCube, if_neg hT]⟩
  map_add' s t := by
    apply Subtype.ext
    funext T
    show cechAugmentationCube F U c (s + t) T =
      cechAugmentationCube F U c s T + cechAugmentationCube F U c t T
    simp only [cechAugmentationCube]
    split_ifs
    · exact map_add _ _ _
    · exact (add_zero 0).symm
  map_smul' r s := by
    apply Subtype.ext
    funext T
    show cechAugmentationCube F U c (r • s) T = r • cechAugmentationCube F U c s T
    simp only [cechAugmentationCube]
    split_ifs
    · exact map_smul _ _ _
    · exact (smul_zero r).symm

omit [LinearOrder ι] in
lemma cechAugmentation_apply_singleton (s : sectionsModuleCat F c ⊤ le_top) (i : ι) :
    (cechAugmentation F U c s).val {i} = sectionsRestrict F c le_top le_top le_top s := by
  show cechAugmentationCube F U c s {i} = _
  simp only [cechAugmentationCube, Finset.card_singleton, if_pos]

lemma cechAugmentation_mem_ker (s : sectionsModuleCat F c ⊤ le_top) :
    cechAugmentation F U c s ∈ LinearMap.ker (subsetCechCardDifferential (cechDiagram F U c) 1) := by
  rw [LinearMap.mem_ker]
  apply Subtype.ext
  change subsetCechDifferential _ (cechAugmentation F U c s).val = 0
  funext T
  by_cases hT : T.card = 2
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hT
    have key : ∀ a b : ι, a < b →
        subsetCechDifferential (cechDiagram F U c) (cechAugmentation F U c s).val {a, b} = 0 := by
      intro a b hab
      rw [subsetCechDifferential_pair' _ _ hab]
      simp only [subsetCechRestriction, cechAugmentation_apply_singleton]
      rw [sectionsRestrict_restrict, sectionsRestrict_restrict, sub_self]
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h
    · rw [Finset.pair_comm]
      exact key j i h
  · rw [subsetCechDifferential_apply]
    apply Finset.sum_eq_zero
    intro k hk
    have hcard : (T.erase k).card ≠ 1 := by
      have := Finset.card_erase_add_one hk
      omega
    show subsetCechSign T k • subsetCechRestriction _ _
      (cechAugmentationCube F U c s (T.erase k)) = 0
    simp only [cechAugmentationCube, if_neg hcard, map_zero, smul_zero]

omit [LinearOrder ι] in
variable {U} in
lemma cechAugmentation_injective (hU : ⨆ i, U i = ⊤) :
    Function.Injective (cechAugmentation F U c) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have hloc : ∀ i : ι,
      sectionsRestrict F c (V := ⊤) (W := ({i} : Finset ι).inf U) le_top le_top le_top s = 0 := by
    intro i
    rw [← cechAugmentation_apply_singleton F U c s i, hs]
    rfl
  change (s : Γ(F, ⊤)) = (0 : Γ(F, ⊤))
  apply TopCat.Presheaf.IsSheaf.section_ext F.isSheaf
  intro x _
  have hx : x ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  refine ⟨({i} : Finset ι).inf U, le_top, by rw [Finset.inf_singleton]; exact hi, ?_⟩
  refine (hloc i).trans ?_
  exact (map_zero _).symm

variable {U} in
lemma cechAugmentation_surjective_ker (hU : ⨆ i, U i = ⊤)
    (z : subsetCechCardPiece (cechDiagram F U c) 1)
    (hz : z ∈ LinearMap.ker (subsetCechCardDifferential (cechDiagram F U c) 1)) :
    ∃ s, cechAugmentation F U c s = z := by
  classical
  have hz' : subsetCechDifferential (cechDiagram F U c) z.val = 0 :=
    congrArg Subtype.val (LinearMap.mem_ker.mp hz)
  -- agreement of the components on pairwise intersections
  have hpair : ∀ a b : ι, a < b →
      sectionsRestrict F c le_top le_top
          (Finset.inf_mono (by simp : ({a} : Finset ι) ⊆ {a, b})) (z.val {a}) =
        sectionsRestrict F c le_top le_top
          (Finset.inf_mono (by simp : ({b} : Finset ι) ⊆ {a, b})) (z.val {b}) := by
    intro a b hab
    have h := congrFun hz' {a, b}
    rw [subsetCechDifferential_pair' _ _ hab] at h
    exact (sub_eq_zero.mp h).symm
  let V : ι → X.Opens := fun i => ({i} : Finset ι).inf U
  let G : TopCat.Sheaf Ab X := ⟨F.presheaf, F.isSheaf⟩
  have hcover : (⊤ : X.Opens) ≤ iSup V := by
    rw [← hU]
    exact iSup_mono fun i => le_of_eq (Finset.inf_singleton).symm
  have hcompat : TopCat.Presheaf.IsCompatible G.1 V (fun i => (z.val {i} : Γ(F, V i))) := by
    intro a b
    rcases lt_trichotomy a b with h | rfl | h
    · have hle : V a ⊓ V b ≤ ({a, b} : Finset ι).inf U := by
        simp only [V, Finset.inf_singleton, Finset.inf_insert]
        exact le_rfl
      have e := congrArg (F.presheaf.map (homOfLE hle).op) (hpair a b h)
      exact (presheaf_map_map F _ hle inf_le_left (z.val {a})).symm.trans
        (e.trans (presheaf_map_map F _ hle inf_le_right (z.val {b})))
    · rfl
    · have hle : V a ⊓ V b ≤ ({b, a} : Finset ι).inf U := by
        simp only [V, Finset.inf_singleton, Finset.inf_insert]
        exact le_of_eq (inf_comm _ _)
      have e := congrArg (F.presheaf.map (homOfLE hle).op) (hpair b a h)
      exact (presheaf_map_map F _ hle inf_le_left (z.val {a})).symm.trans
        (e.symm.trans (presheaf_map_map F _ hle inf_le_right (z.val {b})))
  obtain ⟨s, hs, -⟩ := G.existsUnique_gluing' V ⊤ (fun i => homOfLE le_top) hcover
    (fun i => (z.val {i} : Γ(F, V i))) hcompat
  refine ⟨s, ?_⟩
  apply Subtype.ext
  funext T
  by_cases hT : T.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hT
    exact (cechAugmentation_apply_singleton F U c s i).trans (hs i)
  · change (if T.card = 1 then _ else 0) = z.val T
    rw [if_neg hT, z.property T hT]

variable {U} in
/-- For a covering family, global sections are the degree-zero Čech cocycles (sheaf axiom). -/
def cechZeroCocyclesEquiv (hU : ⨆ i, U i = ⊤) :
    sectionsModuleCat F c ⊤ le_top ≃ₗ[R]
      LinearMap.ker (subsetCechCardDifferential (cechDiagram F U c) 1) :=
  LinearEquiv.ofBijective
    ((cechAugmentation F U c).codRestrict _ (cechAugmentation_mem_ker F U c))
    ⟨fun s t h => cechAugmentation_injective F c hU (congrArg Subtype.val h), fun z => by
      obtain ⟨s, hs⟩ := cechAugmentation_surjective_ker F c hU z.val z.property
      exact ⟨s, Subtype.ext hs⟩⟩

variable {U} in
/-- `Ȟ⁰(U, F) ≅ Γ(X, F)` for a covering family `U` (blueprint `lem:sm-cech-basic`). -/
def cechCohomologyZeroIso (hU : ⨆ i, U i = ⊤) :
    sectionsModuleCat F c ⊤ le_top ≅ cechCohomology F U c 0 :=
  (cechZeroCocyclesEquiv F c hU).toModuleIso ≪≫ subsetCechZeroCocyclesIso (cechDiagram F U c)

end ZeroCohomology

end

end DeJongAlterations.StableModification.Cohomology
