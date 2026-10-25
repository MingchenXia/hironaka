/-
Copyright (c) 2026 Mingchen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia
-/
import DeJongAlterations.StableModification.Cohomology.CechComplex
import DeJongAlterations.Geometry.ProperSteinProjectiveCechSubsetNonemptyExactness
import DeJongAlterations.Geometry.ProperSteinProjectiveCechAffineExactness
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.Algebra.Category.Grp.Limits

/-!
# The long exact sequence of Čech cohomology

Let `0 → F₁ → F₂ → F₃ → 0` be a short exact sequence of `𝒪_X`-modules with `F₂`, `F₃`
quasi-coherent, and `U` a family of opens all of whose nonempty finite intersections are affine.
Sections over any open are left exact, and over an affine open the map `Γ(F₂) → Γ(F₃)` is onto
(Codex's `ProperSteinProjectiveCech.affineQuasicoherent_sectionsSurjective`, transported to an
affine open). Hence `0 → Č(U, F₁) → Č(U, F₂) → Č(U, F₃) → 0` is a short exact sequence of
complexes (`cechShortComplex_shortExact`, via Codex's
`ProperSteinProjectiveCech.SubsetNonemptyExactness.sequence_shortExact`), and Mathlib's homology
sequence gives the connecting maps `cechδ` and the long exact sequence
(`cechCohomology_exact₁`, `cechCohomology_exact₂`, `cechCohomology_exact₃`). Blueprint:
`sm-cohomology-cech.tex`, `thm:sm-cech-les` (`lem:sm-cech-basic`, long exact sequence).
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open DeJongAlterations.Geometry.ProperSteinProjectiveCech

namespace DeJongAlterations.StableModification.Cohomology

noncomputable section

variable {X : Scheme.{u}}

section Sections

variable (W : X.Opens)

/-- The sections functor `M ↦ Γ(M, W)` from `𝒪_X`-modules to abelian groups. -/
def sectionsFunctor : X.Modules ⥤ Ab.{u} :=
  Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (op W)

instance : PreservesLimits (sectionsFunctor W) :=
  have : PreservesLimits ((evaluation (X.Opens)ᵒᵖ Ab.{u}).obj (op W)) :=
    evaluationPreservesLimits _
  comp_preservesLimits (Scheme.Modules.toPresheaf X) ((evaluation _ _).obj (op W))

instance : (sectionsFunctor W).PreservesZeroMorphisms :=
  ⟨fun _ _ => Scheme.Modules.Hom.zero_app⟩

variable {W}

lemma sectionsFunctor_map {M N : X.Modules} (φ : M ⟶ N) :
    (sectionsFunctor W).map φ = φ.app W :=
  rfl

variable (S : ShortComplex X.Modules) (hS : S.ShortExact)
include hS

/-- Sections over any open are left exact: injectivity. -/
lemma sections_injective : Function.Injective (S.f.app W) := by
  have := hS.mono_f
  have h : Mono ((sectionsFunctor W).map S.f) := inferInstance
  rw [AddCommGrpCat.mono_iff_injective] at h
  exact h

/-- Sections over any open are left exact: exactness in the middle. -/
lemma sections_exact : Function.Exact (S.f.app W) (S.g.app W) := by
  have h := hS.exact.map_of_mono_of_preservesKernel (sectionsFunctor W) hS.mono_f inferInstance
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Over an affine open, the sections of an epimorphism of quasi-coherent modules are onto. -/
lemma sections_surjective_of_isAffineOpen [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hW : IsAffineOpen W) : Function.Surjective (S.g.app W) := by
  have : IsAffine W.toScheme := hW
  have := hS.epi_g
  have hepi : Epi ((Scheme.Modules.restrictFunctor W.ι).map S.g) := inferInstance
  have hsurj := affineQuasicoherent_sectionsSurjective
    ((Scheme.Modules.restrictFunctor W.ι).map S.g)
  have heq : W.ι ''ᵁ ⊤ = W := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  intro y
  obtain ⟨x', hx'⟩ := hsurj (S.X₃.presheaf.map (homOfLE heq.le).op y)
  refine ⟨S.X₂.presheaf.map (homOfLE heq.ge).op x', ?_⟩
  have hnat := ConcreteCategory.congr_hom (S.g.mapPresheaf.naturality (homOfLE heq.ge).op) x'
  change S.g.app W (S.X₂.presheaf.map _ x') = _ at hnat ⊢
  rw [hnat]
  change S.X₃.presheaf.map _ (S.g.app (W.ι ''ᵁ ⊤) x') = y
  have hx'' : S.g.app (W.ι ''ᵁ ⊤) x' = S.X₃.presheaf.map (homOfLE heq.le).op y := hx'
  rw [hx'']
  exact presheaf_map_map_self S.X₃ _ _ y

end Sections

section Cech

variable {R : Type u} [CommRing R] {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
  (c : R →+* Γ(X, ⊤))

lemma cechComplexMap_zero (F G : X.Modules) : cechComplexMap U c (0 : F ⟶ G) = 0 := by
  ext p x
  apply Subtype.ext
  funext T
  change (0 : F ⟶ G).app (T.inf U) (x.val T) = 0
  rw [Scheme.Modules.Hom.zero_app]
  rfl

instance : (cechComplexFunctor U c).PreservesZeroMorphisms where
  map_zero F G := cechComplexMap_zero U c F G

/-- The short complex of Čech complexes of a short complex of modules. -/
def cechShortComplex (S : ShortComplex X.Modules) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℕ) :=
  S.map (cechComplexFunctor U c)

variable (S : ShortComplex X.Modules) (hS : S.ShortExact) [S.X₂.IsQuasicoherent]
  [S.X₃.IsQuasicoherent] (haff : ∀ T : Finset ι, T.Nonempty → IsAffineOpen (T.inf U))
include hS haff

/-- **Short exact sequence of Čech complexes** (blueprint `thm:sm-cech-les`). -/
theorem cechShortComplex_shortExact : (cechShortComplex U c S).ShortExact :=
  SubsetNonemptyExactness.sequence_shortExact
    (sectionsDiagramMap c S.f (fun T => T.inf U) (fun _ _ h => Finset.inf_mono h)
      (fun _ => le_top))
    (sectionsDiagramMap c S.g (fun T => T.inf U) (fun _ _ h => Finset.inf_mono h)
      (fun _ => le_top))
    (fun T hT => ⟨sections_exact S hS, sections_injective S hS,
      sections_surjective_of_isAffineOpen S hS (haff T hT)⟩)

/-- The connecting map `Ȟ^p(U, F₃) → Ȟ^{p+1}(U, F₁)`. -/
def cechδ (p : ℕ) : cechCohomology S.X₃ U c p ⟶ cechCohomology S.X₁ U c (p + 1) :=
  (cechShortComplex_shortExact U c S hS haff).δ p (p + 1) (by simp)

/-- Exactness of `Ȟ^p(F₁) → Ȟ^p(F₂) → Ȟ^p(F₃)`. -/
theorem cechCohomology_exact₂ (p : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (cechComplexMap U c S.f) p)
      (HomologicalComplex.homologyMap (cechComplexMap U c S.g) p)
      (by rw [← HomologicalComplex.homologyMap_comp, ← cechComplexMap_comp, S.zero,
        cechComplexMap_zero, HomologicalComplex.homologyMap_zero])).Exact :=
  (cechShortComplex_shortExact U c S hS haff).homology_exact₂ p

/-- Exactness of `Ȟ^p(F₂) → Ȟ^p(F₃) → Ȟ^{p+1}(F₁)`. -/
theorem cechCohomology_exact₃ (p : ℕ) :
    (ShortComplex.mk (HomologicalComplex.homologyMap (cechComplexMap U c S.g) p)
      (cechδ U c S hS haff p)
      ((cechShortComplex_shortExact U c S hS haff).comp_δ p (p + 1) (by simp))).Exact :=
  (cechShortComplex_shortExact U c S hS haff).homology_exact₃ p (p + 1) (by simp)

/-- Exactness of `Ȟ^p(F₃) → Ȟ^{p+1}(F₁) → Ȟ^{p+1}(F₂)`. -/
theorem cechCohomology_exact₁ (p : ℕ) :
    (ShortComplex.mk (cechδ U c S hS haff p)
      (HomologicalComplex.homologyMap (cechComplexMap U c S.f) (p + 1))
      ((cechShortComplex_shortExact U c S hS haff).δ_comp p (p + 1) (by simp))).Exact :=
  (cechShortComplex_shortExact U c S hS haff).homology_exact₁ p (p + 1) (by simp)

end Cech

end

end DeJongAlterations.StableModification.Cohomology
