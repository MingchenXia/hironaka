/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott (Resolution): formalization performed by Claude Fable 5.1
-/
module

public import Hironaka.Scheme.ProjectiveBundle.Affine.Defs
import Hironaka.Algebra.SymmetricAlgebra.Away
import Hironaka.Scheme.BlowUp.Rees.Map

/-!
# Functoriality of the projective bundle of a module

The morphisms `affineProjectiveBundle.map φ f : P(N) ⟶ P(M)` induced by semilinear maps are
functorial: the identity induces the identity (`affineProjectiveBundle.map_eq_id`) and composites
induce composites (`affineProjectiveBundle.map_eq_comp`), from Mathlib's `Proj.map_id` and
`Proj.map_comp` and the corresponding identities of graded maps of symmetric algebras, checked on
the generators `ι(M)` and the constants (`SymmetricAlgebra.ringHom_ext`).
-/

@[expose] public section

universe u

open CategoryTheory SymmetricAlgebra

namespace SymmetricAlgebra

variable {R : Type u} {M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {S : Type u} {N : Type u} [CommRing S] [AddCommGroup N] [Module S N]
variable {T : Type u} {P : Type u} [CommRing T] [AddCommGroup P] [Module T P]

/-- The identity induces the identity graded map. -/
theorem gradedMap_eq_id (f : M →ₛₗ[RingHom.id R] M) (hf : ∀ x, f x = x) :
    gradedMap (RingHom.id R) f = GradedRingHom.id (grading R M) := by
  refine GradedRingHom.ext fun a => RingHom.congr_fun (ringHom_ext
    (F := (gradedMap (RingHom.id R) f).toRingHom) (G := RingHom.id _) (fun r => ?_)
    (fun x => ?_)) a
  · rw [GradedRingHom.coe_toRingHom, gradedMap_algebraMap]; rfl
  · rw [GradedRingHom.coe_toRingHom, gradedMap_ι, hf]; rfl

/-- Composites induce composite graded maps. -/
theorem gradedMap_eq_comp (φ : R →+* S) (ψ : S →+* T) (f : M →ₛₗ[φ] N) (g : N →ₛₗ[ψ] P)
    (k : M →ₛₗ[ψ.comp φ] P) (hk : ∀ x, k x = g (f x)) :
    gradedMap (ψ.comp φ) k = (gradedMap ψ g).comp (gradedMap φ f) := by
  refine GradedRingHom.ext fun a => RingHom.congr_fun (ringHom_ext
    (F := (gradedMap (ψ.comp φ) k).toRingHom)
    (G := (gradedMap ψ g).toRingHom.comp (gradedMap φ f).toRingHom) (fun r => ?_)
    (fun x => ?_)) a
  · simp only [GradedRingHom.coe_toRingHom, RingHom.comp_apply, gradedMap_algebraMap]
  · simp only [GradedRingHom.coe_toRingHom, RingHom.comp_apply, gradedMap_ι, hk]

end SymmetricAlgebra

namespace AlgebraicGeometry.affineProjectiveBundle

variable {R : Type u} {M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {S : Type u} {N : Type u} [CommRing S] [AddCommGroup N] [Module S N]
variable {T : Type u} {P : Type u} [CommRing T] [AddCommGroup P] [Module T P]

/-- Functoriality, identity: a ring map equal to the identity and a semilinear map that is the
identity on elements induce the identity of `P(M)`. -/
theorem map_eq_id {φ : R →+* R} (hφ : φ = RingHom.id R) (f : M →ₛₗ[φ] M) (hf : ∀ x, f x = x)
    (hspan : Submodule.span R (Set.range f) = ⊤) : map φ f hspan = 𝟙 _ := by
  subst hφ
  have key : ∀ (F : grading R M →+*ᵍ grading R M) (hF),
      F = GradedRingHom.id _ → Proj.map F hF = 𝟙 (Proj (grading R M)) := by
    rintro F hF rfl
    exact Proj.map_id
  exact key _ _ (gradedMap_eq_id f hf)

/-- Functoriality, composites. -/
theorem map_eq_comp {φ : R →+* S} {ψ : S →+* T} {χ : R →+* T} (hχ : χ = ψ.comp φ)
    (f : M →ₛₗ[φ] N) (g : N →ₛₗ[ψ] P) (k : M →ₛₗ[χ] P) (hk : ∀ x, k x = g (f x))
    (hf : Submodule.span S (Set.range f) = ⊤) (hg : Submodule.span T (Set.range g) = ⊤)
    (hk' : Submodule.span T (Set.range k) = ⊤) :
    map χ k hk' = map ψ g hg ≫ map φ f hf := by
  subst hχ
  have key : ∀ (F : grading R M →+*ᵍ grading T P) (hF),
      F = (gradedMap ψ g).comp (gradedMap φ f) →
        Proj.map F hF = map ψ g hg ≫ map φ f hf := by
    rintro F hF rfl
    exact Proj.map_comp _ _ _ _
  exact key _ _ (gradedMap_eq_comp φ ψ f g k hk)

/-- The base-change square commutes. -/
theorem map_π (φ : R →+* S) (f : M →ₛₗ[φ] N)
    (hspan : Submodule.span S (Set.range f) = ⊤) :
    map φ f hspan ≫ π R M = π S N ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [map, π, π, Proj.map_toSpecZero_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun r => Subtype.ext ?_)
  exact gradedMap_algebraMap φ f r

section CommRingCat

/-! ### The same statements for morphisms of `CommRingCat` -/

variable {R' S' T' : CommRingCat.{u}} {M' N' P' : Type u} [AddCommGroup M'] [Module R' M']
  [AddCommGroup N'] [Module S' N'] [AddCommGroup P'] [Module T' P']

theorem mapHom_eq_id {φ : R' ⟶ R'} (hφ : φ = 𝟙 R') (f : M' →ₛₗ[φ.hom] M') (hf : ∀ x, f x = x)
    (hspan : Submodule.span R' (Set.range f) = ⊤) : mapHom φ f hspan = 𝟙 _ := by
  subst hφ
  exact map_eq_id CommRingCat.hom_id f hf hspan

theorem mapHom_eq_comp {φ : R' ⟶ S'} {ψ : S' ⟶ T'} {χ : R' ⟶ T'} (hχ : χ = φ ≫ ψ)
    (f : M' →ₛₗ[φ.hom] N') (g : N' →ₛₗ[ψ.hom] P') (k : M' →ₛₗ[χ.hom] P')
    (hk : ∀ x, k x = g (f x)) (hf : Submodule.span S' (Set.range f) = ⊤)
    (hg : Submodule.span T' (Set.range g) = ⊤) (hk' : Submodule.span T' (Set.range k) = ⊤) :
    mapHom χ k hk' = mapHom ψ g hg ≫ mapHom φ f hf := by
  subst hχ
  exact map_eq_comp (CommRingCat.hom_comp φ ψ) f g k hk hf hg hk'

/-- Over the base, for a morphism of `CommRingCat`: `mapHom φ f` lies over `Spec.map φ`. -/
@[reassoc]
theorem mapHom_π (φ : R' ⟶ S') (f : M' →ₛₗ[φ.hom] N')
    (hspan : Submodule.span S' (Set.range f) = ⊤) :
    mapHom φ f hspan ≫ π R' M' = π S' N' ≫ Spec.map φ := by
  rw [mapHom, map_π, CommRingCat.ofHom_hom]

end CommRingCat

end AlgebraicGeometry.affineProjectiveBundle
