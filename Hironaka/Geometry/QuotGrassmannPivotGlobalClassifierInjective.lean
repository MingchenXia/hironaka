import Hironaka.Geometry.QuotGrassmannPivotAffineFactorization
import Hironaka.Geometry.QuotGrassmannFixedPivotOpenCover

/-! The original global native classifier determines every actual relative affine morphism. -/

noncomputable section

open scoped Classical
open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {A ι ν : Type u} [CommRing A] [Algebra R A]
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

/-- SAME entire original native classifier determines the actual morphism over the original
base, with all original pivot neighborhoods and coefficient actions constructed internally. -/
theorem originalGlobalAffineGrassmannianTensorPoint_injective_over_base
    (f g : Spec (.of A) ⟶ projectiveModel R ι ν)
    (hf : f ≫ projectiveStructure R ι ν = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (hg : g ≫ projectiveStructure R ι ν = Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (h : originalGlobalAffineGrassmannianTensorPoint R ι ν f =
      originalGlobalAffineGrassmannianTensorPoint R ι ν g) : f = g := by
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨p, hp⟩ := originalFixedPivotModelMorphism_cover R (f x)
  obtain ⟨t, ht⟩ := originalFixedPivotModelMorphism_cover R (g x)
  let U := (f ⁻¹ᵁ (originalPivotModelMorphism R p).opensRange) ⊓
    (g ⁻¹ᵁ (originalPivotModelMorphism R t).opensRange)
  refine ⟨U, ⟨hp, ht⟩, ?_⟩
  let 𝒰 := U.toScheme.affineOpenCover
  apply 𝒰.openCover.hom_ext
  intro i
  let B := 𝒰.X i
  let a := 𝒰.f i ≫ U.ι
  let ψ : CommRingCat.of A ⟶ B := Spec.preimage a
  let : Algebra R B := (ψ.hom.comp (algebraMap R A)).toAlgebra
  let φ : A →ₐ[R] B := { ψ.hom with commutes' := fun _ => rfl }
  have hf' : (Spec.map ψ ≫ f) ≫ projectiveStructure R ι ν =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [Category.assoc, hf, ← Spec.map_comp]
    rfl
  have hg' : (Spec.map ψ ≫ g) ≫ projectiveStructure R ι ν =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
    rw [Category.assoc, hg, ← Spec.map_comp]
    rfl
  have hp' : Set.range (Spec.map ψ ≫ f) ⊆ Set.range (originalPivotModelMorphism R p) := by
    rw [Spec.map_preimage]
    rintro y ⟨z, rfl⟩
    exact (𝒰.f i z).property.1
  have ht' : Set.range (Spec.map ψ ≫ g) ⊆ Set.range (originalPivotModelMorphism R t) := by
    rw [Spec.map_preimage]
    rintro y ⟨z, rfl⟩
    exact (𝒰.f i z).property.2
  have h₁ := originalGlobalAffineGrassmannianTensorPoint_map R ι ν
    (A := CommRingCat.of A) (B := B) φ f
  have h₂ := originalGlobalAffineGrassmannianTensorPoint_map R ι ν
    (A := CommRingCat.of A) (B := B) φ g
  have hc : originalGlobalAffineGrassmannianTensorPoint R ι ν (Spec.map ψ ≫ f) =
      originalGlobalAffineGrassmannianTensorPoint R ι ν (Spec.map ψ ≫ g) :=
    h₁.symm.trans ((congrArg (Module.Grassmannian.map φ) h).trans h₂)
  have he := originalAffineMorphism_eq_of_classifier_eq_of_ranges R (A := B)
    (Spec.map ψ ≫ f) (Spec.map ψ ≫ g) hf' hg' p t hp' ht' hc
  change Spec.map ψ ≫ f = Spec.map ψ ≫ g at he
  rw [show Spec.map ψ = a from Spec.map_preimage a] at he
  change a ≫ f = a ≫ g
  exact he

end Hironaka.Geometry.QuotGrassmann
