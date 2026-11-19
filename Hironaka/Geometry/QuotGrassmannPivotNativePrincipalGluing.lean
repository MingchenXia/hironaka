import Hironaka.Geometry.QuotGrassmannPivotNativeEvaluatedCover
import Hironaka.Geometry.QuotGrassmannPivotEvaluatedPullback
import Mathlib.AlgebraicGeometry.Gluing

/-! The original native point internally produces actual compatible charts and their gluing. -/

noncomputable section

open scoped Classical TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (ι ν : Type u) [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

/-- The SAME original native quotient internally constructs a genuine global morphism over
the original base, with actual evaluated original inverse triangles on a finite principal cover. -/
theorem originalNativeGrassmannian_exists_principalGluedMorphism
    (N : Module.Grassmannian A (A ⊗[R] ((ι ⊕ ν) → R)) (Fintype.card ι)) :
    ∃ f : Spec (CommRingCat.of A) ⟶ projectiveModel R ι ν,
      f ≫ projectiveStructure R ι ν = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
      ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
        ∀ g ∈ s, ∃ (p : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν (Localization.Away g)),
          Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g))) ≫ f =
              originalMatrixEvaluatedPivotMorphism R p C ∧
            originalGlobalAffineGrassmannianTensorPoint R ι ν
                (originalMatrixEvaluatedPivotMorphism R p C) =
              Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away g)) N := by
  obtain ⟨s, hspan, hs⟩ := originalNativeGrassmannian_exists_finitePrincipalEvaluatedInverse
    R A ι ν N
  have hrange : Ideal.span (Set.range (fun i : s => (i.val : A))) = ⊤ := by
    rw [show Set.range (fun i : s => (i.val : A)) = (s : Set A) by
      ext g
      simp]
    exact hspan
  let 𝒰 := (Scheme.affineOpenCoverOfSpanRangeEqTop
    (R := CommRingCat.of A) (fun i : s => (i.val : A)) hrange).openCover
  choose p C hC using fun i : s => hs i.val i.property
  let f₀ : ∀ i : 𝒰.I₀, 𝒰.X i ⟶ projectiveModel R ι ν :=
    fun i => originalMatrixEvaluatedPivotMorphism R (p i) (C i)
  have hcompat : ∀ i j, pullback.fst (𝒰.f i) (𝒰.f j) ≫ f₀ i =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ f₀ j := by
    intro i j
    exact originalMatrixEvaluatedPivotMorphism_pullback_compatible R N
      (IsScalarTower.toAlgHom R A (Localization.Away i.val))
      (IsScalarTower.toAlgHom R A (Localization.Away j.val))
      (p i) (p j) (C i) (C j) (hC i) (hC j)
  let f := 𝒰.glueMorphisms f₀ hcompat
  have hlocal (i : s) :
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away i.val))) ≫ f =
        originalMatrixEvaluatedPivotMorphism R (p i) (C i) :=
    𝒰.ι_glueMorphisms f₀ hcompat i
  refine ⟨f, ?_, s, hspan, ?_⟩
  · apply 𝒰.hom_ext
    intro i
    change (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away i.val))) ≫ f) ≫
        projectiveStructure R ι ν =
      Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away i.val))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R A))
    rw [hlocal, originalMatrixEvaluatedPivotMorphism_structure, ← Spec.map_comp]
    apply congrArg Spec.map
    ext r
    exact IsScalarTower.algebraMap_apply R A (Localization.Away i.val) r
  · intro g hg
    exact ⟨p ⟨g, hg⟩, C ⟨g, hg⟩, hlocal ⟨g, hg⟩, hC ⟨g, hg⟩⟩

end Hironaka.Geometry.QuotGrassmann
