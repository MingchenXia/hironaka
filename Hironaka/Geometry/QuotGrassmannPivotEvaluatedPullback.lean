import Hironaka.Geometry.QuotGrassmannPivotEvaluatedCocone
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! The actual native affine overlap internally supplies its original coefficient cocone. -/

noncomputable section

open scoped Classical TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type u) [CommRing R] {A A₁ A₂ ι ν : Type u}
  [CommRing A] [CommRing A₁] [CommRing A₂]
  [Algebra R A] [Algebra R A₁] [Algebra R A₂]
  [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

/-- The SAME native original affine overlap derives ALL coefficient maps and the actual
compatibility of original inverse charts, with no overlap comparison certificate. -/
theorem originalMatrixEvaluatedPivotMorphism_pullback_compatible
    (N : Module.Grassmannian A (A ⊗[R] ((ι ⊕ ν) → R)) (Fintype.card ι))
    (α₁ : A →ₐ[R] A₁) (α₂ : A →ₐ[R] A₂)
    (p t : (ι ⊕ ν) ≃ (ι ⊕ ν)) (C : Matrix ι ν A₁) (D : Matrix ι ν A₂)
    (hC : originalGlobalAffineGrassmannianTensorPoint R ι ν
      (originalMatrixEvaluatedPivotMorphism R p C) = Module.Grassmannian.map α₁ N)
    (hD : originalGlobalAffineGrassmannianTensorPoint R ι ν
      (originalMatrixEvaluatedPivotMorphism R t D) = Module.Grassmannian.map α₂ N) :
    pullback.fst (Spec.map (CommRingCat.ofHom α₁.toRingHom))
        (Spec.map (CommRingCat.ofHom α₂.toRingHom)) ≫ originalMatrixEvaluatedPivotMorphism R p C =
      pullback.snd (Spec.map (CommRingCat.ofHom α₁.toRingHom))
        (Spec.map (CommRingCat.ofHom α₂.toRingHom)) ≫ originalMatrixEvaluatedPivotMorphism R t D := by
  let a₁ := Spec.map (CommRingCat.ofHom α₁.toRingHom)
  let a₂ := Spec.map (CommRingCat.ofHom α₂.toRingHom)
  let P := pullback a₁ a₂
  let B := Γ(P, ⊤)
  let ψ₁ : CommRingCat.of A₁ ⟶ B := Spec.preimage (P.isoSpec.inv ≫ pullback.fst a₁ a₂)
  let ψ₂ : CommRingCat.of A₂ ⟶ B := Spec.preimage (P.isoSpec.inv ≫ pullback.snd a₁ a₂)
  have hψ : ψ₁.hom.comp α₁.toRingHom = ψ₂.hom.comp α₂.toRingHom := by
    have hs : CommRingCat.ofHom α₁.toRingHom ≫ ψ₁ = CommRingCat.ofHom α₂.toRingHom ≫ ψ₂ := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
      simpa only [Category.assoc] using
        congrArg (fun f => P.isoSpec.inv ≫ f) (pullback.condition (f := a₁) (g := a₂))
    exact congrArg (fun f : CommRingCat.of A ⟶ B => f.hom) hs
  let χ : A →+* B := ψ₁.hom.comp α₁.toRingHom
  let : Algebra R B := (χ.comp (algebraMap R A)).toAlgebra
  let φ₁ : A₁ →ₐ[R] B :=
    { ψ₁.hom with
      commutes' := by
        intro r
        change ψ₁.hom (algebraMap R A₁ r) = χ (algebraMap R A r)
        exact congrArg ψ₁.hom (α₁.commutes r).symm }
  let φ₂ : A₂ →ₐ[R] B :=
    { ψ₂.hom with
      commutes' := by
        intro r
        change ψ₂.hom (algebraMap R A₂ r) = (ψ₁.hom.comp α₁.toRingHom) (algebraMap R A r)
        rw [hψ]
        exact congrArg ψ₂.hom (α₂.commutes r).symm }
  have hφ : φ₁.comp α₁ = φ₂.comp α₂ := by
    apply AlgHom.ext
    intro a
    exact RingHom.congr_fun hψ a
  have he := originalMatrixEvaluatedPivotMorphism_eq_of_common_cocone R N
    α₁ α₂ φ₁ φ₂ hφ p t C D hC hD
  change Spec.map ψ₁ ≫ originalMatrixEvaluatedPivotMorphism R p C =
    Spec.map ψ₂ ≫ originalMatrixEvaluatedPivotMorphism R t D at he
  rw [Spec.map_preimage, Spec.map_preimage] at he
  exact (cancel_epi P.isoSpec.inv).mp (by simpa only [Category.assoc] using he)

end Hironaka.Geometry.QuotGrassmann
