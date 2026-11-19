import Hironaka.Geometry.QuotGrassmannPivotNativePrincipalGluing
import Hironaka.Geometry.GrassmannPrincipalLocalizationDetection

/-! The actual global native classifier is surjective on the original unframed quotients. -/

noncomputable section

open scoped Classical TensorProduct
open CategoryTheory AlgebraicGeometry

namespace Hironaka.Geometry.QuotGrassmann

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (ι ν : Type u) [Fintype ι] [Fintype ν] [DecidableEq ι] [DecidableEq ν]

/-- Every SAME original native finite-projective unframed quotient is classified by a genuine
global morphism to the SAME original projective model over the SAME original base. -/
theorem originalNativeGrassmannian_exists_globalInverse
    (N : Module.Grassmannian A (A ⊗[R] ((ι ⊕ ν) → R)) (Fintype.card ι)) :
    ∃ f : Spec (CommRingCat.of A) ⟶ projectiveModel R ι ν,
      f ≫ projectiveStructure R ι ν = Spec.map (CommRingCat.ofHom (algebraMap R A)) ∧
        originalGlobalAffineGrassmannianTensorPoint R ι ν f = N := by
  obtain ⟨f, hf, s, hspan, hs⟩ := originalNativeGrassmannian_exists_principalGluedMorphism
    R A ι ν N
  refine ⟨f, hf, ?_⟩
  apply originalNativeGrassmannian_eq_of_principal_localizations (s : Set A) hspan
  intro g hg
  obtain ⟨p, C, hlocal, hpoint⟩ := hs g hg
  have hn := originalGlobalAffineGrassmannianTensorPoint_map R ι ν
    (A := CommRingCat.of A) (B := CommRingCat.of (Localization.Away g))
    (IsScalarTower.toAlgHom R A (Localization.Away g)) f
  change Module.Grassmannian.map (IsScalarTower.toAlgHom R A (Localization.Away g))
      (originalGlobalAffineGrassmannianTensorPoint R ι ν f) =
    originalGlobalAffineGrassmannianTensorPoint R ι ν
      (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away g))) ≫ f) at hn
  rw [hlocal] at hn
  exact hn.trans hpoint

end Hironaka.Geometry.QuotGrassmann
