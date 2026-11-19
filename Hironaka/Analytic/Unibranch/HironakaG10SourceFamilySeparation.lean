import Hironaka.Analytic.Unibranch.HironakaG10SourceIdealSeparation

/-! # Separation of the unpowered source ideal family -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10SourceFamilySeparation

open Hironaka HironakaSingularModuleSheafStalk
  HironakaG10ChowArtinReesCentre
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.HironakaG10SourceIdealSeparation

noncomputable section

/-- Algebraic strict-transform ideals are monotone in the transformed ideal. -/
theorem strictIdeal_mono_source {A R : Type*} [CommRing A] [CommRing R]
    (φ : A →+* R) (I J D : Ideal A) (G : R) (hIJ : I ≤ J) :
    strictIdeal φ I D G ≤ strictIdeal φ J D G := by
  apply Ideal.span_mono
  rintro x ⟨k, y, hy, he⟩
  exact ⟨k, y, ⟨hIJ hy.1, hy.2⟩, he⟩

/-- At a sum centre with positive exponent the strict transforms of the
  original source family and the local flattener family are disjoint. -/
theorem source_families_separated_unpowered
    {X Y : SourceReducedComplexSpace} (f : Y ⟶ X) (Z : LocalFlattener f)
    (IS : ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x)) (β : ℕ) (hβ : β ≠ 0)
    (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
    (hDense : Dense {x : X.obj.left | LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
    (hStalk : ∀ x ∈ Z.V, LinearMap.range
      (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = IS x ^ β ⊔ Z.H x)
    (x' : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left)
    (hx : (stepProj B b hDense).hom.left.base x' ∈ Z.V) :
    ¬ (OnStrictTransform (stepProj B b hDense) x'
         (IS ((stepProj B b hDense).hom.left.base x'))
         (IS ((stepProj B b hDense).hom.left.base x') ^ β ⊔
           Z.H ((stepProj B b hDense).hom.left.base x')) ∧
       OnStrictTransform (stepProj B b hDense) x'
         (Z.H ((stepProj B b hDense).hom.left.base x'))
         (IS ((stepProj B b hDense).hom.left.base x') ^ β ⊔
           Z.H ((stepProj B b hDense).hom.left.base x'))) := by
  intro ⟨hIS, hZ⟩
  apply source_families_separated f Z IS β B b hDense hStalk x' hx
  refine ⟨?_, hZ⟩
  intro G hG hD htop
  apply hIS G hG hD
  apply top_le_iff.mp
  rw [← htop]
  exact strictIdeal_mono_source _ _ _ _ _ (Ideal.pow_le_self hβ)

end
end Hironaka.Analytic.Unibranch.HironakaG10SourceFamilySeparation
