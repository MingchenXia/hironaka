import Hironaka.Analytic.Unibranch.HironakaG10ActualBlowupStrictMembership
import Hironaka.Resolution.HironakaG10GeometricStrictIdeal

/-!
# Actual geometric strict points imply algebraic strict membership

The ordinary blowup supplies one genuine local generating section of the
entire pulled centre ideal. Its germs are units off the actual native centre.
The closure argument then puts every divided source-vanishing generator in
the actual new-point maximal ideal. Only this one direction is asserted;
no full ideal-sheaf or radical correspondence is assumed.

Blueprint: `hironaka-g10-geometric-strict-membership.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10GeometricStrictMembership

open Hironaka HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf HironakaIntrinsicReducedCentreOpenPullback
  HironakaG10ChowArtinReesCentre HironakaG10GeometricStrictIdeal
  HironakaG10ChowTrackedDatum EmbeddedIdealBlowupNonunitLocus
  HironakaG10ActualBlowupStrictMembership

noncomputable section

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType]
  (hDense : Dense {x : X.obj.left |
    LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})

/-- Every actual geometric strict point has a real regular exceptional
equation and satisfies the universal algebraic strict-membership predicate.
The ordinary source and centre ideal retain their exact native definitions. -/
theorem exists_equation_and_onStrictTransform_of_mem_closure
    (W : Set X.obj.left)
    (x : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left)
    (hx : x ∈ closure
      ((OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left.base ⁻¹'
        (W \ nonunitLocus B b)))
    (I : Ideal (X.obj.left.presheaf.stalk
      ((OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left.base x)))
    (hI : I ≤ intrinsicCentreStalkRange X.obj.left W
      ((OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left.base x)) :
    let D := LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
      ((OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left.base x))
    ∃ G : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.presheaf.stalk x,
      IsRegular G ∧
      Ideal.map ((OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left.stalkMap x).hom D =
        Ideal.span {G} ∧
      strictIdeal ((OriginalFiniteIdealBlowup.projectionMorphism B b hDense).hom.left.stalkMap x).hom
          I D G ≤
        IsLocalRing.maximalIdeal
          ((OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.presheaf.stalk x) ∧
      OnStrictTransform (OriginalFiniteIdealBlowup.projectionMorphism B b hDense) x I D := by
  dsimp only
  let σ := OriginalFiniteIdealBlowup.projectionMorphism B b hDense
  let D := LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b
    (σ.hom.left.base x))
  obtain ⟨U,hxU,s,hs⟩ := exists_local_projection_strict_criterion B b hDense x
  have hunit : ∀ (y : (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left)
      (hy : y ∈ U), y ∉ σ.hom.left.base ⁻¹' nonunitLocus B b →
      IsUnit ((OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.presheaf.germ U y hy s.val) := by
    intro y hy hyE
    have hrange : LinearMap.range
        (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b (σ.hom.left.base y)) = ⊤ :=
      not_not.mp hyE
    have hspan := (hs y hy).2.1
    apply Ideal.span_singleton_eq_top.mp
    exact hspan.symm.trans
      ((congrArg (Ideal.map (σ.hom.left.stalkMap y).hom) hrange).trans (Ideal.map_top _))
  have hx' : x ∈ closure (σ.hom.left.base ⁻¹' W \
      σ.hom.left.base ⁻¹' nonunitLocus B b) := hx
  have hproper := strictIdeal_le_maximal_of_mem_closure σ.hom.left W
    (σ.hom.left.base ⁻¹' nonunitLocus B b) x hx' U hxU s.val hunit I D hI
  have hnot : strictIdeal (σ.hom.left.stalkMap x).hom I D
      ((OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.presheaf.germ U x hxU s.val) ≠ ⊤ := by
    intro htop
    have hmax : (⊤ : Ideal
        ((OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.presheaf.stalk x)) ≤
        IsLocalRing.maximalIdeal
          ((OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.presheaf.stalk x) := htop ▸ hproper
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hmax)
  exact ⟨_,(hs x hxU).1,(hs x hxU).2.1,hproper,((hs x hxU).2.2 I).mpr hnot⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10GeometricStrictMembership
