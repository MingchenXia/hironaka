import Hironaka.Analytic.Unibranch.HironakaG10GermFlattenerSquareTransport
import Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
import Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
import Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum

/-! # Transport of a local flattener away from the blowup centre -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry

namespace Hironaka.Analytic.Unibranch.HironakaG10DisjointFlattenerTransport

open Hironaka HironakaG10PNIdealFamily HironakaG10HirIdealGerms
  HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10GermFlattenerSquareTransport
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.HironakaG10ChowNativeIsoCriterion
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- Local finite generation on a set pulls back on its full inverse image. -/
theorem isLocallyFinitelyGeneratedOn_pull {X Y : LocallyRingedSpace.{0}} (f : Y ⟶ X)
    (V : Set X) (J : ∀ x : X, Ideal (X.presheaf.stalk x))
    (hJ : IsLocallyFinitelyGeneratedOn X V J) :
    IsLocallyFinitelyGeneratedOn Y (f.base ⁻¹' V) (pullFamily f J) := by
  intro y hy
  obtain ⟨W,hyW,r,s,hs⟩ := hJ (f.base y) hy
  refine ⟨(Opens.map f.base).obj W,hyW,r,fun i => f.c.app (op W) (s i),?_⟩
  intro y' hy' hyV
  rw [pullFamily, hs (f.base y') hy' hyV, Ideal.map_span, ← Set.range_comp]
  exact congrArg Ideal.span (congrArg Set.range
    (funext fun i => LocallyRingedSpace.stalkMap_germ_apply f W y' hy' (s i)))

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf)) [B.IsFiniteType]
  (hDense : Dense {x : X.obj.left |
    LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤})
  (f : Y ⟶ X) (Z : LocalFlattener f)

/-- A local flattener pulls back to the actual strict-transform family when
the blowup centre is disjoint from its support. -/
def disjointTransport (hdisj : Disjoint (nonunitLocus B b) Z.support) :
    LocalFlattener (strictP B b hDense f) where
  V := (stepProj B b hDense).hom.left.base ⁻¹' Z.V
  isOpen := Z.isOpen.preimage (stepProj B b hDense).hom.left.base.hom.continuous
  H := pullFamily (stepProj B b hDense).hom.left Z.H
  fg := isLocallyFinitelyGeneratedOn_pull (stepProj B b hDense).hom.left Z.V Z.H Z.fg
  flattener := by
    intro x' hxV hne
    let σ := stepProj B b hDense
    let p := strictP B b hDense f
    let q := strictQ B b f
    have hneZ : Z.H (σ.hom.left.base x') ≠ ⊤ := by
      intro htop
      apply hne
      change Ideal.map (σ.hom.left.stalkMap x').hom (Z.H (σ.hom.left.base x')) = ⊤
      rw [htop, Ideal.map_top]
    have hxZ : σ.hom.left.base x' ∈ Z.support := ⟨hxV,hneZ⟩
    have hxoff : σ.hom.left.base x' ∉ nonunitLocus B b :=
      fun h => Set.disjoint_left.mp hdisj h hxZ
    have hxE : x' ∉ stepExcep B b hDense := hxoff
    have hσ : IsIso (σ.hom.left.stalkMap x') :=
      isIso_stalkMap_of_isIsoOver (stepProj_isIsoOver B b hDense) x' hxoff
    have hq : ∀ y' : (strictSource B b f).obj.left, p.hom.left.base y' = x' →
        IsIso (q.hom.left.stalkMap y') := by
      intro y' hy'
      apply isIso_stalkMap_of_isOpenImmersionOn (strict_openImmersionOn B b hDense f) y'
      change p.hom.left.base y' ∉ stepExcep B b hDense
      simpa only [hy'] using hxE
    have hcover : ∀ y : Y.obj.left, f.hom.left.base y = σ.hom.left.base x' →
        ∃ y' : (strictSource B b f).obj.left, p.hom.left.base y' = x' ∧ q.hom.left.base y' = y :=
      fun y hy => strict_covers B b hDense f y x' hxE hy
    exact isGermFlattenerAt_of_isomorphic_square f σ p q (strictP_comp B b hDense f) x'
      hσ hq hcover (Z.H (σ.hom.left.base x')) (Z.flattener _ hxV hneZ)

/-- The transported support is exactly the inverse image of the original
flattener support under the actual blowup projection. -/
theorem disjointTransport_support (hdisj : Disjoint (nonunitLocus B b) Z.support) :
    (disjointTransport B b hDense f Z hdisj).support =
      (stepProj B b hDense).hom.left.base ⁻¹' Z.support := by
  ext x'
  have hX : IsLocalRing (X.obj.left.presheaf.stalk ((stepProj B b hDense).hom.left.base x')) :=
    X.obj.left.isLocalRing _
  have hX' : IsLocalRing ((OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.presheaf.stalk x') :=
    (OriginalFiniteIdealBlowup.sourceObject B b hDense).obj.left.isLocalRing x'
  change (_ ∧ Ideal.map ((stepProj B b hDense).hom.left.stalkMap x').hom
    (Z.H ((stepProj B b hDense).hom.left.base x')) ≠ ⊤) ↔
      (_ ∧ Z.H ((stepProj B b hDense).hom.left.base x') ≠ ⊤)
  exact and_congr_right fun _ => not_congr (local_map_ideal_eq_top_iff
    ((stepProj B b hDense).hom.left.stalkMap x').hom _)

/-- The support of the transported local flattener agrees with the
existing tracked strict-transform set for that flattener. -/
theorem disjointTransport_support_eq_tracked
    (hdisj : Disjoint (nonunitLocus B b) Z.support) (d : TrackedDatum X) (i : Fin d.q)
    (hd : d.Z i = Z.support) :
    (disjointTransport B b hDense f Z hdisj).support = (d.transport B b hDense f).Z i := by
  rw [disjointTransport_support]
  ext x'
  constructor
  · intro hx
    have hxZ : (stepProj B b hDense).hom.left.base x' ∈ Z.support := hx
    have hxD : (stepProj B b hDense).hom.left.base x' ∈ d.Z i := hd.symm ▸ hxZ
    have hxoff : (stepProj B b hDense).hom.left.base x' ∉ nonunitLocus B b :=
      fun h => Set.disjoint_left.mp hdisj h hxZ
    exact mem_transport_of_not_mem_nonunitLocus B b hDense f d i x' hxD hxoff
  · intro hx
    change (stepProj B b hDense).hom.left.base x' ∈ Z.support
    exact hd ▸ hx.1

end

end Hironaka.Analytic.Unibranch.HironakaG10DisjointFlattenerTransport
