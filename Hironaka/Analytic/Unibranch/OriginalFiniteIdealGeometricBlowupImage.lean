import Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowup
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

/-!
# The exact image of the SAME arbitrary finite-ideal geometric projection

Global source good density, real local off-centre lifting and SAME-p properness
prove image = closure(unit-stalk-image locus), without target density.
Surjectivity iff dense-unit and actual zero-ideal empty source follow.
Blueprint FIRST: `original-finite-ideal-geometric-blowup-image.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowupImage

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaActualAnalyticSubspace HironakaSingularModuleSheafStalk HironakaNativePulledIdealSheaf
  SourceReducedComplexSpace EmbeddedGeometricBlowup EmbeddedIdealBlowupNonunitLocus
  BlowupStrictSubmanifold

noncomputable section

variable {X : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))

/-- The literal entire native target ideal image is the UNIT ideal. -/
abbrev unitLocus : Set X.obj.left :=
  {x | LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤}

namespace Model

variable {ι : Type} {n : ι → ℕ} {M Y : ι → Type}
  [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (Y i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (M i)] [∀ i, IsComplexManifold (n i) (M i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (Y i)] [∀ i, IsComplexManifold (n i) (Y i)]
  {C W : ∀ i, Set (M i)} {π : ∀ i, Y i → M i}
  (hW : ∀ i, IsComplexAnalyticSubset (n := n i) (W i))
  (hπ : ∀ i, IsBlowupAlong (n i) (C i) (π i))
  (J : ∀ i, ofClosedAnalytic (W i) (hW i) ⟶ X)
  [hJopen : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left]
  (hJ : ∀ i (y : W i),
    Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap y).hom
      (HironakaSmoothCentreRealDomainActualSheafStalk.actualWholeSheafStalkIdeal
        (vanishingIdeal (n := n i) (C i)) y.val) =
      nativePulledIdealStalkIdeal (J i).hom.left B b y)
  (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : W i), (J i).hom.left.base w = x)

include hπ hJ in
omit [∀ i, IsComplexManifold (n i) (Y i)] hJopen in
private theorem chart_unit_iff (i : ι) (w : W i) :
    w.val ∉ C i ↔ (J i).hom.left.base w ∈ unitLocus B b := by
  have h := not_congr (chart_mem_nonunitLocus B b hW hπ J hJ i w)
  change w.val ∉ C i ↔ ¬¬((J i).hom.left.base w ∈ unitLocus B b) at h
  exact h.trans not_not

/-- The SAME global source's unit-preimage is dense, derived from literal GEO closures. -/
theorem source_unit_preimage_dense :
    Dense ((EmbeddedGeometricIdealOriginalObject.projectionMorphism hW hπ J B b hJ hcover).hom.left.base ⁻¹'
      unitLocus B b) := by
  change Dense ((EmbeddedGeometricIdealObjectGluing.projection hW hπ J B b hJ).base ⁻¹' unitLocus B b)
  intro y
  obtain ⟨i,z,rfl⟩ := EmbeddedGeometricIdealObjectGluing.inclusion_jointly_surjective hW hπ J B b hJ y
  let k := EmbeddedGeometricIdealObjectGluing.inclusion hW hπ J B b hJ i
  let p := EmbeddedGeometricIdealObjectGluing.projection hW hπ J B b hJ
  let p₀ := geometricProjection (hπ i) (hW i).isClosed
  have hz := geometricProjection_dense_compl_centre (hπ i) (hW i).isClosed z
  have hm := mem_closure_image k.base.hom.continuous.continuousAt hz
  apply closure_mono (fun t ht => ?_) hm
  obtain ⟨w,hw,rfl⟩ := ht
  have hs := congrArg (fun f => f.base w)
    (EmbeddedGeometricIdealObjectGluing.inclusion_projection hW hπ J B b hJ i)
  change p.base (k.base w) ∈ unitLocus B b
  exact hs.symm ▸ (chart_unit_iff B b hW hπ J hJ i (p₀.base w)).mp hw

/-- Properness and actual off-centre lifting give the EXACT global projection image. -/
theorem projection_range :
    range (EmbeddedGeometricIdealOriginalObject.projectionMorphism hW hπ J B b hJ hcover).hom.left.base =
      closure (unitLocus B b) := by
  let p := (EmbeddedGeometricIdealOriginalObject.projectionMorphism hW hπ J B b hJ hcover).hom.left
  have hd := source_unit_preimage_dense B b hW hπ J hJ hcover
  apply Subset.antisymm
  · exact (p.base.hom.continuous.range_subset_closure_image_dense hd).trans
      (closure_mono (image_preimage_subset p.base (unitLocus B b)))
  · have hU : unitLocus B b ⊆ range p.base := by
      intro x hx
      obtain ⟨i,w,hw⟩ := hcover x
      have hwU : (J i).hom.left.base w ∈ unitLocus B b := hw.symm ▸ hx
      have hwC : w.val ∉ C i := (chart_unit_iff B b hW hπ J hJ i w).mpr hwU
      have hwim : w.val ∈ (π i) '' geoStrictTransform (π i) (C i) (W i) := by
        rw [image_geometricSource (hπ i)]
        exact subset_closure ⟨w.property,hwC⟩
      obtain ⟨y,hy,hyp⟩ := hwim
      let z : geoStrictTransform (π i) (C i) (W i) := ⟨y,hy⟩
      refine ⟨(EmbeddedGeometricIdealObjectGluing.inclusion hW hπ J B b hJ i).base z, ?_⟩
      have hs := congrArg (fun f => f.base z)
        (EmbeddedGeometricIdealObjectGluing.inclusion_projection hW hπ J B b hJ i)
      refine hs.trans ?_
      change (J i).hom.left.base ((geometricProjection (hπ i) (hW i).isClosed).base z) = x
      have hpw : (geometricProjection (hπ i) (hW i).isClosed).base z = w := Subtype.ext hyp
      exact (congrArg (J i).hom.left.base hpw).trans hw
    have hp := EmbeddedGeometricIdealOriginalObject.projection_isProperMap hW hπ J B b hJ hcover
    exact closure_minimal hU hp.isClosedMap.isClosed_range

/-- Surjectivity has precisely the genuine dense-unit-locus boundary. -/
theorem projection_surjective_iff :
    Function.Surjective (EmbeddedGeometricIdealOriginalObject.projectionMorphism hW hπ J B b hJ hcover).hom.left.base ↔
      Dense (unitLocus B b) := by
  rw [← Set.range_eq_univ,projection_range B b hW hπ J hJ hcover,dense_iff_closure_eq]

/-- An everywhere-zero ENTIRE target image ideal gives an ACTUAL empty source. -/
theorem source_isEmpty_of_zero
    (hzero : ∀ x : X.obj.left,
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊥) :
    IsEmpty (EmbeddedGeometricIdealOriginalObject.sourceObject hW hπ J B b hJ hcover).obj.left := by
  have hU : unitLocus B b = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    change LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊤ at hx
    let : Nontrivial ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj x) := by
      change Nontrivial (X.obj.left.presheaf.stalk x).carrier
      exact (X.obj.left.isLocalRing x).toNontrivial
    have h1 : (1 : ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj x)) ∈
        LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) := by
      rw [hx]
      exact Submodule.mem_top
    have h10 : (1 : ↑(TopCat.Presheaf.stalk X.obj.left.toSheafedSpace.sheaf.obj x)) = 0 := by
      rw [hzero x] at h1
      exact h1
    exact one_ne_zero h10
  constructor
  intro y
  have hy := mem_range_self (f := (EmbeddedGeometricIdealOriginalObject.projectionMorphism hW hπ J B b hJ hcover).hom.left.base) y
  rw [projection_range B b hW hπ J hJ hcover,hU,closure_empty] at hy
  exact hy

end Model

variable [B.IsFiniteType]

/-- ONLY the ordinary finite-type data, with the SAME original constructed p. -/
theorem projection_range :
    range (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base = closure (unitLocus B b) := by
  unfold OriginalFiniteIdealGeometricBlowup.projectionMorphism
  exact Model.projection_range B b _ _ _ _ _

/-- The ordinary SAME projection is surjective exactly on the proved density boundary. -/
theorem projection_surjective_iff :
    Function.Surjective (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base ↔
      Dense (unitLocus B b) := by
  rw [← Set.range_eq_univ,projection_range B b,dense_iff_closure_eq]

/-- Zero ENTIRE ideal means actual empty ordinary source, no clopen-component removal. -/
theorem source_isEmpty_of_zero
    (hzero : ∀ x : X.obj.left,
      LinearMap.range (stalkInclusionLinearMap X.obj.left.toSheafedSpace.sheaf B b x) = ⊥) :
    IsEmpty (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left := by
  unfold OriginalFiniteIdealGeometricBlowup.sourceObject
  exact Model.source_isEmpty_of_zero B b _ _ _ _ _ hzero

end
end Hironaka.Analytic.Unibranch.OriginalFiniteIdealGeometricBlowupImage
