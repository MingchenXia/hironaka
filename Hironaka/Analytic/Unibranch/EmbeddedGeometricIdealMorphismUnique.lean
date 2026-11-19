import Hironaka.Analytic.Unibranch.EmbeddedGeometricBlowup
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
import Hironaka.Resolution.HironakaIntrinsicMorphismGluingAnalytic

/-!
# Full raw geometric model maps are unique, without target density

Actual centre-relative source density, SAME whole ideal traces and true
off-centre injectivity give base equality. Analytic charts are DERIVED
along the genuine source OI; native faithfulness gives ENTIRE map equality.
Blueprint FIRST: `embedded-geometric-ideal-morphism-unique.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealMorphismUnique

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  BlowupStrictSubmanifold HironakaActualAnalyticSubspace
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaNativePulledIdealSheaf
  HironakaSingularModuleSheafStalk HironakaReducedComplexAnalyticSpaces
  HironakaIntrinsicMorphismGluingAnalytic SourceReducedComplexSpace
  EmbeddedGeometricBlowup EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- Point-map equality for ANY actual raw source follows from its genuine
good-locus density. No arbitrary-source full sheaf faithfulness is claimed. -/
theorem base_eq_of_dense_projection_eq {d : ℕ} {N T : Type}
    [TopologicalSpace N] [TopologicalSpace T]
    [ChartedSpace (ComplexModel d) N] [IsComplexManifold d N]
    [ChartedSpace (ComplexModel d) T] [IsComplexManifold d T]
    {D V : Set N} {ρ : T → N} (hρ : IsBlowupAlong d D ρ) (hV : IsClosed V)
    {H : LocallyRingedSpace} (F : H ⟶ actualSubspaceLocallyRingedSpace (n := d) V)
    (hd : Dense {x : H | (F.base x).val ∉ D})
    (L₁ L₂ : H ⟶ actualSubspaceLocallyRingedSpace (n := d) (geoStrictTransform ρ D V))
    (h₁ : L₁ ≫ geometricProjection hρ hV = F)
    (h₂ : L₂ ≫ geometricProjection hρ hV = F) : L₁.base = L₂.base := by
  have hproj := h₁.trans h₂.symm
  have heqOn : {x : H | (F.base x).val ∉ D} ⊆ {x | L₁.base x = L₂.base x} := by
    intro x hx
    have hp : ρ (L₁.base x).val = ρ (L₂.base x).val :=
      congrArg (fun t => (t.base x).val) hproj
    have hpF : ρ (L₁.base x).val = (F.base x).val := congrArg (fun t => (t.base x).val) h₁
    have hx₁ : ρ (L₁.base x).val ∉ D := by rw [hpF]; exact hx
    have hx₂ : ρ (L₂.base x).val ∉ D := hp ▸ hx₁
    have hiso := BlowupIsomorphismOff.isIsomorphismOver_compl_of_isBlowupAlong hρ
    exact Subtype.ext (hiso.1.injOn hx₁ hx₂ hp)
  let : T2Space (actualSubspaceLocallyRingedSpace (n := d) (geoStrictTransform ρ D V)).toPresheafedSpace := by
    change T2Space (geoStrictTransform ρ D V)
    infer_instance
  have hc : IsClosed {x : H | L₁.base x = L₂.base x} :=
    isClosed_eq L₁.base.hom.continuous L₂.base.hom.continuous
  have hall : (univ : Set H) ⊆ {x | L₁.base x = L₂.base x} := by
    rw [← hd.closure_eq]
    exact closure_minimal heqOn hc
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro x
  exact hall (mem_univ x)

variable {X : SourceReducedComplexSpace} {ι : Type} {n : ι → ℕ}
  {M Y : ι → Type} [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (Y i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (M i)] [∀ i, IsComplexManifold (n i) (M i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (Y i)] [∀ i, IsComplexManifold (n i) (Y i)]
  {C W : ∀ i, Set (M i)} {π : ∀ i, Y i → M i}
  (hW : ∀ i, IsComplexAnalyticSubset (n := n i) (W i))
  (hπ : ∀ i, IsBlowupAlong (n i) (C i) (π i))
  (J : ∀ i, ofClosedAnalytic (W i) (hW i) ⟶ X)
  [hJopen : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left]
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (hJ : ∀ i (y : W i),
    Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n i) (C i)) y.val) =
        nativePulledIdealStalkIdeal (J i).hom.left B b y)

include hJ

/-- SAME full projection squares determine the ENTIRE map on any genuine
raw geometric source open. No target density/source packet/UP is supplied. -/
theorem raw_hom_ext_of_projection_eq (i j : ι) {H : LocallyRingedSpace}
    (r : H ⟶ actualSubspaceLocallyRingedSpace (n := n i) (geoStrictTransform (π i) (C i) (W i)))
    [hr : LocallyRingedSpace.IsOpenImmersion r]
    (L₁ L₂ : H ⟶ actualSubspaceLocallyRingedSpace (n := n j) (geoStrictTransform (π j) (C j) (W j)))
    (h₁ : L₁ ≫ geometricProjection (hπ j) (hW j).isClosed ≫ (J j).hom.left =
      r ≫ geometricProjection (hπ i) (hW i).isClosed ≫ (J i).hom.left)
    (h₂ : L₂ ≫ geometricProjection (hπ j) (hW j).isClosed ≫ (J j).hom.left =
      r ≫ geometricProjection (hπ i) (hW i).isClosed ≫ (J i).hom.left) : L₁ = L₂ := by
  let pᵢ := geometricProjection (hπ i) (hW i).isClosed
  let pⱼ := geometricProjection (hπ j) (hW j).isClosed
  let F := L₁ ≫ pⱼ
  have hproj : L₁ ≫ pⱼ = L₂ ≫ pⱼ := by
    apply (cancel_mono (J j).hom.left).mp
    exact (Category.assoc _ _ _).trans ((h₁.trans h₂.symm).trans (Category.assoc _ _ _).symm)
  have hdᵢ : Dense {x : H | ((r ≫ pᵢ).base x).val ∉ C i} :=
    (geometricProjection_dense_compl_centre (hπ i) (hW i).isClosed).preimage hr.base_open.isOpenMap
  have hset : {x : H | (F.base x).val ∉ C j} =
      {x : H | ((r ≫ pᵢ).base x).val ∉ C i} := by
    ext x
    have hp : (J j).hom.left.base (F.base x) = (J i).hom.left.base ((r ≫ pᵢ).base x) :=
      congrArg (fun t => t.base x) h₁
    exact not_congr ((chart_mem_nonunitLocus B b hW hπ J hJ j (F.base x)).trans
      ((iff_of_eq (congrArg (fun z => z ∈ nonunitLocus B b) hp)).trans
        (chart_mem_nonunitLocus B b hW hπ J hJ i ((r ≫ pᵢ).base x)).symm))
  have hdF : Dense {x : H | (F.base x).val ∉ C j} := by rw [hset]; exact hdᵢ
  have hbase : L₁.base = L₂.base :=
    base_eq_of_dense_projection_eq (hπ j) (hW j).isClosed F hdF L₁ L₂ rfl hproj.symm
  let σH := r ≫ subspacePointMap (n := n i) (geoStrictTransform (π i) (C i) (W i))
  have hGᵢ : hasAnalyticCharts (Over.mk (subspacePointMap (n := n i)
      (geoStrictTransform (π i) (C i) (W i)))) := by
    refine ⟨(geometricSource (hπ i) (hW i)).property.1,?_,
      (geometricSource (hπ i) (hW i)).property.2.2⟩
    change SecondCountableTopology (geoStrictTransform (π i) (C i) (W i))
    infer_instance
  have hH : hasAnalyticCharts (Over.mk σH) :=
    hasAnalyticCharts_of_openImmersion _ _ hGᵢ r (hj := hr) rfl
  have hpᵢ : pᵢ ≫ (J i).hom.left ≫ X.obj.hom =
      subspacePointMap (n := n i) (geoStrictTransform (π i) (C i) (W i)) := by
    exact (congrArg (fun t => pᵢ ≫ t) (Over.w (J i).hom)).trans
      (geometricProjection_point (hπ i) (hW i).isClosed)
  have hpⱼ : pⱼ ≫ (J j).hom.left ≫ X.obj.hom =
      subspacePointMap (n := n j) (geoStrictTransform (π j) (C j) (W j)) := by
    exact (congrArg (fun t => pⱼ ≫ t) (Over.w (J j).hom)).trans
      (geometricProjection_point (hπ j) (hW j).isClosed)
  have hσ (L : H ⟶ actualSubspaceLocallyRingedSpace (n := n j)
      (geoStrictTransform (π j) (C j) (W j)))
      (h : L ≫ pⱼ ≫ (J j).hom.left = r ≫ pᵢ ≫ (J i).hom.left) :
      L ≫ subspacePointMap (n := n j) (geoStrictTransform (π j) (C j) (W j)) = σH :=
    ((congrArg (fun t => L ≫ t) hpⱼ.symm).trans (Category.assoc _ _ _).symm).trans
      ((congrArg (fun t => t ≫ X.obj.hom) h).trans
        ((Category.assoc _ _ _).trans (congrArg (fun t => r ≫ t) hpᵢ)))
  exact morphism_eq_of_base_eq σH hH L₁ L₂ (hσ L₁ h₁) (hσ L₂ h₂) hbase

end
end Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealMorphismUnique
