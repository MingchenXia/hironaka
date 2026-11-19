import Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealOpenSource
import Hironaka.Analytic.Unibranch.EmbeddedBlowupOpenRestriction

/-!
# Actual original geometric overlaps with NO target density

Literal p-preimages, genuine no-density geometric UP lifts and derived
whole-map inverse identities construct all actual overlap isomorphisms.
No centre containment/equalranges/incoming transition or targethd packet.
Blueprint FIRST: `embedded-geometric-ideal-overlap.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealOverlap

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaSingularSubspaceBlowupLift HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf SourceReducedComplexSpace EmbeddedBlowup
  EmbeddedBlowupOpenRestriction EmbeddedGeometricIdealOpenSource EmbeddedGeometricBlowup BlowupStrictSubmanifold

noncomputable section

variable {X : SourceReducedComplexSpace} {ι : Type} {n : ι → ℕ}
  {M Y : ι → Type} [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (Y i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (M i)] [∀ i, IsComplexManifold (n i) (M i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (Y i)] [∀ i, IsComplexManifold (n i) (Y i)]
  {C W : ∀ i, Set (M i)} {π : ∀ i, Y i → M i}
  (hW : ∀ i, IsComplexAnalyticSubset (n := n i) (W i))
  (hπ : ∀ i, IsBlowupAlong (n i) (C i) (π i))

/-- The SAME literal original analytic GEOMETRIC transform model. -/
def localSpace (i : ι) : SourceReducedComplexSpace := geometricSource (hπ i) (hW i)

include hW hπ in
private theorem geometricAnalytic (i : ι) :
    IsComplexAnalyticSubset (n := n i) (geoStrictTransform (π i) (C i) (W i)) := by
  have hC := AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold (hπ i).1
  simpa only [geoStrictTransform,preimage_sdiff] using
    ClosureDifferenceAnalytic.isComplexAnalyticSubset_closure_diff
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (hπ i).contMDiff (hW i))
      (AnalyticSubsetPreimage.isComplexAnalyticSubset_preimage (hπ i).contMDiff hC)

variable (j : ∀ i, ofClosedAnalytic (W i) (hW i) ⟶ X)
  [hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (j i).hom.left]

/-- The full original projection to the SAME global X. -/
def localProjection (i : ι) : localSpace hW hπ i ⟶ X :=
  geometricProjectionMorphism (hπ i) (hW i) ≫ j i

/-- The literal p-preimage of the OTHER actual original chart image. -/
def overlapOpen (i k : ι) : Opens (geoStrictTransform (π i) (C i) (W i)) :=
  ⟨(localProjection hW hπ j i).hom.left.base ⁻¹' range (j k).hom.left.base,
    (hj k).base_open.isOpen_range.preimage (localProjection hW hπ j i).hom.left.base.hom.continuous⟩

/-- Existing original restriction on the SAME overlap point set and sheaf. -/
def overlapSpace (i k : ι) : SourceReducedComplexSpace :=
  restrictedClosedAnalytic
    (geometricAnalytic hW hπ i)
    (overlapOpen hW hπ j i k)

/-- The full actual original restriction inclusion. -/
def overlapInclusion (i k : ι) : overlapSpace hW hπ j i k ⟶ localSpace hW hπ i :=
  restrictionInclusion
    (geometricAnalytic hW hπ i)
    (overlapOpen hW hπ j i k)

instance overlapInclusion_isOpenImmersion (i k : ι) :
    LocallyRingedSpace.IsOpenImmersion (overlapInclusion hW hπ j i k).hom.left :=
  restrictionInclusion_isOpenImmersion _ _

/-- The point-containment required by the original UP is a subtype fact. -/
theorem overlap_point_mem (i k : ι) (x : (overlapSpace hW hπ j i k).obj.left) :
    (localProjection hW hπ j i).hom.left.base ((overlapInclusion hW hπ j i k).hom.left.base x) ∈
      range (j k).hom.left.base := x.property

instance overlapInclusion_self_isIso (i : ι) : IsIso (overlapInclusion hW hπ j i i).hom.left := by
  have hs : Function.Surjective (overlapInclusion hW hπ j i i).hom.left.base := by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    exact ⟨(geometricProjectionMorphism (hπ i) (hW i)).hom.left.base x, rfl⟩
  let : Epi (overlapInclusion hW hπ j i i).hom.left.base := (TopCat.epi_iff_surjective _).mpr hs
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

variable
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (hJ : ∀ i (y : W i),
    Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n i) (C i)) y.val) =
        nativePulledIdealStalkIdeal (j i).hom.left B b y)

private def localLift (i k : ι) : overlapSpace hW hπ j i k ⟶ localSpace hW hπ k :=
  (exists_unique_lift_over_X B b (hπ i) (hπ k) (hW i) (hW k) (j i) (j k)
    (hJ i) (hJ k) (overlapSpace hW hπ j i k) (overlapInclusion hW hπ j i k)
    (hr := overlapInclusion_isOpenImmersion hW hπ j i k)
    (by rintro _ ⟨x,rfl⟩; exact overlap_point_mem hW hπ j i k x)).choose

private theorem localLift_over (i k : ι) :
    localLift hW hπ j B b hJ i k ≫ localProjection hW hπ j k =
      overlapInclusion hW hπ j i k ≫ localProjection hW hπ j i :=
  (exists_unique_lift_over_X B b (hπ i) (hπ k) (hW i) (hW k) (j i) (j k)
    (hJ i) (hJ k) (overlapSpace hW hπ j i k) (overlapInclusion hW hπ j i k)
    (hr := overlapInclusion_isOpenImmersion hW hπ j i k)
    (by rintro _ ⟨x,rfl⟩; exact overlap_point_mem hW hπ j i k x)).choose_spec.1

private theorem localLift_range (i k : ι) :
    range (localLift hW hπ j B b hJ i k).hom.left.base ⊆
      range (overlapInclusion hW hπ j k i).hom.left.base := by
  rintro _ ⟨x,rfl⟩
  refine ⟨⟨(localLift hW hπ j B b hJ i k).hom.left.base x, ?_⟩, rfl⟩
  change (localProjection hW hπ j k).hom.left.base
    ((localLift hW hπ j B b hJ i k).hom.left.base x) ∈ range (j i).hom.left.base
  have hp := congrArg (fun H => H.hom.left.base x) (localLift_over hW hπ j B b hJ i k)
  exact hp.symm ▸ ⟨(geometricProjectionMorphism (hπ i) (hW i)).hom.left.base
    ((overlapInclusion hW hπ j i k).hom.left.base x), rfl⟩

/-- The actual full original overlap transition; no transition is input. -/
def transition (i k : ι) : overlapSpace hW hπ j i k ⟶ overlapSpace hW hπ j k i := by
  let s := overlapInclusion hW hπ j k i
  let L := localLift hW hπ j B b hJ i k
  let t := LocallyRingedSpace.IsOpenImmersion.lift s.hom.left L.hom.left
    (localLift_range hW hπ j B b hJ i k)
  have ht : t ≫ s.hom.left = L.hom.left := LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  have hσ : t ≫ (overlapSpace hW hπ j k i).obj.hom = (overlapSpace hW hπ j i k).obj.hom := by
    rw [← Over.w s.hom, ← Category.assoc, ht]
    exact Over.w L.hom
  exact ObjectProperty.homMk (Over.homMk t hσ)

private theorem transition_inclusion (i k : ι) :
    transition hW hπ j B b hJ i k ≫ overlapInclusion hW hπ j k i =
      localLift hW hπ j B b hJ i k := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact LocallyRingedSpace.IsOpenImmersion.lift_fac
    (overlapInclusion hW hπ j k i).hom.left (localLift hW hπ j B b hJ i k).hom.left
    (localLift_range hW hπ j B b hJ i k)

/-- The ENTIRE original transition square over the SAME global X. -/
theorem transition_over (i k : ι) :
    transition hW hπ j B b hJ i k ≫ overlapInclusion hW hπ j k i ≫ localProjection hW hπ j k =
      overlapInclusion hW hπ j i k ≫ localProjection hW hπ j i := by
  rw [← Category.assoc, transition_inclusion]
  exact localLift_over hW hπ j B b hJ i k

/-- Inverses are derived by the whole-map UP, not supplied as a packet. -/
theorem transition_comp_reverse (i k : ι) :
    transition hW hπ j B b hJ i k ≫ transition hW hπ j B b hJ k i = 𝟙 _ := by
  let a := transition hW hπ j B b hJ i k
  let c := transition hW hπ j B b hJ k i
  let r := overlapInclusion hW hπ j i k
  have hover : ((a ≫ c) ≫ r) ≫ localProjection hW hπ j i = r ≫ localProjection hW hπ j i := by
    calc
      _ = a ≫ (c ≫ r ≫ localProjection hW hπ j i) := by simp only [Category.assoc]
      _ = a ≫ (overlapInclusion hW hπ j k i ≫ localProjection hW hπ j k) :=
        congrArg (fun t => a ≫ t) (transition_over hW hπ j B b hJ k i)
      _ = _ := transition_over hW hπ j B b hJ i k
  have heq := lift_eq_of_over_X B b (hπ i) (hπ i) (hW i) (hW i) (j i) (j i)
    (hJ i) (hJ i) (overlapSpace hW hπ j i k) r
    (hr := overlapInclusion_isOpenImmersion hW hπ j i k) ((a ≫ c) ≫ r) r
    hover rfl
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono r.hom.left).mp
  exact (congrArg (fun t => t.hom.left) heq).trans (Category.id_comp _).symm

/-- The same-index transition is the full identity. -/
theorem transition_self (i : ι) : transition hW hπ j B b hJ i i = 𝟙 _ := by
  let r := overlapInclusion hW hπ j i i
  have heq := lift_eq_of_over_X B b (hπ i) (hπ i) (hW i) (hW i) (j i) (j i)
    (hJ i) (hJ i) (overlapSpace hW hπ j i i) r
    (hr := overlapInclusion_isOpenImmersion hW hπ j i i)
    (transition hW hπ j B b hJ i i ≫ r) r
    ((Category.assoc _ _ _).trans (transition_over hW hπ j B b hJ i i)) rfl
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono r.hom.left).mp
  exact (congrArg (fun t => t.hom.left) heq).trans (Category.id_comp _).symm

/-- The constructed FULL original overlap isomorphism. -/
def transitionIso (i k : ι) : overlapSpace hW hπ j i k ≅ overlapSpace hW hπ j k i where
  hom := transition hW hπ j B b hJ i k
  inv := transition hW hπ j B b hJ k i
  hom_inv_id := transition_comp_reverse hW hπ j B b hJ i k
  inv_hom_id := transition_comp_reverse hW hπ j B b hJ k i

end
end Hironaka.Analytic.Unibranch.EmbeddedGeometricIdealOverlap
