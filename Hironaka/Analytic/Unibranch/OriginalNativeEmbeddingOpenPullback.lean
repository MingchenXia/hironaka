import Hironaka.Analytic.Unibranch.OriginalNativeSmoothOpenLocality
import Hironaka.Analytic.Unibranch.EmbeddedBlowupOverlap

/-! Actual whole embedding restriction through an ordinary native OPEN immersion.
The ambient trace, reduced quotient lift and full square are derived internally.
Blueprint FIRST: original-native-embedding-open-pullback.tex.
Supporting SAME local-centre restriction; no algorithmic/history packet. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.Analytic.Unibranch.OriginalNativeEmbeddingOpenPullback
noncomputable section
open Hironaka Hironaka SourceReducedComplexSpace
  HironakaReducedComplexAnalyticSpaces OriginalNativeSmoothOpenLocality

variable {X Y : SourceReducedComplexSpace} (e : LocalEmbedding X) (j : Y ⟶ X)

/-- Whole actual carrier trace of the original native open image. -/
structure AmbientTrace where
  openSet : Opens e.ambient
  trace : (Subtype.val : e.carrier → e.ambient) ⁻¹' (openSet : Set e.ambient) =
    e.toPoint ⁻¹' range j.hom.left.base

theorem exists_ambientTrace (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) :
    Nonempty (AmbientTrace e j) := by
  have hs : IsOpen (e.toPoint ⁻¹' range j.hom.left.base) :=
    hj.base_open.isOpen_range.preimage e.isOpenEmbedding_toPoint.continuous
  obtain ⟨t, ht, heq⟩ := isOpen_induced_iff.mp hs
  exact ⟨⟨⟨t, ht⟩, heq⟩⟩

variable (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)

def ambientTrace : AmbientTrace e j := (exists_ambientTrace e j hj).some

def coordinateOpen : Opens (ComplexModel e.dim) :=
  ⟨(Subtype.val : e.ambient → ComplexModel e.dim) '' (ambientTrace e j hj).openSet,
    e.ambient.isOpen.isOpenMap_subtype_val _ (ambientTrace e j hj).openSet.isOpen⟩

theorem coordinateOpen_subset : coordinateOpen e j hj ≤ e.ambient := by
  rintro _ ⟨u, -, rfl⟩
  exact u.property

/-- SAME actual restricted full reduced model and original native map. -/
def restricted : LocalEmbedding X :=
  e.restrict (coordinateOpen e j hj) (coordinateOpen_subset e j hj)

theorem restricted_range : range (restricted e j hj).toPoint ⊆ range j.hom.left.base := by
  rintro _ ⟨z, rfl⟩
  dsimp only [restricted] at z ⊢
  change e.toPoint ⟨Opens.inclusion (coordinateOpen_subset e j hj) z.val, z.property⟩ ∈
    range j.hom.left.base
  have hz : Opens.inclusion (coordinateOpen_subset e j hj) z.val ∈ (ambientTrace e j hj).openSet := by
    obtain ⟨u, hu, heq⟩ := z.val.property
    have h : u = Opens.inclusion (coordinateOpen_subset e j hj) z.val := Subtype.ext heq
    exact h ▸ hu
  exact (Set.ext_iff.mp (ambientTrace e j hj).trace _).mp hz

/-- Full native quotient map, derived from genuine target-open lifting. -/
def nativeLift : ofClosedAnalytic (restricted e j hj).carrier (restricted e j hj).analytic ⟶ Y :=
  (exists_native_open_lift j (EmbeddedBlowupOverlap.chartMorphism (restricted e j hj)) hj
    (restricted e j hj).isOpenImmersion (restricted_range e j hj)).choose

theorem nativeLift_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (nativeLift e j hj).hom.left :=
  (exists_native_open_lift j (EmbeddedBlowupOverlap.chartMorphism (restricted e j hj)) hj
    (restricted e j hj).isOpenImmersion (restricted_range e j hj)).choose_spec.1

theorem nativeLift_square : nativeLift e j hj ≫ j =
    EmbeddedBlowupOverlap.chartMorphism (restricted e j hj) :=
  (exists_native_open_lift j (EmbeddedBlowupOverlap.chartMorphism (restricted e j hj)) hj
    (restricted e j hj).isOpenImmersion (restricted_range e j hj)).choose_spec.2

/-- The ACTUAL original local embedding of the target-open source. -/
def embedding : LocalEmbedding Y where
  dim := e.dim
  ambient := coordinateOpen e j hj
  carrier := (restricted e j hj).carrier
  analytic := (restricted e j hj).analytic
  map := (nativeLift e j hj).hom.left
  isOpenImmersion := nativeLift_isOpenImmersion e j hj
  overPoint := Over.w (nativeLift e j hj).hom

theorem full_square : (embedding e j hj).map ≫ j.hom.left = (restricted e j hj).map :=
  congrArg (fun f => f.hom.left) (nativeLift_square e j hj)

theorem scalar : (embedding e j hj).map ≫ Y.obj.hom =
    (modelOver (embedding e j hj).ambient (embedding e j hj).carrier).hom :=
  (embedding e j hj).overPoint

theorem point_square (c : (embedding e j hj).carrier) :
    j.hom.left.base ((embedding e j hj).toPoint c) = (restricted e j hj).toPoint c :=
  congrArg (fun f => f.base c) (full_square e j hj)

/-- ENTIRE old window over the actual target open, not a pointwise germ certificate. -/
theorem range_dictionary :
    j.hom.left.base ⁻¹' range e.toPoint = range (embedding e j hj).toPoint := by
  ext y
  constructor
  · rintro ⟨c, hc⟩
    have hcA : c.val ∈ (ambientTrace e j hj).openSet :=
      (Set.ext_iff.mp (ambientTrace e j hj).trace c).mpr ⟨y, hc.symm⟩
    let cT : (embedding e j hj).carrier :=
      ⟨⟨c.val.val, ⟨c.val, hcA, rfl⟩⟩, c.property⟩
    refine ⟨cT, hj.base_open.injective ?_⟩
    exact (point_square e j hj cT).trans
      ((e.restrict_toPoint (coordinateOpen e j hj) (coordinateOpen_subset e j hj) cT).trans hc)
  · rintro ⟨c, rfl⟩
    change j.hom.left.base ((embedding e j hj).toPoint c) ∈ range e.toPoint
    have h : (restricted e j hj).toPoint c ∈ range e.toPoint :=
      ⟨⟨Opens.inclusion (coordinateOpen_subset e j hj) c.val, c.property⟩,
        (e.restrict_toPoint (coordinateOpen e j hj) (coordinateOpen_subset e j hj) c).symm⟩
    exact (point_square e j hj c).symm ▸ h

end
end Hironaka.Analytic.Unibranch.OriginalNativeEmbeddingOpenPullback
