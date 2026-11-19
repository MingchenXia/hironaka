import Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspaceOverlap
import Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspaceStalkQuotient
import Hironaka.Resolution.HironakaIntrinsicReducedCentreOpenPullback
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Compactness.Paracompact

/-!
# The reduced analytic closed subspace of an arbitrary ORIGINAL complex space

Ordinary local analyticity internally supplies the centre charts and full
overlap gluing. Native LRS gluing gives the actual object and full inclusion.
Saturation proves a global embedding; the closed analytic image supplies
Hausdorffness and paracompactness on that SAME object. Actual chart stalk
isomorphisms retain the full quotient map and exact intrinsic ideal kernel.

Blueprint FIRST: `original-analytic-closed-subspace.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspace

open Hironaka Hironaka
  HironakaReducedComplexAnalyticSpaces HironakaIntrinsicReducedCentreIdealModel
  HironakaIntrinsicReducedCentreOpenPullback
  OriginalAnalyticClosedSubspaceOverlap OriginalAnalyticClosedSubspaceStalkQuotient

noncomputable section

variable (X : SourceReducedComplexSpace) (C : Set X.obj.left) (hC : X.IsAnalyticSubset C)

/-- Native object gluing of the internally produced original analytic-centre charts. -/
def glued : LocallyRingedSpace := (glueData X C hC).toGlueData.glued

/-- The genuine native full chart inclusion on the SAME local centre object. -/
def chartInclusion (a : X.obj.left) :
    (localObject X C hC a).obj.left ⟶ glued X C hC :=
  (glueData X C hC).toGlueData.ι a

instance chartInclusion_isOpenImmersion (a : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (chartInclusion X C hC a) :=
  (glueData X C hC).ι_isOpenImmersion a

/-- The SAME full local original maps descend through the native multicoequalizer. -/
def projection : glued X C hC ⟶ X.obj.left :=
  Multicoequalizer.desc (glueData X C hC).toGlueData.diagram X.obj.left
    (fun a => (localProjection X C hC a).hom.left) (by
      rintro ⟨a, b⟩
      change (overlapInclusion X C hC a b).hom.left ≫
          (localProjection X C hC a).hom.left =
        ((transition X C hC a b).hom.left ≫ (overlapInclusion X C hC b a).hom.left) ≫
          (localProjection X C hC b).hom.left
      have h := congrArg (fun F => F.hom.left) (transition_over X C hC a b)
      change (transition X C hC a b).hom.left ≫ (overlapInclusion X C hC b a).hom.left ≫
          (localProjection X C hC b).hom.left =
        (overlapInclusion X C hC a b).hom.left ≫ (localProjection X C hC a).hom.left at h
      exact h.symm)

/-- Every entire original local sheaf map is recovered on its native chart. -/
theorem chartInclusion_projection (a : X.obj.left) :
    chartInclusion X C hC a ≫ projection X C hC = (localProjection X C hC a).hom.left := by
  exact Multicoequalizer.π_desc (glueData X C hC).toGlueData.diagram X.obj.left
    (fun a => (localProjection X C hC a).hom.left) _ a

/-- Native charts cover the WHOLE actual glued point set, including empty cases. -/
theorem chartInclusion_jointly_surjective (s : glued X C hC) :
    ∃ (a : X.obj.left) (y : (localObject X C hC a).obj.left),
      (chartInclusion X C hC a).base y = s :=
  (glueData X C hC).ι_jointly_surjective s

/-- The original target chart opens are exactly saturated by the actual centre charts. -/
theorem preimage_chartOpen (a : X.obj.left) :
    (projection X C hC).base ⁻¹' (chartOpen X C hC a : Set X.obj.left) =
      range (chartInclusion X C hC a).base := by
  ext s
  constructor
  · intro hs
    obtain ⟨b, y, rfl⟩ := chartInclusion_jointly_surjective X C hC s
    have hp := congrArg (fun F => F.base y) (chartInclusion_projection X C hC b)
    have hy : (localProjection X C hC b).hom.left.base y ∈ chartOpen X C hC a := hp ▸ hs
    obtain ⟨u, hu⟩ := exists_overlap_lift X C hC b a y hy
    refine ⟨(overlapInclusion X C hC a b).hom.left.base
      ((transition X C hC b a).hom.left.base u), ?_⟩
    have he := congrArg (fun F => F.base u)
      ((glueData X C hC).toGlueData.glue_condition b a)
    change (chartInclusion X C hC a).base ((overlapInclusion X C hC a b).hom.left.base
        ((transition X C hC b a).hom.left.base u)) =
      (chartInclusion X C hC b).base ((overlapInclusion X C hC b a).hom.left.base u) at he
    exact he.trans (congrArg (chartInclusion X C hC b).base hu)
  · rintro ⟨y, rfl⟩
    change (chartInclusion X C hC a ≫ projection X C hC).base y ∈ chartOpen X C hC a
    rw [chartInclusion_projection]
    have hr : (localProjection X C hC a).hom.left.base y ∈
        range (localProjection X C hC a).hom.left.base := ⟨y, rfl⟩
    exact ((localProjection_range X C hC a) ▸ hr).2

/-- The actual full glued inclusion has exactly the ORIGINAL analytic subset as image. -/
theorem projection_range : range (projection X C hC).base = C := by
  ext x
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨a, y, rfl⟩ := chartInclusion_jointly_surjective X C hC s
    change (chartInclusion X C hC a ≫ projection X C hC).base y ∈ C
    rw [chartInclusion_projection]
    have hr : (localProjection X C hC a).hom.left.base y ∈
        range (localProjection X C hC a).hom.left.base := ⟨y, rfl⟩
    exact ((localProjection_range X C hC a) ▸ hr).1
  · intro hx
    have hr : x ∈ range (localProjection X C hC x).hom.left.base := by
      rw [localProjection_range]
      exact ⟨hx, mem_chartOpen_self X C hC x⟩
    obtain ⟨y, hy⟩ := hr
    refine ⟨(chartInclusion X C hC x).base y, ?_⟩
    exact (congrArg (fun F => F.base y) (chartInclusion_projection X C hC x)).trans hy

/-- Global embedding follows from SAME local embeddings and actual chart saturation. -/
theorem projection_isEmbedding : IsEmbedding (projection X C hC).base := by
  apply isEmbedding_of_iSup_eq_top_of_preimage_subset_range
    (projection X C hC).base (projection X C hC).base.hom.continuous
    (chartOpen X C hC) ?_ (fun a => (localObject X C hC a).obj.left)
    (fun a => (chartInclusion X C hC a).base)
    (fun a => (chartInclusion X C hC a).base.hom.continuous) ?_ ?_
  · intro x _hx
    exact Opens.mem_iSup.mpr ⟨x, mem_chartOpen_self X C hC x⟩
  · intro a
    exact (preimage_chartOpen X C hC a).le
  · intro a
    change IsEmbedding (chartInclusion X C hC a ≫ projection X C hC).base
    rw [chartInclusion_projection]
    exact localProjection_isEmbedding X C hC a

/-- Closedness of the ORDINARY analytic centre upgrades the actual global embedding. -/
theorem projection_isClosedEmbedding : IsClosedEmbedding (projection X C hC).base := by
  refine ⟨projection_isEmbedding X C hC, ?_⟩
  rw [projection_range]
  exact hC.isClosed

/-- Genuine original local analytic models on the SAME glued LRS and scalar map. -/
theorem original_analytic_atlas (s : glued X C hC) :
    ∃ (n : ℕ) (U : Opens (ComplexModel n)) (D : Set U),
      IsComplexAnalyticSubset (n := n) D ∧
      ∃ k : (modelOver U D).left ⟶ glued X C hC,
        LocallyRingedSpace.IsOpenImmersion k ∧
        k ≫ (projection X C hC ≫ X.obj.hom) = (modelOver U D).hom ∧ s ∈ range k.base := by
  obtain ⟨a, y, hy⟩ := chartInclusion_jointly_surjective X C hC s
  obtain ⟨n, U, D, hD, k, hk, hkp, z, hzy⟩ := (localObject X C hC a).property.2.2 y
  let : LocallyRingedSpace.IsOpenImmersion k := hk
  refine ⟨n, U, D, hD, k ≫ chartInclusion X C hC a, inferInstance, ?_, z, ?_⟩
  · calc
      _ = k ≫ (chartInclusion X C hC a ≫ projection X C hC) ≫ X.obj.hom := by
        simp only [Category.assoc]
      _ = k ≫ (localProjection X C hC a).hom.left ≫ X.obj.hom := by
        rw [chartInclusion_projection]
      _ = k ≫ (localObject X C hC a).obj.hom :=
        congrArg (fun F => k ≫ F) (Over.w (localProjection X C hC a).hom)
      _ = _ := hkp
  · change (chartInclusion X C hC a).base (k.base z) = s
    rw [hzy]
    exact hy

/-- The SAME actual glued centre object belongs to the EXISTING original category. -/
@[implicit_reducible]
def sourceObject : SourceReducedComplexSpace := by
  letI : T2Space X.obj.left.toPresheafedSpace := X.property.1
  letI : ParacompactSpace X.obj.left.toPresheafedSpace := X.property.2.1
  exact ⟨Over.mk (projection X C hC ≫ X.obj.hom),
    (projection_isClosedEmbedding X C hC).isEmbedding.t2Space,
    (projection_isClosedEmbedding X C hC).paracompactSpace,
    original_analytic_atlas X C hC⟩

/-- Actual full original closed-centre inclusion, with the SAME entire descended map. -/
def inclusion : sourceObject X C hC ⟶ X :=
  ObjectProperty.homMk (Over.homMk (projection X C hC) rfl)

theorem inclusion_range : range (inclusion X C hC).hom.left.base = C :=
  projection_range X C hC

theorem inclusion_isClosedEmbedding : IsClosedEmbedding (inclusion X C hC).hom.left.base :=
  projection_isClosedEmbedding X C hC

/-- EVERY original source stalk is the actual quotient image, via the full native square. -/
theorem inclusion_stalk_surjective (s : (sourceObject X C hC).obj.left) :
    Function.Surjective ((inclusion X C hC).hom.left.stalkMap s) := by
  change Function.Surjective ((projection X C hC).stalkMap s)
  obtain ⟨a, y, rfl⟩ := chartInclusion_jointly_surjective X C hC s
  have hs : Function.Surjective
      ((chartInclusion X C hC a ≫ projection X C hC).stalkMap y) := by
    rw [chartInclusion_projection]
    exact localProjection_stalk_surjective X C hC a y
  rw [LocallyRingedSpace.stalkMap_comp] at hs
  have hi : Function.Injective ((chartInclusion X C hC a).stalkMap y) :=
    (ConcreteCategory.bijective_of_isIso _).1
  intro t
  obtain ⟨r, hr⟩ := hs ((chartInclusion X C hC a).stalkMap y t)
  exact ⟨r, hi hr⟩

private theorem localProjection_stalk_kernel (a : X.obj.left)
    (y : (localObject X C hC a).obj.left) :
    RingHom.ker ((localProjection X C hC a).hom.left.stalkMap y).hom =
      intrinsicCentreStalkRange X.obj.left C ((localProjection X C hC a).hom.left.base y) := by
  let e := localEmbedding X C hC a
  let j := EmbeddedBlowupOverlap.chartMorphism e
  let i := OriginalClosedSubspaceFactorization.inclusion
    (localCentre_analytic X C hC a) e.analytic (localCentre_subset X C hC a)
  have ht : j.hom.left.base ⁻¹' C =
      (Subtype.val : e.carrier → e.ambient) ⁻¹' localCentre X C hC a := by
    change e.toPoint ⁻¹' C = _
    rw [ambientTrace_eq X C hC a]
    ext w
    exact ⟨fun hw => ⟨w.property, hw⟩, fun hw => hw.2⟩
  rw [localProjection_fac]
  change RingHom.ker ((i.hom.left ≫ j.hom.left).stalkMap y).hom = _
  rw [LocallyRingedSpace.stalkMap_comp]
  change RingHom.ker (((i.hom.left.stalkMap y).hom).comp
    (j.hom.left.stalkMap (i.hom.left.base y)).hom) = _
  rw [← RingHom.comap_ker,
    contained_inclusion_stalk_kernel_eq_intrinsicCentreStalkRange]
  have hp := openImmersion_pulled_stalkIdeal_eq j.hom.left C (i.hom.left.base y)
  change Ideal.map (j.hom.left.stalkMap (i.hom.left.base y)).hom
      (intrinsicCentreStalkRange X.obj.left C (j.hom.left.base (i.hom.left.base y))) =
    intrinsicCentreStalkRange _ (j.hom.left.base ⁻¹' C) (i.hom.left.base y) at hp
  rw [ht] at hp
  rw [← hp, Ideal.comap_map_of_bijective _ (ConcreteCategory.bijective_of_isIso _)]
  rfl

/-- The actual global inclusion kernel is EXACTLY the SAME intrinsic whole ideal. -/
theorem inclusion_stalk_kernel (s : (sourceObject X C hC).obj.left) :
    RingHom.ker ((inclusion X C hC).hom.left.stalkMap s).hom =
      intrinsicCentreStalkRange X.obj.left C ((inclusion X C hC).hom.left.base s) := by
  change RingHom.ker ((projection X C hC).stalkMap s).hom =
    intrinsicCentreStalkRange X.obj.left C ((projection X C hC).base s)
  obtain ⟨a, y, rfl⟩ := chartInclusion_jointly_surjective X C hC s
  have hk : RingHom.ker ((chartInclusion X C hC a ≫ projection X C hC).stalkMap y).hom =
      intrinsicCentreStalkRange X.obj.left C
        ((chartInclusion X C hC a ≫ projection X C hC).base y) := by
    rw [chartInclusion_projection]
    exact localProjection_stalk_kernel X C hC a y
  rw [LocallyRingedSpace.stalkMap_comp] at hk
  change RingHom.ker (((chartInclusion X C hC a).stalkMap y).hom.comp
      ((projection X C hC).stalkMap ((chartInclusion X C hC a).base y)).hom) = _ at hk
  rw [RingHom.ker_comp_of_injective _ (ConcreteCategory.bijective_of_isIso _).1] at hk
  exact hk

/-- The literal original quotient-ring dictionary, retaining the SAME actual stalk map. -/
def stalkQuotientEquiv (s : (sourceObject X C hC).obj.left) :
    (X.obj.left.presheaf.stalk ((inclusion X C hC).hom.left.base s)).carrier ⧸
        intrinsicCentreStalkRange X.obj.left C ((inclusion X C hC).hom.left.base s) ≃+*
      ((sourceObject X C hC).obj.left.presheaf.stalk s).carrier :=
  (Ideal.quotEquivOfEq (inclusion_stalk_kernel X C hC s).symm).trans
    (RingHom.quotientKerEquivOfSurjective (inclusion_stalk_surjective X C hC s))

theorem stalkQuotientEquiv_apply_mk (s : (sourceObject X C hC).obj.left)
    (r : (X.obj.left.presheaf.stalk ((inclusion X C hC).hom.left.base s)).carrier) :
    stalkQuotientEquiv X C hC s
      (Ideal.Quotient.mk (intrinsicCentreStalkRange X.obj.left C
        ((inclusion X C hC).hom.left.base s)) r) =
      (inclusion X C hC).hom.left.stalkMap s r := by
  exact (RingHom.quotientKerEquivOfSurjective_apply_mk
    (inclusion_stalk_surjective X C hC s) r)

/-- Ordinary original X and an ordinary analytic subset construct their full
original reduced closed subspace, with every exact original quotient map. -/
theorem exists_original_analytic_closed_subspace (hC : X.IsAnalyticSubset C) :
    ∃ (S : SourceReducedComplexSpace) (i : S ⟶ X),
      range i.hom.left.base = C ∧ IsClosedEmbedding i.hom.left.base ∧
      (∀ s : S.obj.left, Function.Surjective (i.hom.left.stalkMap s)) ∧
      (∀ s : S.obj.left, RingHom.ker (i.hom.left.stalkMap s).hom =
        intrinsicCentreStalkRange X.obj.left C (i.hom.left.base s)) ∧
      ∀ s : S.obj.left,
        ∃ E : (X.obj.left.presheaf.stalk (i.hom.left.base s)).carrier ⧸
            intrinsicCentreStalkRange X.obj.left C (i.hom.left.base s) ≃+*
          (S.obj.left.presheaf.stalk s).carrier,
          ∀ r : (X.obj.left.presheaf.stalk (i.hom.left.base s)).carrier,
            E (Ideal.Quotient.mk (intrinsicCentreStalkRange X.obj.left C
              (i.hom.left.base s)) r) = i.hom.left.stalkMap s r := by
  refine ⟨sourceObject X C hC, inclusion X C hC, inclusion_range X C hC,
    inclusion_isClosedEmbedding X C hC, inclusion_stalk_surjective X C hC,
    inclusion_stalk_kernel X C hC, ?_⟩
  intro s
  exact ⟨stalkQuotientEquiv X C hC s, stalkQuotientEquiv_apply_mk X C hC s⟩

end

end Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspace
