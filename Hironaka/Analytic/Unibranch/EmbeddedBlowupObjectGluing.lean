import Hironaka.Analytic.Unibranch.EmbeddedBlowupOverlapUnique
import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Actual gluing of the ORIGINAL local blowup objects

Ordinary indexed original chart/blowup geometry internally produces overlap
transitions, native pullback rotations and their full cocycle. The actual LRS
object and projection then come from native object gluing. No global space,
transition/cocycle or global source topology certificate is supplied.
Blueprint: `embedded-blowup-object-gluing.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedBlowupObjectGluing

open Hironaka Hironaka.BlowupSequences
  Hironaka HironakaActualAnalyticSubspace
  HironakaReducedComplexAnalyticSpaces HironakaResolutionSpaceComplex
  HironakaSingularSubspaceBlowupLift SourceReducedComplexSpace
  EmbeddedBlowup EmbeddedBlowupOpenRestriction EmbeddedBlowupOverlap EmbeddedBlowupOverlapUnique

noncomputable section

variable {X : SourceReducedComplexSpace} {ι : Type} (E : ι → LocalEmbedding X)
  {Y : ι → Type} [∀ i, TopologicalSpace (Y i)]
  [∀ i, ChartedSpace (ComplexModel (E i).dim) (Y i)]
  [∀ i, IsComplexManifold (E i).dim (Y i)]
  {C : ∀ i, Set (E i).ambient} {π : ∀ i, Y i → (E i).ambient}
  (hπ : ∀ i, IsBlowupAlong (E i).dim (C i) (π i))

/-- The SAME literal analytic local strict-transform object. -/
def localObject (i : ι) : LocallyRingedSpace :=
  (ofClosedAnalytic (strictTransform (E i).dim (π i) (E i).carrier)
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      (hπ i) (E i).analytic)).obj.left

/-- The full SAME original local projection to X. -/
def localProjection (i : ι) : localObject E hπ i ⟶ X.obj.left := by
  change actualSubspaceLocallyRingedSpace (n := (E i).dim)
    (strictTransform (E i).dim (π i) (E i).carrier) ⟶ X.obj.left
  exact strictTransformProjection (hπ i) (E i).analytic.isClosed ≫ (E i).map

/-- The literal original p-preimage overlap restriction. -/
def overlapObject (i j : ι) : LocallyRingedSpace :=
  (restrictedClosedAnalytic
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      (hπ i) (E i).analytic) (projectionOpen (hπ i) (E i).analytic (overlapOpen (E i) (E j)))).obj.left

/-- Its SAME actual restriction inclusion. -/
def overlapInclusion (i j : ι) : overlapObject E hπ i j ⟶ localObject E hπ i :=
  (restrictionInclusion
    (HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
      (hπ i) (E i).analytic) (projectionOpen (hπ i) (E i).analytic (overlapOpen (E i) (E j)))).hom.left

instance overlapInclusion_isOpenImmersion (i j : ι) :
    LocallyRingedSpace.IsOpenImmersion (overlapInclusion E hπ i j) :=
  restrictionInclusion_isOpenImmersion _ _

/-- Actual overlap points project into the OTHER original chart image. -/
theorem overlap_point_mem (i j : ι) (x : overlapObject E hπ i j) :
    (localProjection E hπ i).base ((overlapInclusion E hπ i j).base x) ∈ range (E j).toPoint := by
  exact x.property

instance overlapInclusion_self_isIso (i : ι) : IsIso (overlapInclusion E hπ i i) := by
  have hs : Function.Surjective (overlapInclusion E hπ i i).base := by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    exact ⟨_, rfl⟩
  let : Epi (overlapInclusion E hπ i i).base := (TopCat.epi_iff_surjective _).mpr hs
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

variable (hCW : ∀ i, C i ⊆ (E i).carrier)
  (hd : ∀ i, (E i).carrier ⊆ closure ((E i).carrier \ C i))
  (Z : Set X.obj.left)
  (htrace : ∀ i (x : (E i).carrier), x.val ∈ C i ↔ (E i).toPoint x ∈ Z)

/-- The original unique-overlap theorem INTERNALLY produces this full map. -/
def transition (i j : ι) : overlapObject E hπ i j ⟶ overlapObject E hπ j i :=
  (exists_unique_overlap_transition (E i) (E j) (hπ i) (hπ j) (hCW i) (hCW j)
    (hd i) (hd j) (htrace i) (htrace j)).choose.hom.hom.left

instance transition_isIso (i j : ι) : IsIso (transition E hπ hCW hd Z htrace i j) := by
  change IsIso ((SourceReducedComplexSpace.isoLeft
    (exists_unique_overlap_transition (E i) (E j) (hπ i) (hπ j) (hCW i) (hCW j)
      (hd i) (hd j) (htrace i) (htrace j)).choose).hom)
  infer_instance

/-- The entire original over-X transition square, with all sheaf maps. -/
theorem transition_over (i j : ι) :
    transition E hπ hCW hd Z htrace i j ≫ overlapInclusion E hπ j i ≫ localProjection E hπ j =
      overlapInclusion E hπ i j ≫ localProjection E hπ i :=
  congrArg (fun H => H.hom.left)
    (exists_unique_overlap_transition (E i) (E j) (hπ i) (hπ j) (hCW i) (hCW j)
      (hd i) (hd j) (htrace i) (htrace j)).choose_spec.1

/-- The same-index transition is the full original identity, derived by
density and actual morphism faithfulness, not supplied as gluing data. -/
theorem transition_self (i : ι) : transition E hπ hCW hd Z htrace i i = 𝟙 _ := by
  apply (cancel_mono (overlapInclusion E hπ i i)).mp
  have heq := raw_hom_ext_of_original_projection_eq (E i) (E i) (hπ i) (hπ i)
    (hd i) (htrace i) (htrace i) (overlapInclusion E hπ i i)
    (transition E hπ hCW hd Z htrace i i ≫ overlapInclusion E hπ i i)
    (overlapInclusion E hπ i i)
    (by simpa only [localProjection, id_eq, Category.assoc] using transition_over E hπ hCW hd Z htrace i i) rfl
  simpa only [Category.id_comp] using heq

/-- The genuine native pullback triple source, with no SourceSpace packet. -/
def tripleObject (i j k : ι) : LocallyRingedSpace :=
  pullback (overlapInclusion E hπ i j) (overlapInclusion E hπ i k)

/-- Its actual open immersion into the SAME local strict transform. -/
def tripleInclusion (i j k : ι) : tripleObject E hπ i j k ⟶ localObject E hπ i :=
  pullback.fst (overlapInclusion E hπ i j) (overlapInclusion E hπ i k) ≫ overlapInclusion E hπ i j

instance tripleInclusion_isOpenImmersion (i j k : ι) :
    LocallyRingedSpace.IsOpenImmersion (tripleInclusion E hπ i j k) := by
  dsimp only [tripleInclusion]
  infer_instance

private theorem triple_transition_range (i j k : ι) :
    range (pullback.fst (overlapInclusion E hπ i j) (overlapInclusion E hπ i k) ≫
      transition E hπ hCW hd Z htrace i j ≫ overlapInclusion E hπ j i).base ⊆
        range (overlapInclusion E hπ j k).base := by
  let a := pullback.fst (overlapInclusion E hπ i j) (overlapInclusion E hπ i k)
  let b := pullback.snd (overlapInclusion E hπ i j) (overlapInclusion E hπ i k)
  let t := transition E hπ hCW hd Z htrace i j
  have heq : (a ≫ t ≫ overlapInclusion E hπ j i) ≫ localProjection E hπ j =
      (b ≫ overlapInclusion E hπ i k) ≫ localProjection E hπ i := by
    calc
      _ = a ≫ (t ≫ overlapInclusion E hπ j i ≫ localProjection E hπ j) := by simp only [Category.assoc]
      _ = a ≫ (overlapInclusion E hπ i j ≫ localProjection E hπ i) :=
        congrArg (fun u => a ≫ u) (transition_over E hπ hCW hd Z htrace i j)
      _ = _ := by rw [← Category.assoc, pullback.condition]
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨(a ≫ t ≫ overlapInclusion E hπ j i).base x, ?_⟩, rfl⟩
  change (localProjection E hπ j).base ((a ≫ t ≫ overlapInclusion E hπ j i).base x) ∈
    range (E k).toPoint
  have hp := congrArg (fun H => H.base x) heq
  exact hp.symm ▸ overlap_point_mem E hπ i k (b.base x)

/-- The genuine full native triple rotation is internally lifted through
the actual target overlap OI, then the actual native pullback. -/
def tripleTransition (i j k : ι) : tripleObject E hπ i j k ⟶ tripleObject E hπ j k i := by
  let a := pullback.fst (overlapInclusion E hπ i j) (overlapInclusion E hπ i k) ≫
    transition E hπ hCW hd Z htrace i j
  let b := LocallyRingedSpace.IsOpenImmersion.lift (overlapInclusion E hπ j k)
    (a ≫ overlapInclusion E hπ j i) (triple_transition_range E hπ hCW hd Z htrace i j k)
  exact pullback.lift b a
    (LocallyRingedSpace.IsOpenImmersion.lift_fac (overlapInclusion E hπ j k)
      (a ≫ overlapInclusion E hπ j i) _)

/-- The full native triple factorization equation. -/
theorem tripleTransition_fac (i j k : ι) :
    tripleTransition E hπ hCW hd Z htrace i j k ≫
        pullback.snd (overlapInclusion E hπ j k) (overlapInclusion E hπ j i) =
      pullback.fst (overlapInclusion E hπ i j) (overlapInclusion E hπ i k) ≫
        transition E hπ hCW hd Z htrace i j := by
  exact pullback.lift_snd _ _ _

/-- Actual triple rotations preserve the SAME full original projection. -/
theorem tripleTransition_over (i j k : ι) :
    tripleTransition E hπ hCW hd Z htrace i j k ≫ tripleInclusion E hπ j k i ≫
        localProjection E hπ j = tripleInclusion E hπ i j k ≫ localProjection E hπ i := by
  have hc : tripleInclusion E hπ j k i =
      pullback.snd (overlapInclusion E hπ j k) (overlapInclusion E hπ j i) ≫
        overlapInclusion E hπ j i := pullback.condition
  calc
    _ = tripleTransition E hπ hCW hd Z htrace i j k ≫
        (pullback.snd (overlapInclusion E hπ j k) (overlapInclusion E hπ j i) ≫
          overlapInclusion E hπ j i) ≫ localProjection E hπ j := by
      exact congrArg (fun u => tripleTransition E hπ hCW hd Z htrace i j k ≫ u ≫
        localProjection E hπ j) hc
    _ = (tripleTransition E hπ hCW hd Z htrace i j k ≫
        pullback.snd (overlapInclusion E hπ j k) (overlapInclusion E hπ j i)) ≫
          overlapInclusion E hπ j i ≫ localProjection E hπ j := by simp only [Category.assoc]
    _ = (pullback.fst (overlapInclusion E hπ i j) (overlapInclusion E hπ i k) ≫
        transition E hπ hCW hd Z htrace i j) ≫ overlapInclusion E hπ j i ≫
          localProjection E hπ j :=
      congrArg (fun u => u ≫ overlapInclusion E hπ j i ≫ localProjection E hπ j)
        (tripleTransition_fac E hπ hCW hd Z htrace i j k)
    _ = pullback.fst (overlapInclusion E hπ i j) (overlapInclusion E hπ i k) ≫
        (transition E hπ hCW hd Z htrace i j ≫ overlapInclusion E hπ j i ≫
          localProjection E hπ j) := by simp only [Category.assoc]
    _ = pullback.fst (overlapInclusion E hπ i j) (overlapInclusion E hπ i k) ≫
        (overlapInclusion E hπ i j ≫ localProjection E hπ i) :=
      congrArg (fun u => pullback.fst (overlapInclusion E hπ i j) (overlapInclusion E hπ i k) ≫ u)
        (transition_over E hπ hCW hd Z htrace i j)
    _ = _ := (Category.assoc _ _ _).symm

/-- The entire native pullback cocycle follows from original dense-projection
uniqueness on the ACTUAL triple open source, with no incoming cocycle. -/
theorem tripleTransition_cocycle (i j k : ι) :
    tripleTransition E hπ hCW hd Z htrace i j k ≫
        tripleTransition E hπ hCW hd Z htrace j k i ≫
          tripleTransition E hπ hCW hd Z htrace k i j = 𝟙 _ := by
  let a := tripleTransition E hπ hCW hd Z htrace i j k
  let b := tripleTransition E hπ hCW hd Z htrace j k i
  let c := tripleTransition E hπ hCW hd Z htrace k i j
  let r := tripleInclusion E hπ i j k
  have hover : ((a ≫ b ≫ c) ≫ r) ≫ localProjection E hπ i = r ≫ localProjection E hπ i := by
    calc
      _ = a ≫ b ≫ (c ≫ r ≫ localProjection E hπ i) := by simp only [Category.assoc]
      _ = a ≫ b ≫ (tripleInclusion E hπ k i j ≫ localProjection E hπ k) :=
        congrArg (fun u => a ≫ b ≫ u) (tripleTransition_over E hπ hCW hd Z htrace k i j)
      _ = a ≫ (b ≫ tripleInclusion E hπ k i j ≫ localProjection E hπ k) := rfl
      _ = a ≫ (tripleInclusion E hπ j k i ≫ localProjection E hπ j) :=
        congrArg (fun u => a ≫ u) (tripleTransition_over E hπ hCW hd Z htrace j k i)
      _ = r ≫ localProjection E hπ i := tripleTransition_over E hπ hCW hd Z htrace i j k
  have heq := raw_hom_ext_of_original_projection_eq (E i) (E i) (hπ i) (hπ i)
    (hd i) (htrace i) (htrace i) r ((a ≫ b ≫ c) ≫ r) r
    (by simpa only [localProjection, id_eq, Category.assoc] using hover) rfl
  apply (cancel_mono r).mp
  simpa only [Category.id_comp] using heq

/-- Actual native OBJECT gluing data; every transition, factorization and
cocycle field is produced from the original chart/blowup geometry. -/
def glueData : LocallyRingedSpace.GlueData where
  J := ι
  U := localObject E hπ
  V := fun p => overlapObject E hπ p.1 p.2
  f := overlapInclusion E hπ
  f_id _ := inferInstance
  t := transition E hπ hCW hd Z htrace
  t_id := transition_self E hπ hCW hd Z htrace
  t' := tripleTransition E hπ hCW hd Z htrace
  t_fac := tripleTransition_fac E hπ hCW hd Z htrace
  cocycle := tripleTransition_cocycle E hπ hCW hd Z htrace
  f_open _ _ := inferInstance

/-- The actual native glued locally ringed object. No global space is input. -/
def glued : LocallyRingedSpace := (glueData E hπ hCW hd Z htrace).toGlueData.glued

/-- The native full chart inclusion of the SAME local strict transform. -/
def inclusion (i : ι) : localObject E hπ i ⟶ glued E hπ hCW hd Z htrace :=
  (glueData E hπ hCW hd Z htrace).toGlueData.ι i

instance inclusion_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (inclusion E hπ hCW hd Z htrace i) :=
  (glueData E hπ hCW hd Z htrace).ι_isOpenImmersion i

/-- The full original local projections descend to a full actual LRS map. -/
def projection : glued E hπ hCW hd Z htrace ⟶ X.obj.left :=
  Multicoequalizer.desc (glueData E hπ hCW hd Z htrace).toGlueData.diagram X.obj.left
    (localProjection E hπ) (by
      rintro ⟨i, j⟩
      change overlapInclusion E hπ i j ≫ localProjection E hπ i =
        (transition E hπ hCW hd Z htrace i j ≫ overlapInclusion E hπ j i) ≫ localProjection E hπ j
      simpa only [Category.assoc] using (transition_over E hπ hCW hd Z htrace i j).symm)

/-- The SAME local entire sheaf maps are recovered on every chart. -/
theorem inclusion_projection (i : ι) :
    inclusion E hπ hCW hd Z htrace i ≫ projection E hπ hCW hd Z htrace = localProjection E hπ i := by
  exact Multicoequalizer.π_desc (glueData E hπ hCW hd Z htrace).toGlueData.diagram X.obj.left
    (localProjection E hπ) _ i

/-- The actual native local charts cover the WHOLE original glued point set. -/
theorem inclusion_jointly_surjective (x : glued E hπ hCW hd Z htrace) :
    ∃ (i : ι) (y : localObject E hπ i), (inclusion E hπ hCW hd Z htrace i).base y = x :=
  (glueData E hπ hCW hd Z htrace).ι_jointly_surjective x

/-- Original base-chart images are saturated for the actual full projection. -/
theorem preimage_chart_range (i : ι) :
    (projection E hπ hCW hd Z htrace).base ⁻¹' range (E i).toPoint =
      range (inclusion E hπ hCW hd Z htrace i).base := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, y, rfl⟩ := inclusion_jointly_surjective E hπ hCW hd Z htrace x
    have hp := congrArg (fun H => H.base y) (inclusion_projection E hπ hCW hd Z htrace j)
    have hy : (localProjection E hπ j).base y ∈ range (E i).toPoint := hp ▸ hx
    let u : overlapObject E hπ j i := ⟨y, hy⟩
    refine ⟨(overlapInclusion E hπ i j).base ((transition E hπ hCW hd Z htrace j i).base u), ?_⟩
    exact congrArg (fun H => H.base u) ((glueData E hπ hCW hd Z htrace).toGlueData.glue_condition j i)
  · rintro ⟨y, rfl⟩
    have hp := congrArg (fun H => H.base y) (inclusion_projection E hπ hCW hd Z htrace i)
    change (inclusion E hπ hCW hd Z htrace i ≫ projection E hπ hCW hd Z htrace).base y ∈
      range (E i).toPoint
    exact hp.symm ▸ ⟨(strictTransformProjection (hπ i) (E i).analytic.isClosed).base y, rfl⟩

/-- The actual OI and derived saturation identify the LITERAL saturated
open with the SAME local strict-transform point space. -/
def saturatedHomeomorph (i : ι) :
    ((projection E hπ hCW hd Z htrace).base ⁻¹' range (E i).toPoint) ≃ₜ localObject E hπ i :=
  ((inclusion_isOpenImmersion E hπ hCW hd Z htrace i).base_open.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (preimage_chart_range E hπ hCW hd Z htrace i).symm)).symm

/-- Its inverse is the SAME original native inclusion on points. -/
theorem saturatedHomeomorph_symm_val (i : ι) (y : localObject E hπ i) :
    ((saturatedHomeomorph E hπ hCW hd Z htrace i).symm y).val =
      (inclusion E hπ hCW hd Z htrace i).base y := rfl

/-- Saturated local models retain the SAME original point projection. -/
theorem saturatedHomeomorph_projection (i : ι)
    (x : (projection E hπ hCW hd Z htrace).base ⁻¹' range (E i).toPoint) :
    (localProjection E hπ i).base ((saturatedHomeomorph E hπ hCW hd Z htrace i) x) =
      (projection E hπ hCW hd Z htrace).base x.val := by
  let e := saturatedHomeomorph E hπ hCW hd Z htrace i
  have hv : (inclusion E hπ hCW hd Z htrace i).base (e x) = x.val := by
    exact congrArg Subtype.val (e.symm_apply_apply x)
  have hp := congrArg (fun H => H.base (e x)) (inclusion_projection E hπ hCW hd Z htrace i)
  calc
    _ = (projection E hπ hCW hd Z htrace).base
        ((inclusion E hπ hCW hd Z htrace i).base (e x)) := hp.symm
    _ = _ := congrArg (projection E hπ hCW hd Z htrace).base hv

/-- The actual glued map is surjective whenever the GIVEN original charts
cover X; local surjectivity comes from the ordinary off-centre density. -/
theorem projection_surjective
    (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : (E i).carrier), (E i).toPoint w = x) :
    Function.Surjective (projection E hπ hCW hd Z htrace).base := by
  intro x
  obtain ⟨i, w, hw⟩ := hcover x
  obtain ⟨y, hy⟩ := strictTransformMorphism_surjective (hπ i) (E i).analytic (hd i) w
  refine ⟨(inclusion E hπ hCW hd Z htrace i).base y, ?_⟩
  have hp := congrArg (fun H => H.base y) (inclusion_projection E hπ hCW hd Z htrace i)
  refine hp.trans ?_
  change (E i).toPoint ((strictTransformMorphism (hπ i) (E i).analytic).hom.left.base y) = x
  rw [hy]
  exact hw

/-- The SAME actual local maps preserve the original scalar maps. -/
theorem localProjection_point (i : ι) :
    localProjection E hπ i ≫ X.obj.hom =
      subspacePointMap (n := (E i).dim) (strictTransform (E i).dim (π i) (E i).carrier) := by
  change (strictTransformProjection (hπ i) (E i).analytic.isClosed ≫ (E i).map) ≫ X.obj.hom = _
  rw [Category.assoc, (E i).overPoint]
  exact strictTransformProjection_point (hπ i) (E i).analytic.isClosed

/-- Genuine original analytic local models on the ACTUAL glued LRS object.
Only the exact local-model clause is asserted; no global SC/topology packet. -/
theorem original_analytic_atlas (x : glued E hπ hCW hd Z htrace) :
    ∃ (n : ℕ) (U : Opens (ComplexModel n)) (D : Set U),
      IsComplexAnalyticSubset (n := n) D ∧
      ∃ k : (modelOver U D).left ⟶ glued E hπ hCW hd Z htrace,
        LocallyRingedSpace.IsOpenImmersion k ∧
        k ≫ (projection E hπ hCW hd Z htrace ≫ X.obj.hom) = (modelOver U D).hom ∧
        x ∈ range k.base := by
  obtain ⟨i, y, hy⟩ := inclusion_jointly_surjective E hπ hCW hd Z htrace x
  let hS := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
    (hπ i) (E i).analytic
  obtain ⟨U, D, hD, k, hk, hkp, z, hzy⟩ := exists_model_chart hS y
  let : LocallyRingedSpace.IsOpenImmersion k := hk
  refine ⟨(E i).dim, U, D, hD, k ≫ inclusion E hπ hCW hd Z htrace i, inferInstance, ?_, z, ?_⟩
  · calc
      _ = k ≫ (inclusion E hπ hCW hd Z htrace i ≫ projection E hπ hCW hd Z htrace) ≫
          X.obj.hom := by simp only [Category.assoc]
      _ = k ≫ localProjection E hπ i ≫ X.obj.hom := by rw [inclusion_projection]
      _ = k ≫ subspacePointMap (n := (E i).dim)
          (strictTransform (E i).dim (π i) (E i).carrier) :=
        congrArg (fun t => k ≫ t) (localProjection_point E hπ i)
      _ = _ := hkp
  · change (inclusion E hπ hCW hd Z htrace i).base (k.base z) = x
    rw [hzy]
    exact hy

end

end Hironaka.Analytic.Unibranch.EmbeddedBlowupObjectGluing
