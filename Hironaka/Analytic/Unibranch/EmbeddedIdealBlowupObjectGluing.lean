import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupOverlap
import Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupRawOpenSource
import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Actual object gluing for the SAME native whole ideal

The preceding source-derived actual unequal-range transitions give native
pullback rotations. FULL raw UP uniqueness proves the cocycle. Existing
native LRS object gluing then constructs the real object and full map.
No reduced inverse-centre replacement or transition/cocycle packet.
Blueprint FIRST: `embedded-ideal-blowup-object-gluing.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupObjectGluing

open Hironaka Hironaka.HolomorphicIdealSheaves
  Hironaka.BlowupSequences Hironaka
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspace
  HironakaSingularSubspaceBlowupLift HironakaSingularModuleSheafStalk
  HironakaNativePulledIdealSheaf HironakaReducedComplexAnalyticSpaces
  HironakaResolutionSpaceComplex SourceReducedComplexSpace EmbeddedBlowup
  EmbeddedIdealBlowupRawOpenSource

noncomputable section

variable {X : SourceReducedComplexSpace} {ι : Type} {n : ι → ℕ}
  {M Y : ι → Type} [∀ i, TopologicalSpace (M i)] [∀ i, TopologicalSpace (Y i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (M i)] [∀ i, IsComplexManifold (n i) (M i)]
  [∀ i, ChartedSpace (ComplexModel (n i)) (Y i)] [∀ i, IsComplexManifold (n i) (Y i)]
  {C W : ∀ i, Set (M i)} {π : ∀ i, Y i → M i}
  (hW : ∀ i, IsComplexAnalyticSubset (n := n i) (W i))
  (hπ : ∀ i, IsBlowupAlong (n i) (C i) (π i))

/-- The SAME actual local strict-transform LRS, retaining the original sheaf. -/
def localObject (i : ι) : LocallyRingedSpace :=
  (EmbeddedIdealBlowupOverlap.localSpace hW hπ i).obj.left

variable (J : ∀ i, ofClosedAnalytic (W i) (hW i) ⟶ X)
  [hj : ∀ i, LocallyRingedSpace.IsOpenImmersion (J i).hom.left]

/-- The SAME full original projection, with only category wrappers forgotten. -/
def localProjection (i : ι) : localObject hW hπ i ⟶ X.obj.left :=
  (EmbeddedIdealBlowupOverlap.localProjection hW hπ J i).hom.left

/-- The literal p-preimage original overlap restriction. -/
def overlapObject (i k : ι) : LocallyRingedSpace :=
  (EmbeddedIdealBlowupOverlap.overlapSpace hW hπ J i k).obj.left

/-- The SAME actual full restriction inclusion. -/
def overlapInclusion (i k : ι) : overlapObject hW hπ J i k ⟶ localObject hW hπ i :=
  (EmbeddedIdealBlowupOverlap.overlapInclusion hW hπ J i k).hom.left

instance overlapInclusion_isOpenImmersion (i k : ι) :
    LocallyRingedSpace.IsOpenImmersion (overlapInclusion hW hπ J i k) :=
  EmbeddedIdealBlowupOverlap.overlapInclusion_isOpenImmersion hW hπ J i k

/-- The actual overlap subtype implies precisely the required point containment. -/
theorem overlap_point_mem (i k : ι) (x : overlapObject hW hπ J i k) :
    (localProjection hW hπ J i).base ((overlapInclusion hW hπ J i k).base x) ∈
      range (J k).hom.left.base := EmbeddedIdealBlowupOverlap.overlap_point_mem hW hπ J i k x

instance overlapInclusion_self_isIso (i : ι) : IsIso (overlapInclusion hW hπ J i i) :=
  EmbeddedIdealBlowupOverlap.overlapInclusion_self_isIso hW hπ J i

variable
  (B : SheafOfModules.{0} (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing X.obj.left.toSheafedSpace.sheaf))
  (hd : ∀ i, W i ⊆ closure (W i \ C i))
  (hJ : ∀ i (y : W i),
    Ideal.map ((actualSubspaceInclusion (n := n i) (W i)).stalkMap y).hom
      (actualWholeSheafStalkIdeal (vanishingIdeal (n := n i) (C i)) y.val) =
        nativePulledIdealStalkIdeal (J i).hom.left B b y)

/-- The constructed original overlap iso's SAME entire raw map. -/
def transition (i k : ι) : overlapObject hW hπ J i k ⟶ overlapObject hW hπ J k i :=
  (EmbeddedIdealBlowupOverlap.transition hW hπ J B b hd hJ i k).hom.left

instance transition_isIso (i k : ι) : IsIso (transition hW hπ J B b hd hJ i k) := by
  change IsIso ((SourceReducedComplexSpace.isoLeft
    (EmbeddedIdealBlowupOverlap.transitionIso hW hπ J B b hd hJ i k)).hom)
  infer_instance

/-- The actual whole transition projection square. -/
theorem transition_over (i k : ι) :
    transition hW hπ J B b hd hJ i k ≫ overlapInclusion hW hπ J k i ≫ localProjection hW hπ J k =
      overlapInclusion hW hπ J i k ≫ localProjection hW hπ J i :=
  congrArg (fun H => H.hom.left) (EmbeddedIdealBlowupOverlap.transition_over hW hπ J B b hd hJ i k)

/-- Self identity for the actual entire map, inherited from its derived original identity. -/
theorem transition_self (i : ι) : transition hW hπ J B b hd hJ i i = 𝟙 _ :=
  congrArg (fun H => H.hom.left) (EmbeddedIdealBlowupOverlap.transition_self hW hπ J B b hd hJ i)

/-- The genuine native pullback triple source, with no SourceSpace packet. -/
def tripleObject (i j k : ι) : LocallyRingedSpace :=
  pullback (overlapInclusion hW hπ J i j) (overlapInclusion hW hπ J i k)

/-- Its actual open immersion into the SAME local strict transform. -/
def tripleInclusion (i j k : ι) : tripleObject hW hπ J i j k ⟶ localObject hW hπ i :=
  pullback.fst (overlapInclusion hW hπ J i j) (overlapInclusion hW hπ J i k) ≫ overlapInclusion hW hπ J i j

instance tripleInclusion_isOpenImmersion (i j k : ι) :
    LocallyRingedSpace.IsOpenImmersion (tripleInclusion hW hπ J i j k) := by
  have hf : LocallyRingedSpace.IsOpenImmersion
      (pullback.fst (overlapInclusion hW hπ J i j) (overlapInclusion hW hπ J i k)) :=
    LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right
      (overlapInclusion hW hπ J i k) (overlapInclusion hW hπ J i j)
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ _ hf _
    (overlapInclusion_isOpenImmersion hW hπ J i j)

private theorem triple_transition_range (i j k : ι) :
    range (pullback.fst (overlapInclusion hW hπ J i j) (overlapInclusion hW hπ J i k) ≫
      transition hW hπ J B b hd hJ i j ≫ overlapInclusion hW hπ J j i).base ⊆
        range (overlapInclusion hW hπ J j k).base := by
  let a := pullback.fst (overlapInclusion hW hπ J i j) (overlapInclusion hW hπ J i k)
  let q := pullback.snd (overlapInclusion hW hπ J i j) (overlapInclusion hW hπ J i k)
  let t := transition hW hπ J B b hd hJ i j
  have heq : (a ≫ t ≫ overlapInclusion hW hπ J j i) ≫ localProjection hW hπ J j =
      (q ≫ overlapInclusion hW hπ J i k) ≫ localProjection hW hπ J i := by
    calc
      _ = a ≫ (t ≫ overlapInclusion hW hπ J j i ≫ localProjection hW hπ J j) := by simp only [Category.assoc]
      _ = a ≫ (overlapInclusion hW hπ J i j ≫ localProjection hW hπ J i) :=
        congrArg (fun u => a ≫ u) (transition_over hW hπ J B b hd hJ i j)
      _ = _ := by rw [← Category.assoc, pullback.condition]
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨(a ≫ t ≫ overlapInclusion hW hπ J j i).base x, ?_⟩, rfl⟩
  change (localProjection hW hπ J j).base ((a ≫ t ≫ overlapInclusion hW hπ J j i).base x) ∈
    range (J k).hom.left.base
  have hp := congrArg (fun H => H.base x) heq
  exact hp.symm ▸ overlap_point_mem hW hπ J i k (q.base x)

/-- The genuine full native triple rotation is internally lifted through
the actual target overlap OI, then the actual native pullback. -/
def tripleTransition (i j k : ι) : tripleObject hW hπ J i j k ⟶ tripleObject hW hπ J j k i := by
  let a := pullback.fst (overlapInclusion hW hπ J i j) (overlapInclusion hW hπ J i k) ≫
    transition hW hπ J B b hd hJ i j
  let b := LocallyRingedSpace.IsOpenImmersion.lift (overlapInclusion hW hπ J j k)
    (a ≫ overlapInclusion hW hπ J j i) (triple_transition_range hW hπ J B b hd hJ i j k)
  exact pullback.lift b a
    (LocallyRingedSpace.IsOpenImmersion.lift_fac (overlapInclusion hW hπ J j k)
      (a ≫ overlapInclusion hW hπ J j i) _)

/-- The full native triple factorization equation. -/
theorem tripleTransition_fac (i j k : ι) :
    tripleTransition hW hπ J B b hd hJ i j k ≫
        pullback.snd (overlapInclusion hW hπ J j k) (overlapInclusion hW hπ J j i) =
      pullback.fst (overlapInclusion hW hπ J i j) (overlapInclusion hW hπ J i k) ≫
        transition hW hπ J B b hd hJ i j := by
  exact pullback.lift_snd _ _ _

/-- Actual triple rotations preserve the SAME full original projection. -/
theorem tripleTransition_over (i j k : ι) :
    tripleTransition hW hπ J B b hd hJ i j k ≫ tripleInclusion hW hπ J j k i ≫
        localProjection hW hπ J j = tripleInclusion hW hπ J i j k ≫ localProjection hW hπ J i := by
  let T := tripleTransition hW hπ J B b hd hJ i j k
  let q : tripleObject hW hπ J j k i ⟶ overlapObject hW hπ J j i :=
    pullback.snd (overlapInclusion hW hπ J j k) (overlapInclusion hW hπ J j i)
  let f : tripleObject hW hπ J i j k ⟶ overlapObject hW hπ J i j :=
    pullback.fst (overlapInclusion hW hπ J i j) (overlapInclusion hW hπ J i k)
  let t := transition hW hπ J B b hd hJ i j
  let rji := overlapInclusion hW hπ J j i
  let rij := overlapInclusion hW hπ J i j
  let Pj := localProjection hW hπ J j
  let Pi := localProjection hW hπ J i
  have hc : tripleInclusion hW hπ J j k i = q ≫ rji := pullback.condition
  have hf : T ≫ q = f ≫ t := tripleTransition_fac hW hπ J B b hd hJ i j k
  have ho : t ≫ rji ≫ Pj = rij ≫ Pi := transition_over hW hπ J B b hd hJ i j
  have hleft : T ≫ tripleInclusion hW hπ J j k i ≫ Pj =
      (T ≫ q) ≫ (rji ≫ Pj) :=
    (congrArg (fun u => T ≫ u ≫ Pj) hc).trans
      ((congrArg (fun u => T ≫ u) (Category.assoc q rji Pj)).trans
        (Category.assoc T q (rji ≫ Pj)).symm)
  have hmid : (T ≫ q) ≫ (rji ≫ Pj) = (f ≫ rij) ≫ Pi :=
    (congrArg (fun u => u ≫ (rji ≫ Pj)) hf).trans
      ((Category.assoc f t (rji ≫ Pj)).trans
        ((congrArg (fun u => f ≫ u) ho).trans (Category.assoc f rij Pi).symm))
  exact hleft.trans hmid

/-- The entire native pullback cocycle follows from the whole-ideal UP
full raw uniqueness on the ACTUAL triple open source, with no incoming cocycle. -/
theorem tripleTransition_cocycle (i j k : ι) :
    tripleTransition hW hπ J B b hd hJ i j k ≫
        tripleTransition hW hπ J B b hd hJ j k i ≫
          tripleTransition hW hπ J B b hd hJ k i j = 𝟙 _ := by
  let a := tripleTransition hW hπ J B b hd hJ i j k
  let middle := tripleTransition hW hπ J B b hd hJ j k i
  let c := tripleTransition hW hπ J B b hd hJ k i j
  let r := tripleInclusion hW hπ J i j k
  have hover : ((a ≫ middle ≫ c) ≫ r) ≫ localProjection hW hπ J i = r ≫ localProjection hW hπ J i := by
    calc
      _ = a ≫ middle ≫ (c ≫ r ≫ localProjection hW hπ J i) := by simp only [Category.assoc]
      _ = a ≫ middle ≫ (tripleInclusion hW hπ J k i j ≫ localProjection hW hπ J k) :=
        congrArg (fun u => a ≫ middle ≫ u) (tripleTransition_over hW hπ J B b hd hJ k i j)
      _ = a ≫ (middle ≫ tripleInclusion hW hπ J k i j ≫ localProjection hW hπ J k) := rfl
      _ = a ≫ (tripleInclusion hW hπ J j k i ≫ localProjection hW hπ J j) :=
        congrArg (fun u => a ≫ u) (tripleTransition_over hW hπ J B b hd hJ j k i)
      _ = r ≫ localProjection hW hπ J i := tripleTransition_over hW hπ J B b hd hJ i j k
  have heq := raw_lift_eq_of_over_X B b (hπ i) (hπ i) (hW i) (hW i) (J i) (J i)
    (hd i) (hJ i) (hJ i) r (hr := tripleInclusion_isOpenImmersion hW hπ J i j k)
    ((a ≫ middle ≫ c) ≫ r) r hover rfl
  have heq' : ((a ≫ middle ≫ c) ≫ r) = r := heq
  change a ≫ middle ≫ c = 𝟙 _
  apply (cancel_mono r).mp
  exact heq'.trans (Category.id_comp r).symm

/-- Actual native OBJECT gluing data; every transition, factorization and
cocycle field is produced from the original chart/blowup geometry. -/
def glueData : LocallyRingedSpace.GlueData where
  J := ι
  U := localObject hW hπ
  V := fun p => overlapObject hW hπ J p.1 p.2
  f := overlapInclusion hW hπ J
  f_id _ := inferInstance
  t := transition hW hπ J B b hd hJ
  t_id := transition_self hW hπ J B b hd hJ
  t' := tripleTransition hW hπ J B b hd hJ
  t_fac := tripleTransition_fac hW hπ J B b hd hJ
  cocycle := tripleTransition_cocycle hW hπ J B b hd hJ
  f_open _ _ := inferInstance

/-- The actual native glued locally ringed object. No global space is input. -/
def glued : LocallyRingedSpace := (glueData hW hπ J B b hd hJ).toGlueData.glued

/-- The native full chart inclusion of the SAME local strict transform. -/
def inclusion (i : ι) : localObject hW hπ i ⟶ glued hW hπ J B b hd hJ :=
  (glueData hW hπ J B b hd hJ).toGlueData.ι i

instance inclusion_isOpenImmersion (i : ι) :
    LocallyRingedSpace.IsOpenImmersion (inclusion hW hπ J B b hd hJ i) :=
  (glueData hW hπ J B b hd hJ).ι_isOpenImmersion i

/-- The full original local projections descend to a full actual LRS map. -/
def projection : glued hW hπ J B b hd hJ ⟶ X.obj.left :=
  Multicoequalizer.desc (glueData hW hπ J B b hd hJ).toGlueData.diagram X.obj.left
    (localProjection hW hπ J) (by
      rintro ⟨i, j⟩
      change overlapInclusion hW hπ J i j ≫ localProjection hW hπ J i =
        (transition hW hπ J B b hd hJ i j ≫ overlapInclusion hW hπ J j i) ≫ localProjection hW hπ J j
      simpa only [Category.assoc] using (transition_over hW hπ J B b hd hJ i j).symm)

/-- The SAME local entire sheaf maps are recovered on every chart. -/
theorem inclusion_projection (i : ι) :
    inclusion hW hπ J B b hd hJ i ≫ projection hW hπ J B b hd hJ = localProjection hW hπ J i := by
  exact Multicoequalizer.π_desc (glueData hW hπ J B b hd hJ).toGlueData.diagram X.obj.left
    (localProjection hW hπ J) _ i

/-- The actual native local charts cover the WHOLE original glued point set. -/
theorem inclusion_jointly_surjective (x : glued hW hπ J B b hd hJ) :
    ∃ (i : ι) (y : localObject hW hπ i), (inclusion hW hπ J B b hd hJ i).base y = x :=
  (glueData hW hπ J B b hd hJ).ι_jointly_surjective x

/-- Original base-chart images are saturated for the actual full projection. -/
theorem preimage_chart_range (i : ι) :
    (projection hW hπ J B b hd hJ).base ⁻¹' range (J i).hom.left.base =
      range (inclusion hW hπ J B b hd hJ i).base := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, y, rfl⟩ := inclusion_jointly_surjective hW hπ J B b hd hJ x
    have hp := congrArg (fun H => H.base y) (inclusion_projection hW hπ J B b hd hJ j)
    have hy : (localProjection hW hπ J j).base y ∈ range (J i).hom.left.base := hp ▸ hx
    let u : overlapObject hW hπ J j i := ⟨y, hy⟩
    refine ⟨(overlapInclusion hW hπ J i j).base ((transition hW hπ J B b hd hJ j i).base u), ?_⟩
    exact congrArg (fun H => H.base u) ((glueData hW hπ J B b hd hJ).toGlueData.glue_condition j i)
  · rintro ⟨y, rfl⟩
    have hp := congrArg (fun H => H.base y) (inclusion_projection hW hπ J B b hd hJ i)
    change (inclusion hW hπ J B b hd hJ i ≫ projection hW hπ J B b hd hJ).base y ∈
      range (J i).hom.left.base
    exact hp.symm ▸ ⟨(strictTransformProjection (hπ i) (hW i).isClosed).base y, rfl⟩

/-- The actual OI and derived saturation identify the LITERAL saturated
open with the SAME local strict-transform point space. -/
def saturatedHomeomorph (i : ι) :
    ((projection hW hπ J B b hd hJ).base ⁻¹' range (J i).hom.left.base) ≃ₜ localObject hW hπ i :=
  ((inclusion_isOpenImmersion hW hπ J B b hd hJ i).base_open.isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (preimage_chart_range hW hπ J B b hd hJ i).symm)).symm

/-- Its inverse is the SAME original native inclusion on points. -/
theorem saturatedHomeomorph_symm_val (i : ι) (y : localObject hW hπ i) :
    ((saturatedHomeomorph hW hπ J B b hd hJ i).symm y).val =
      (inclusion hW hπ J B b hd hJ i).base y := rfl

/-- Saturated local models retain the SAME original point projection. -/
theorem saturatedHomeomorph_projection (i : ι)
    (x : (projection hW hπ J B b hd hJ).base ⁻¹' range (J i).hom.left.base) :
    (localProjection hW hπ J i).base ((saturatedHomeomorph hW hπ J B b hd hJ i) x) =
      (projection hW hπ J B b hd hJ).base x.val := by
  let e := saturatedHomeomorph hW hπ J B b hd hJ i
  have hv : (inclusion hW hπ J B b hd hJ i).base (e x) = x.val := by
    exact congrArg Subtype.val (e.symm_apply_apply x)
  have hp := congrArg (fun H => H.base (e x)) (inclusion_projection hW hπ J B b hd hJ i)
  calc
    _ = (projection hW hπ J B b hd hJ).base
        ((inclusion hW hπ J B b hd hJ i).base (e x)) := hp.symm
    _ = _ := congrArg (projection hW hπ J B b hd hJ).base hv

/-- The actual glued map is surjective whenever the GIVEN original charts
cover X; local surjectivity comes from the ordinary off-centre density. -/
theorem projection_surjective
    (hcover : ∀ x : X.obj.left, ∃ (i : ι) (w : (W i)), (J i).hom.left.base w = x) :
    Function.Surjective (projection hW hπ J B b hd hJ).base := by
  intro x
  obtain ⟨i, w, hw⟩ := hcover x
  obtain ⟨y, hy⟩ := strictTransformMorphism_surjective (hπ i) (hW i) (hd i) w
  refine ⟨(inclusion hW hπ J B b hd hJ i).base y, ?_⟩
  have hp := congrArg (fun H => H.base y) (inclusion_projection hW hπ J B b hd hJ i)
  refine hp.trans ?_
  change (J i).hom.left.base ((strictTransformMorphism (hπ i) (hW i)).hom.left.base y) = x
  rw [hy]
  exact hw

omit hj in
/-- The SAME actual local maps preserve the original scalar maps. -/
theorem localProjection_point (i : ι) :
    localProjection hW hπ J i ≫ X.obj.hom =
      subspacePointMap (n := (n i)) (strictTransform (n i) (π i) (W i)) := by
  exact Over.w (EmbeddedIdealBlowupOverlap.localProjection hW hπ J i).hom

/-- Genuine original analytic local models on the ACTUAL glued LRS object.
Only the exact local-model clause is asserted; no global SC/topology packet. -/
theorem original_analytic_atlas (x : glued hW hπ J B b hd hJ) :
    ∃ (n : ℕ) (U : Opens (ComplexModel n)) (D : Set U),
      IsComplexAnalyticSubset (n := n) D ∧
      ∃ k : (modelOver U D).left ⟶ glued hW hπ J B b hd hJ,
        LocallyRingedSpace.IsOpenImmersion k ∧
        k ≫ (projection hW hπ J B b hd hJ ≫ X.obj.hom) = (modelOver U D).hom ∧
        x ∈ range k.base := by
  obtain ⟨i, y, hy⟩ := inclusion_jointly_surjective hW hπ J B b hd hJ x
  let hS := HironakaEmbeddedResolutionLocal.isComplexAnalyticSubset_strictTransform_of_isBlowupAlong
    (hπ i) (hW i)
  obtain ⟨U, D, hD, k, hk, hkp, z, hzy⟩ := exists_model_chart hS y
  let k₀ : (modelOver U D).left ⟶ localObject hW hπ i := k
  have hk₀ : LocallyRingedSpace.IsOpenImmersion k₀ := hk
  refine ⟨(n i), U, D, hD, k₀ ≫ inclusion hW hπ J B b hd hJ i,
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ k₀ hk₀ _
      (inclusion_isOpenImmersion hW hπ J B b hd hJ i), ?_, z, ?_⟩
  · calc
      _ = k₀ ≫ (inclusion hW hπ J B b hd hJ i ≫ projection hW hπ J B b hd hJ) ≫
          X.obj.hom :=
        (Category.assoc _ _ _).trans (congrArg (fun t => k₀ ≫ t) (Category.assoc _ _ _).symm)
      _ = k₀ ≫ localProjection hW hπ J i ≫ X.obj.hom :=
        congrArg (fun t => k₀ ≫ t ≫ X.obj.hom) (inclusion_projection hW hπ J B b hd hJ i)
      _ = k₀ ≫ subspacePointMap (n := (n i))
          (strictTransform (n i) (π i) (W i)) :=
        congrArg (fun t => k₀ ≫ t) (localProjection_point hW hπ J i)
      _ = _ := hkp
  · change (inclusion hW hπ J B b hd hJ i).base (k.base z) = x
    rw [hzy]
    exact hy

end
end Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupObjectGluing
