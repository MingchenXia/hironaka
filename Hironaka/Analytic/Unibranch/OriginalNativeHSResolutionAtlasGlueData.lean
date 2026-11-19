import Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionAtlasTransition
import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-! Concrete LRS GlueData from ONLY ordinary original X. Actual saved histories,
true triple-native dictionary, full rotations/cocycle; no gluing packet.
Blueprint FIRST: original-native-hs-resolution-atlas-glue-data.tex. -/
set_option autoImplicit false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionAtlasGlueData
noncomputable section
open SourceReducedComplexSpace

variable {X : SourceReducedComplexSpace}
local notation "I" => OriginalNativeHSResolutionAtlasChoice.Index X
local notation "Y" => OriginalNativeHSResolutionAtlasChoice.source
local notation "P" => OriginalNativeHSResolutionAtlasChoice.projection
local notation "baseIncl" => OriginalNativeHSResolutionAtlasChoice.baseInclusion
local notation "baseOpen" => OriginalNativeHSResolutionAtlasChoice.openSet

abbrev localObject (i : I) : LocallyRingedSpace := (Y i).obj.left
abbrev overlapObject (i j : I) : LocallyRingedSpace :=
  (OriginalNativeHSResolutionAtlasOverlap.leftSource i j).obj.left
abbrev overlapInclusion (i j : I) : overlapObject i j ⟶ localObject i :=
  (OriginalNativeHSResolutionAtlasOverlap.leftMap i j).hom.left
abbrev localProjection (i : I) : localObject i ⟶ X.obj.left := (P i ≫ baseIncl i).hom.left
abbrev transition (i j : I) : overlapObject i j ⟶ overlapObject j i :=
  (OriginalNativeHSResolutionAtlasTransition.orderedIso i j).hom.hom.left

instance overlapInclusion_isOpenImmersion (i j : I) :
    LocallyRingedSpace.IsOpenImmersion (overlapInclusion i j) :=
  OriginalNativeHSResolutionAtlasOverlap.sourceMap_isOpenImmersion i
    (OriginalNativeHSResolutionAtlasOverlap.overlap i j) (fun _ hx => hx.1)

instance transition_isIso (i j : I) : IsIso (transition i j) := by
  change IsIso (SourceReducedComplexSpace.isoLeft
    (OriginalNativeHSResolutionAtlasTransition.orderedIso i j)).hom
  infer_instance

theorem overlap_square (i j : I) :
    transition i j ≫ overlapInclusion j i ≫ localProjection j =
      overlapInclusion i j ≫ localProjection i :=
  congrArg (fun a => a.hom.left)
    (OriginalNativeHSResolutionAtlasTransition.ordered_original_square i j)

theorem overlap_range (i j : I) : range (overlapInclusion i j).base =
    (localProjection i).base ⁻¹' range (baseIncl j).hom.left.base := by
  rw [OriginalNativeHSResolutionAtlasChoice.baseInclusion_range]
  exact OriginalNativeHSResolutionAtlasOverlap.leftMap_range i j

private theorem overlap_point_mem (i j : I) (y : overlapObject i j) :
    (localProjection i).base ((overlapInclusion i j).base y) ∈ baseOpen j := by
  have h : (overlapInclusion i j).base y ∈ range (overlapInclusion i j).base := ⟨y,rfl⟩
  rw [OriginalNativeHSResolutionAtlasOverlap.leftMap_range] at h
  exact h

/-- Uniqueness is used on the genuine saved-history source, never a raw arbitrary open. -/
private theorem prescribed_raw_end_eq_id (i k : I) (hki : baseOpen k ≤ baseOpen i)
    (a : (OriginalNativeHSResolutionAtlasOverlap.sourceOn i k hki).obj.left ⟶
      (OriginalNativeHSResolutionAtlasOverlap.sourceOn i k hki).obj.left)
    (ha : a ≫ (OriginalNativeHSResolutionAtlasOverlap.projectionOn i k hki ≫ baseIncl k).hom.left =
      (OriginalNativeHSResolutionAtlasOverlap.projectionOn i k hki ≫ baseIncl k).hom.left) : a = 𝟙 _ := by
  let Z := OriginalNativeHSResolutionAtlasOverlap.sourceOn i k hki
  let q := OriginalNativeHSResolutionAtlasOverlap.projectionOn i k hki
  have hs : a ≫ Z.obj.hom = Z.obj.hom := by
    calc
      _ = a ≫ ((q ≫ baseIncl k).hom.left ≫ X.obj.hom) :=
        congrArg (fun b => a ≫ b) (Over.w (q ≫ baseIncl k).hom).symm
      _ = (a ≫ (q ≫ baseIncl k).hom.left) ≫ X.obj.hom := (Category.assoc _ _ _).symm
      _ = (q ≫ baseIncl k).hom.left ≫ X.obj.hom := congrArg (fun b => b ≫ X.obj.hom) ha
      _ = _ := Over.w (q ≫ baseIncl k).hom
  let an : Z ⟶ Z := ObjectProperty.homMk (Over.homMk a hs)
  have hq : an ≫ q = q := by
    let : LocallyRingedSpace.IsOpenImmersion (baseIncl k).hom.left :=
      OriginalNativeHSResolutionAtlasChoice.baseInclusion_isOpenImmersion k
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply (cancel_mono (baseIncl k).hom.left).mp
    exact ha
  have he := OriginalNativeHSResolutionAtlasTransition.prescribed_maps_eq i i k hki hki
    an (𝟙 Z) hq (Category.id_comp q)
  exact congrArg (fun b => b.hom.left) he

instance overlapInclusion_self_isIso (i : I) : IsIso (overlapInclusion i i) := by
  have hs : Function.Surjective (overlapInclusion i i).base := by
    intro y
    have hy : y ∈ range (overlapInclusion i i).base := by
      rw [OriginalNativeHSResolutionAtlasOverlap.leftMap_range]
      exact OriginalNativeHSResolutionAtlasChoice.projection_mem_open i y
    exact hy
  let : Epi (overlapInclusion i i).base := (TopCat.epi_iff_surjective _).mpr hs
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

private theorem sub_projection (i k : I) (hki : baseOpen k ≤ baseOpen i) :
    (OriginalNativeHSResolutionAtlasOverlap.sourceMap i k hki).hom.left ≫ localProjection i =
      (OriginalNativeHSResolutionAtlasOverlap.projectionOn i k hki ≫ baseIncl k).hom.left := by
  have h := OriginalNativeHSResolutionAtlasOverlap.projection_square i k hki
  have hb := OriginalNativeHSResolutionAtlasOverlap.baseMap_square i k hki
  have he := congrArg (fun a => a ≫ baseIncl i) h
  rw [Category.assoc,hb] at he
  exact congrArg (fun a => a.hom.left) he.symm

private theorem self_le (i : I) : baseOpen (OriginalNativeHSResolutionAtlasOverlap.overlap i i) ≤ baseOpen i :=
  fun _ hx => hx.1

theorem transition_self (i : I) : transition i i = 𝟙 _ := by
  apply prescribed_raw_end_eq_id i (OriginalNativeHSResolutionAtlasOverlap.overlap i i) (self_le i)
  have hfull := sub_projection i (OriginalNativeHSResolutionAtlasOverlap.overlap i i) (self_le i)
  rw [← hfull]
  change transition i i ≫ overlapInclusion i i ≫ localProjection i =
    overlapInclusion i i ≫ localProjection i
  exact overlap_square i i

/-- The original triple open is a genuine precompact atlas index. -/
def tripleIndex (i j k : I) : I :=
  OriginalNativeHSResolutionAtlasOverlap.overlap
    (OriginalNativeHSResolutionAtlasOverlap.overlap i j) k

private theorem triple_le (i j k : I) : baseOpen (tripleIndex i j k) ≤ baseOpen i := fun _ hx => hx.1.1

abbrev tripleModel (i j k : I) :=
  OriginalNativeHSResolutionAtlasOverlap.sourceOn i (tripleIndex i j k) (triple_le i j k)

abbrev modelInclusion (i j k : I) : (tripleModel i j k).obj.left ⟶ localObject i :=
  (OriginalNativeHSResolutionAtlasOverlap.sourceMap i (tripleIndex i j k) (triple_le i j k)).hom.left

instance modelInclusion_isOpenImmersion (i j k : I) :
    LocallyRingedSpace.IsOpenImmersion (modelInclusion i j k) :=
  OriginalNativeHSResolutionAtlasOverlap.sourceMap_isOpenImmersion i (tripleIndex i j k) (triple_le i j k)

private theorem model_range (i j k : I) : range (modelInclusion i j k).base =
    (localProjection i).base ⁻¹' (baseOpen (tripleIndex i j k) : Set X.obj.left) :=
  OriginalNativeHSResolutionAtlasOverlap.sourceMap_range i (tripleIndex i j k) (triple_le i j k)

private theorem model_projection (i j k : I) : modelInclusion i j k ≫ localProjection i =
    (OriginalNativeHSResolutionAtlasOverlap.projectionOn i (tripleIndex i j k) (triple_le i j k) ≫
      baseIncl (tripleIndex i j k)).hom.left := by
  exact sub_projection i (tripleIndex i j k) (triple_le i j k)

abbrev tripleObject (i j k : I) : LocallyRingedSpace :=
  pullback (overlapInclusion i j) (overlapInclusion i k)

def tripleInclusion (i j k : I) : tripleObject i j k ⟶ localObject i :=
  pullback.fst (overlapInclusion i j) (overlapInclusion i k) ≫ overlapInclusion i j

instance tripleInclusion_isOpenImmersion (i j k : I) :
    LocallyRingedSpace.IsOpenImmersion (tripleInclusion i j k) := by
  dsimp only [tripleInclusion]
  infer_instance

private theorem triple_range_subset (i j k : I) : range (tripleInclusion i j k).base ⊆
    range (modelInclusion i j k).base := by
  rw [model_range]
  rintro _ ⟨z,rfl⟩
  have hj := overlap_point_mem i j ((pullback.fst (overlapInclusion i j) (overlapInclusion i k)).base z)
  have hk := overlap_point_mem i k ((pullback.snd (overlapInclusion i j) (overlapInclusion i k)).base z)
  have hc := congrArg (fun a => (a ≫ localProjection i).base z)
    (pullback.condition (f := overlapInclusion i j) (g := overlapInclusion i k))
  exact ⟨⟨OriginalNativeHSResolutionAtlasChoice.projection_mem_open i ((tripleInclusion i j k).base z),hj⟩,
    hc.symm ▸ hk⟩

private theorem model_range_left (i j k : I) : range (modelInclusion i j k).base ⊆
    range (overlapInclusion i j).base := by
  rw [model_range,OriginalNativeHSResolutionAtlasOverlap.leftMap_range]
  intro y hy
  exact hy.1.2

private theorem model_range_right (i j k : I) : range (modelInclusion i j k).base ⊆
    range (overlapInclusion i k).base := by
  rw [model_range,OriginalNativeHSResolutionAtlasOverlap.leftMap_range]
  intro y hy
  exact hy.2

private def modelToTriple (i j k : I) : (tripleModel i j k).obj.left ⟶ tripleObject i j k :=
  pullback.lift
    (LocallyRingedSpace.IsOpenImmersion.lift (overlapInclusion i j) (modelInclusion i j k) (model_range_left i j k))
    (LocallyRingedSpace.IsOpenImmersion.lift (overlapInclusion i k) (modelInclusion i j k) (model_range_right i j k))
    ((LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _).trans
      (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _).symm)

private theorem modelToTriple_fac (i j k : I) :
    modelToTriple i j k ≫ tripleInclusion i j k = modelInclusion i j k := by
  dsimp only [tripleInclusion]
  rw [← Category.assoc]
  exact (congrArg (fun a => a ≫ overlapInclusion i j) (pullback.lift_fst _ _ _)).trans
    (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _)

/-- Genuine full LRS dictionary from an actual original native triple source. -/
def tripleModelIso (i j k : I) : (tripleModel i j k).obj.left ≅ tripleObject i j k := by
  let b := LocallyRingedSpace.IsOpenImmersion.lift (modelInclusion i j k)
    (tripleInclusion i j k) (triple_range_subset i j k)
  have hb : b ≫ modelInclusion i j k = tripleInclusion i j k :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _
  refine ⟨modelToTriple i j k,b,?_,?_⟩
  · apply (cancel_mono (modelInclusion i j k)).mp
    rw [Category.assoc,hb,modelToTriple_fac,Category.id_comp]
  · apply (cancel_mono (tripleInclusion i j k)).mp
    rw [Category.assoc,modelToTriple_fac,hb,Category.id_comp]

private theorem tripleModelIso_fac (i j k : I) :
    (tripleModelIso i j k).hom ≫ tripleInclusion i j k = modelInclusion i j k :=
  modelToTriple_fac i j k

private theorem triple_rotation_range (i j k : I) :
    range (pullback.fst (overlapInclusion i j) (overlapInclusion i k) ≫
      transition i j ≫ overlapInclusion j i).base ⊆ range (overlapInclusion j k).base := by
  rw [OriginalNativeHSResolutionAtlasOverlap.leftMap_range]
  rintro _ ⟨z,rfl⟩
  have he : (pullback.fst (overlapInclusion i j) (overlapInclusion i k) ≫
      transition i j ≫ overlapInclusion j i) ≫ localProjection j =
      (pullback.snd (overlapInclusion i j) (overlapInclusion i k) ≫ overlapInclusion i k) ≫ localProjection i := by
    calc
      _ = pullback.fst (overlapInclusion i j) (overlapInclusion i k) ≫
          (transition i j ≫ overlapInclusion j i ≫ localProjection j) := by simp only [Category.assoc]
      _ = pullback.fst (overlapInclusion i j) (overlapInclusion i k) ≫
          (overlapInclusion i j ≫ localProjection i) :=
        congrArg (fun a => pullback.fst (overlapInclusion i j) (overlapInclusion i k) ≫ a) (overlap_square i j)
      _ = _ := by rw [← Category.assoc,pullback.condition]
  have hp := congrArg (fun a => a.base z) he
  change (localProjection j).base
    ((pullback.fst (overlapInclusion i j) (overlapInclusion i k) ≫ transition i j ≫ overlapInclusion j i).base z) ∈ baseOpen k
  have hk : ((pullback.snd (overlapInclusion i j) (overlapInclusion i k) ≫ overlapInclusion i k) ≫ localProjection i).base z ∈ baseOpen k :=
    overlap_point_mem i k ((pullback.snd (overlapInclusion i j) (overlapInclusion i k)).base z)
  exact hp.symm ▸ hk

def tripleTransition (i j k : I) : tripleObject i j k ⟶ tripleObject j k i := by
  let a := pullback.fst (overlapInclusion i j) (overlapInclusion i k) ≫ transition i j
  let b := LocallyRingedSpace.IsOpenImmersion.lift (overlapInclusion j k)
    (a ≫ overlapInclusion j i) (triple_rotation_range i j k)
  exact pullback.lift b a (LocallyRingedSpace.IsOpenImmersion.lift_fac _ _ _)

theorem tripleTransition_fac (i j k : I) :
    tripleTransition i j k ≫ pullback.snd (overlapInclusion j k) (overlapInclusion j i) =
      pullback.fst (overlapInclusion i j) (overlapInclusion i k) ≫ transition i j :=
  pullback.lift_snd _ _ _

theorem tripleTransition_over (i j k : I) :
    tripleTransition i j k ≫ tripleInclusion j k i ≫ localProjection j =
      tripleInclusion i j k ≫ localProjection i := by
  have hc : tripleInclusion j k i =
      pullback.snd (overlapInclusion j k) (overlapInclusion j i) ≫ overlapInclusion j i := pullback.condition
  calc
    _ = (tripleTransition i j k ≫ pullback.snd (overlapInclusion j k) (overlapInclusion j i)) ≫
        overlapInclusion j i ≫ localProjection j := by rw [hc]; simp only [Category.assoc]
    _ = (pullback.fst (overlapInclusion i j) (overlapInclusion i k) ≫ transition i j) ≫
        overlapInclusion j i ≫ localProjection j := congrArg (fun a => a ≫ overlapInclusion j i ≫ localProjection j)
          (tripleTransition_fac i j k)
    _ = _ := by simp only [Category.assoc,overlap_square,tripleInclusion]

theorem tripleTransition_cocycle (i j k : I) :
    tripleTransition i j k ≫ tripleTransition j k i ≫ tripleTransition k i j = 𝟙 _ := by
  let a := tripleTransition i j k ≫ tripleTransition j k i ≫ tripleTransition k i j
  let e := tripleModelIso i j k
  let r := tripleInclusion i j k ≫ localProjection i
  have ha : a ≫ r = r := by
    dsimp only [a,r]
    simp only [Category.assoc,tripleTransition_over]
  have hf : e.hom ≫ r =
      (OriginalNativeHSResolutionAtlasOverlap.projectionOn i (tripleIndex i j k) (triple_le i j k) ≫
        baseIncl (tripleIndex i j k)).hom.left := by
    rw [← Category.assoc,tripleModelIso_fac,model_projection]
  have he : (e.hom ≫ a ≫ e.inv) ≫
      (OriginalNativeHSResolutionAtlasOverlap.projectionOn i (tripleIndex i j k) (triple_le i j k) ≫
        baseIncl (tripleIndex i j k)).hom.left =
      (OriginalNativeHSResolutionAtlasOverlap.projectionOn i (tripleIndex i j k) (triple_le i j k) ≫
        baseIncl (tripleIndex i j k)).hom.left := by
    rw [← hf]
    simp only [Category.assoc,Iso.inv_hom_id_assoc,ha]
  have hid := prescribed_raw_end_eq_id i (tripleIndex i j k) (triple_le i j k) _ he
  apply (cancel_epi e.hom).mp
  apply (cancel_mono e.inv).mp
  simpa only [a,Category.assoc,Category.comp_id,Category.id_comp,Iso.hom_inv_id] using hid

/-- Concrete full gluing data; ordinary original X is the only external input. -/
def glueData (X : SourceReducedComplexSpace) : LocallyRingedSpace.GlueData where
  J := OriginalNativeHSResolutionAtlasChoice.Index X
  U := localObject
  V := fun p => overlapObject p.1 p.2
  f := overlapInclusion
  f_id _ := inferInstance
  t := transition
  t_id := transition_self
  t' := tripleTransition
  t_fac := tripleTransition_fac
  cocycle := tripleTransition_cocycle
  f_open _ _ := inferInstance

end
end Hironaka.Analytic.Unibranch.OriginalNativeHSResolutionAtlasGlueData
