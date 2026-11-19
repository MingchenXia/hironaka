import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Full locally ringed morphism descent on the ORIGINAL source open cover

Native locally ringed gluing already supplies the full sheaf-map descent.
This module proves the missing fixed-source comparison: gluing an actual open
cover of the ORIGINAL space gives that same space up to its internally proved
canonical isomorphism. It then transports native descent to the original source.

The cover-gluing construction follows Mathlib's `Scheme.Cover.gluedCover`,
at the genuine locally ringed-space level. No alternate source category or
global comparison-isomorphism hypothesis is introduced.
Blueprint: `hironaka-intrinsic-morphism-gluing.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Hironaka.HironakaIntrinsicMorphismGluing

noncomputable section

universe u

variable {J : Type u} {T : LocallyRingedSpace.{u}}
  (U : J → LocallyRingedSpace.{u}) (j : ∀ i, U i ⟶ T)
  [∀ i, LocallyRingedSpace.IsOpenImmersion (j i)]

private def coverTripleOverlapMap (a b c : J) :
    pullback (pullback.fst (j a) (j b)) (pullback.fst (j a) (j c)) ⟶
      pullback (pullback.fst (j b) (j c)) (pullback.fst (j b) (j a)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp

@[simp, reassoc]
private theorem coverTripleOverlapMap_fst_fst (a b c : J) :
    coverTripleOverlapMap U j a b c ≫ pullback.fst _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta coverTripleOverlapMap
  simp

@[simp, reassoc]
private theorem coverTripleOverlapMap_fst_snd (a b c : J) :
    coverTripleOverlapMap U j a b c ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  delta coverTripleOverlapMap
  simp

@[simp, reassoc]
private theorem coverTripleOverlapMap_snd_fst (a b c : J) :
    coverTripleOverlapMap U j a b c ≫ pullback.snd _ _ ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ pullback.snd _ _ := by
  delta coverTripleOverlapMap
  simp

@[simp, reassoc]
private theorem coverTripleOverlapMap_snd_snd (a b c : J) :
    coverTripleOverlapMap U j a b c ≫ pullback.snd _ _ ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ pullback.fst _ _ := by
  delta coverTripleOverlapMap
  simp

private theorem coverTripleOverlapMap_cocycle (a b c : J) :
    coverTripleOverlapMap U j a b c ≫ coverTripleOverlapMap U j b c a ≫
      coverTripleOverlapMap U j c a b = 𝟙 _ := by
  apply pullback.hom_ext <;> simp_rw [Category.id_comp, Category.assoc]
  · apply pullback.hom_ext <;> simp
  · apply pullback.hom_ext <;> simp [pullback.condition]

/-- Native locally ringed gluing data from the actual pullbacks of an ORIGINAL
family of open immersions. -/
def coverGlueData : LocallyRingedSpace.GlueData.{u} where
  J := J
  U := U
  V := fun p => pullback (j p.1) (j p.2)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id _ := by simp
  t' := coverTripleOverlapMap U j
  t_fac _ _ _ := by apply pullback.hom_ext <;> simp
  cocycle := coverTripleOverlapMap_cocycle U j
  f_open _ _ := inferInstance

/-- The canonical FULL locally ringed map from native cover gluing to the
ORIGINAL covered source. -/
def fromGlued : (coverGlueData U j).toGlueData.glued ⟶ T :=
  Multicoequalizer.desc (coverGlueData U j).toGlueData.diagram T j (by
    rintro ⟨a, b⟩
    change pullback.fst (j a) (j b) ≫ j a =
      ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ j b
    simpa using pullback.condition (f := j a) (g := j b))

@[reassoc (attr := simp)]
theorem ι_fromGlued (i : J) :
    (coverGlueData U j).toGlueData.ι i ≫ fromGlued U j = j i := by
  unfold fromGlued
  exact Multicoequalizer.π_desc (coverGlueData U j).toGlueData.diagram T j _ i

private theorem overlap_chart_condition (a b : J) :
    pullback.fst (j a) (j b) ≫ (coverGlueData U j).toGlueData.ι a =
      pullback.snd (j a) (j b) ≫ (coverGlueData U j).toGlueData.ι b := by
  simpa [coverGlueData, Category.assoc] using
    ((coverGlueData U j).toGlueData.glue_condition a b).symm

private theorem fromGlued_injective : Function.Injective (fromGlued U j).base := by
  intro x y h
  obtain ⟨a, x, rfl⟩ := (coverGlueData U j).ι_jointly_surjective x
  obtain ⟨b, y, rfl⟩ := (coverGlueData U j).ι_jointly_surjective y
  have hxy : (j a).base x = (j b).base y := by
    have ha := congrArg (fun k => k.base x) (ι_fromGlued U j a)
    have hb := congrArg (fun k => k.base y) (ι_fromGlued U j b)
    exact ha.symm.trans (h.trans hb)
  let F := LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget CommRingCat
  let e := (TopCat.pullbackConeIsLimit (j a).base (j b).base).conePointUniqueUpToIso
    (isLimitOfHasPullbackOfPreservesLimit F (j a) (j b))
  let v : (pullback (j a) (j b) : LocallyRingedSpace.{u}) := e.hom ⟨⟨x, y⟩, hxy⟩
  have hfst : (pullback.fst (j a) (j b)).base v = x := by
    change ((e.hom ≫ F.map (pullback.fst (j a) (j b)))
      ⟨⟨x, y⟩, hxy⟩) = x
    erw [IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.left]
    rfl
  have hsnd : (pullback.snd (j a) (j b)).base v = y := by
    change ((e.hom ≫ F.map (pullback.snd (j a) (j b)))
      ⟨⟨x, y⟩, hxy⟩) = y
    erw [IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right]
    rfl
  have hc := congrArg (fun k => k.base v) (overlap_chart_condition U j a b)
  change ((coverGlueData U j).toGlueData.ι a).base
      ((pullback.fst (j a) (j b)).base v) =
    ((coverGlueData U j).toGlueData.ι b).base
      ((pullback.snd (j a) (j b)).base v) at hc
  rwa [hfst, hsnd] at hc

private theorem fromGlued_isOpenMap : IsOpenMap (fromGlued U j).base := by
  intro A hA
  have heq : (fromGlued U j).base '' A =
      ⋃ i, (j i).base '' ((coverGlueData U j).toGlueData.ι i).base ⁻¹' A := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, y, rfl⟩ := (coverGlueData U j).ι_jointly_surjective x
      refine mem_iUnion.mpr ⟨i, y, hx, ?_⟩
      exact (congrArg (fun k => k.base y) (ι_fromGlued U j i)).symm
    · intro ht
      obtain ⟨i, y, hy, rfl⟩ := mem_iUnion.mp ht
      refine ⟨((coverGlueData U j).toGlueData.ι i).base y, hy, ?_⟩
      exact congrArg (fun k => k.base y) (ι_fromGlued U j i)
  rw [heq]
  exact isOpen_iUnion (fun i =>
    (inferInstance : LocallyRingedSpace.IsOpenImmersion (j i)).base_open.isOpenMap _
      (hA.preimage ((coverGlueData U j).toGlueData.ι i).base.hom.continuous))

/-- The native gluing comparison is an ACTUAL isomorphism whenever the original
open immersions cover the original source. -/
theorem fromGlued_isIso (hcover : ∀ t : T, ∃ (i : J) (u : U i), (j i).base u = t) :
    IsIso (fromGlued U j) := by
  have hbase : IsOpenEmbedding (fromGlued U j).base :=
    .of_continuous_injective_isOpenMap (fromGlued U j).base.hom.continuous
      (fromGlued_injective U j) (fromGlued_isOpenMap U j)
  have hsurj : Function.Surjective (fromGlued U j).base := by
    intro t
    obtain ⟨i, u, hu⟩ := hcover t
    refine ⟨((coverGlueData U j).toGlueData.ι i).base u, ?_⟩
    exact (congrArg (fun k => k.base u) (ι_fromGlued U j i)).trans hu
  let : Epi (fromGlued U j).base := (TopCat.epi_iff_surjective _).mpr hsurj
  let : ∀ x, IsIso ((fromGlued U j).stalkMap x) := fun x => by
    obtain ⟨i, u, rfl⟩ := (coverGlueData U j).ι_jointly_surjective x
    have hcomp : IsIso ((((coverGlueData U j).toGlueData.ι i) ≫
        fromGlued U j).stalkMap u) := by
      rw [ι_fromGlued U j i]
      infer_instance
    rw [LocallyRingedSpace.stalkMap_comp] at hcomp
    exact IsIso.of_isIso_comp_right _ (((coverGlueData U j).toGlueData.ι i).stalkMap u)
  let : LocallyRingedSpace.IsOpenImmersion (fromGlued U j) :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso (fromGlued U j) hbase
  exact LocallyRingedSpace.IsOpenImmersion.to_iso (fromGlued U j)

/-- Equality of the FULL original locally ringed morphisms can be checked on
the actual original open cover. -/
theorem hom_ext (hcover : ∀ t : T, ∃ (i : J) (u : U i), (j i).base u = t)
    {Y : LocallyRingedSpace.{u}} (f g : T ⟶ Y)
    (h : ∀ i, j i ≫ f = j i ≫ g) : f = g := by
  let := fromGlued_isIso U j hcover
  apply (cancel_epi (fromGlued U j)).mp
  apply Multicoequalizer.hom_ext (coverGlueData U j).toGlueData.diagram
  intro i
  change (coverGlueData U j).toGlueData.ι i ≫ (fromGlued U j ≫ f) =
    (coverGlueData U j).toGlueData.ι i ≫ (fromGlued U j ≫ g)
  rw [ι_fromGlued_assoc, ι_fromGlued_assoc]
  exact h i

/-- Compatible ORIGINAL local maps produce a unique FULL morphism on the
ORIGINAL source, rather than a morphism only on a manufactured glued object. -/
theorem exists_unique_morphism
    (hcover : ∀ t : T, ∃ (i : J) (u : U i), (j i).base u = t)
    {Y : LocallyRingedSpace.{u}} (f : ∀ i, U i ⟶ Y)
    (hf : ∀ i k, pullback.fst (j i) (j k) ≫ f i =
      pullback.snd (j i) (j k) ≫ f k) :
    ∃! F : T ⟶ Y, ∀ i, j i ≫ F = f i := by
  let := fromGlued_isIso U j hcover
  let d : (coverGlueData U j).toGlueData.glued ⟶ Y :=
    Multicoequalizer.desc (coverGlueData U j).toGlueData.diagram Y f (by
      rintro ⟨i, k⟩
      change pullback.fst (j i) (j k) ≫ f i =
        ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ f k
      simpa using hf i k)
  refine ⟨inv (fromGlued U j) ≫ d, ?_, ?_⟩
  · intro i
    rw [← ι_fromGlued U j i, Category.assoc, IsIso.hom_inv_id_assoc]
    exact Multicoequalizer.π_desc (coverGlueData U j).toGlueData.diagram Y f _ i
  · intro G hG
    apply hom_ext U j hcover
    intro i
    rw [hG i, ← ι_fromGlued U j i, Category.assoc, IsIso.hom_inv_id_assoc]
    exact (Multicoequalizer.π_desc (coverGlueData U j).toGlueData.diagram Y f _ i).symm

/-- The same ORIGINAL-cover construction gives an actual morphism in the
existing slice category. In particular the base can be the actual complex
point; no supplied global structural triangle is required. -/
theorem exists_unique_over
    (hcover : ∀ t : T, ∃ (i : J) (u : U i), (j i).base u = t)
    {Y S : LocallyRingedSpace.{u}} (σT : T ⟶ S) (σY : Y ⟶ S)
    (f : ∀ i, U i ⟶ Y)
    (hf : ∀ i k, pullback.fst (j i) (j k) ≫ f i =
      pullback.snd (j i) (j k) ≫ f k)
    (hp : ∀ i, f i ≫ σY = j i ≫ σT) :
    ∃! F : Over.mk σT ⟶ Over.mk σY, ∀ i, j i ≫ F.left = f i := by
  obtain ⟨F, hF, huniq⟩ := exists_unique_morphism U j hcover f hf
  have hpoint : F ≫ σY = σT := by
    apply hom_ext U j hcover
    intro i
    rw [← Category.assoc, hF i, hp i]
  refine ⟨Over.homMk F hpoint, hF, ?_⟩
  intro G hG
  apply Over.OverMorphism.ext
  exact huniq G.left hG

end

end Hironaka.HironakaIntrinsicMorphismGluing
