import Hironaka.Resolution.Algebraic.ActualClopenPaddingRefinement

/-!
# Actual global padded maps with both original projection and zero identities

Source-first proof: `actual-clopen-padded-map-20261102.tex`.
Original disjoint partitions and genuine injected coordinates derive the
assembled smooth/SURJ map; no desired map/history geometry is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u

namespace Hironaka.Resolution.Algebraic.ActualClopenPaddedMap

noncomputable section
open ActualClopenPaddingRefinement ActualAffineCoordinateForgetting

def partitionZero {ι : Type} {X : Scheme.{u}} (U : ι → X.Opens) (A : ι → Type u)
    (hc : (⨆ i, U i) = ⊤) (hd : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X))) :
    X ⟶ ∐ sourcePiece U A := by
  have := partitionDesc_isIso U hc hd
  exact inv (partitionDesc U) ≫ Limits.Sigma.map (fun i => AffineSpace.homOfVector (𝟙 (U i).toScheme) (fun _ : A i => 0))

theorem partitionZero_piece {ι : Type} {X : Scheme.{u}} (U : ι → X.Opens) (A : ι → Type u)
    (hc : (⨆ i, U i) = ⊤) (hd : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X))) (i : ι) :
    (U i).ι ≫ partitionZero U A hc hd =
      AffineSpace.homOfVector (𝟙 (U i).toScheme) (fun _ : A i => 0) ≫ Sigma.ι (sourcePiece U A) i := by
  have := partitionDesc_isIso U hc hd
  have hz : partitionDesc U ≫ partitionZero U A hc hd =
      Limits.Sigma.map (fun i => AffineSpace.homOfVector (𝟙 (U i).toScheme) (fun _ : A i => 0)) := by
    rw [partitionZero, IsIso.hom_inv_id_assoc]
  calc
    (U i).ι ≫ partitionZero U A hc hd =
        (Sigma.ι (fun i => (U i).toScheme) i ≫ partitionDesc U) ≫ partitionZero U A hc hd := by
      rw [partitionDesc, Sigma.ι_desc]
    _ = _ := by
      rw [Category.assoc, hz, Sigma.ι_map]
      rfl

theorem partitionZero_projection {ι : Type} {X : Scheme.{u}} (U : ι → X.Opens) (A : ι → Type u)
    (hc : (⨆ i, U i) = ⊤) (hd : Pairwise (fun i j => Disjoint (U i : Set X) (U j : Set X))) :
    partitionZero U A hc hd ≫ sourceProjection U A = 𝟙 X := by
  have := partitionDesc_isIso U hc hd
  apply (cancel_epi (partitionDesc U)).mp
  apply Sigma.hom_ext
  intro i
  rw [← Category.assoc, ← Category.assoc, partitionDesc, Sigma.ι_desc,
    partitionZero_piece, Category.assoc, sourceProjection, Sigma.ι_desc,
    ← Category.assoc, AffineSpace.homOfVector_over, Category.id_comp,
    Category.comp_id, Sigma.ι_desc]

variable {ι κ : Type} {X Y : Scheme.{u}} (U : ι → Y.Opens) (V : κ → X.Opens) (f : Y ⟶ X)
variable (A : ι → Type u) (B : κ → Type u) (keep : ∀ a : ι × κ, B a.2 → A a.1)

def localMap (a : ι × κ) : refinedPiece U V f A a ⟶ ∐ sourcePiece V B :=
  coordinateMap (keep a) (refinedTargetMap U V f a) ≫ Sigma.ι (sourcePiece V B) a.2

theorem localMap_projection (a : ι × κ) :
    localMap U V f A B keep a ≫ sourceProjection V B =
      (AffineSpace (A a.1) (refinedBase U V f a).toScheme ↘ (refinedBase U V f a).toScheme) ≫
        refinedBaseMap U V f a ≫ f := by
  rw [localMap, Category.assoc, sourceProjection, Sigma.ι_desc, ← Category.assoc,
    coordinateMap_over, Category.assoc, refinedTargetMap_over]

variable (hUd : Pairwise (fun i l => Disjoint (U i : Set Y) (U l : Set Y)))
variable (hVc : (⨆ j, V j) = ⊤) (hVd : Pairwise (fun j l => Disjoint (V j : Set X) (V l : Set X)))

def paddedMap : (∐ sourcePiece U A) ⟶ ∐ sourcePiece V B := by
  have := refinedDesc_isIso U V f A hUd hVc hVd
  exact inv (refinedDesc U V f A) ≫ Sigma.desc (localMap U V f A B keep)

theorem refinedDesc_paddedMap : refinedDesc U V f A ≫ paddedMap U V f A B keep hUd hVc hVd =
    Sigma.desc (localMap U V f A B keep) := by
  have := refinedDesc_isIso U V f A hUd hVc hVd
  rw [paddedMap, IsIso.hom_inv_id_assoc]

theorem refinedInclusion_paddedMap (a : ι × κ) :
    refinedInclusion U V f A a ≫ paddedMap U V f A B keep hUd hVc hVd = localMap U V f A B keep a := by
  calc
    refinedInclusion U V f A a ≫ paddedMap U V f A B keep hUd hVc hVd =
        (Sigma.ι (refinedPiece U V f A) a ≫ refinedDesc U V f A) ≫
          paddedMap U V f A B keep hUd hVc hVd := by rw [refinedDesc, Sigma.ι_desc]
    _ = _ := by rw [Category.assoc, refinedDesc_paddedMap, Sigma.ι_desc]

theorem paddedMap_projection : paddedMap U V f A B keep hUd hVc hVd ≫ sourceProjection V B =
    sourceProjection U A ≫ f := by
  have := refinedDesc_isIso U V f A hUd hVc hVd
  apply (cancel_epi (refinedDesc U V f A)).mp
  apply Sigma.hom_ext
  intro a
  simp only [← Category.assoc, refinedDesc, Sigma.ι_desc]
  rw [refinedInclusion_paddedMap, localMap_projection, refinedInclusion_projection, Category.assoc]

def refinedZero : (∐ fun a => (refinedBase U V f a).toScheme) ⟶ ∐ refinedPiece U V f A :=
  Limits.Sigma.map (fun a => AffineSpace.homOfVector (𝟙 (refinedBase U V f a).toScheme) (fun _ : A a.1 => 0))

private theorem zero_map {σ : Type u} {Z W : Scheme.{u}} (g : Z ⟶ W) :
    AffineSpace.homOfVector (𝟙 Z) (fun _ : σ => 0) ≫ AffineSpace.map σ g =
      g ≫ AffineSpace.homOfVector (𝟙 W) (fun _ : σ => 0) := by
  simpa only [coordinateMap, AffineSpace.reindex_id, Category.id_comp] using coordinateMap_zero (id : σ → σ) g

variable (hUc : (⨆ i, U i) = ⊤)

theorem refinedZero_desc : refinedZero U V f A ≫ refinedDesc U V f A =
    refinedBaseDesc U V f ≫ partitionZero U A hUc hUd := by
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, refinedZero, Sigma.ι_map, Category.assoc, refinedDesc, Sigma.ι_desc,
    refinedInclusion, ← Category.assoc, zero_map, Category.assoc,
    ← partitionZero_piece U A hUc hUd a.1, ← Category.assoc,
    ← Category.assoc, refinedBaseDesc, Sigma.ι_desc]
  rfl

theorem paddedMap_zero : partitionZero U A hUc hUd ≫ paddedMap U V f A B keep hUd hVc hVd =
    f ≫ partitionZero V B hVc hVd := by
  have := refinedBaseDesc_isIso U V f hUc hUd hVc hVd
  apply (cancel_epi (refinedBaseDesc U V f)).mp
  rw [← Category.assoc, ← refinedZero_desc, Category.assoc, refinedDesc_paddedMap]
  apply Sigma.hom_ext
  intro a
  rw [← Category.assoc, refinedZero, Sigma.ι_map, Category.assoc, Sigma.ι_desc,
    localMap, ← Category.assoc, coordinateMap_zero, Category.assoc,
    ← partitionZero_piece V B hVc hVd a.2,
    ← Category.assoc, refinedTargetMap_over]
  simp only [← Category.assoc, refinedBaseDesc, Sigma.ι_desc]

theorem paddedMap_smooth [∀ i, Finite (A i)] [Smooth f]
    (hinj : ∀ a, Function.Injective (keep a)) : Smooth (paddedMap U V f A B keep hUd hVc hVd) := by
  have := refinedDesc_isIso U V f A hUd hVc hVd
  have hs : ∀ a, Smooth (localMap U V f A B keep a) := by
    intro a
    have := refinedTargetMap_smooth U V f a
    have := coordinateMap_smooth (keep a) (hinj a) (refinedTargetMap U V f a)
    dsimp only [localMap]
    infer_instance
  have : IsZariskiLocalAtSource @Smooth := @HasRingHomProperty.instIsZariskiLocalAtSource _ _ inferInstance
  have : Smooth (Sigma.desc (localMap U V f A B keep)) := IsZariskiLocalAtSource.sigmaDesc hs
  dsimp only [paddedMap]
  infer_instance

include hUc in
theorem paddedMap_surjective [Surjective f] (hinj : ∀ a, Function.Injective (keep a)) :
    Surjective (paddedMap U V f A B keep hUd hVc hVd) := by
  constructor
  intro z
  obtain ⟨j, z, rfl⟩ := (sigmaOpenCover (sourcePiece V B)).exists_eq z
  let b := (AffineSpace (B j) (V j).toScheme ↘ (V j).toScheme) z
  obtain ⟨y, hy⟩ := (inferInstance : Surjective f).1 ((V j).ι b)
  have hu : y ∈ ⨆ i, U i := by rw [hUc]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hu
  let w : (refinedBase U V f (i, j)).toScheme := ⟨⟨y, hi⟩, by change f y ∈ V j; rw [hy]; exact b.property⟩
  have hw : refinedTargetMap U V f (i, j) w = b := by
    apply (V j).ι.injective
    have he := congrArg (fun g => g w) (refinedTargetMap_over U V f (i, j))
    simpa only [Scheme.Hom.comp_apply, refinedBaseMap, w, Scheme.Opens.ι_apply] using he.trans hy
  obtain ⟨q, hq, -⟩ := Scheme.exists_preimage_of_isPullback
    (AffineSpace.isPullback_map (n := B j) (refinedTargetMap U V f (i, j))) z w hw.symm
  have := reindex_surjective_of_injective (keep (i, j)) (hinj (i, j)) (refinedBase U V f (i, j)).toScheme
  obtain ⟨t, ht⟩ := (inferInstance : Surjective (AffineSpace.reindex (keep (i, j)) _)).1 q
  refine ⟨refinedInclusion U V f A (i, j) t, ?_⟩
  have he := congrArg (fun g => g t) (refinedInclusion_paddedMap U V f A B keep hUd hVc hVd (i, j))
  rw [Scheme.Hom.comp_apply] at he
  rw [he]
  change Sigma.ι (sourcePiece V B) j
      (AffineSpace.map (B j) (refinedTargetMap U V f (i, j))
        (AffineSpace.reindex (keep (i, j)) (refinedBase U V f (i, j)).toScheme t)) = _
  rw [ht, hq]
  rfl

end
end Hironaka.Resolution.Algebraic.ActualClopenPaddedMap
