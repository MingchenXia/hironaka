import Hironaka.Resolution.Algebraic.ActualAffineCoordinateForgetting

/-!
# Genuine double clopen refinement of the SAME actual padded input

Source-first proof: `actual-clopen-padding-refinement-20261102.tex`.
Actual original partitions/base map derive genuine refined base/padded
coproduct isomorphisms and actual restricted base maps; no output certificates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u

namespace Hironaka.Resolution.Algebraic.ActualClopenPaddingRefinement

noncomputable section

theorem coproductDesc_isIso_of_disjoint_cover {ι : Type} {F : ι → Scheme.{u}} {X : Scheme.{u}}
    (j : ∀ i, F i ⟶ X) [∀ i, IsOpenImmersion (j i)]
    (hdisj : Pairwise (fun i l => Disjoint (Set.range (j i)) (Set.range (j l))))
    (hcover : ∀ x : X, ∃ i, ∃ y : F i, j i y = x) : IsIso (Sigma.desc j) := by
  have : IsOpenImmersion (Sigma.desc j) := isOpenImmersion_sigmaDesc F j hdisj
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  apply top_le_iff.mp
  intro x _
  obtain ⟨i, y, rfl⟩ := hcover x
  exact ⟨Sigma.ι F i y, congrArg (fun f => f y) (Sigma.ι_desc j i)⟩

def partitionDesc {ι : Type} {X : Scheme.{u}} (U : ι → X.Opens) : (∐ fun i => (U i).toScheme) ⟶ X :=
  Sigma.desc (fun i => (U i).ι)

theorem partitionDesc_isIso {ι : Type} {X : Scheme.{u}} (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤) (hdisj : Pairwise (fun i l => Disjoint (U i : Set X) (U l : Set X))) :
    IsIso (partitionDesc U) := by
  apply coproductDesc_isIso_of_disjoint_cover
  · simpa only [Scheme.Opens.range_ι] using hdisj
  · intro x
    have hx : x ∈ ⨆ i, U i := by rw [hcover]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨i, ⟨x, hi⟩, rfl⟩

variable {ι κ : Type} {X Y : Scheme.{u}} (U : ι → Y.Opens) (V : κ → X.Opens) (f : Y ⟶ X)

def refinedBase (a : ι × κ) : (U a.1).toScheme.Opens := ((U a.1).ι ≫ f) ⁻¹ᵁ V a.2

def refinedBaseMap (a : ι × κ) : (refinedBase U V f a).toScheme ⟶ Y :=
  (refinedBase U V f a).ι ≫ (U a.1).ι

private instance refinedBaseMap_isOpenImmersion (a : ι × κ) : IsOpenImmersion (refinedBaseMap U V f a) := by
  dsimp only [refinedBaseMap]
  infer_instance

private theorem refinedBaseMap_source_mem (a : ι × κ) (z : (refinedBase U V f a).toScheme) :
    refinedBaseMap U V f a z ∈ U a.1 := ((refinedBase U V f a).ι z).property

private theorem refinedBaseMap_target_mem (a : ι × κ) (z : (refinedBase U V f a).toScheme) :
    f (refinedBaseMap U V f a z) ∈ V a.2 := z.property

private theorem disjoint_of_memberships {Z : Scheme.{u}} {F : ι × κ → Scheme.{u}}
    (P : Z ⟶ Y) (j : ∀ a, F a ⟶ Z)
    (hU : Pairwise (fun i l => Disjoint (U i : Set Y) (U l : Set Y)))
    (hV : Pairwise (fun i l => Disjoint (V i : Set X) (V l : Set X)))
    (hs : ∀ a z, P (j a z) ∈ U a.1) (ht : ∀ a z, f (P (j a z)) ∈ V a.2) :
    Pairwise (fun a b => Disjoint (Set.range (j a)) (Set.range (j b))) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro x ⟨z, hz⟩ ⟨w, hw⟩
  by_cases hi : a.1 = b.1
  · have hj : a.2 ≠ b.2 := fun hj => hab (Prod.ext hi hj)
    exact Set.disjoint_left.mp (hV hj) (hz ▸ ht a z) (hw ▸ ht b w)
  · exact Set.disjoint_left.mp (hU hi) (hz ▸ hs a z) (hw ▸ hs b w)

def refinedBaseDesc : (∐ fun a => (refinedBase U V f a).toScheme) ⟶ Y :=
  Sigma.desc (refinedBaseMap U V f)

theorem refinedBaseDesc_isIso (hUc : (⨆ i, U i) = ⊤)
    (hUd : Pairwise (fun i l => Disjoint (U i : Set Y) (U l : Set Y)))
    (hVc : (⨆ j, V j) = ⊤) (hVd : Pairwise (fun j l => Disjoint (V j : Set X) (V l : Set X))) :
    IsIso (refinedBaseDesc U V f) := by
  apply coproductDesc_isIso_of_disjoint_cover
  · exact disjoint_of_memberships U V f (𝟙 Y) (refinedBaseMap U V f) hUd hVd
      (refinedBaseMap_source_mem U V f) (refinedBaseMap_target_mem U V f)
  · intro y
    have hy : y ∈ ⨆ i, U i := by rw [hUc]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    have hf : f y ∈ ⨆ j, V j := by rw [hVc]; trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hf
    exact ⟨(i, j), ⟨⟨y, hi⟩, hj⟩, rfl⟩

variable (A : ι → Type u)

def sourcePiece (i : ι) : Scheme.{u} := AffineSpace (A i) (U i).toScheme

def sourceProjection : (∐ sourcePiece U A) ⟶ Y :=
  Sigma.desc (fun i => (AffineSpace (A i) (U i).toScheme ↘ (U i).toScheme) ≫ (U i).ι)

def refinedPiece (a : ι × κ) : Scheme.{u} := AffineSpace (A a.1) (refinedBase U V f a).toScheme

def refinedInclusion (a : ι × κ) : refinedPiece U V f A a ⟶ ∐ sourcePiece U A :=
  AffineSpace.map (A a.1) (refinedBase U V f a).ι ≫ Sigma.ι (sourcePiece U A) a.1

instance refinedInclusion_isOpenImmersion (a : ι × κ) : IsOpenImmersion (refinedInclusion U V f A a) := by
  have : IsOpenImmersion (AffineSpace.map (A a.1) (refinedBase U V f a).ι) :=
    property_of_isPullback _ (AffineSpace.isPullback_map (n := A a.1) (refinedBase U V f a).ι) inferInstance
  dsimp only [refinedInclusion]
  infer_instance

theorem refinedInclusion_projection (a : ι × κ) : refinedInclusion U V f A a ≫ sourceProjection U A =
    (AffineSpace (A a.1) (refinedBase U V f a).toScheme ↘ (refinedBase U V f a).toScheme) ≫ refinedBaseMap U V f a := by
  rw [refinedInclusion, Category.assoc, sourceProjection, Sigma.ι_desc, ← Category.assoc,
    AffineSpace.map_over, Category.assoc]
  rfl

def refinedDesc : (∐ refinedPiece U V f A) ⟶ ∐ sourcePiece U A := Sigma.desc (refinedInclusion U V f A)

theorem refinedDesc_isIso
    (hUd : Pairwise (fun i l => Disjoint (U i : Set Y) (U l : Set Y)))
    (hVc : (⨆ j, V j) = ⊤) (hVd : Pairwise (fun j l => Disjoint (V j : Set X) (V l : Set X))) :
    IsIso (refinedDesc U V f A) := by
  apply coproductDesc_isIso_of_disjoint_cover
  · apply disjoint_of_memberships U V f (sourceProjection U A) (refinedInclusion U V f A) hUd hVd
    · intro a z
      have h := congrArg (fun g => g z) (refinedInclusion_projection U V f A a)
      simp only [Scheme.Hom.comp_apply] at h
      rw [h]
      exact refinedBaseMap_source_mem U V f a _
    · intro a z
      have h := congrArg (fun g => g z) (refinedInclusion_projection U V f A a)
      simp only [Scheme.Hom.comp_apply] at h
      rw [h]
      exact refinedBaseMap_target_mem U V f a _
  · intro x
    obtain ⟨i, z, rfl⟩ := (sigmaOpenCover (sourcePiece U A)).exists_eq x
    let b := (AffineSpace (A i) (U i).toScheme ↘ (U i).toScheme) z
    have hf : f ((U i).ι b) ∈ ⨆ j, V j := by rw [hVc]; trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hf
    let w : (refinedBase U V f (i, j)).toScheme := ⟨b, hj⟩
    obtain ⟨t, ht, -⟩ := Scheme.exists_preimage_of_isPullback
      (AffineSpace.isPullback_map (n := A i) (refinedBase U V f (i, j)).ι) z w rfl
    refine ⟨(i, j), t, ?_⟩
    change Sigma.ι (sourcePiece U A) i (AffineSpace.map (A i) (refinedBase U V f (i, j)).ι t) =
      Sigma.ι (sourcePiece U A) i z
    rw [ht]

def refinedTargetMap (a : ι × κ) : (refinedBase U V f a).toScheme ⟶ (V a.2).toScheme :=
  ((U a.1).ι ≫ f) ∣_ V a.2

theorem refinedTargetMap_over (a : ι × κ) :
    refinedTargetMap U V f a ≫ (V a.2).ι = refinedBaseMap U V f a ≫ f := by
  simpa only [refinedTargetMap, refinedBaseMap, refinedBase, Category.assoc] using morphismRestrict_ι ((U a.1).ι ≫ f) (V a.2)

theorem refinedTargetMap_smooth [Smooth f] (a : ι × κ) : Smooth (refinedTargetMap U V f a) :=
  IsZariskiLocalAtTarget.restrict (inferInstance : Smooth ((U a.1).ι ≫ f)) (V a.2)

end
end Hironaka.Resolution.Algebraic.ActualClopenPaddingRefinement
