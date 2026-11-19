import Hironaka.Analytic.Unibranch.OriginalClosedSubspaceFactorization
import Hironaka.Analytic.Unibranch.EmbeddedBlowupOverlap
import Hironaka.Analytic.Unibranch.EmbeddedBlowupOpenRestriction
import Hironaka.Analytic.Unibranch.SmoothCentreModification
import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Actual original analytic-centre charts and full overlap transitions

Ordinary ORIGINAL X and analytic C internally select the SAME local witnesses.
The reduced centre is the actual intersection W ∩ A, with its true contained
inclusion. Literal open restrictions and unique full original factorizations
derive overlap transitions; native monicity derives all inverse/cocycle data.
No atlas, transition, topology or desired global object is an input.

Blueprint FIRST: `original-analytic-closed-subspace-overlap.tex`.
-/

set_option autoImplicit false

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Topology Manifold ContDiff

namespace Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspaceOverlap

open Hironaka Hironaka
  HironakaActualAnalyticSubspace HironakaReducedComplexAnalyticSpaces
  SourceReducedComplexSpace EmbeddedBlowupOpenRestriction

noncomputable section

variable (X : SourceReducedComplexSpace) (C : Set X.obj.left) (hC : X.IsAnalyticSubset C)

/-- The embedding from the SAME ordinary analyticity witness at a. -/
def localEmbedding (a : X.obj.left) : LocalEmbedding X := (hC a).choose

/-- The ambient analytic trace from that SAME selected witness. -/
def ambientTrace (a : X.obj.left) : Set (localEmbedding X C hC a).ambient :=
  (hC a).choose_spec.2.choose

theorem ambientTrace_analytic (a : X.obj.left) :
    IsComplexAnalyticSubset (n := (localEmbedding X C hC a).dim) (ambientTrace X C hC a) :=
  (hC a).choose_spec.2.choose_spec.1

theorem ambientTrace_eq (a : X.obj.left) :
    (localEmbedding X C hC a).toPoint ⁻¹' C =
      (Subtype.val : (localEmbedding X C hC a).carrier → (localEmbedding X C hC a).ambient) ⁻¹'
        ambientTrace X C hC a :=
  (hC a).choose_spec.2.choose_spec.2

/-- The REDUCED analytic centre is W ∩ A, never merely the ambient A. -/
def localCentre (a : X.obj.left) : Set (localEmbedding X C hC a).ambient :=
  (localEmbedding X C hC a).carrier ∩ ambientTrace X C hC a

theorem localCentre_analytic (a : X.obj.left) :
    IsComplexAnalyticSubset (n := (localEmbedding X C hC a).dim) (localCentre X C hC a) :=
  (localEmbedding X C hC a).analytic.inter (ambientTrace_analytic X C hC a)

theorem localCentre_subset (a : X.obj.left) :
    localCentre X C hC a ⊆ (localEmbedding X C hC a).carrier := inter_subset_left

/-- The SAME actual original reduced quotient centre model. -/
@[implicit_reducible]
def localObject (a : X.obj.left) : SourceReducedComplexSpace :=
  ofClosedAnalytic (localCentre X C hC a) (localCentre_analytic X C hC a)

/-- The FULL original contained inclusion followed by the original chart. -/
def localProjection (a : X.obj.left) : localObject X C hC a ⟶ X :=
  OriginalClosedSubspaceFactorization.inclusion (localCentre_analytic X C hC a)
    (localEmbedding X C hC a).analytic (localCentre_subset X C hC a) ≫
      EmbeddedBlowupOverlap.chartMorphism (localEmbedding X C hC a)

theorem localProjection_fac (a : X.obj.left) :
    localProjection X C hC a =
      OriginalClosedSubspaceFactorization.inclusion (localCentre_analytic X C hC a)
        (localEmbedding X C hC a).analytic (localCentre_subset X C hC a) ≫
          EmbeddedBlowupOverlap.chartMorphism (localEmbedding X C hC a) := rfl

def chartOpen (a : X.obj.left) : Opens X.obj.left.toTopCat :=
  ⟨range (localEmbedding X C hC a).toPoint, (localEmbedding X C hC a).isOpen_range_toPoint⟩

theorem mem_chartOpen_self (a : X.obj.left) : a ∈ chartOpen X C hC a :=
  (hC a).choose_spec.1

theorem localProjection_range (a : X.obj.left) :
    range (localProjection X C hC a).hom.left.base = C ∩ (chartOpen X C hC a : Set X.obj.left) := by
  ext x
  constructor
  · rintro ⟨d, rfl⟩
    let w : (localEmbedding X C hC a).carrier := ⟨d.val, d.property.1⟩
    refine ⟨?_, ⟨w, rfl⟩⟩
    exact (Set.ext_iff.mp (ambientTrace_eq X C hC a) w).mpr d.property.2
  · rintro ⟨hxC, w, rfl⟩
    have hw : w.val ∈ ambientTrace X C hC a :=
      (Set.ext_iff.mp (ambientTrace_eq X C hC a) w).mp hxC
    exact ⟨⟨w.val, ⟨w.property, hw⟩⟩, rfl⟩

theorem localProjection_isEmbedding (a : X.obj.left) :
    Topology.IsEmbedding (localProjection X C hC a).hom.left.base := by
  change Topology.IsEmbedding ((localEmbedding X C hC a).toPoint ∘
    (OriginalClosedSubspaceFactorization.inclusion (localCentre_analytic X C hC a)
      (localEmbedding X C hC a).analytic (localCentre_subset X C hC a)).hom.left.base)
  exact (localEmbedding X C hC a).isOpenEmbedding_toPoint.isEmbedding.comp
    (SmoothCentreModification.contained_inclusion_isClosedEmbedding
      (localCentre_analytic X C hC a) (localEmbedding X C hC a).analytic
        (localCentre_subset X C hC a)).isEmbedding

instance localProjection_left_mono (a : X.obj.left) :
    Mono (localProjection X C hC a).hom.left := by
  let j := EmbeddedBlowupOverlap.chartMorphism (localEmbedding X C hC a)
  let : LocallyRingedSpace.IsOpenImmersion j.hom.left :=
    (localEmbedding X C hC a).isOpenImmersion
  change Mono ((OriginalClosedSubspaceFactorization.inclusion (localCentre_analytic X C hC a)
    (localEmbedding X C hC a).analytic (localCentre_subset X C hC a)).hom.left ≫
      j.hom.left)
  infer_instance

theorem localProjection_stalk_surjective (a : X.obj.left) (s : (localObject X C hC a).obj.left) :
    Function.Surjective ((localProjection X C hC a).hom.left.stalkMap s) := by
  let j := EmbeddedBlowupOverlap.chartMorphism (localEmbedding X C hC a)
  let : LocallyRingedSpace.IsOpenImmersion j.hom.left :=
    (localEmbedding X C hC a).isOpenImmersion
  change Function.Surjective
    (((OriginalClosedSubspaceFactorization.inclusion (localCentre_analytic X C hC a)
      (localEmbedding X C hC a).analytic (localCentre_subset X C hC a)).hom.left ≫
        j.hom.left).stalkMap s)
  rw [LocallyRingedSpace.stalkMap_comp]
  have hj := (ConcreteCategory.bijective_of_isIso
    (j.hom.left.stalkMap ((OriginalClosedSubspaceFactorization.inclusion
      (localCentre_analytic X C hC a) (localEmbedding X C hC a).analytic
        (localCentre_subset X C hC a)).hom.left.base s))).surjective
  exact (SmoothCentreModification.contained_inclusion_stalk_surjective
    (localCentre_analytic X C hC a) (localEmbedding X C hC a).analytic
      (localCentre_subset X C hC a) s).comp hj

def overlapOpen (a b : X.obj.left) : Opens (localObject X C hC a).obj.left.toTopCat :=
  (Opens.map (localProjection X C hC a).hom.left.base).obj (chartOpen X C hC b)

@[implicit_reducible]
def overlapObject (a b : X.obj.left) : SourceReducedComplexSpace :=
  restrictedClosedAnalytic (localCentre_analytic X C hC a) (overlapOpen X C hC a b)

def overlapInclusion (a b : X.obj.left) : overlapObject X C hC a b ⟶ localObject X C hC a :=
  restrictionInclusion (localCentre_analytic X C hC a) (overlapOpen X C hC a b)

instance overlapInclusion_isOpenImmersion (a b : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (overlapInclusion X C hC a b).hom.left :=
  restrictionInclusion_isOpenImmersion _ _

theorem overlapInclusion_range (a b : X.obj.left) :
    range (overlapInclusion X C hC a b).hom.left.base =
      (localProjection X C hC a).hom.left.base ⁻¹' (chartOpen X C hC b : Set X.obj.left) := by
  exact Subtype.range_coe

theorem overlap_point_mem (a b : X.obj.left) (u : (overlapObject X C hC a b).obj.left) :
    (localProjection X C hC a).hom.left.base ((overlapInclusion X C hC a b).hom.left.base u) ∈
      chartOpen X C hC b := u.property

theorem exists_overlap_lift (a b : X.obj.left) (y : (localObject X C hC a).obj.left)
    (hy : (localProjection X C hC a).hom.left.base y ∈ chartOpen X C hC b) :
    ∃ u : (overlapObject X C hC a b).obj.left,
      (overlapInclusion X C hC a b).hom.left.base u = y := ⟨⟨y, hy⟩, rfl⟩

private theorem exists_original_open_lift
    {A B T : SourceReducedComplexSpace} (j : B ⟶ T)
    [LocallyRingedSpace.IsOpenImmersion j.hom.left] (F : A ⟶ T)
    (h : range F.hom.left.base ⊆ range j.hom.left.base) :
    ∃ L : A ⟶ B, L ≫ j = F := by
  let l := LocallyRingedSpace.IsOpenImmersion.lift j.hom.left F.hom.left h
  have hl : l ≫ j.hom.left = F.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac j.hom.left F.hom.left h
  have hp : l ≫ B.obj.hom = A.obj.hom := by
    rw [← Over.w j.hom, ← Category.assoc, hl, Over.w F.hom]
  refine ⟨ObjectProperty.homMk (Over.homMk l hp), ?_⟩
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact hl

/-- Ordinary actual overlap landing derives a UNIQUE FULL ORIGINAL transition. -/
theorem exists_unique_overlap_transition (a b : X.obj.left) :
    ∃! t : overlapObject X C hC a b ⟶ overlapObject X C hC b a,
      t ≫ overlapInclusion X C hC b a ≫ localProjection X C hC b =
        overlapInclusion X C hC a b ≫ localProjection X C hC a := by
  classical
  let j := EmbeddedBlowupOverlap.chartMorphism (localEmbedding X C hC b)
  let : LocallyRingedSpace.IsOpenImmersion j.hom.left :=
    (localEmbedding X C hC b).isOpenImmersion
  let F := overlapInclusion X C hC a b ≫ localProjection X C hC a
  have hRange : range F.hom.left.base ⊆ range j.hom.left.base := by
    rintro _ ⟨u, rfl⟩
    exact overlap_point_mem X C hC a b u
  obtain ⟨K, hK⟩ := exists_original_open_lift j F hRange
  have hland (u : (overlapObject X C hC a b).obj.left) :
      (K.hom.left.base u).val ∈ localCentre X C hC b := by
    refine ⟨(K.hom.left.base u).property, ?_⟩
    apply (Set.ext_iff.mp (ambientTrace_eq X C hC b) (K.hom.left.base u)).mp
    have hp : (localEmbedding X C hC b).toPoint (K.hom.left.base u) = F.hom.left.base u :=
      congrArg (fun H => H.hom.left.base u) hK
    change (localEmbedding X C hC b).toPoint (K.hom.left.base u) ∈ C
    rw [hp]
    exact ((Set.ext_iff.mp (localProjection_range X C hC a) _).mp
      ⟨(overlapInclusion X C hC a b).hom.left.base u, rfl⟩).1
  obtain ⟨H, hH, _⟩ := OriginalClosedSubspaceFactorization.exists_unique_factorization
    (localCentre_analytic X C hC b) (localEmbedding X C hC b).analytic
    (localCentre_subset X C hC b) (overlapObject X C hC a b) K hland
  have hHF : H ≫ localProjection X C hC b = F := by
    change H ≫ (OriginalClosedSubspaceFactorization.inclusion (localCentre_analytic X C hC b)
      (localEmbedding X C hC b).analytic (localCentre_subset X C hC b) ≫ j) = F
    rw [← Category.assoc, hH, hK]
  have hHrange : range H.hom.left.base ⊆ range (overlapInclusion X C hC b a).hom.left.base := by
    rw [overlapInclusion_range]
    rintro _ ⟨u, rfl⟩
    change (localProjection X C hC b).hom.left.base (H.hom.left.base u) ∈ chartOpen X C hC a
    have hp : (localProjection X C hC b).hom.left.base (H.hom.left.base u) =
        F.hom.left.base u := congrArg (fun f => f.hom.left.base u) hHF
    rw [hp]
    exact ((Set.ext_iff.mp (localProjection_range X C hC a) _).mp
      ⟨(overlapInclusion X C hC a b).hom.left.base u, rfl⟩).2
  obtain ⟨L, hL⟩ := exists_original_open_lift (overlapInclusion X C hC b a) H hHrange
  have hOver : L ≫ overlapInclusion X C hC b a ≫ localProjection X C hC b = F := by
    rw [← Category.assoc, hL, hHF]
  refine ⟨L, hOver, ?_⟩
  intro L' hL'
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono ((overlapInclusion X C hC b a).hom.left ≫
    (localProjection X C hC b).hom.left)).mp
  exact congrArg (fun f => f.hom.left) (hL'.trans hOver.symm)

def transition (a b : X.obj.left) : overlapObject X C hC a b ⟶ overlapObject X C hC b a :=
  (exists_unique_overlap_transition X C hC a b).choose

theorem transition_over (a b : X.obj.left) :
    transition X C hC a b ≫ overlapInclusion X C hC b a ≫ localProjection X C hC b =
      overlapInclusion X C hC a b ≫ localProjection X C hC a :=
  (exists_unique_overlap_transition X C hC a b).choose_spec.1

theorem transition_self (a : X.obj.left) : transition X C hC a a = 𝟙 _ := by
  exact ((exists_unique_overlap_transition X C hC a a).choose_spec.2 (𝟙 _)
    (by
      change (𝟙 (overlapObject X C hC a a)) ≫ overlapInclusion X C hC a a ≫
        localProjection X C hC a = _
      rw [Category.id_comp])).symm

theorem transition_inverse (a b : X.obj.left) :
    transition X C hC a b ≫ transition X C hC b a = 𝟙 _ := by
  have hOver : (transition X C hC a b ≫ transition X C hC b a) ≫
      overlapInclusion X C hC a b ≫ localProjection X C hC a =
        overlapInclusion X C hC a b ≫ localProjection X C hC a := by
    rw [Category.assoc, transition_over, transition_over]
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply (cancel_mono ((overlapInclusion X C hC a b).hom.left ≫
    (localProjection X C hC a).hom.left)).mp
  have hn := congrArg (fun f => f.hom.left) hOver
  change ((transition X C hC a b).hom.left ≫ (transition X C hC b a).hom.left) ≫
    (overlapInclusion X C hC a b).hom.left ≫ (localProjection X C hC a).hom.left =
      (overlapInclusion X C hC a b).hom.left ≫ (localProjection X C hC a).hom.left at hn
  change ((transition X C hC a b).hom.left ≫ (transition X C hC b a).hom.left) ≫
    (overlapInclusion X C hC a b).hom.left ≫ (localProjection X C hC a).hom.left =
      (𝟙 _) ≫ (overlapInclusion X C hC a b).hom.left ≫ (localProjection X C hC a).hom.left
  simpa only [Category.id_comp] using hn

instance transition_isIso (a b : X.obj.left) : IsIso (transition X C hC a b).hom.left := by
  let e : (overlapObject X C hC a b).obj.left ≅ (overlapObject X C hC b a).obj.left :=
    { hom := (transition X C hC a b).hom.left
      inv := (transition X C hC b a).hom.left
      hom_inv_id := congrArg (fun f => f.hom.left) (transition_inverse X C hC a b)
      inv_hom_id := congrArg (fun f => f.hom.left) (transition_inverse X C hC b a) }
  exact e.isIso_hom

instance overlapInclusion_self_isIso (a : X.obj.left) :
    IsIso (overlapInclusion X C hC a a).hom.left := by
  have hs : Function.Surjective (overlapInclusion X C hC a a).hom.left.base := by
    intro y
    apply exists_overlap_lift
    exact ((Set.ext_iff.mp (localProjection_range X C hC a) _).mp ⟨y, rfl⟩).2
  let : Epi (overlapInclusion X C hC a a).hom.left.base := (TopCat.epi_iff_surjective _).mpr hs
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

/-- The genuine native pullback of TWO actual original overlap inclusions. -/
def tripleObject (a b c : X.obj.left) : LocallyRingedSpace :=
  pullback (overlapInclusion X C hC a b).hom.left (overlapInclusion X C hC a c).hom.left

def tripleInclusion (a b c : X.obj.left) : tripleObject X C hC a b c ⟶ (localObject X C hC a).obj.left :=
  pullback.fst (overlapInclusion X C hC a b).hom.left (overlapInclusion X C hC a c).hom.left ≫
    (overlapInclusion X C hC a b).hom.left

instance tripleInclusion_isOpenImmersion (a b c : X.obj.left) :
    LocallyRingedSpace.IsOpenImmersion (tripleInclusion X C hC a b c) := by
  let f := (overlapInclusion X C hC a b).hom.left
  let g := (overlapInclusion X C hC a c).hom.left
  let : LocallyRingedSpace.IsOpenImmersion f := overlapInclusion_isOpenImmersion X C hC a b
  let : LocallyRingedSpace.IsOpenImmersion g := overlapInclusion_isOpenImmersion X C hC a c
  have hfst : LocallyRingedSpace.IsOpenImmersion (pullback.fst f g) := inferInstance
  exact @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (pullback.fst f g) hfst f inferInstance

private theorem triple_transition_range (a b c : X.obj.left) :
    range (pullback.fst (overlapInclusion X C hC a b).hom.left
        (overlapInclusion X C hC a c).hom.left ≫ (transition X C hC a b).hom.left ≫
          (overlapInclusion X C hC b a).hom.left).base ⊆
      range (overlapInclusion X C hC b c).hom.left.base := by
  let l := pullback.fst (overlapInclusion X C hC a b).hom.left (overlapInclusion X C hC a c).hom.left
  let m := pullback.snd (overlapInclusion X C hC a b).hom.left (overlapInclusion X C hC a c).hom.left
  let t := (transition X C hC a b).hom.left
  have ht : t ≫ (overlapInclusion X C hC b a).hom.left ≫ (localProjection X C hC b).hom.left =
      (overlapInclusion X C hC a b).hom.left ≫ (localProjection X C hC a).hom.left :=
    congrArg (fun f => f.hom.left) (transition_over X C hC a b)
  have heq : (l ≫ t ≫ (overlapInclusion X C hC b a).hom.left) ≫
      (localProjection X C hC b).hom.left =
        (m ≫ (overlapInclusion X C hC a c).hom.left) ≫ (localProjection X C hC a).hom.left := by
    calc
      _ = l ≫ (t ≫ (overlapInclusion X C hC b a).hom.left ≫
          (localProjection X C hC b).hom.left) := by simp only [Category.assoc]
      _ = l ≫ ((overlapInclusion X C hC a b).hom.left ≫
          (localProjection X C hC a).hom.left) := congrArg (fun u => l ≫ u) ht
      _ = _ := by rw [← Category.assoc, pullback.condition]
  rintro _ ⟨x, rfl⟩
  refine ⟨⟨(l ≫ t ≫ (overlapInclusion X C hC b a).hom.left).base x, ?_⟩, rfl⟩
  change (localProjection X C hC b).hom.left.base
    ((l ≫ t ≫ (overlapInclusion X C hC b a).hom.left).base x) ∈ chartOpen X C hC c
  have hp := congrArg (fun H => H.base x) heq
  exact hp.symm ▸ overlap_point_mem X C hC a c (m.base x)

/-- Actual OI lifting and the native pullback construct the full triple rotation. -/
def tripleTransition (a b c : X.obj.left) :
    tripleObject X C hC a b c ⟶ tripleObject X C hC b c a := by
  let l := pullback.fst (overlapInclusion X C hC a b).hom.left
    (overlapInclusion X C hC a c).hom.left ≫ (transition X C hC a b).hom.left
  let m := LocallyRingedSpace.IsOpenImmersion.lift (overlapInclusion X C hC b c).hom.left
    (l ≫ (overlapInclusion X C hC b a).hom.left) (triple_transition_range X C hC a b c)
  exact pullback.lift m l
    (LocallyRingedSpace.IsOpenImmersion.lift_fac (overlapInclusion X C hC b c).hom.left
      (l ≫ (overlapInclusion X C hC b a).hom.left) _)

theorem tripleTransition_fac (a b c : X.obj.left) :
    tripleTransition X C hC a b c ≫
        pullback.snd (overlapInclusion X C hC b c).hom.left (overlapInclusion X C hC b a).hom.left =
      pullback.fst (overlapInclusion X C hC a b).hom.left (overlapInclusion X C hC a c).hom.left ≫
        (transition X C hC a b).hom.left := by
  exact pullback.lift_snd _ _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
theorem tripleTransition_over (a b c : X.obj.left) :
    tripleTransition X C hC a b c ≫ tripleInclusion X C hC b c a ≫
        (localProjection X C hC b).hom.left =
      tripleInclusion X C hC a b c ≫ (localProjection X C hC a).hom.left := by
  have hc : tripleInclusion X C hC b c a =
      pullback.snd (overlapInclusion X C hC b c).hom.left (overlapInclusion X C hC b a).hom.left ≫
        (overlapInclusion X C hC b a).hom.left := pullback.condition
  have ht : (transition X C hC a b).hom.left ≫ (overlapInclusion X C hC b a).hom.left ≫
      (localProjection X C hC b).hom.left =
        (overlapInclusion X C hC a b).hom.left ≫ (localProjection X C hC a).hom.left :=
    congrArg (fun f => f.hom.left) (transition_over X C hC a b)
  have hfac := congrArg (fun f => f ≫ (overlapInclusion X C hC b a).hom.left ≫
    (localProjection X C hC b).hom.left) (tripleTransition_fac X C hC a b c)
  rw [hc]
  simpa only [tripleInclusion, Category.assoc, ht] using hfac

/-- The entire full native cocycle follows by cancelling the actual mono triple projection. -/
theorem tripleTransition_cocycle (a b c : X.obj.left) :
    tripleTransition X C hC a b c ≫ tripleTransition X C hC b c a ≫
      tripleTransition X C hC c a b = 𝟙 _ := by
  let l := tripleTransition X C hC a b c
  let m := tripleTransition X C hC b c a
  let n := tripleTransition X C hC c a b
  let q := tripleInclusion X C hC a b c ≫ (localProjection X C hC a).hom.left
  have hOver : (l ≫ m ≫ n) ≫ q = q := by
    change (l ≫ m ≫ n) ≫ tripleInclusion X C hC a b c ≫
      (localProjection X C hC a).hom.left = _
    simp only [Category.assoc]
    rw [tripleTransition_over X C hC c a b, tripleTransition_over X C hC b c a,
      tripleTransition_over X C hC a b c]
  have : Mono q := by
    dsimp only [q]
    infer_instance
  apply (cancel_mono q).mp
  simpa only [Category.id_comp] using hOver

/-- Every native gluing datum is DERIVED from the ordinary analytic centre. -/
def glueData : LocallyRingedSpace.GlueData where
  J := X.obj.left
  U a := (localObject X C hC a).obj.left
  V p := (overlapObject X C hC p.1 p.2).obj.left
  f a b := (overlapInclusion X C hC a b).hom.left
  f_id _ := inferInstance
  t a b := (transition X C hC a b).hom.left
  t_id a := congrArg (fun f => f.hom.left) (transition_self X C hC a)
  t' := tripleTransition X C hC
  t_fac := tripleTransition_fac X C hC
  cocycle := tripleTransition_cocycle X C hC
  f_open _ _ := inferInstance

end

end Hironaka.Analytic.Unibranch.OriginalAnalyticClosedSubspaceOverlap
