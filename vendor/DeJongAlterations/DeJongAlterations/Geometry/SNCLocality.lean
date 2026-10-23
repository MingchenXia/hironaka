import DeJongAlterations.Geometry.SNCIso
import Mathlib.Topology.LocalAtTarget

/-!
# Zariski locality of native strict normal crossings

The component restrictions and their intersection structures are constructed
from the actual open immersions of native closed subschemes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open Scheme.IdealSheafData
open DeJongAlterations.Geometry.ReducedClosedSubscheme

namespace DeJongAlterations.Geometry.SNCLocality

universe u v

variable {X U : Scheme.{u}}

/-- The actual map from a pulled-back native closed subscheme. -/
def comapSubschemeMap (f : U ⟶ X) (D : X.IdealSheafData) :
    (D.comap f).subscheme ⟶ D.subscheme :=
  (D.comapIso f).hom ≫ pullback.snd f D.subschemeι

instance comapSubschemeMap_isOpenImmersion (f : U ⟶ X) [IsOpenImmersion f]
    (D : X.IdealSheafData) : IsOpenImmersion (comapSubschemeMap f D) := by
  dsimp [comapSubschemeMap]
  infer_instance

@[reassoc (attr := simp)]
theorem comapSubschemeMap_ι (f : U ⟶ X) (D : X.IdealSheafData) :
    comapSubschemeMap f D ≫ D.subschemeι = (D.comap f).subschemeι ≫ f := by
  dsimp [comapSubschemeMap]
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, comapIso_hom_fst]

theorem comapSubschemeMap_val (f : U ⟶ X) (D : X.IdealSheafData)
    (z : (D.comap f).subscheme) : (comapSubschemeMap f D z).val = f z.val := by
  have h := congrArg (fun g : (D.comap f).subscheme ⟶ X ↦ g z) (comapSubschemeMap_ι f D)
  simpa only [Scheme.Hom.comp_apply, subschemeι_apply] using h

/-- Actual compatible points lift to the native pulled-back closed subscheme. -/
theorem exists_subschemeLift (f : U ⟶ X) (D : X.IdealSheafData) (y : U) (z : D.subscheme)
    (hy : f y = z.val) :
    ∃ w : (D.comap f).subscheme, w.val = y ∧ comapSubschemeMap f D w = z := by
  obtain ⟨p, hp₁, hp₂⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := D.subschemeι) y z hy
  refine ⟨(D.comapIso f).inv p, ?_, ?_⟩
  · have h := congrArg (fun g : pullback f D.subschemeι ⟶ U ↦ g p)
      (comapIso_inv_subschemeι D f)
    have h' := h.trans hp₁
    simpa only [Scheme.Hom.comp_apply, subschemeι_apply] using h'
  · have hcomp : (D.comapIso f).inv ≫ comapSubschemeMap f D = pullback.snd f D.subschemeι := by
      simp only [comapSubschemeMap, Iso.inv_hom_id_assoc]
    have h := congrArg (fun g : pullback f D.subschemeι ⟶ D.subscheme ↦ g p) hcomp
    exact h.trans hp₂

theorem isReduced_comap (f : U ⟶ X) [IsOpenImmersion f] (D : X.IdealSheafData)
    [IsReduced D.subscheme] : IsReduced (D.comap f).subscheme :=
  isReduced_of_isOpenImmersion (comapSubschemeMap f D)

theorem comap_vanishingIdeal (f : U ⟶ X) [IsOpenImmersion f] (T : Closeds X) :
    (vanishingIdeal T).comap f = vanishingIdeal (T.preimage f.continuous) := by
  let : IsReduced (vanishingIdeal T).subscheme := isReduced_vanishingIdeal_subscheme T
  let : IsReduced ((vanishingIdeal T).comap f).subscheme := isReduced_comap f _
  let : IsReduced (vanishingIdeal (T.preimage f.continuous)).subscheme :=
    isReduced_vanishingIdeal_subscheme _
  apply idealSheaf_eq_of_isReduced_of_support_eq
  simp only [support_comap, support_vanishingIdeal]

/-- Regularity at a point is detected on its actual open restriction. -/
theorem isRegularLocalRing_of_comap (f : U ⟶ X) [IsOpenImmersion f] (D : X.IdealSheafData)
    (y : U) (z : D.subscheme) (hy : f y = z.val)
    (hreg : IsRegularScheme (D.comap f).subscheme) :
    IsRegularLocalRing (D.subscheme.presheaf.stalk z) := by
  obtain ⟨w, _, hw⟩ := exists_subschemeLift f D y z hy
  let : IsRegularLocalRing ((D.comap f).subscheme.presheaf.stalk w) := hreg w
  have hr := IsRegularLocalRing.of_ringEquiv
    (asIso ((comapSubschemeMap f D).stalkMap w)).symm.commRingCatIsoToRingEquiv
  rw [hw] at hr
  exact hr

theorem isReduced_of_openCover_comap (D : X.IdealSheafData) (𝒰 : X.OpenCover.{v})
    (hD : ∀ i, IsReduced (D.comap (𝒰.f i)).subscheme) : IsReduced D.subscheme := by
  let : ∀ z : D.subscheme, _root_.IsReduced (D.subscheme.presheaf.stalk z) := by
    intro z
    obtain ⟨y, hy⟩ := 𝒰.covers z.val
    obtain ⟨w, _, hw⟩ := exists_subschemeLift (𝒰.f (𝒰.idx z.val)) D y z hy
    let : IsReduced (D.comap (𝒰.f (𝒰.idx z.val))).subscheme := hD _
    have hr : _root_.IsReduced (D.subscheme.presheaf.stalk
        (comapSubschemeMap (𝒰.f (𝒰.idx z.val)) D w)) :=
      isReduced_of_injective ((comapSubschemeMap (𝒰.f (𝒰.idx z.val)) D).stalkMap w).hom
        (asIso ((comapSubschemeMap (𝒰.f (𝒰.idx z.val)) D).stalkMap w)).commRingCatIsoToRingEquiv.injective
    rw [hw] at hr
    exact hr
  exact isReduced_of_isReduced_stalk _

theorem divisorComponent_isIrreducible (D : X.IdealSheafData) (C : DivisorComponent D) :
    IsIrreducible (C.val : Set X) := by
  obtain ⟨S, hS, hC⟩ := C.property
  rw [← hC]
  exact hS.1.image Subtype.val continuous_subtype_val.continuousOn

/-- A global component meeting an actual open chart restricts to an actual component. -/
def componentRestrict (f : U ⟶ X) [IsOpenImmersion f] (D : X.IdealSheafData)
    (C : DivisorComponent D) (hC : ((C.val : Set X) ∩ Set.range f).Nonempty) :
    DivisorComponent (D.comap f) := by
  refine ⟨C.val.preimage f.continuous, ?_⟩
  obtain ⟨S, hS, hSC⟩ := C.property
  let g := comapSubschemeMap f D
  have hmeet : (S ∩ Set.range g).Nonempty := by
    obtain ⟨x, hx, y, hfy⟩ := hC
    rw [← hSC] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    obtain ⟨w, _, hw⟩ := exists_subschemeLift f D y z (hfy.trans hzx.symm)
    exact ⟨z, hz, w, hw⟩
  refine ⟨g ⁻¹' S, preimage_mem_irreducibleComponents hS g.isOpenEmbedding hmeet, ?_⟩
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hmem : (g w).val ∈ (C.val : Set X) := hSC ▸ Set.mem_image_of_mem Subtype.val hw
    change f w.val ∈ (C.val : Set X)
    simpa only [g, comapSubschemeMap_val] using hmem
  · intro hy
    change f y ∈ (C.val : Set X) at hy
    rw [← hSC] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    obtain ⟨w, hw, hgw⟩ := exists_subschemeLift f D y z hzy.symm
    refine ⟨w, ?_, hw⟩
    change g w ∈ S
    rw [hgw]
    exact hz

theorem componentRestrict_val (f : U ⟶ X) [IsOpenImmersion f] (D : X.IdealSheafData)
    (C : DivisorComponent D) (hC : ((C.val : Set X) ∩ Set.range f).Nonempty) :
    (componentRestrict f D C hC).val = C.val.preimage f.continuous := rfl

/-- A nonempty open restriction remembers its entire global irreducible component. -/
theorem componentRestrict_closure (f : U ⟶ X) [IsOpenImmersion f] (D : X.IdealSheafData)
    (C : DivisorComponent D) (hC : ((C.val : Set X) ∩ Set.range f).Nonempty) :
    closure (f '' ((componentRestrict f D C hC).val : Set U)) = (C.val : Set X) := by
  apply closure_image_preimage_of_isPreirreducible f f.isOpenEmbedding.isOpenMap
  · obtain ⟨_, hx, y, rfl⟩ := hC
    exact ⟨y, hx⟩
  · exact (divisorComponent_isIrreducible D C).2
  · exact C.val.isClosed

/-- Distinct actual global components cannot coincide in an open meeting both. -/
theorem componentRestrict_injective (f : U ⟶ X) [IsOpenImmersion f] (D : X.IdealSheafData)
    (C C' : DivisorComponent D)
    (hC : ((C.val : Set X) ∩ Set.range f).Nonempty)
    (hC' : ((C'.val : Set X) ∩ Set.range f).Nonempty)
    (heq : componentRestrict f D C hC = componentRestrict f D C' hC') : C = C' := by
  apply Subtype.ext
  apply Closeds.ext
  rw [← componentRestrict_closure f D C hC, ← componentRestrict_closure f D C' hC', heq]

/-- Restrict the finite family of actual components that meet the open chart. -/
def restrictedFamily (f : U ⟶ X) [IsOpenImmersion f] (D : X.IdealSheafData)
    (J : Finset (DivisorComponent D))
    (hmeet : ∀ C ∈ J, ((C.val : Set X) ∩ Set.range f).Nonempty) :
    Finset (DivisorComponent (D.comap f)) := by
  classical
  exact J.attach.image (fun C ↦ componentRestrict f D C.val (hmeet C.val C.property))

theorem restrictedFamily_card (f : U ⟶ X) [IsOpenImmersion f] (D : X.IdealSheafData)
    (J : Finset (DivisorComponent D))
    (hmeet : ∀ C ∈ J, ((C.val : Set X) ∩ Set.range f).Nonempty) :
    (restrictedFamily f D J hmeet).card = J.card := by
  classical
  have hinj : Function.Injective (fun C : {C // C ∈ J} ↦
      componentRestrict f D C.val (hmeet C.val C.property)) := by
    intro C C' h
    exact Subtype.ext (componentRestrict_injective f D C.val C'.val _ _ h)
  simp only [restrictedFamily, Finset.card_image_of_injective _ hinj, Finset.card_attach]

theorem restrictedFamily_nonempty (f : U ⟶ X) [IsOpenImmersion f] (D : X.IdealSheafData)
    (J : Finset (DivisorComponent D))
    (hmeet : ∀ C ∈ J, ((C.val : Set X) ∩ Set.range f).Nonempty) (hJ : J.Nonempty) :
    (restrictedFamily f D J hmeet).Nonempty := by
  classical
  simpa only [restrictedFamily, Finset.image_nonempty, Finset.attach_nonempty_iff] using hJ

theorem comap_iSup {ι : Sort*} (f : U ⟶ X) (D : ι → X.IdealSheafData) :
    (⨆ i, D i).comap f = ⨆ i, (D i).comap f :=
  (map_gc f).l_iSup

/-- The actual intersection ideal pulls back to the sum of the restricted
component ideals, without radicalizing that sum. -/
theorem componentIntersection_comap_of_meets (f : U ⟶ X) [IsOpenImmersion f]
    (D : X.IdealSheafData) (J : Finset (DivisorComponent D))
    (hmeet : ∀ C ∈ J, ((C.val : Set X) ∩ Set.range f).Nonempty) :
    (componentIntersection D J).comap f =
      componentIntersection (D.comap f) (restrictedFamily f D J hmeet) := by
  classical
  simp only [componentIntersection, comap_iSup]
  apply le_antisymm
  · refine iSup_le fun C ↦ iSup_le fun hC ↦ ?_
    have hmem : componentRestrict f D C (hmeet C hC) ∈ restrictedFamily f D J hmeet := by
      unfold restrictedFamily
      exact Finset.mem_image.mpr ⟨⟨C, hC⟩, Finset.mem_attach _ _, rfl⟩
    apply le_iSup_of_le (componentRestrict f D C (hmeet C hC))
    apply le_iSup_of_le hmem
    rw [componentRestrict_val, comap_vanishingIdeal]
  · refine iSup_le fun C ↦ iSup_le fun hC ↦ ?_
    unfold restrictedFamily at hC
    obtain ⟨C₀, _, rfl⟩ := Finset.mem_image.mp hC
    apply le_iSup_of_le C₀.val
    apply le_iSup_of_le C₀.property
    rw [componentRestrict_val, comap_vanishingIdeal]

section Topology

variable {P Q : Type*} [TopologicalSpace P] [TopologicalSpace Q]

theorem genericPoint_preimage {f : P → Q} (hf : Topology.IsEmbedding f)
    {S : Set Q} {x : P} (hx : IsGenericPoint (f x) S) :
    IsGenericPoint x (f ⁻¹' S) := by
  change closure {x} = f ⁻¹' S
  have heq : closure {f x} = S := hx
  rw [← heq]
  simpa only [Set.image_singleton] using hf.closure_eq_preimage_closure_image {x}

end Topology

/-- Pure codimension in an open chart gives the actual ambient stalk dimension
at any global component generic point contained in that chart. -/
theorem krullDim_at_genericPoint_of_comap (f : U ⟶ X) [IsOpenImmersion f]
    (E : X.IdealSheafData) {r : ℕ} (hE : HasPureCodimension (E.comap f).support r)
    (C : Set E.support) (hC : C ∈ irreducibleComponents E.support)
    (x : X) (hx : IsGenericPoint x (Subtype.val '' C)) (y : U) (hy : f y = x) :
    ringKrullDim (X.presheaf.stalk x) = r := by
  subst x
  let C₀ := divisorComponentOf E C hC
  have hmeet : ((C₀.val : Set X) ∩ Set.range f).Nonempty :=
    ⟨f y, hx.mem, y, rfl⟩
  let C' := componentRestrict f E C₀ hmeet
  obtain ⟨S, hS, hSC'⟩ := C'.property
  have hygeneric : IsGenericPoint y (Subtype.val '' S) := by
    rw [hSC']
    change IsGenericPoint y (f ⁻¹' (Subtype.val '' C))
    exact genericPoint_preimage f.isOpenEmbedding.isEmbedding hx
  have hdim := hE S hS y hygeneric
  exact
    (ringKrullDim_eq_of_ringEquiv
      (asIso (f.stalkMap y)).commRingCatIsoToRingEquiv).trans hdim

/-- Every selected component meets any chart through a point of its actual intersection. -/
theorem components_meet_of_mem_intersection (f : U ⟶ X) (D : X.IdealSheafData)
    (J : Finset (DivisorComponent D)) (x : X)
    (hx : x ∈ (componentIntersection D J).support) (y : U) (hy : f y = x) :
    ∀ C ∈ J, ((C.val : Set X) ∩ Set.range f).Nonempty := by
  intro C hC
  refine ⟨x, ?_, y, hy⟩
  rw [componentIntersection_support] at hx
  exact (Closeds.mem_iInf.mp (Closeds.mem_iInf.mp hx C)) hC

/-- Native strict normal crossings descends from a genuine Zariski open cover. -/
theorem isStrictNormalCrossings_of_openCover (D : X.IdealSheafData) (𝒰 : X.OpenCover.{v})
    (hD : ∀ i, IsStrictNormalCrossings (D.comap (𝒰.f i))) :
    IsStrictNormalCrossings D := by
  refine ⟨CartierLocality.of_openCover D 𝒰 (fun i ↦ (hD i).cartier),
    isReduced_of_openCover_comap D 𝒰 (fun i ↦ (hD i).reduced), ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy⟩ := 𝒰.covers x
    have hymem : y ∈ (D.comap (𝒰.f (𝒰.idx x))).support := by
      rw [support_comap]
      change (𝒰.f (𝒰.idx x)) y ∈ D.support
      rw [hy]
      exact hx
    let : IsRegularLocalRing ((𝒰.X (𝒰.idx x)).presheaf.stalk y) :=
      (hD (𝒰.idx x)).regularAlong y hymem
    have hr := IsRegularLocalRing.of_ringEquiv
      (asIso ((𝒰.f (𝒰.idx x)).stalkMap y)).symm.commRingCatIsoToRingEquiv
    rw [hy] at hr
    exact hr
  · intro J hJ z
    let E := componentIntersection D J
    obtain ⟨y, hy⟩ := 𝒰.covers z.val
    have hmeet := components_meet_of_mem_intersection
      (𝒰.f (𝒰.idx z.val)) D J z.val z.property y hy
    have hreg := (hD (𝒰.idx z.val)).intersectionsRegular
      (restrictedFamily (𝒰.f (𝒰.idx z.val)) D J hmeet)
      (restrictedFamily_nonempty _ D J hmeet hJ)
    have hreg' : IsRegularScheme (E.comap (𝒰.f (𝒰.idx z.val))).subscheme := by
      dsimp only [E]
      rw [componentIntersection_comap_of_meets _ D J hmeet]
      exact hreg
    exact isRegularLocalRing_of_comap _ E y z hy hreg'
  · intro J hJ C hC x hx
    let E := componentIntersection D J
    obtain ⟨y, hy⟩ := 𝒰.covers x
    have hxE : x ∈ E.support := by
      obtain ⟨z, _, hzx⟩ := hx.mem
      exact hzx ▸ z.property
    have hmeet := components_meet_of_mem_intersection
      (𝒰.f (𝒰.idx x)) D J x hxE y hy
    have hcodim := (hD (𝒰.idx x)).intersectionsCodimension
      (restrictedFamily (𝒰.f (𝒰.idx x)) D J hmeet)
      (restrictedFamily_nonempty _ D J hmeet hJ)
    have hcodim' : HasPureCodimension (E.comap (𝒰.f (𝒰.idx x))).support J.card := by
      dsimp only [E]
      rw [componentIntersection_comap_of_meets _ D J hmeet]
      rw [restrictedFamily_card] at hcodim
      exact hcodim
    exact krullDim_at_genericPoint_of_comap _ E hcodim' C hC x hx y hy

end DeJongAlterations.Geometry.SNCLocality
