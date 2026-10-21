/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspace

/-!
# Actual holomorphic presentation maps of reduced analytic subspace models

Literal pullback of original holomorphic sections descends through the entire
vanishing section ideals. Actual sheafification and inverse-image adjunctions
construct the subspace morphism, without any structure-sheaf isomorphism input.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticSubspaceMaps
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaSmoothCentreRealDomainActualIdealPresheaf
  HironakaSmoothCentreRealDomainActualCentreRingSheaf
  HironakaActualAnalyticSubspace
variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

/-- Actual subspace inclusions are monomorphisms because their whole stalk maps are surjective. -/
instance actualSubspaceInclusion_mono (C : Set M) : Mono (actualSubspaceInclusion (n := n) C) := by
  apply LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map
  apply SheafedSpace.mono_of_base_injective_of_stalk_epi
  · exact Subtype.val_injective
  · intro x
    exact ConcreteCategory.epi_of_surjective _
      (actualSubspaceInclusionRingedHom_stalk_surjective (n := n) C x)

/-- The literal original continuous ambient map. -/
@[implicit_reducible]
def actualAmbientMap {f : M → N} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f) :
    TopCat.of M ⟶ TopCat.of N := TopCat.ofHom ⟨f,hf.continuous⟩

/-- The literal original map restricted to the two genuine subspaces. -/
@[implicit_reducible]
def actualSubspaceMapTop {f : M → N} (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) : TopCat.of C ⟶ TopCat.of D :=
  TopCat.ofHom ⟨fun x => ⟨f x.val,hCD x.val x.property⟩,
    (hf.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Literal holomorphic pullback sends the whole target vanishing section ideal into the source one. -/
theorem actualSectionPullback_vanishing {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D)
    (U : Opens N) (s : actualComplexSection (n := m) U)
    (hs : s ∈ actualSectionIdeal (vanishingIdeal (n := m) D) U) :
    (ChartedSpace.locallyRingedSpaceMap f hf).toHom.c.app (op U) s ∈
      actualSectionIdeal (vanishingIdeal (n := n) C) ((Opens.map (actualAmbientMap hf)).obj U) := by
  apply (actualSectionIdeal_vanishing_iff C _ _).mpr
  intro x hx hxC
  change s ⟨f x,hx⟩ = 0
  exact (actualSectionIdeal_vanishing_iff D U s).mp hs (f x) hx (hCD x hxC)

/-- Pullback of actual section quotients is constructed from the original holomorphic map. -/
def actualQuotientSectionMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) (U : Opens N) :
    actualCentreRingSection (n := m) D U →+*
      actualCentreRingSection (n := n) C ((Opens.map (actualAmbientMap hf)).obj U) :=
  Ideal.Quotient.lift (actualSectionIdeal (vanishingIdeal (n := m) D) U)
    ((Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C)
      ((Opens.map (actualAmbientMap hf)).obj U))).comp
      ((ChartedSpace.locallyRingedSpaceMap f hf).toHom.c.app (op U)).hom)
    (fun s hs => Ideal.Quotient.eq_zero_iff_mem.mpr (actualSectionPullback_vanishing hf hCD U s hs))

/-- Whole quotient numerator classes retain the literal original section pullback. -/
theorem actualQuotientSectionMap_mk {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) (U : Opens N)
    (s : actualComplexSection (n := m) U) :
    actualQuotientSectionMap hf hCD U (Ideal.Quotient.mk _ s) =
      Ideal.Quotient.mk _ ((ChartedSpace.locallyRingedSpaceMap f hf).toHom.c.app (op U) s) := rfl

/-- Literal original restrictions make the quotient maps an actual natural transformation. -/
def actualQuotientPresheafMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    actualCentreRingPresheaf (n := m) D ⟶
      (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).obj
        (actualCentreRingPresheaf (n := n) C) where
  app U := CommRingCat.ofHom (actualQuotientSectionMap hf hCD (unop U))
  naturality U V i := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext s
    exact congrArg
      (Ideal.Quotient.mk (actualSectionIdeal (vanishingIdeal (n := n) C)
        ((Opens.map (actualAmbientMap hf)).obj (unop V))))
      (ConcreteCategory.congr_hom ((ChartedSpace.locallyRingedSpaceMap f hf).toHom.c.naturality i) s)

/-- Actual sheafification constructs the whole ambient quotient-sheaf pullback morphism. -/
def actualQuotientSheafMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    (actualCentreRingSheaf (n := m) D).presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).obj
        (actualCentreRingSheaf (n := n) C).presheaf :=
  sheafifyLift (Opens.grothendieckTopology (TopCat.of N))
    (actualQuotientPresheafMap hf hCD ≫
      (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map
        (actualCentreRingSheafUnit (n := n) C))
    ((TopCat.Sheaf.pushforward CommRingCat (actualAmbientMap hf)).obj
      (actualCentreRingSheaf (n := n) C)).property

/-- The actual ambient quotient sheaf has its original inverse-image unit into the subspace. -/
def actualQuotientToSubspace (C : Set M) :
    (actualCentreRingSheaf (n := n) C).presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion C)).obj
        (actualSubspaceSheaf (n := n) C).presheaf :=
  (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
    (actualSubspaceTopInclusion C)).unit.app (actualCentreRingSheaf (n := n) C).presheaf ≫
    (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion C)).map
      (actualSubspaceSheafUnit (n := n) C)

/-- The genuine inverse-image adjunction uses the literal commutative subtype square. -/
def actualSubspacePresheafMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    actualSubspacePresheaf (n := m) D ⟶
      (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceMapTop hf hCD)).obj
        (actualSubspaceSheaf (n := n) C).presheaf := by
  exact ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
    (actualSubspaceTopInclusion D)).homEquiv (actualCentreRingSheaf (n := m) D).presheaf
      ((TopCat.Presheaf.pushforward CommRingCat (actualSubspaceMapTop hf hCD)).obj
        (actualSubspaceSheaf (n := n) C).presheaf)).symm
    (actualQuotientSheafMap hf hCD ≫
      (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map (actualQuotientToSubspace C))

/-- The actual subspace structure-sheaf morphism is built by its genuine universal property. -/
def actualSubspaceSheafMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    (actualSubspaceSheaf (n := m) D).presheaf ⟶
      (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceMapTop hf hCD)).obj
        (actualSubspaceSheaf (n := n) C).presheaf :=
  sheafifyLift (Opens.grothendieckTopology (TopCat.of D)) (actualSubspacePresheafMap hf hCD)
    ((TopCat.Sheaf.pushforward CommRingCat (actualSubspaceMapTop hf hCD)).obj
      (actualSubspaceSheaf (n := n) C)).property

/-- A true global morphism of the independently constructed ringed subspaces. -/
@[implicit_reducible]
def actualSubspaceRingedMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    (actualSubspaceLocallyRingedSpace (n := n) C).toPresheafedSpace ⟶
      (actualSubspaceLocallyRingedSpace (n := m) D).toPresheafedSpace where
  base := actualSubspaceMapTop hf hCD
  c := actualSubspaceSheafMap hf hCD


/-- The actual quotient-sheaf lift retains the complete original quotient-presheaf map. -/
theorem actualQuotientSheafMap_unit {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    actualCentreRingSheafUnit (n := m) D ≫ actualQuotientSheafMap hf hCD =
      actualQuotientPresheafMap hf hCD ≫
        (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map
          (actualCentreRingSheafUnit (n := n) C) :=
  toSheafify_sheafifyLift _ _ _

/-- The descended whole ambient quotient map commutes with the original holomorphic pullback. -/
theorem actualQuotientSheafMap_ambient {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    (actualCentreAmbientRingSheafMap (n := m) D).hom ≫ actualQuotientSheafMap hf hCD =
      (ChartedSpace.locallyRingedSpaceMap f hf).toHom.c ≫
        (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map
          (actualCentreAmbientRingSheafMap (n := n) C).hom := by
  change (actualCentreAmbientRingMap (n := m) D ≫ actualCentreRingSheafUnit (n := m) D) ≫ _ = _
  rw [Category.assoc,actualQuotientSheafMap_unit]
  ext U s
  rfl

/-- The second actual sheafification lift retains its genuine inverse-image presheaf map. -/
theorem actualSubspaceSheafMap_unit {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    actualSubspaceSheafUnit (n := m) D ≫ actualSubspaceSheafMap hf hCD =
      actualSubspacePresheafMap hf hCD := toSheafify_sheafifyLift _ _ _

/-- The actual inverse-image adjunction satisfies its original numerator unit equation. -/
theorem actualSubspacePresheafMap_unit {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
      (actualSubspaceTopInclusion D)).unit.app (actualCentreRingSheaf (n := m) D).presheaf ≫
      (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion D)).map
        (actualSubspacePresheafMap hf hCD) =
      actualQuotientSheafMap hf hCD ≫
        (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map
          (actualQuotientToSubspace C) := by
  have h := ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat
    (actualSubspaceTopInclusion D)).homEquiv (actualCentreRingSheaf (n := m) D).presheaf
      ((TopCat.Presheaf.pushforward CommRingCat (actualSubspaceMapTop hf hCD)).obj
        (actualSubspaceSheaf (n := n) C).presheaf)).apply_symm_apply
    (actualQuotientSheafMap hf hCD ≫
      (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map (actualQuotientToSubspace C))
  rw [Adjunction.homEquiv_unit] at h
  exact h

private theorem actualQuotientToSubspace_map {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    actualQuotientToSubspace (n := m) D ≫
      (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion D)).map
        (actualSubspaceSheafMap hf hCD) =
      actualQuotientSheafMap hf hCD ≫
        (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map
          (actualQuotientToSubspace C) := by
  change (_ ≫ (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion D)).map
      (actualSubspaceSheafUnit (n := m) D)) ≫ _ = _
  rw [Category.assoc,← Functor.map_comp,actualSubspaceSheafMap_unit]
  exact actualSubspacePresheafMap_unit hf hCD

private theorem actualSubspaceRingedMap_c {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    (ChartedSpace.locallyRingedSpaceMap f hf).toHom.c ≫
      (TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)).map
        ((actualCentreAmbientRingSheafMap (n := n) C).hom ≫ actualQuotientToSubspace C) =
    ((actualCentreAmbientRingSheafMap (n := m) D).hom ≫ actualQuotientToSubspace D) ≫
      (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion D)).map
        (actualSubspaceSheafMap hf hCD) := by
  let F := (ChartedSpace.locallyRingedSpaceMap f hf).toHom.c
  let A := (actualCentreAmbientRingSheafMap (n := n) C).hom
  let B := (actualCentreAmbientRingSheafMap (n := m) D).hom
  let Q := actualQuotientToSubspace (n := n) C
  let R := actualQuotientToSubspace (n := m) D
  let P := TopCat.Presheaf.pushforward CommRingCat (actualAmbientMap hf)
  let H := actualQuotientSheafMap hf hCD
  let G := (TopCat.Presheaf.pushforward CommRingCat (actualSubspaceTopInclusion D)).map
    (actualSubspaceSheafMap hf hCD)
  have hA : B ≫ H=F ≫ P.map A := actualQuotientSheafMap_ambient hf hCD
  have hB : R ≫ G=H ≫ P.map Q := actualQuotientToSubspace_map hf hCD
  change F ≫ P.map (A ≫ Q)=(B ≫ R) ≫ G
  calc
    F ≫ P.map (A ≫ Q)=F ≫ (P.map A ≫ P.map Q) :=
      congrArg (fun a => F ≫ a) (P.map_comp A Q)
    _ = (F ≫ P.map A) ≫ P.map Q := (Category.assoc _ _ _).symm
    _ = (B ≫ H) ≫ P.map Q := congrArg (fun a => a ≫ P.map Q) hA.symm
    _ = B ≫ (H ≫ P.map Q) := Category.assoc _ _ _
    _ = B ≫ (R ≫ G) := congrArg (fun a => B ≫ a) hB.symm
    _ = (B ≫ R) ≫ G := (Category.assoc _ _ _).symm

/-- The constructed actual ringed subspace morphism commutes with both original inclusions. -/
theorem actualSubspaceRingedMap_inclusion {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    actualSubspaceInclusionRingedHom (n := n) C ≫
        (ChartedSpace.locallyRingedSpaceMap f hf).toHom =
      actualSubspaceRingedMap hf hCD ≫ actualSubspaceInclusionRingedHom (n := m) D := by
  refine PresheafedSpace.hext
    (actualSubspaceInclusionRingedHom (n := n) C ≫ (ChartedSpace.locallyRingedSpaceMap f hf).toHom)
    (actualSubspaceRingedMap hf hCD ≫ actualSubspaceInclusionRingedHom (n := m) D) rfl ?_
  exact heq_of_eq (actualSubspaceRingedMap_c hf hCD)

private theorem inclusionRingedHom_base_apply (C : Set M) (x : C) :
    (actualSubspaceInclusionRingedHom (n := n) C).base x=x.val := rfl

private theorem subspaceRingedMap_base_apply {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) (x : C) :
    (actualSubspaceRingedMap hf hCD).base x=actualSubspaceMapTop hf hCD x := rfl

omit [IsComplexManifold n M] [IsComplexManifold m N] in
private theorem subspaceMapTop_val {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) (x : C) :
    (actualSubspaceMapTop hf hCD x).val=f x.val := rfl

omit [IsComplexManifold n M] [IsComplexManifold m N] in
private theorem ambientRingedMap_base_apply {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f) (x : M) :
    (ChartedSpace.locallyRingedSpaceMap f hf).toHom.base x=f x := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The actual whole stalk square is induced by the independently constructed global morphisms. -/
theorem actualSubspaceRingedMap_stalk_square {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) (x : C) :
    (actualSubspaceInclusion (n := m) D).toHom.stalkMap (actualSubspaceMapTop hf hCD x) ≫
        (actualSubspaceRingedMap hf hCD).stalkMap x =
      (ChartedSpace.locallyRingedSpaceMap f hf).toHom.stalkMap x.val ≫
        (actualSubspaceInclusion (n := n) C).toHom.stalkMap x := by
  change (actualSubspaceInclusionRingedHom (n := m) D).stalkMap (actualSubspaceMapTop hf hCD x) ≫
      (actualSubspaceRingedMap hf hCD).stalkMap x =
    (ChartedSpace.locallyRingedSpaceMap f hf).toHom.stalkMap x.val ≫
      (actualSubspaceInclusionRingedHom (n := n) C).stalkMap x
  have h := PresheafedSpace.stalkMap.congr_hom
    (actualSubspaceInclusionRingedHom (n := n) C ≫ (ChartedSpace.locallyRingedSpaceMap f hf).toHom)
    (actualSubspaceRingedMap hf hCD ≫ actualSubspaceInclusionRingedHom (n := m) D)
    (actualSubspaceRingedMap_inclusion hf hCD) x
  simpa only [PresheafedSpace.stalkMap.comp,PresheafedSpace.comp_base,TopCat.comp_app,
    inclusionRingedHom_base_apply,subspaceRingedMap_base_apply,subspaceMapTop_val,
    ambientRingedMap_base_apply,eqToHom_refl,Category.id_comp] using h.symm

/-- The true constructed quotient-subspace stalk pullback is local. -/
theorem actualSubspaceRingedMap_stalk_isLocalHom {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) (x : C) :
    IsLocalHom ((actualSubspaceRingedMap hf hCD).stalkMap x).hom := by
  refine ⟨?_⟩
  intro a ha
  obtain ⟨r,rfl⟩ := actualSubspaceInclusionRingedHom_stalk_surjective (n := m) D
    (actualSubspaceMapTop hf hCD x) a
  have h := ConcreteCategory.congr_hom (actualSubspaceRingedMap_stalk_square hf hCD x) r
  simp only [ConcreteCategory.comp_apply] at h
  let k := ((actualSubspaceInclusion (n := n) C).stalkMap x).hom.comp
    ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val).hom
  let : IsLocalHom k := by
    dsimp only [k]
    infer_instance
  have hk : IsUnit (k r) := h ▸ ha
  have hr := isUnit_of_map_unit k r hk
  exact ((actualSubspaceInclusion (n := m) D).stalkMap (actualSubspaceMapTop hf hCD x)).hom.isUnit_map hr

/-- Actual original holomorphic geometry supplies the genuine local subspace morphism. -/
@[implicit_reducible]
def actualSubspaceMap {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    actualSubspaceLocallyRingedSpace (n := n) C ⟶ actualSubspaceLocallyRingedSpace (n := m) D where
  toHom := actualSubspaceRingedMap hf hCD
  prop := actualSubspaceRingedMap_stalk_isLocalHom hf hCD

/-- The genuine locally ringed subspace pullback commutes with both actual ambient inclusions. -/
theorem actualSubspaceMap_inclusion {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) :
    actualSubspaceInclusion (n := n) C ≫ ChartedSpace.locallyRingedSpaceMap f hf =
      actualSubspaceMap hf hCD ≫ actualSubspaceInclusion (n := m) D := by
  apply LocallyRingedSpace.Hom.ext'
  exact actualSubspaceRingedMap_inclusion hf hCD

/-- On every whole original quotient numerator the genuine subspace map is literal original pullback. -/
theorem actualSubspaceMap_stalk {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    {C : Set M} {D : Set N} (hCD : ∀ x ∈ C, f x ∈ D) (x : C)
    (r : actualComplexStructureStalk (n := m) (f x.val)) :
    actualSubspaceStalkWholeEquiv (n := n) C x
      ((actualSubspaceMap hf hCD).stalkMap x
        ((actualSubspaceInclusion (n := m) D).stalkMap (actualSubspaceMapTop hf hCD x) r)) =
      Ideal.Quotient.mk (actualWholeSheafStalkIdeal (vanishingIdeal (n := n) C) x.val)
        ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val r) := by
  have h := ConcreteCategory.congr_hom (actualSubspaceRingedMap_stalk_square hf hCD x) r
  simp only [ConcreteCategory.comp_apply] at h
  exact (congrArg (actualSubspaceStalkWholeEquiv (n := n) C x) h).trans
    (actualSubspaceInclusion_stalk (n := n) C x
      ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x.val r))


/-- The actual original identity induces the literal identity on the constructed subspace. -/
theorem actualSubspaceMap_id (C : Set M) :
    actualSubspaceMap (f := (id : M → M)) contMDiff_id (fun _ hx => hx) =
      𝟙 (actualSubspaceLocallyRingedSpace (n := n) C) := by
  apply (cancel_mono (actualSubspaceInclusion (n := n) C)).mp
  simpa only [ChartedSpace.locallyRingedSpace_id,Category.comp_id,Category.id_comp] using
    (actualSubspaceMap_inclusion (f := (id : M → M)) contMDiff_id (fun _ hx => hx)).symm

/-- Actual original holomorphic composition is retained at the entire constructed subspace level. -/
theorem actualSubspaceMap_comp {p : ℕ} {P : Type} [TopologicalSpace P]
    [ChartedSpace (ComplexModel p) P] [IsComplexManifold p P]
    {f : M → N} {g : N → P}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel p) ∞ g)
    {C : Set M} {D : Set N} {E : Set P}
    (hCD : ∀ x ∈ C, f x ∈ D) (hDE : ∀ y ∈ D, g y ∈ E) :
    actualSubspaceMap (hg.comp hf) (fun x hx => hDE (f x) (hCD x hx)) =
      actualSubspaceMap hf hCD ≫ actualSubspaceMap hg hDE := by
  apply (cancel_mono (actualSubspaceInclusion (n := p) E)).mp
  calc
    _ = actualSubspaceInclusion (n := n) C ≫ ChartedSpace.locallyRingedSpaceMap (g ∘ f) (hg.comp hf) :=
      (actualSubspaceMap_inclusion (hg.comp hf) (fun x hx => hDE (f x) (hCD x hx))).symm
    _ = actualSubspaceInclusion (n := n) C ≫
        (ChartedSpace.locallyRingedSpaceMap f hf ≫ ChartedSpace.locallyRingedSpaceMap g hg) := by
      rw [ChartedSpace.locallyRingedSpace_comp (IM := 𝓘(ℂ, ComplexModel n))
        (IN := 𝓘(ℂ, ComplexModel m)) (IP := 𝓘(ℂ, ComplexModel p)) hf hg]
    _ = _ := by
      rw [← Category.assoc,actualSubspaceMap_inclusion hf hCD,Category.assoc,
        actualSubspaceMap_inclusion hg hDE,← Category.assoc]

/-- Actual ambient biholomorphisms internally induce genuine isomorphisms of the quotient subspaces. -/
def actualSubspaceBiholomorphicIso
    (e : M ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel m)⟯ N)
    (C : Set M) (D : Set N) (hCD : ∀ x, x ∈ C ↔ e x ∈ D) :
    actualSubspaceLocallyRingedSpace (n := n) C ≅ actualSubspaceLocallyRingedSpace (n := m) D where
  hom := actualSubspaceMap e.contMDiff (fun x hx => (hCD x).mp hx)
  inv := actualSubspaceMap e.symm.contMDiff (fun y hy =>
    (hCD (e.symm y)).mpr (by simpa only [e.apply_symm_apply] using hy))
  hom_inv_id := by
    rw [← actualSubspaceMap_comp]
    have hi : (e.symm : N → M) ∘ (e : M → N)=id := funext e.symm_apply_apply
    simpa only [hi] using actualSubspaceMap_id (n := n) C
  inv_hom_id := by
    rw [← actualSubspaceMap_comp]
    have hi : (e : M → N) ∘ (e.symm : N → M)=id := funext e.apply_symm_apply
    simpa only [hi] using actualSubspaceMap_id (n := m) D

end
end Hironaka.HironakaActualAnalyticSubspaceMaps
