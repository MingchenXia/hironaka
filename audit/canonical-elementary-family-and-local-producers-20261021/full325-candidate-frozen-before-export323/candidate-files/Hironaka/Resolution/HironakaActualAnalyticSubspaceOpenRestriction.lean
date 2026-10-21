/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaActualAnalyticSubspacePresentationIndependence
import Hironaka.Resolution.HironakaActualVanishingIntrinsicHSTransport

/-!
# Actual reduced quotient-subspace models commute with genuine open restriction

The native entire sheaf-stalk pullback is identified with the actual chart-germ
pullback on every original numerator. Existing whole vanishing-ideal transport
then proves true quotient-stalk isomorphisms and an actual open immersion; its
universal restriction isomorphism is constructed internally.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaActualAnalyticSubspaceOpenRestriction
noncomputable section
open Hironaka.HolomorphicIdealSheaves
  HironakaSmoothCentreRealDomainActualSheafStalk
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualWholeStalkHolomorphicPullback HironakaActualOpenIntrinsicHS
  HironakaActualVanishingIntrinsicHSTransport HironakaHolomorphicJetChartInvariance
  HironakaHolomorphicJetRankLoci
variable {n m : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (ComplexModel n) M] [IsComplexManifold n M]
  [ChartedSpace (ComplexModel m) N] [IsComplexManifold m N]

set_option backward.isDefEq.respectTransparency.types false in
/-- The native original sheaf pullback is the independently constructed genuine chart-germ pullback. -/
theorem actualNativeStalk_chart_pullback {f : M → N}
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel m) ∞ f)
    (x : M) (r : actualComplexStructureStalk (n := m) (f x)) :
    actualStalkChartEquiv (n := n) x ((ChartedSpace.locallyRingedSpaceMap f hf).stalkMap x r) =
      actualHolomorphicGermPullback hf x (actualStalkChartEquiv (n := m) (f x) r) := by
  obtain ⟨U,hx,s,rfl⟩ := (actualComplexStructureSheaf (n := m) N).presheaf.exists_germ_eq r
  have hF := PresheafedSpace.stalkMap_germ_apply
    (ChartedSpace.locallyRingedSpaceMap f hf).toHom U x hx s
  let V := (Opens.map (actualAmbientMap hf)).obj U
  let a := (ChartedSpace.locallyRingedSpaceMap f hf).toHom.c.app (op U) s
  calc
    _ = actualStalkChartEquiv (n := n) x
        ((actualComplexStructureSheaf (n := n) M).presheaf.germ V x hx a) :=
      congrArg (actualStalkChartEquiv (n := n) x) hF
    _ = sectionChartRingHom V x hx a := actualStalkChartEquiv_germ V x hx a
    _ = _ := by
      rw [actualStalkChartEquiv_germ]
      change chartTranslatedGerm x x (mem_chart_source _ x) (sectionExtension V a)
          (sectionExtension_holomorphicAt V a x hx) =
        actualHolomorphicGermPullback hf x
          (chartTranslatedGerm (f x) (f x) (mem_chart_source _ (f x)) (sectionExtension U s)
            (sectionExtension_holomorphicAt U s (f x) hx))
      rw [actualHolomorphicGermPullback_original_function]
      apply chartTranslatedGerm_congr_original
      filter_upwards [V.isOpen.mem_nhds hx] with z hz
      rw [sectionExtension_apply V a z hz,Function.comp_apply,sectionExtension_apply U s (f z) hz]
      rfl

variable (C : Set M) (U : Opens M)

/-- The SAME actual holomorphic open inclusion induces the genuine quotient-subspace map. -/
@[implicit_reducible]
def actualOpenSubspaceMap :
    actualSubspaceLocallyRingedSpace (n := n) ((Subtype.val : U → M) ⁻¹' C) ⟶
      actualSubspaceLocallyRingedSpace (n := n) C :=
  actualSubspaceMap (f := (Subtype.val : U → M)) contMDiff_subtype_val (fun _ hx => hx)

private theorem inclusion_stalk_chart (D : Set M) (x : D)
    (r : actualComplexStructureStalk (n := n) x.val) :
    actualSubspaceStalkChartEquiv (n := n) D x ((actualSubspaceInclusion (n := n) D).stalkMap x r) =
      Ideal.Quotient.mk _ (actualStalkChartEquiv (n := n) x.val r) := by
  change (Ideal.quotientEquiv _ _ (actualStalkChartEquiv (n := n) x.val)
      (map_actualWholeSheafStalkIdeal (vanishingIdeal (n := n) D) x.val).symm)
    (actualSubspaceStalkWholeEquiv (n := n) D x ((actualSubspaceInclusion (n := n) D).stalkMap x r)) = _
  rw [actualSubspaceInclusion_stalk]
  rfl

/-- Existing actual zero-extension transport constructs a full actual quotient-stalk equivalence. -/
def actualOpenSubspaceStalkEquiv (x : ((Subtype.val : U → M) ⁻¹' C)) :
    ((actualSubspaceSheaf (n := n) C).presheaf.stalk ((actualOpenSubspaceMap (n := n) C U).base x)).carrier ≃+*
      ((actualSubspaceSheaf (n := n) ((Subtype.val : U → M) ⁻¹' C)).presheaf.stalk x).carrier :=
  (actualSubspaceStalkChartEquiv (n := n) C ((actualOpenSubspaceMap (n := n) C U).base x)).trans
    ((Ideal.quotEquivOfEq (wholeChartStalkIdeal_vanishing_actual_open (n := n) U C x.val).symm).trans
      (actualSubspaceStalkChartEquiv (n := n) ((Subtype.val : U → M) ⁻¹' C) x).symm)

set_option backward.isDefEq.respectTransparency.types false in
/-- Every original numerator identifies the actual induced stalk map with that genuine full equivalence. -/
theorem actualOpenSubspaceMap_stalk_apply (x : ((Subtype.val : U → M) ⁻¹' C))
    (r : ((actualSubspaceSheaf (n := n) C).presheaf.stalk ((actualOpenSubspaceMap (n := n) C U).base x)).carrier) :
    (actualOpenSubspaceMap (n := n) C U).stalkMap x r = actualOpenSubspaceStalkEquiv (n := n) C U x r := by
  obtain ⟨a,rfl⟩ := actualSubspaceInclusionRingedHom_stalk_surjective (n := n) C
    ((actualOpenSubspaceMap (n := n) C U).base x) r
  apply (actualSubspaceStalkChartEquiv (n := n) ((Subtype.val : U → M) ⁻¹' C) x).injective
  have h := ConcreteCategory.congr_hom
    (actualSubspaceRingedMap_stalk_square (f := (Subtype.val : U → M)) contMDiff_subtype_val
      (fun _ hx => hx) x) a
  simp only [ConcreteCategory.comp_apply] at h
  calc
    _ = actualSubspaceStalkChartEquiv (n := n) ((Subtype.val : U → M) ⁻¹' C) x
        ((actualSubspaceInclusion (n := n) ((Subtype.val : U → M) ⁻¹' C)).stalkMap x
          ((ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → M) contMDiff_subtype_val).stalkMap x.val a)) :=
      congrArg (actualSubspaceStalkChartEquiv (n := n) ((Subtype.val : U → M) ⁻¹' C) x) h
    _ = Ideal.Quotient.mk _ (actualStalkChartEquiv (n := n) x.val
        ((ChartedSpace.locallyRingedSpaceMap (Subtype.val : U → M) contMDiff_subtype_val).stalkMap x.val a)) :=
      inclusion_stalk_chart (n := n) ((Subtype.val : U → M) ⁻¹' C) x _
    _ = Ideal.Quotient.mk _ (actualStalkChartEquiv (n := n) x.val.val a) := by
      rw [actualNativeStalk_chart_pullback,actualHolomorphicGermPullback_val]
      rfl
    _ = _ := by
      simp only [actualOpenSubspaceStalkEquiv,RingEquiv.trans_apply,RingEquiv.apply_symm_apply]
      exact (congrArg (Ideal.quotEquivOfEq
        (wholeChartStalkIdeal_vanishing_actual_open (n := n) U C x.val).symm)
        (inclusion_stalk_chart (n := n) C ((actualOpenSubspaceMap (n := n) C U).base x) a)).symm

/-- The genuine original open-subspace map has isomorphic ENTIRE actual quotient stalks. -/
instance actualOpenSubspaceMap_stalk_isIso (x : ((Subtype.val : U → M) ⁻¹' C)) :
    IsIso ((actualOpenSubspaceMap (n := n) C U).stalkMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro a b hab
    apply (actualOpenSubspaceStalkEquiv (n := n) C U x).injective
    rw [← actualOpenSubspaceMap_stalk_apply,← actualOpenSubspaceMap_stalk_apply]
    exact hab
  · intro a
    obtain ⟨b,hb⟩ := (actualOpenSubspaceStalkEquiv (n := n) C U x).surjective a
    exact ⟨b,(actualOpenSubspaceMap_stalk_apply (n := n) C U x b).trans hb⟩

private def actualOpenSubspaceHomeomorph :
    ((Subtype.val : U → M) ⁻¹' C) ≃ₜ {x : C | x.val ∈ U} where
  toFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  invFun x := ⟨⟨x.val.val,x.property⟩,x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _).subtype_mk _

/-- The same actual quotient-subspace map is topologically an open embedding. -/
theorem actualOpenSubspaceMap_base_isOpenEmbedding :
    IsOpenEmbedding (actualOpenSubspaceMap (n := n) C U).base :=
  ((U.isOpen.preimage (continuous_subtype_val : Continuous (Subtype.val : C → M))).isOpenEmbedding_subtypeVal).comp
    (actualOpenSubspaceHomeomorph C U).isOpenEmbedding

/-- Actual whole quotient stalks and actual open topology internally prove the genuine open immersion. -/
instance actualOpenSubspaceMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (actualOpenSubspaceMap (n := n) C U) :=
  LocallyRingedSpace.IsOpenImmersion.of_stalk_iso (actualOpenSubspaceMap (n := n) C U)
    (actualOpenSubspaceMap_base_isOpenEmbedding (n := n) C U)

/-- The independently constructed actual quotient model is the true open restriction of the original model. -/
def actualOpenSubspaceRestrictionIso :
    actualSubspaceLocallyRingedSpace (n := n) ((Subtype.val : U → M) ⁻¹' C) ≅
      (actualSubspaceLocallyRingedSpace (n := n) C).restrict
        (actualOpenSubspaceMap_base_isOpenEmbedding (n := n) C U) :=
  LocallyRingedSpace.IsOpenImmersion.isoRestrict (actualOpenSubspaceMap (n := n) C U)

/-- Its actual restriction inclusion recovers the SAME original holomorphic quotient-subspace map. -/
theorem actualOpenSubspaceRestrictionIso_inclusion :
    (actualOpenSubspaceRestrictionIso (n := n) C U).hom ≫
        (actualSubspaceLocallyRingedSpace (n := n) C).ofRestrict
          (actualOpenSubspaceMap_base_isOpenEmbedding (n := n) C U) = actualOpenSubspaceMap (n := n) C U :=
  LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict (actualOpenSubspaceMap (n := n) C U)

end
end Hironaka.HironakaActualAnalyticSubspaceOpenRestriction
