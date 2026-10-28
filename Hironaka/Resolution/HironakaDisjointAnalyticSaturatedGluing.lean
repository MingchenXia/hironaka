/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaReducedComplexAnalyticGluing
/-! Actual Hausdorff, second-countable native analytic gluing over a common
Hausdorff base with genuine saturated overlap windows. Existing native
GlueData and conditional analytic-space construction are consumed unchanged.
No glued T2, desired analytic object or canonical comparison is input.
Complete mathematical blueprint preceded the first scratch. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Hironaka.HironakaDisjointAnalyticSaturatedGluing
noncomputable section
open HironakaActualTwoModelAnalyticGlueData HironakaReducedComplexAnalyticSpaces

structure SaturatedBase (A : ActualTwoModelHolomorphicOverlaps) (X : Type) [TopologicalSpace X] where
  window : Bool → Opens X
  project : (i : Bool) → A.carrier i → X
  continuous_project : ∀ i, Continuous (project i)
  lands : ∀ i (x : A.carrier i), project i x ∈ window i
  overlap_iff : ∀ i j, i≠j → ∀ x : A.carrier i,
    x.val∈A.overlap i j ↔ project i x∈window j
  compatible : ∀ i j (hij : i≠j) (z : A.overlap i j) (hz : z.val∈A.carrier i),
    project j ⟨(A.transition i j z).val,A.mapsTo i j hij z hz⟩=project i ⟨z.val,hz⟩

variable (A : ActualTwoModelHolomorphicOverlaps)

abbrev topData : TopCat.GlueData :=
  (actualTwoModelGlueData A).toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toTopGlueData

abbrev gluedTop : TopCat := (topData A).toGlueData.glued
abbrev chartMap (i : Bool) : TopCat.of (A.carrier i) ⟶ gluedTop A := (topData A).toGlueData.ι i

variable {X : Type} [TopologicalSpace X] (B : SaturatedBase A X)

private def projectMap (i : Bool) : TopCat.of (A.carrier i) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨B.project i,B.continuous_project i⟩

private theorem project_compatible (ij : Bool×Bool) :
    (topData A).toGlueData.diagram.fst ij ≫ projectMap A B ij.1=
      (topData A).toGlueData.diagram.snd ij ≫ projectMap A B ij.2 := by
  rcases ij with ⟨i,j⟩
  cases i <;> cases j
  all_goals
    simp only [topData,actualTwoModelGlueData,CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f',actualTwoModelOffDiagonalGlueData,projectMap,
      CategoryTheory.GlueData.diagram,CategoryTheory.GlueData.mapGlueData,
      Bool.false_eq_true,Bool.true_eq_false,not_false_eq_true,dif_pos,dif_neg]
  all_goals
    simp only [Functor.map_comp,eqToHom_map,Category.assoc,eqToHom_trans_assoc,
      eqToHom_refl,Category.id_comp]
  all_goals try rw [cancel_epi]
  all_goals ext z
  all_goals try rfl
  · exact (B.compatible false true (by decide) z.val z.property).symm
  · exact (B.compatible true false (by decide) z.val z.property).symm

def gluedProjection : gluedTop A ⟶ TopCat.of X :=
  Multicoequalizer.desc (topData A).toGlueData.diagram (TopCat.of X)
    (projectMap A B) (project_compatible A B)

private theorem chart_projection (i : Bool) : chartMap A i ≫ gluedProjection A B=projectMap A B i :=
  Multicoequalizer.π_desc (topData A).toGlueData.diagram (TopCat.of X)
    (projectMap A B) (project_compatible A B) i

theorem projection_chart (i : Bool) (x : A.carrier i) :
    gluedProjection A B (chartMap A i x)=B.project i x :=
  ConcreteCategory.congr_hom (chart_projection A B i) x

private theorem transition_chart (i j : Bool) (hij : i≠j)
    (z : A.overlap i j) (hz : z.val∈A.carrier i) :
    chartMap A i ⟨z.val,hz⟩=
      chartMap A j ⟨(A.transition i j z).val,A.mapsTo i j hij z hz⟩ := by
  have h:=(topData A).toGlueData.glue_condition i j
  cases i <;> cases j
  all_goals try exact (hij rfl).elim
  all_goals
    simp only [topData,actualTwoModelGlueData,CategoryTheory.GlueData.ofGlueData',
      CategoryTheory.GlueData'.f',actualTwoModelOffDiagonalGlueData,
      CategoryTheory.GlueData.mapGlueData,Bool.false_eq_true,Bool.true_eq_false,
      not_false_eq_true,dif_neg,Functor.map_comp,eqToHom_map,Category.assoc,
      eqToHom_trans_assoc,eqToHom_refl,Category.id_comp] at h
    rw [cancel_epi] at h
    exact (ConcreteCategory.congr_hom h ⟨z,hz⟩).symm

theorem chart_range_saturated (i : Bool) :
    Set.range (chartMap A i)=gluedProjection A B ⁻¹' (B.window i : Set X) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    change gluedProjection A B (chartMap A i y)∈B.window i
    rw [projection_chart]
    exact B.lands i y
  · intro hx
    obtain ⟨j,y,rfl⟩:=(topData A).ι_jointly_surjective x
    by_cases hji : j=i
    · subst j
      exact ⟨y,rfl⟩
    · have hy : y.val∈A.overlap j i := (B.overlap_iff j i hji y).mpr
        (by
          change gluedProjection A B (chartMap A j y)∈B.window i at hx
          rwa [projection_chart] at hx)
      refine ⟨⟨(A.transition j i ⟨y.val,hy⟩).val,A.mapsTo j i hji _ y.property⟩,?_⟩
      exact (transition_chart A j i hji ⟨y.val,hy⟩ y.property).symm

include B in
theorem gluedTop_t2 [T2Space X] : T2Space (gluedTop A) := by
  constructor
  intro x y hxy
  by_cases he : gluedProjection A B x=gluedProjection A B y
  · obtain ⟨i,z,rfl⟩:=(topData A).ι_jointly_surjective x
    have hy : y∈Set.range (chartMap A i) := by
      rw [chart_range_saturated A B i]
      change gluedProjection A B y∈B.window i
      rw [←he]
      exact (projection_chart A B i z) ▸ B.lands i z
    obtain ⟨w,rfl⟩:=hy
    have hzw : z≠w := fun h => hxy (congrArg (chartMap A i) h)
    have : T2Space ((topData A).U i) := by
      change T2Space (A.carrier i)
      infer_instance
    obtain ⟨S,T,hS,hT,hz,hw,hST⟩:=t2_separation hzw
    have hι:=(topData A).ι_isOpenEmbedding i
    refine ⟨chartMap A i '' S,chartMap A i '' T,hι.isOpenMap _ hS,hι.isOpenMap _ hT,
      ⟨z,hz,rfl⟩,⟨w,hw,rfl⟩,?_⟩
    apply Set.disjoint_left.mpr
    rintro q ⟨a,ha,rfl⟩ ⟨b,hb,hba⟩
    exact Set.disjoint_left.mp hST ha (hι.injective hba ▸ hb)
  · obtain ⟨S,T,hS,hT,hx,hy,hST⟩:=t2_separation he
    refine ⟨gluedProjection A B ⁻¹' S,gluedProjection A B ⁻¹' T,
      hS.preimage (gluedProjection A B).hom.continuous,hT.preimage (gluedProjection A B).hom.continuous,
      hx,hy,?_⟩
    exact Set.disjoint_left.mpr fun z hzS hzT => Set.disjoint_left.mp hST hzS hzT

theorem gluedTop_secondCountable : SecondCountableTopology (gluedTop A) := by
  let q : (Σi : Bool,A.carrier i) → gluedTop A := fun z => chartMap A z.1 z.2
  have hq : Continuous q := continuous_sigma fun i => (chartMap A i).hom.continuous
  have ho : IsOpenMap q := isOpenMap_sigma.mpr fun i => ((topData A).ι_isOpenEmbedding i).isOpenMap
  have hs : Function.Surjective q := by
    intro x
    obtain ⟨i,y,h⟩:=(topData A).ι_jointly_surjective x
    exact ⟨⟨i,y⟩,h⟩
  exact (ho.isQuotientMap hq hs).secondCountableTopology ho

def overlapGraph (i j : Bool) : Set ((A.carrier i)×(A.carrier j)) :=
  {z | ∃ h : z.1.val∈A.overlap i j, (A.transition i j ⟨z.1.val,h⟩).val=z.2.val}

include B in
theorem overlapGraph_eq_equalizer (i j : Bool) (hij : i≠j) :
    overlapGraph A i j={z | chartMap A i z.1=chartMap A j z.2} := by
  ext z
  constructor
  · rintro ⟨h,he⟩
    have ht:=transition_chart A i j hij ⟨z.1.val,h⟩ z.1.property
    have he' : (⟨(A.transition i j ⟨z.1.val,h⟩).val,A.mapsTo i j hij _ z.1.property⟩ : A.carrier j)=z.2 :=
      Subtype.ext he
    rw [he'] at ht
    exact ht
  · intro he
    have hp:=congrArg (gluedProjection A B) he
    rw [projection_chart,projection_chart] at hp
    have hx : z.1.val∈A.overlap i j := (B.overlap_iff i j hij z.1).mpr
      (hp.symm ▸ B.lands j z.2)
    refine ⟨hx,?_⟩
    have ht:=transition_chart A i j hij ⟨z.1.val,hx⟩ z.1.property
    have hy := ((topData A).ι_injective j) (ht.symm.trans he)
    exact congrArg Subtype.val hy

include B in
theorem overlapGraph_isClosed [T2Space X] (i j : Bool) (hij : i≠j) :
    IsClosed (overlapGraph A i j) := by
  have := gluedTop_t2 A B
  rw [overlapGraph_eq_equalizer A B i j hij]
  exact isClosed_eq ((chartMap A i).hom.continuous.comp continuous_fst)
    ((chartMap A j).hom.continuous.comp continuous_snd)

abbrev gluedNative : LocallyRingedSpace := (actualTwoModelGlueData A).toGlueData.glued

def underlyingGluingIso : LocallyRingedSpace.forgetToTop.obj (gluedNative A) ≅ gluedTop A := by
  let D := (actualTwoModelGlueData A).toSheafedSpaceGlueData.toPresheafedSpaceGlueData
  letI (i j k : D.J) : PreservesLimit (cospan (D.f i j) (D.f i k)) (PresheafedSpace.forget CommRingCat) := by
    have : PresheafedSpace.IsOpenImmersion (D.f i j) := D.f_open i j
    infer_instance
  exact ((SheafedSpace.forget CommRingCat).mapIso (actualTwoModelGlueData A).isoSheafedSpace).trans
    (((PresheafedSpace.forget CommRingCat).mapIso
      (actualTwoModelGlueData A).toSheafedSpaceGlueData.isoPresheafedSpace).trans
      ((actualTwoModelGlueData A).toSheafedSpaceGlueData.toPresheafedSpaceGlueData.toGlueData.gluedIso
        (PresheafedSpace.forget CommRingCat)))

def underlyingGluingHomeomorph : gluedNative A ≃ₜ gluedTop A :=
  TopCat.homeoOfIso (underlyingGluingIso A)

include B in
theorem gluedNative_t2 [T2Space X] : T2Space (gluedNative A) := by
  have := gluedTop_t2 A B
  exact (underlyingGluingHomeomorph A).isEmbedding.t2Space

theorem gluedNative_secondCountable : SecondCountableTopology (gluedNative A) := by
  have := gluedTop_secondCountable A
  exact (underlyingGluingHomeomorph A).isEmbedding.secondCountableTopology

open HironakaReducedComplexAnalyticGluing

def actualSaturatedAnalyticSpace [T2Space X] : ReducedComplexAnalyticSpace := by
  have := gluedNative_t2 A B
  exact actualTwoModelAnalyticSpace A

def actualSaturatedChartMap [T2Space X] (i : Bool) :
    embeddedModel (A.domain i) (A.carrier i) (A.analytic i) ⟶ actualSaturatedAnalyticSpace A B := by
  have := gluedNative_t2 A B
  exact actualTwoModelChartMap A i

theorem actualSaturatedChartMap_properties [T2Space X] :
    (actualSaturatedAnalyticSpace A B).obj.left=gluedNative A ∧
    (∀ i : Bool,(actualSaturatedChartMap A B i).hom.left=(actualTwoModelGlueData A).toGlueData.ι i) ∧
    (∀ i : Bool,LocallyRingedSpace.IsOpenImmersion (actualSaturatedChartMap A B i).hom.left) ∧
    ∀ x : (actualSaturatedAnalyticSpace A B).obj.left,
      ∃ (i : Bool) (y : A.carrier i),(actualSaturatedChartMap A B i).hom.left.base y=x := by
  have := gluedNative_t2 A B
  exact actualTwoModelChartMap_properties A

end
end Hironaka.HironakaDisjointAnalyticSaturatedGluing
