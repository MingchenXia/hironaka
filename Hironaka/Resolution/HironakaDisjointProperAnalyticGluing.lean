/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaDisjointAnalyticSaturatedGluing
import Mathlib.Topology.Maps.Proper.Basic
/-! Actual local properness descends from the genuine window-corestricted
maps through the unchanged saturated analytic gluing. Whole image/fibre
identities construct global closedness and compact fibres. Compatible original
analytic piece maps construct a genuine proper descended analytic morphism.
No global properness, global morphism or canonical comparison is an input.
Complete mathematical blueprint preceded the first scratch. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Hironaka.HironakaDisjointProperAnalyticGluing
noncomputable section
open HironakaActualTwoModelAnalyticGlueData HironakaReducedComplexAnalyticSpaces
 HironakaDisjointAnalyticSaturatedGluing
variable (A : ActualTwoModelHolomorphicOverlaps) {X : Type} [TopologicalSpace X]
 (B : SaturatedBase A X)

def windowProjection (i : Bool) : A.carrier i → B.window i :=
  fun z => ⟨B.project i z,B.lands i z⟩

theorem windowProjection_continuous (i : Bool) : Continuous (windowProjection A B i) :=
  (B.continuous_project i).subtype_mk _

theorem window_image_dictionary (i : Bool) (S : Set (gluedTop A)) :
    (Subtype.val : B.window i→X) ⁻¹' (gluedProjection A B '' S)=
      windowProjection A B i '' ((chartMap A i) ⁻¹' S) := by
  ext y
  constructor
  · rintro ⟨z,hz,hzy⟩
    have hr : z∈range (chartMap A i) := by
      rw [chart_range_saturated A B i]
      change gluedProjection A B z∈B.window i
      rw [hzy]
      exact y.property
    obtain ⟨a,rfl⟩:=hr
    exact ⟨a,hz,Subtype.ext ((projection_chart A B i a).symm.trans hzy)⟩
  · rintro ⟨a,ha,hay⟩
    refine ⟨chartMap A i a,ha,?_⟩
    rw [projection_chart]
    exact congrArg Subtype.val hay

theorem fibre_dictionary (i : Bool) (x : X) (hx : x∈B.window i) :
    gluedProjection A B ⁻¹' {x}=
      chartMap A i '' (windowProjection A B i ⁻¹' {(⟨x,hx⟩ : B.window i)}) := by
  ext z
  constructor
  · intro hz
    have hp : gluedProjection A B z=x := hz
    have hr : z∈range (chartMap A i) := by
      rw [chart_range_saturated A B i]
      change gluedProjection A B z∈B.window i
      rwa [hp]
    obtain ⟨a,rfl⟩:=hr
    refine ⟨a,?_,rfl⟩
    apply Subtype.ext
    exact (projection_chart A B i a).symm.trans hp
  · rintro ⟨a,ha,rfl⟩
    have hp : windowProjection A B i a=(⟨x,hx⟩ : B.window i) := ha
    change gluedProjection A B (chartMap A i a)=x
    rw [projection_chart]
    exact congrArg Subtype.val hp

theorem gluedProjection_isClosedMap
    (hcover : ∀x : X,∃i : Bool,x∈B.window i)
    (hproper : ∀i : Bool,IsProperMap (windowProjection A B i)) :
    IsClosedMap (gluedProjection A B) := by
  intro S hS
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨i,hi⟩:=hcover x
  have hclosed : IsClosed ((Subtype.val : B.window i→X) ⁻¹' (gluedProjection A B '' S)) := by
    rw [window_image_dictionary A B i S]
    exact (hproper i).isClosedMap _ (hS.preimage (chartMap A i).hom.continuous)
  let V : Set (B.window i) := ((Subtype.val : B.window i→X) ⁻¹' (gluedProjection A B '' S))ᶜ
  have hV : IsOpen V := hclosed.isOpen_compl
  have hVO : IsOpen ((Subtype.val : B.window i→X) '' V) :=
    (B.window i).isOpen.isOpenMap_subtype_val _ hV
  have hxV : x∈(Subtype.val : B.window i→X) '' V := ⟨⟨x,hi⟩,hx,rfl⟩
  apply Filter.mem_of_superset (hVO.mem_nhds hxV)
  rintro y ⟨z,hz,rfl⟩
  exact hz

theorem gluedProjection_compact_fibres
    (hcover : ∀x : X,∃i : Bool,x∈B.window i)
    (hproper : ∀i : Bool,IsProperMap (windowProjection A B i)) (x : X) :
    IsCompact (gluedProjection A B ⁻¹' {x}) := by
  obtain ⟨i,hi⟩:=hcover x
  rw [fibre_dictionary A B i x hi]
  exact ((hproper i).isCompact_preimage isCompact_singleton).image (chartMap A i).hom.continuous

theorem gluedProjection_isProper
    (hcover : ∀x : X,∃i : Bool,x∈B.window i)
    (hproper : ∀i : Bool,IsProperMap (windowProjection A B i)) :
    IsProperMap (gluedProjection A B) :=
  isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨(gluedProjection A B).hom.continuous,gluedProjection_isClosedMap A B hcover hproper,
      gluedProjection_compact_fibres A B hcover hproper⟩

def nativeProjection : gluedNative A → X :=
  gluedProjection A B ∘ underlyingGluingHomeomorph A

theorem nativeProjection_isProper
    (hcover : ∀x : X,∃i : Bool,x∈B.window i)
    (hproper : ∀i : Bool,IsProperMap (windowProjection A B i)) :
    IsProperMap (nativeProjection A B) :=
  (gluedProjection_isProper A B hcover hproper).comp (underlyingGluingHomeomorph A).isProperMap
theorem native_chart_homeomorph (i : Bool) (x : A.carrier i) :
    underlyingGluingHomeomorph A (((actualTwoModelGlueData A).toGlueData.ι i).base x)=
      chartMap A i x := by
  let D := actualTwoModelGlueData A
  let D1 := D.toSheafedSpaceGlueData
  let D2 := D1.toPresheafedSpaceGlueData
  let (i j k : D2.J) : PreservesLimit (cospan (D2.f i j) (D2.f i k))
      (PresheafedSpace.forget CommRingCat) := by
    have : PresheafedSpace.IsOpenImmersion (D2.f i j) := D2.f_open i j
    infer_instance
  have h1 : (D.toGlueData.ι i).toShHom ≫ D.isoSheafedSpace.hom=D1.toGlueData.ι i := by
    rw [←D.ι_isoSheafedSpace_inv i,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  have h2 : (D1.toGlueData.ι i).hom ≫ D1.isoPresheafedSpace.hom=D2.toGlueData.ι i := by
    rw [←D1.ι_isoPresheafedSpace_inv i,Category.assoc,Iso.inv_hom_id,Category.comp_id]
  have h1t : LocallyRingedSpace.forgetToTop.map (D.toGlueData.ι i) ≫
      (SheafedSpace.forget CommRingCat).map D.isoSheafedSpace.hom=
      (SheafedSpace.forget CommRingCat).map (D1.toGlueData.ι i) := by
    change (SheafedSpace.forget CommRingCat).map (D.toGlueData.ι i).toShHom ≫ _=_
    rw [←Functor.map_comp,h1]
  have h2t : (SheafedSpace.forget CommRingCat).map (D1.toGlueData.ι i) ≫
      (PresheafedSpace.forget CommRingCat).map D1.isoPresheafedSpace.hom=
      (PresheafedSpace.forget CommRingCat).map (D2.toGlueData.ι i) := by
    change (PresheafedSpace.forget CommRingCat).map (D1.toGlueData.ι i).hom ≫ _=_
    rw [←Functor.map_comp,h2]
  have ht : LocallyRingedSpace.forgetToTop.map (D.toGlueData.ι i) ≫
      (underlyingGluingIso A).hom=chartMap A i := by
    change _ ≫ ((SheafedSpace.forget CommRingCat).map D.isoSheafedSpace.hom ≫
      ((PresheafedSpace.forget CommRingCat).map D1.isoPresheafedSpace.hom ≫
        (D2.toGlueData.gluedIso (PresheafedSpace.forget CommRingCat)).hom))=_
    rw [←Category.assoc,h1t,←Category.assoc,h2t]
    exact D2.toGlueData.ι_gluedIso_hom (PresheafedSpace.forget CommRingCat) i
  exact ConcreteCategory.congr_hom ht x

theorem nativeProjection_chart (i : Bool) (x : A.carrier i) :
    nativeProjection A B (((actualTwoModelGlueData A).toGlueData.ι i).base x)=B.project i x := by
  unfold nativeProjection
  rw [Function.comp_apply,native_chart_homeomorph,projection_chart]

section Analytic
open HironakaReducedComplexAnalyticGluing
local instance chartIndex_countable : Countable (actualTwoModelGlueData A).J := by
  change Countable Bool
  infer_instance

local instance analyticTarget_t2 (Q : ReducedComplexAnalyticSpace) : T2Space Q.obj.left := Q.property.1

variable (Q : ReducedComplexAnalyticSpace) (BQ : SaturatedBase A Q.obj.left)
 (f : ∀i : Bool,actualChartModel A i ⟶ Q.obj.left)
 (hf : ∀i j,(actualTwoModelGlueData A).f i j ≫ f i=
   ((actualTwoModelGlueData A).t i j ≫ (actualTwoModelGlueData A).f j i) ≫ f j)
 (hp : ∀i,f i ≫ Q.obj.hom=actualChartPointMap A i)

def descendedMap : actualSaturatedAnalyticSpace A BQ ⟶ Q := by
  have := gluedNative_t2 A BQ
  exact gluedAnalyticMap (actualTwoModelGlueData A) (actualChartPointMap A)
    (fun i j => (actualTwoModelGlueData_point_compatible A i j).trans (Category.assoc _ _ _).symm)
    (fun i => hasAnalyticCharts_model (A.domain i) (A.carrier i) (A.analytic i)) Q f hf hp

theorem descendedMap_chart (i : Bool) :
    (actualTwoModelGlueData A).toGlueData.ι i ≫ (descendedMap A Q BQ f hf hp).hom.left=f i := by
  have := gluedNative_t2 A BQ
  exact Multicoequalizer.π_desc (actualTwoModelGlueData A).toGlueData.diagram Q.obj.left f
    (fun ij => hf ij.1 ij.2) i

theorem descendedMap_base_eq
    (hbase : ∀i (x : A.carrier i),(f i).base x=BQ.project i x) :
    (fun x => (descendedMap A Q BQ f hf hp).hom.left.base x)=nativeProjection A BQ := by
  funext x
  obtain ⟨i,y,rfl⟩:=(actualTwoModelGlueData A).ι_jointly_surjective x
  have h:=congrArg (fun g : actualChartModel A i ⟶ Q.obj.left => g.base y)
    (descendedMap_chart A Q BQ f hf hp i)
  exact h.trans ((hbase i y).trans (nativeProjection_chart A BQ i y).symm)

theorem descendedMap_isProper
    (hbase : ∀i (x : A.carrier i),(f i).base x=BQ.project i x)
    (hcover : ∀x : Q.obj.left,∃i : Bool,x∈BQ.window i)
    (hproper : ∀i : Bool,IsProperMap (windowProjection A BQ i)) :
    IsProperMap (descendedMap A Q BQ f hf hp).hom.left.base := by
  change IsProperMap (fun x => (descendedMap A Q BQ f hf hp).hom.left.base x)
  rw [descendedMap_base_eq A Q BQ f hf hp hbase]
  exact nativeProjection_isProper A BQ hcover hproper

include hf hp in
theorem exists_actual_proper_analytic_map
    (hbase : ∀i (x : A.carrier i),(f i).base x=BQ.project i x)
    (hcover : ∀x : Q.obj.left,∃i : Bool,x∈BQ.window i)
    (hproper : ∀i : Bool,IsProperMap (windowProjection A BQ i)) :
    ∃ F : actualSaturatedAnalyticSpace A BQ ⟶ Q,
      (∀i : Bool,(actualTwoModelGlueData A).toGlueData.ι i ≫ F.hom.left=f i) ∧
      IsProperMap F.hom.left.base :=
  ⟨descendedMap A Q BQ f hf hp,descendedMap_chart A Q BQ f hf hp,
    descendedMap_isProper A Q BQ f hf hp hbase hcover hproper⟩
end Analytic

end
end Hironaka.HironakaDisjointProperAnalyticGluing
