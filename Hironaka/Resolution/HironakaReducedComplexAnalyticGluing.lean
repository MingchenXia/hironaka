/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hironaka contributors
-/
import Hironaka.Resolution.HironakaReducedComplexAnalyticSpaces
import Hironaka.Resolution.HironakaActualTwoModelAnalyticGlueData
import Mathlib.Geometry.RingedSpace.PresheafedSpace.Gluing

/-!
# Effective gluing of genuine reduced analytic local models over the complex point

Native locally ringed gluing constructs the scalar map, actual open charts
and effective map descent. Countable analytic pieces give second countability;
Hausdorffness is explicitly retained as the genuine topological gluing condition.
No resolution or centre-descent certificate is part of this construction.
Blueprint: `hironaka-reduced-complex-analytic-gluing-extension.tex`.
-/
set_option autoImplicit false
open Set TopologicalSpace Topology CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Hironaka.HironakaReducedComplexAnalyticGluing
noncomputable section
open HironakaReducedComplexAnalyticSpaces

variable (D : LocallyRingedSpace.GlueData)
  (σ : ∀ i : D.J,D.U i ⟶ complexPoint)
  (hσ : ∀ i j,D.f i j ≫ σ i=(D.t i j ≫ D.f j i) ≫ σ j)

/-- Native effective descent constructs the actual complex structural map. -/
def gluedPointMap : D.toGlueData.glued ⟶ complexPoint :=
  Multicoequalizer.desc D.toGlueData.diagram complexPoint σ (fun p => hσ p.1 p.2)

/-- Every actual chart retains its literal original complex structural map. -/
theorem gluedPointMap_ι (i : D.J) : D.toGlueData.ι i ≫ gluedPointMap D σ hσ=σ i :=
  Multicoequalizer.π_desc D.toGlueData.diagram complexPoint σ (fun p => hσ p.1 p.2) i

/-- The structural map is unique by the genuine native gluing universal property. -/
theorem gluedPointMap_unique (f : D.toGlueData.glued ⟶ complexPoint)
    (hf : ∀ i,D.toGlueData.ι i ≫ f=σ i) : f=gluedPointMap D σ hσ := by
  apply Multicoequalizer.hom_ext D.toGlueData.diagram
  intro i
  exact (hf i).trans (gluedPointMap_ι D σ hσ i).symm

variable (hA : ∀ i,hasAnalyticCharts (Over.mk (σ i)))
include hA

/-- Countably many genuine analytic open chart images give a countable basis. -/
theorem secondCountable_glued [Countable D.J] : SecondCountableTopology D.toGlueData.glued := by
  let : ∀ i : D.J,SecondCountableTopology (D.U i) := fun i => (hA i).2.1
  let R : D.J → Set D.toGlueData.glued := fun i => range (D.toGlueData.ι i).base
  have hopen (i : D.J) : IsOpenEmbedding (D.toGlueData.ι i).base :=
    (inferInstance : LocallyRingedSpace.IsOpenImmersion (D.toGlueData.ι i)).base_open
  let : ∀ i : D.J,SecondCountableTopology (R i) := fun i => by
    let : SecondCountableTopology (D.U i).toPresheafedSpace := (hA i).2.1
    exact (hopen i).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  apply secondCountableTopology_of_countable_cover (U := R) (fun i => (hopen i).isOpen_range)
  apply iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨i,y,hy⟩ := D.ι_jointly_surjective x
  exact ⟨i,y,hy⟩

/-- Genuine local model charts compose with actual native chart inclusions. -/
theorem hasAnalyticCharts_glued [Countable D.J] [T2Space D.toGlueData.glued] :
    hasAnalyticCharts (Over.mk (gluedPointMap D σ hσ)) := by
  refine ⟨?_,?_,?_⟩
  · change T2Space D.toGlueData.glued
    infer_instance
  · change SecondCountableTopology D.toGlueData.glued
    exact secondCountable_glued D σ hA
  · intro x
    obtain ⟨i,y,rfl⟩ := D.ι_jointly_surjective x
    obtain ⟨n,U,C,hC,j,hj,hpoint,c,hc⟩ := (hA i).2.2 y
    let : LocallyRingedSpace.IsOpenImmersion j := hj
    refine ⟨n,U,C,hC,j ≫ D.toGlueData.ι i,inferInstance,?_,?_⟩
    · change (j ≫ D.toGlueData.ι i) ≫ gluedPointMap D σ hσ=(modelOver U C).hom
      rw [Category.assoc,gluedPointMap_ι]
      exact hpoint
    · refine ⟨c,?_⟩
      change (D.toGlueData.ι i).base (j.base c)=(D.toGlueData.ι i).base y
      exact congrArg (D.toGlueData.ι i).base hc

/-- The internally constructed actual glued object of the analytic category. -/
def gluedAnalyticSpace [Countable D.J] [T2Space D.toGlueData.glued] : ReducedComplexAnalyticSpace :=
  ⟨Over.mk (gluedPointMap D σ hσ),hasAnalyticCharts_glued D σ hσ hA⟩

/-- The original native chart inclusion is a genuine complex-structural analytic morphism. -/
def gluedChartMap [Countable D.J] [T2Space D.toGlueData.glued] (i : D.J) :
    (⟨Over.mk (σ i),hA i⟩ : ReducedComplexAnalyticSpace) ⟶ gluedAnalyticSpace D σ hσ hA :=
  ObjectProperty.homMk (Over.homMk (D.toGlueData.ι i) (gluedPointMap_ι D σ hσ i))

/-- Actual open-immersion charts cover the entire constructed analytic object. -/
theorem gluedChartMaps_properties [Countable D.J] [T2Space D.toGlueData.glued] :
    (∀ i : D.J,LocallyRingedSpace.IsOpenImmersion (gluedChartMap D σ hσ hA i).hom.left) ∧
      ∀ x : (gluedAnalyticSpace D σ hσ hA).obj.left,
        ∃ (i : D.J) (y : D.U i),(gluedChartMap D σ hσ hA i).hom.left.base y=x := by
  refine ⟨?_,D.ι_jointly_surjective⟩
  intro i
  change LocallyRingedSpace.IsOpenImmersion (D.toGlueData.ι i)
  infer_instance

/-- Actual compatible piece maps descend to a genuine analytic morphism, with no global map input. -/
def gluedAnalyticMap [Countable D.J] [T2Space D.toGlueData.glued]
    (X : ReducedComplexAnalyticSpace) (f : ∀ i,D.U i ⟶ X.obj.left)
    (hf : ∀ i j,D.f i j ≫ f i=(D.t i j ≫ D.f j i) ≫ f j)
    (hp : ∀ i,f i ≫ X.obj.hom=σ i) : gluedAnalyticSpace D σ hσ hA ⟶ X :=
  ObjectProperty.homMk (Over.homMk
    (Multicoequalizer.desc D.toGlueData.diagram X.obj.left f (fun p => hf p.1 p.2)) (by
      apply Multicoequalizer.hom_ext D.toGlueData.diagram
      intro i
      change D.toGlueData.ι i ≫
        (Multicoequalizer.desc D.toGlueData.diagram X.obj.left f (fun p => hf p.1 p.2) ≫
          X.obj.hom)=D.toGlueData.ι i ≫ gluedPointMap D σ hσ
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (fun k : D.U i ⟶ X.obj.left => k ≫ X.obj.hom)
          (Multicoequalizer.π_desc D.toGlueData.diagram X.obj.left f
            (fun p => hf p.1 p.2) i)).trans
          ((hp i).trans (gluedPointMap_ι D σ hσ i).symm))))

/-- The constructed analytic map is the unique map with the genuine prescribed chart restrictions. -/
theorem exists_unique_glued_analytic_map [Countable D.J] [T2Space D.toGlueData.glued]
    (X : ReducedComplexAnalyticSpace) (f : ∀ i,D.U i ⟶ X.obj.left)
    (hf : ∀ i j,D.f i j ≫ f i=(D.t i j ≫ D.f j i) ≫ f j)
    (hp : ∀ i,f i ≫ X.obj.hom=σ i) :
    ∃! F : gluedAnalyticSpace D σ hσ hA ⟶ X,
      ∀ i,D.toGlueData.ι i ≫ F.hom.left=f i := by
  refine ⟨gluedAnalyticMap D σ hσ hA X f hf hp,?_,?_⟩
  · intro i
    exact Multicoequalizer.π_desc D.toGlueData.diagram X.obj.left f (fun p => hf p.1 p.2) i
  · intro G hG
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply Multicoequalizer.hom_ext D.toGlueData.diagram
    intro i
    exact (hG i).trans (Multicoequalizer.π_desc D.toGlueData.diagram X.obj.left f (fun p => hf p.1 p.2) i).symm

omit hA
section OriginalTwoModels
open HironakaActualTwoModelAnalyticGlueData

variable (A : ActualTwoModelHolomorphicOverlaps)
  [T2Space (actualTwoModelGlueData A).toGlueData.glued]

local instance : Countable (actualTwoModelGlueData A).J := by
  change Countable Bool
  infer_instance

/-- Ordinary original two-model data internally construct the actual analytic object. -/
def actualTwoModelAnalyticSpace : ReducedComplexAnalyticSpace :=
  gluedAnalyticSpace (actualTwoModelGlueData A) (actualChartPointMap A)
    (fun i j => (actualTwoModelGlueData_point_compatible A i j).trans (Category.assoc _ _ _).symm)
    (fun i => hasAnalyticCharts_model (A.domain i) (A.carrier i) (A.analytic i))

/-- Each unchanged original model is a genuine analytic chart of the constructed object. -/
def actualTwoModelChartMap (i : Bool) :
    embeddedModel (A.domain i) (A.carrier i) (A.analytic i) ⟶ actualTwoModelAnalyticSpace A :=
  gluedChartMap (actualTwoModelGlueData A) (actualChartPointMap A)
    (fun i j => (actualTwoModelGlueData_point_compatible A i j).trans (Category.assoc _ _ _).symm)
    (fun i => hasAnalyticCharts_model (A.domain i) (A.carrier i) (A.analytic i)) i

/-- The actual native object and original chart inclusions retain whole-space open coverage. -/
theorem actualTwoModelChartMap_properties :
    (actualTwoModelAnalyticSpace A).obj.left=(actualTwoModelGlueData A).toGlueData.glued ∧
      (∀ i : Bool,(actualTwoModelChartMap A i).hom.left=(actualTwoModelGlueData A).toGlueData.ι i) ∧
      (∀ i : Bool,LocallyRingedSpace.IsOpenImmersion (actualTwoModelChartMap A i).hom.left) ∧
      ∀ x : (actualTwoModelAnalyticSpace A).obj.left,
        ∃ (i : Bool) (y : actualChartModel A i),(actualTwoModelChartMap A i).hom.left.base y=x := by
  refine ⟨rfl,fun _ => rfl,?_,(actualTwoModelGlueData A).ι_jointly_surjective⟩
  intro i
  change LocallyRingedSpace.IsOpenImmersion ((actualTwoModelGlueData A).toGlueData.ι i)
  exact LocallyRingedSpace.GlueData.ι_isOpenImmersion (actualTwoModelGlueData A) i

end OriginalTwoModels

end
end Hironaka.HironakaReducedComplexAnalyticGluing
